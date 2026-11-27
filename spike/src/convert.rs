//! Schema-directed conversion of Kubernetes object JSON to Cedar attribute JSON (R-8, R-13 seed).
//!
//! The type environment is read from the Cedar schema itself (`SchemaFragment::to_json_value`),
//! so the converter and the schema cannot drift. Undeclared object fields are dropped and
//! recorded (policies cannot see them); a declared field of the wrong JSON type is an error
//! (fail closed in the caller).
use serde_json::{json, Map, Value};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Str,
    Long,
    Bool,
    Set(Box<Ty>),
    Rec { attrs: Vec<(String, Ty, bool)>, open: bool },
}

#[derive(Debug, Default, Clone)]
pub struct ConvStats {
    /// JSON paths of object fields that the schema does not declare (dropped).
    pub dropped: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConvError(pub String);
impl std::fmt::Display for ConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.0) }
}

pub struct TypeEnv {
    /// fully qualified common type name -> schema JSON node
    common: HashMap<String, Value>,
    /// fully qualified entity type name -> shape node
    entities: HashMap<String, Value>,
}

impl TypeEnv {
    pub fn from_schema_json(v: &Value) -> Self {
        let mut common = HashMap::new();
        let mut entities = HashMap::new();
        for (ns, body) in v.as_object().expect("schema json") {
            let q = |n: &str| if ns.is_empty() { n.to_string() } else { format!("{ns}::{n}") };
            if let Some(c) = body.get("commonTypes").and_then(|c| c.as_object()) {
                for (n, t) in c { common.insert(q(n), t.clone()); }
            }
            if let Some(e) = body.get("entityTypes").and_then(|c| c.as_object()) {
                for (n, t) in e { entities.insert(q(n), t["shape"].clone()); }
            }
        }
        TypeEnv { common, entities }
    }

    fn resolve(&self, node: &Value, ns: &str) -> Result<Ty, ConvError> {
        let ty = node["type"].as_str().ok_or_else(|| ConvError(format!("untyped node {node}")))?;
        match ty {
            "String" => Ok(Ty::Str),
            "Long" => Ok(Ty::Long),
            "Boolean" | "Bool" => Ok(Ty::Bool),
            "Set" => Ok(Ty::Set(Box::new(self.resolve(&node["element"], ns)?))),
            "Record" => {
                let mut attrs = Vec::new();
                if let Some(a) = node["attributes"].as_object() {
                    for (k, v) in a {
                        let req = v.get("required").and_then(|r| r.as_bool()).unwrap_or(true);
                        attrs.push((k.clone(), self.resolve(v, ns)?, req));
                    }
                }
                Ok(Ty::Rec { attrs, open: node["additionalAttributes"].as_bool().unwrap_or(false) })
            }
            "EntityOrCommon" | "Entity" | "CommonType" => {
                let name = node["name"].as_str().ok_or_else(|| ConvError("no name".into()))?;
                match name {
                    "String" => return Ok(Ty::Str),
                    "Long" => return Ok(Ty::Long),
                    "Bool" | "Boolean" => return Ok(Ty::Bool),
                    _ => {}
                }
                let local = if ns.is_empty() { name.to_string() } else { format!("{ns}::{name}") };
                let (qn, t) = if let Some(t) = self.common.get(&local) { (local, t) }
                    else if let Some(t) = self.common.get(name) { (name.to_string(), t) }
                    else { return Err(ConvError(format!("cannot resolve type {name}"))) };
                let ns2 = qn.rsplit_once("::").map(|(a, _)| a).unwrap_or("").to_string();
                self.resolve(t, &ns2)
            }
            other => Err(ConvError(format!("unsupported schema type {other}"))),
        }
    }

    /// Attribute types of entity type `ety` (fully qualified), e.g. `core::ConfigMap`.
    pub fn entity_shape(&self, ety: &str) -> Result<Ty, ConvError> {
        let shape = self.entities.get(ety).ok_or_else(|| ConvError(format!("no entity type {ety}")))?;
        let ns = ety.rsplit_once("::").map(|(a, _)| a).unwrap_or("");
        self.resolve(shape, ns)
    }

    pub fn has_attr(&self, ety: &str, attr: &str) -> bool {
        matches!(self.entity_shape(ety), Ok(Ty::Rec { attrs, .. }) if attrs.iter().any(|(k, _, _)| k == attr))
    }

    /// Type of the named attribute of entity type `ety`.
    pub fn attr_ty(&self, ety: &str, attr: &str) -> Result<Ty, ConvError> {
        match self.entity_shape(ety)? {
            Ty::Rec { attrs, .. } => attrs.into_iter().find(|(k, _, _)| k == attr).map(|(_, t, _)| t)
                .ok_or_else(|| ConvError(format!("{ety} has no attribute {attr}"))),
            _ => Err(ConvError("entity shape is not a record".into())),
        }
    }
}

/// Convert `v` to the Cedar JSON value of type `ty`. `Ok(None)` means "omit the attribute"
/// (JSON null). Undeclared fields of records are dropped (recorded in `stats`) unless the
/// record is open.
pub fn convert(ty: &Ty, v: &Value, path: &str, stats: &mut ConvStats) -> Result<Option<Value>, ConvError> {
    if v.is_null() { return Ok(None); }
    let mism = |what: &str| ConvError(format!("{path}: expected {what}, got {v}"));
    match ty {
        Ty::Str => v.as_str().map(|s| Some(json!(s))).ok_or_else(|| mism("string")),
        Ty::Bool => v.as_bool().map(|s| Some(json!(s))).ok_or_else(|| mism("bool")),
        Ty::Long => match v.as_i64() { Some(n) => Ok(Some(json!(n))), None => Err(mism("integer")) },
        Ty::Set(el) => {
            let a = v.as_array().ok_or_else(|| mism("array"))?;
            let mut out = Vec::new();
            for (i, x) in a.iter().enumerate() {
                match convert(el, x, &format!("{path}[{i}]"), stats)? { Some(c) => out.push(c), None => return Err(mism("non-null set element")) }
            }
            Ok(Some(Value::Array(out)))
        }
        Ty::Rec { attrs, open } => {
            let o = v.as_object().ok_or_else(|| mism("object"))?;
            let mut out = Map::new();
            for (k, x) in o {
                match attrs.iter().find(|(n, _, _)| n == k) {
                    Some((_, t, _)) => {
                        if let Some(c) = convert(t, x, &format!("{path}.{k}"), stats)? { out.insert(k.clone(), c); }
                    }
                    None if *open => { out.insert(k.clone(), x.clone()); }
                    None => stats.dropped.push(format!("{path}.{k}")),
                }
            }
            for (n, _, req) in attrs {
                if *req && !out.contains_key(n) { return Err(ConvError(format!("{path}: missing required attribute {n}"))); }
            }
            Ok(Some(Value::Object(out)))
        }
    }
}
