//! R-13 / schema generator prototype: Kubernetes OpenAPI v3 component schema -> Cedar JSON type.
//! Rules (each counted in `GenStats`): all attributes optional; arrays -> Set; map[string]string
//! (and map[string]Quantity) -> Set<{key,value}> (R-9 variant C); int-or-string -> String;
//! numbers (floats), opaque objects (`x-kubernetes-preserve-unknown-fields`, RawExtension,
//! managedFields.fieldsV1) and maps of non-strings are not representable and are dropped;
//! recursion is cut at depth 10.
use serde_json::{json, Map, Value};

#[derive(Debug, Default, Clone)]
pub struct GenStats {
    pub dropped_float: usize,
    pub dropped_opaque: usize,
    pub dropped_map_non_string: usize,
    pub dropped_recursion: usize,
    pub map_pairs: usize,
    pub int_or_string: usize,
    pub attrs: usize,
}

fn deref<'a>(doc: &'a Value, node: &'a Value) -> &'a Value {
    let r = node["$ref"].as_str().or_else(|| node["allOf"][0]["$ref"].as_str());
    match r {
        Some(r) => &doc["components"]["schemas"][r.rsplit('/').next().unwrap()],
        None => node,
    }
}

pub fn gen_type(doc: &Value, node: &Value, depth: usize, st: &mut GenStats) -> Option<Value> {
    if depth > 16 { st.dropped_recursion += 1; return None; }
    let n = deref(doc, node);
    if n["x-kubernetes-int-or-string"] == true || n["format"] == "int-or-string" { st.int_or_string += 1; return Some(json!({"type": "String", "required": false})); }
    match n["type"].as_str() {
        Some("string") => Some(json!({"type": "String", "required": false})),
        Some("integer") => Some(json!({"type": "Long", "required": false})),
        Some("boolean") => Some(json!({"type": "Boolean", "required": false})),
        Some("number") => { st.dropped_float += 1; None }
        Some("array") => {
            let el = gen_type(doc, &n["items"], depth + 1, st)?;
            let mut el = el;
            el.as_object_mut().unwrap().remove("required");
            Some(json!({"type": "Set", "element": el, "required": false}))
        }
        Some("object") | None => {
            if let Some(props) = n["properties"].as_object() {
                let mut attrs = Map::new();
                for (k, v) in props {
                    if let Some(t) = gen_type(doc, v, depth + 1, st) { attrs.insert(k.clone(), t); st.attrs += 1; }
                }
                Some(json!({"type": "Record", "attributes": attrs, "required": false}))
            } else if n["additionalProperties"].is_object() {
                let ap = deref(doc, &n["additionalProperties"]);
                if ap["type"] == "string" {
                    st.map_pairs += 1;
                    Some(json!({"type": "Set", "required": false, "element":
                        {"type": "Record", "attributes": {"key": {"type": "String"}, "value": {"type": "String"}}}}))
                } else { st.dropped_map_non_string += 1; None }
            } else { st.dropped_opaque += 1; None }
        }
        Some(_) => None,
    }
}

/// Cedar JSON schema with one entity type `Res` whose optional `request` has the kind's shape.
pub fn kind_schema(doc: &Value, schema_name: &str) -> (Value, GenStats) {
    let mut st = GenStats::default();
    let node = &doc["components"]["schemas"][schema_name];
    let ty = gen_type(doc, node, 0, &mut st).expect("kind type");
    let schema = json!({"": {
        "entityTypes": {
            "User": {"shape": {"type": "Record", "attributes": {"name": {"type": "String"}}}},
            "Res": {"shape": {"type": "Record", "attributes": {"request": ty}}}},
        "actions": {"Create": {"appliesTo": {"principalTypes": ["User"], "resourceTypes": ["Res"], "context": {"type": "Record", "attributes": {}}}}}}});
    (schema, st)
}

/// Locate the OpenAPI document and component schema name for a fixture file stem such as
/// `core.v1.Pod` or `rbac.authorization.k8s.io.v1.Role`. Returns (doc path suffix, kind).
pub fn locate(stem: &str) -> Option<(String, String, String)> {
    let parts: Vec<&str> = stem.split('.').collect();
    let kind = parts.last()?.to_string();
    let version = parts[parts.len() - 2].to_string();
    let group = parts[..parts.len() - 2].join(".");
    let file = if group == "core" { format!("api__{version}_openapi.json") } else { format!("apis__{group}__{version}_openapi.json") };
    Some((file, version, kind))
}

pub fn find_schema_name(doc: &Value, version: &str, kind: &str) -> Option<String> {
    let suffix = format!(".{version}.{kind}");
    doc["components"]["schemas"].as_object()?.keys().find(|k| k.ends_with(&suffix) && k.starts_with("io.k8s.api")).cloned()
        .or_else(|| doc["components"]["schemas"].as_object()?.keys().find(|k| k.ends_with(&suffix)).cloned())
}
