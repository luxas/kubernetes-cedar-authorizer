//! Phase 1 (authorization time: SAR attributes -> partial request/entities -> TPE -> case split of
//! PLAN 3.2) and phase 2 (admission time: concrete data -> plain `Authorizer` over the JSON
//! conditions). Uses only the public `cedar-policy` API (#2581).
use crate::convert::{convert, ConvStats, Ty, TypeEnv};
use crate::model::{POLICIES, RESERVED_UID, SCHEMA};
use cedar_policy::*;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Class { Deny, NoOpinion, Allow }

/// One Cedar-JSON condition (PLAN 3.2 "Condition encoding").
#[derive(Debug, Clone)]
pub struct Cond { pub policy_id: String, pub json: Value }

#[derive(Debug, Clone)]
pub enum Outcome {
    Unconditional(Class),
    /// ConditionsMap: Deny and Allow conditions (no NoOpinion conditions in Cedar).
    Conditional { deny: Vec<Cond>, allow: Vec<Cond> },
    /// A remaining residual has an `error` node (T-4) or cannot be encoded: FailureDecision.
    FailClosed { class: Class, why: String },
}

#[derive(Debug, Clone)]
pub struct ResidualStat { pub policy_id: String, pub effect: &'static str, pub text_len: usize, pub json_len: usize, pub has_error_node: bool }

#[derive(Debug)]
pub struct Phase1 {
    pub outcome: Outcome,
    pub residuals: Vec<ResidualStat>,
    pub tpe_decision: Option<Decision>,
    pub resource_type: String,
    pub action: String,
    pub plain_residual_set_json_roundtrip: bool,
    /// numbers of policies per TPE class: (true, false, error, residual) for permits and forbids
    pub counts: Counts,
}

#[derive(Debug, Default, Clone, Copy)]
pub struct Counts { pub tp: usize, pub fp: usize, pub ep: usize, pub rp: usize, pub tf: usize, pub ff: usize, pub ef: usize, pub rf: usize }

pub struct Attrs {
    pub verb: String,
    pub group: String,
    pub version: String,
    pub resource: String,
    pub subresource: String,
    pub name: String,
    pub namespace: String,
    pub user: Value,
}

impl Attrs {
    pub fn from_sar(sar: &Value) -> Attrs {
        let ra = &sar["resourceAttributes"];
        let s = |k: &str| ra[k].as_str().unwrap_or("").to_string();
        Attrs { verb: s("verb"), group: s("group"), version: s("version"), resource: s("resource"),
                subresource: s("subresource"), name: s("name"), namespace: s("namespace"), user: sar["user"].clone() }
    }
}

pub struct Principal { pub ty: &'static str, pub id: String, pub attrs: Value }

/// Deterministic principal (D-12): type from the username prefix, id = uid if set else sha256(username).
pub fn principal(user: &Value) -> Principal {
    let name = user["username"].as_str().unwrap_or("");
    let uid = user["uid"].as_str().unwrap_or("");
    let id = if uid.is_empty() { hex(&Sha256::digest(name.as_bytes())) } else { uid.to_string() };
    let groups: Vec<Value> = user["groups"].as_array().cloned().unwrap_or_default();
    if let Some(rest) = name.strip_prefix("system:serviceaccount:") {
        let (ns, sa) = rest.split_once(':').unwrap_or(("", rest));
        Principal { ty: "k8s::ServiceAccount", id, attrs: json!({"name": name, "groups": groups, "namespace": ns, "saName": sa}) }
    } else if let Some(n) = name.strip_prefix("system:node:") {
        Principal { ty: "k8s::Node", id, attrs: json!({"name": name, "groups": groups, "nodeName": n}) }
    } else {
        Principal { ty: "k8s::User", id, attrs: json!({"name": name, "groups": groups}) }
    }
}

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }

/// Resource type per (group, resource, subresource). `None` = out of scope for the spike.
pub fn resource_type(group: &str, resource: &str, sub: &str) -> Option<&'static str> {
    match (group, resource, sub) {
        ("", "configmaps", "") => Some("core::ConfigMap"),
        ("", "pods", "") => Some("core::Pod"),
        ("", "pods", "exec") => Some("core::PodExec"),
        ("", "serviceaccounts", "token") => Some("core::ServiceAccountToken"),
        ("example.com", "widgets", "") => Some("example::Widget"),
        _ => None,
    }
}

fn pm(s: &str) -> Value { json!({"__extn": {"fn": "partial", "arg": s}}) }

#[derive(Debug)]
pub struct EngineError(pub String);
impl<E: std::fmt::Display> From<E> for EngineError { fn from(e: E) -> Self { EngineError(e.to_string()) } }
type R<T> = Result<T, EngineError>;

pub struct Engine {
    pub schema: Schema,
    pub policies: PolicySet,
    pub types: TypeEnv,
}

pub fn split_policies(text: &str) -> Vec<(String, String)> {
    text.split("\n\n").map(str::trim).filter(|p| !p.is_empty()).map(|p| {
        let s = p.find("@id(\"").expect("@id") + 5;
        let e = s + p[s..].find('"').unwrap();
        (p[s..e].to_string(), p.to_string())
    }).collect()
}

pub fn policy_set_from(text: &str) -> PolicySet {
    let mut ps = PolicySet::new();
    for (id, body) in split_policies(text) {
        ps.add(Policy::parse(Some(PolicyId::new(id)), body).expect("policy")).unwrap();
    }
    ps
}

fn has_error_node(v: &Value) -> bool {
    match v {
        Value::Object(o) => o.contains_key("error") || o.values().any(has_error_node),
        Value::Array(a) => a.iter().any(has_error_node),
        _ => false,
    }
}

pub fn classify(r: &Response) -> Class {
    match r.decision() {
        Decision::Allow => Class::Allow,
        Decision::Deny if r.diagnostics().reason().next().is_some() => Class::Deny,
        Decision::Deny => Class::NoOpinion,
    }
}

impl Engine {
    pub fn new() -> Engine { Engine::with(SCHEMA, POLICIES) }

    pub fn with(schema_src: &str, policies_src: &str) -> Engine {
        let (frag, _) = SchemaFragment::from_cedarschema_str(schema_src).expect("schema");
        let types = TypeEnv::from_schema_json(&frag.clone().to_json_value().unwrap());
        let schema = Schema::from_schema_fragments([frag]).unwrap();
        Engine { schema, policies: policy_set_from(policies_src), types }
    }

    fn uid(ty: &str, id: &str) -> R<EntityUid> {
        Ok(EntityUid::from_type_name_and_id(EntityTypeName::from_str(ty)?, EntityId::from_str(id)?))
    }

    fn action_uid(verb: &str) -> R<EntityUid> { Self::uid("k8s::Action", verb) }
    pub fn action_uid_pub(verb: &str) -> EntityUid { Self::action_uid(verb).expect("action uid") }

    /// Action entities (schema-declared, with their groups) must be part of every entity set so
    /// `action in k8s::Action::"update"` can be decided.
    fn action_entities(&self) -> Vec<Value> {
        let mut v = Vec::new();
        for (a, parents) in [("create", vec![]), ("update", vec![]), ("delete", vec![]), ("evaluate", vec![]),
                             ("patch", vec!["update"]), ("deletecollection", vec!["delete"])] {
            v.push(json!({"uid": {"type": "k8s::Action", "id": a}, "attrs": {},
                          "parents": parents.iter().map(|p| json!({"type": "k8s::Action", "id": p})).collect::<Vec<_>>()}));
        }
        v
    }

    /// Phase 1. `attrs.name` empty means unknown for create without subresource and always for
    /// deletecollection (PLAN 1.3 table).
    pub fn phase1(&self, a: &Attrs) -> R<Phase1> { Ok(self.phase1_with(a, |_| ())?.0) }

    /// Like `phase1`, also hands the live `TpeResponse` to `f` (for the R-7 differential checks).
    pub fn phase1_with<T>(&self, a: &Attrs, f: impl FnOnce(&TpeResponse) -> T) -> R<(Phase1, Option<T>)> {
        let Some(rt) = resource_type(&a.group, &a.resource, &a.subresource) else {
            // out of scope shapes are NoOpinion, never an error
            return Ok((Phase1 { outcome: Outcome::Unconditional(Class::NoOpinion), residuals: vec![], tpe_decision: None,
                resource_type: String::new(), action: a.verb.clone(), plain_residual_set_json_roundtrip: true, counts: Counts::default() }, None));
        };
        let pr = principal(&a.user);
        let name_known = match a.verb.as_str() {
            "create" => !a.subresource.is_empty() && !a.name.is_empty(),
            "deletecollection" => false,
            _ => !a.name.is_empty(),
        };
        let writes_object = matches!(a.verb.as_str(), "create" | "update" | "patch");
        let mut res_attrs = json!({"apiGroup": a.group, "resource": a.resource});
        let o = res_attrs.as_object_mut().unwrap();
        if !a.subresource.is_empty() { o.insert("subresource".into(), json!(a.subresource)); }
        if !a.namespace.is_empty() { o.insert("namespace".into(), json!(a.namespace)); }
        if name_known { o.insert("name".into(), json!(a.name)); } else { o.insert("name".into(), pm("unknown")); }
        if self.types.has_attr(rt, "request") {
            o.insert("request".into(), pm(if writes_object { "present" } else { "absent" }));
        }
        if self.types.has_attr(rt, "stored") {
            o.insert("stored".into(), pm(if a.verb == "create" { "absent" } else { "unknown" }));
        }
        let ents = vec![
            json!({"uid": {"type": pr.ty, "id": pr.id}, "attrs": pr.attrs, "parents": []}),
            json!({"uid": {"type": rt, "id": RESERVED_UID}, "attrs": res_attrs, "parents": []}),
        ];
        let pes = PartialEntities::from_json_value(Value::Array(ents), &self.schema)?;
        let action = Self::action_uid(&a.verb)?;
        let ctx = PartialContext::from_json_value(json!({}), &action, &self.schema)?;
        let preq = PartialRequest::new(
            PartialEntityUid::from_concrete(Self::uid(pr.ty, &pr.id)?), action.clone(),
            PartialEntityUid::from_concrete(Self::uid(rt, RESERVED_UID)?), ctx, &self.schema)?;
        let resp = self.policies.tpe(&preq, &pes, &self.schema)?;
        let set = |it: Box<dyn Iterator<Item = &PolicyId> + '_>| it.map(|p| p.to_string()).collect::<BTreeSet<_>>();
        let tp = set(Box::new(resp.true_permits()));
        let tf = set(Box::new(resp.true_forbids()));
        let rp = set(Box::new(resp.residual_permits()));
        let rf = set(Box::new(resp.residual_forbids()));
        let ep = set(Box::new(resp.error_permits()));
        let ef = set(Box::new(resp.error_forbids()));
        let fp = set(Box::new(resp.false_permits()));
        let ff = set(Box::new(resp.false_forbids()));
        let counts = Counts { tp: tp.len(), fp: fp.len(), ep: ep.len(), rp: rp.len(), tf: tf.len(), ff: ff.len(), ef: ef.len(), rf: rf.len() };
        let mut stats = Vec::new();
        let mut roundtrip_ok = true;
        let mut conds = |ids: &BTreeSet<String>, effect: &'static str| -> (Vec<Cond>, bool) {
            let mut v = Vec::new();
            let mut err = false;
            for id in ids {
                let p = resp.get_policy(&PolicyId::new(id)).expect("residual policy");
                let text = p.to_string();
                match p.to_json() {
                    Ok(j) => {
                        let en = has_error_node(&j) || Policy::from_json(Some(PolicyId::new(id)), j.clone()).is_err();
                        stats.push(ResidualStat { policy_id: id.clone(), effect, text_len: text.len(), json_len: j.to_string().len(), has_error_node: en });
                        if en { err = true; roundtrip_ok = false; }
                        v.push(Cond { policy_id: id.clone(), json: j });
                    }
                    Err(_) => { err = true; roundtrip_ok = false;
                        stats.push(ResidualStat { policy_id: id.clone(), effect, text_len: text.len(), json_len: 0, has_error_node: true }); }
                }
            }
            (v, err)
        };
        let (fconds, ferr) = conds(&rf, "forbid");
        let mut pids: BTreeSet<String> = rp.clone();
        pids.extend(tp.iter().cloned());
        let (pconds, perr) = conds(&pids, "permit");
        let outcome = if !tf.is_empty() {
            Outcome::Unconditional(Class::Deny)
        } else if rf.is_empty() && !tp.is_empty() {
            Outcome::Unconditional(Class::Allow)
        } else if rf.is_empty() && rp.is_empty() && tp.is_empty() {
            Outcome::Unconditional(Class::NoOpinion)
        } else if ferr || perr {
            let class = if rf.is_empty() { Class::NoOpinion } else { Class::Deny };
            Outcome::FailClosed { class, why: "residual with an error node cannot be encoded (T-4)".into() }
        } else if fconds.len() + pconds.len() > 128 {
            Outcome::FailClosed { class: if rf.is_empty() { Class::NoOpinion } else { Class::Deny }, why: ">128 conditions".into() }
        } else {
            Outcome::Conditional { deny: fconds, allow: pconds }
        };
        let p1 = Phase1 { outcome, residuals: stats, tpe_decision: resp.decision(), resource_type: rt.to_string(),
            action: a.verb.clone(), plain_residual_set_json_roundtrip: roundtrip_ok, counts };
        let extra = f(&resp);
        Ok((p1, Some(extra)))
    }
}

/// Concrete data derived from one AdmissionRequest (PLAN 3.2 `dataToConcrete`, review B I4).
pub struct Concrete {
    pub principal_uid: EntityUid,
    pub resource_uid: EntityUid,
    pub entities: Entities,
    pub resource_type: String,
    pub stats: ConvStats,
}

/// Which AdmissionRequest field supplies the object type/version (mutation hook for tests).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NameSource { Plan, AdmissionName }

pub fn expected_api_version(gk: &Value) -> String {
    let g = gk["group"].as_str().unwrap_or("");
    let v = gk["version"].as_str().unwrap_or("");
    if g.is_empty() { v.to_string() } else { format!("{g}/{v}") }
}

impl Engine {
    pub fn concrete(&self, ar: &Value, name_source: NameSource) -> R<Concrete> {
        let pr = principal(&ar["userInfo"]);
        let rr = &ar["requestResource"];
        let sub = ar["requestSubResource"].as_str().unwrap_or("");
        let group = rr["group"].as_str().unwrap_or("");
        let rt = resource_type(group, rr["resource"].as_str().unwrap_or(""), sub)
            .ok_or_else(|| EngineError("resource type out of scope".into()))?;
        // object/oldObject are in the request version (requestKind), not the storage version (kind).
        let want = expected_api_version(&ar["requestKind"]);
        let mut stats = ConvStats::default();
        let mut attrs = json!({"apiGroup": group, "resource": rr["resource"]});
        let o = attrs.as_object_mut().unwrap();
        if !sub.is_empty() { o.insert("subresource".into(), json!(sub)); }
        if let Some(ns) = ar["namespace"].as_str().filter(|s| !s.is_empty()) { o.insert("namespace".into(), json!(ns)); }
        let obj = &ar["object"];
        let create_no_sub = ar["operation"] == "CREATE" && sub.is_empty();
        let name = match name_source {
            NameSource::Plan if create_no_sub => obj["metadata"]["name"].as_str().map(str::to_string),
            _ => ar["name"].as_str().filter(|s| !s.is_empty()).map(str::to_string),
        };
        if let Some(n) = name.filter(|s| !s.is_empty()) { o.insert("name".into(), json!(n)); }
        for (field, key) in [("object", "request"), ("oldObject", "stored")] {
            let v = &ar[field];
            if v.is_null() { continue; }
            if v["apiVersion"].as_str() != Some(want.as_str()) {
                return Err(EngineError(format!("{field}.apiVersion {} != requestKind {want}", v["apiVersion"])));
            }
            if !self.types.has_attr(rt, key) { stats.dropped.push(format!("{key} (not declared for {rt})")); continue; }
            let ty: Ty = self.types.attr_ty(rt, key)?;
            if let Some(c) = convert(&ty, v, key, &mut stats)? { o.insert(key.to_string(), c); }
        }
        let ents = vec![
            json!({"uid": {"type": pr.ty, "id": pr.id}, "attrs": pr.attrs, "parents": []}),
            json!({"uid": {"type": rt, "id": RESERVED_UID}, "attrs": attrs, "parents": []}),
        ];
        let entities = Entities::from_json_value(Value::Array(ents), Some(&self.schema))?;
        Ok(Concrete { principal_uid: Self::uid(pr.ty, &pr.id)?, resource_uid: Self::uid(rt, RESERVED_UID)?, entities, resource_type: rt.into(), stats })
    }

    fn request(&self, c: &Concrete, action: &str) -> R<Request> {
        Ok(Request::new(c.principal_uid.clone(), Self::action_uid(action)?, c.resource_uid.clone(), Context::empty(), Some(&self.schema))?)
    }

    /// Reference semantics: the original policies on the concrete data with the real action.
    pub fn baseline(&self, c: &Concrete, verb: &str) -> R<Class> {
        let r = Authorizer::new().is_authorized(&self.request(c, verb)?, &self.policies, &c.entities);
        if r.diagnostics().errors().next().is_some() { return Err(EngineError(format!("baseline errors: {:?}", r.diagnostics().errors().map(|e| e.to_string()).collect::<Vec<_>>()))); }
        Ok(classify(&r))
    }

    /// Phase 2: evaluate an outcome on concrete data with a plain `Authorizer` over a `PolicySet`
    /// rebuilt from the JSON conditions and a fixed placeholder action (D-13).
    pub fn phase2(&self, o: &Outcome, c: &Concrete) -> R<Class> {
        match o {
            Outcome::Unconditional(k) => Ok(*k),
            Outcome::FailClosed { class, .. } => Ok(*class),
            Outcome::Conditional { deny, allow } => {
                let mut ps = PolicySet::new();
                for cd in deny.iter().chain(allow.iter()) {
                    ps.add(Policy::from_json(Some(PolicyId::new(&cd.policy_id)), cd.json.clone())?)?;
                }
                let r = Authorizer::new().is_authorized(&self.request(c, "evaluate")?, &ps, &c.entities);
                Ok(classify(&r))
            }
        }
    }
}
