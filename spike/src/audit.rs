//! Mini scenario of the TPE audit (docs/tpe-risk-report.md) re-run against the pinned SHAs:
//! a small schema, the five KEP-style policies, and partial-state scenarios. Used by R-1..R-4,
//! R-6..R-8, R-10, R-11. The Lean counterpart is spike/lean/R10.lean.
use cedar_policy::*;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::str::FromStr;

pub const SCHEMA: &str = r#"
entity User = { name: String, nodeName: String };
type Meta = { name?: String, labels?: { owner?: String }, finalizers?: Set<String> };
type Obj = { metadata?: Meta, spec?: { nodeName?: String, replicas?: Long } };
entity Res = { name?: String, request?: Obj, stored?: Obj };
action Create appliesTo { principal: User, resource: Res, context: {} };
action Update appliesTo { principal: User, resource: Res, context: {} };
"#;

/// The five KEP-style policies (owner label, sensitive field unchanged, name prefix, finalizer,
/// node-bound). Every optional access is `has`-guarded.
pub const KEP5: &str = r#"
@id("owner")
permit(principal, action in [Action::"Create", Action::"Update"], resource)
when { resource has request && resource.request has metadata && resource.request.metadata has labels && resource.request.metadata.labels has owner && resource.request.metadata.labels.owner == principal.name };

@id("unchanged")
forbid(principal, action == Action::"Update", resource)
when { resource has stored && resource.stored has spec && resource.stored.spec has nodeName && resource has request && resource.request has spec && resource.request.spec has nodeName && resource.stored.spec.nodeName != resource.request.spec.nodeName };

@id("prefix")
permit(principal, action == Action::"Create", resource)
when { resource has name && resource.name like "safe-*" };

@id("finalizer")
forbid(principal, action, resource)
when { resource has request && resource.request has metadata && resource.request.metadata has finalizers && resource.request.metadata.finalizers.contains("protected") };

@id("nodebound")
permit(principal, action == Action::"Update", resource)
when { resource has stored && resource.stored has spec && resource.stored.spec has nodeName && resource.stored.spec.nodeName == principal.nodeName };
"#;

pub fn pm(s: &str) -> Value { json!({"__extn": {"fn": "partial", "arg": s}}) }

pub fn schema() -> Schema { Schema::from_cedarschema_str(SCHEMA).unwrap().0 }
pub fn kep5() -> PolicySet { crate::engine::policy_set_from(KEP5) }

/// One scenario = action + resource attribute states (JSON with partial markers).
pub struct Scenario { pub name: &'static str, pub action: &'static str, pub res_attrs: Value }

pub fn scenarios() -> Vec<Scenario> {
    vec![
        Scenario { name: "create", action: "Create", res_attrs: json!({"name": pm("unknown"), "request": pm("present"), "stored": pm("absent")}) },
        Scenario { name: "update", action: "Update", res_attrs: json!({"name": "settings", "request": pm("present"), "stored": pm("unknown")}) },
        Scenario { name: "update-partial", action: "Update", res_attrs: json!({"name": "settings",
            "request": {"metadata": pm("present"), "spec": {"nodeName": pm("present")}},
            "stored": {"metadata": pm("unknown"), "spec": {"nodeName": "n1", "replicas": pm("unknown")}} }) },
        Scenario { name: "delete-like", action: "Update", res_attrs: json!({"name": "settings", "request": pm("absent"), "stored": pm("present")}) },
    ]
}

pub fn partial_entities(schema: &Schema, res_attrs: &Value) -> PartialEntities {
    PartialEntities::from_json_value(json!([
        {"uid": {"type": "User", "id": "alice"}, "attrs": {"name": "alice", "nodeName": "n1"}, "parents": []},
        {"uid": {"type": "Res", "id": "r1"}, "attrs": res_attrs, "parents": []}
    ]), schema).unwrap()
}

pub fn preq(schema: &Schema, action: &str) -> PartialRequest {
    let a = EntityUid::from_str(&format!("Action::\"{action}\"")).unwrap();
    let ctx = PartialContext::from_json_value(json!({}), &a, schema).unwrap();
    PartialRequest::new(
        PartialEntityUid::from_concrete(EntityUid::from_str("User::\"alice\"").unwrap()), a,
        PartialEntityUid::from_concrete(EntityUid::from_str("Res::\"r1\"").unwrap()), ctx, schema).unwrap()
}

/// Canonical, association-normalised s-expression of a Cedar EST expression (JSON): `&&`/`||`
/// chains are flattened, `!=` is `(! (== ..))`, literals are printed uniformly. Shared with the
/// Lean printer in spike/lean/R10.lean (same grammar).
pub fn canon(v: &Value) -> String {
    let o = v.as_object().expect("est node");
    let (k, a) = o.iter().next().expect("est op");
    let c = |x: &Value| canon(x);
    match k.as_str() {
        "Value" => canon_value(a),
        "&&" | "||" => {
            let mut parts = vec![];
            flatten(v, k, &mut parts);
            format!("({} {})", if k == "&&" { "and" } else { "or" }, parts.join(" "))
        }
        "!" => format!("(! {})", c(&a["arg"])),
        "==" => format!("(== {} {})", c(&a["left"]), c(&a["right"])),
        "!=" => format!("(! (== {} {}))", c(&a["left"]), c(&a["right"])),
        "in" => format!("(in {} {})", c(&a["left"]), c(&a["right"])),
        "contains" => format!("(contains {} {})", c(&a["left"]), c(&a["right"])),
        "containsAny" => format!("(containsAny {} {})", c(&a["left"]), c(&a["right"])),
        "<" | "<=" | ">" | ">=" | "+" | "-" | "*" => format!("({} {} {})", k, c(&a["left"]), c(&a["right"])),
        "." => format!("(. {} {})", c(&a["left"]), a["attr"].as_str().unwrap()),
        "has" => format!("(has {} {})", c(&a["left"]), a["attr"].as_str().unwrap()),
        "like" => format!("(like {} {})", c(&a["left"]), canon_pattern(&a["pattern"])),
        "Set" => format!("(set {})", a.as_array().unwrap().iter().map(c).collect::<Vec<_>>().join(" ")),
        "Var" | "var" => a.as_str().unwrap().to_string(),
        "error" => "error".into(),
        other => format!("(?{other} {a})"),
    }
}

fn flatten(v: &Value, op: &str, out: &mut Vec<String>) {
    let a = &v[op];
    for side in ["left", "right"] {
        let s = &a[side];
        if s.as_object().map(|o| o.contains_key(op)).unwrap_or(false) { flatten(s, op, out) } else { out.push(canon(s)) }
    }
}

fn canon_value(a: &Value) -> String {
    match a {
        Value::Bool(b) => b.to_string(),
        Value::Number(n) => n.to_string(),
        Value::String(s) => format!("{s:?}"),
        Value::Object(o) if o.contains_key("__entity") => format!("{}::{:?}", o["__entity"]["type"].as_str().unwrap(), o["__entity"]["id"].as_str().unwrap()),
        Value::Array(xs) => format!("(set {})", xs.iter().map(canon_value).collect::<Vec<_>>().join(" ")),
        other => format!("?{other}"),
    }
}

fn canon_pattern(p: &Value) -> String {
    let mut s = String::new();
    for el in p.as_array().unwrap() {
        match el { Value::String(x) if x == "Wildcard" => s.push('*'), Value::Object(o) => s.push_str(o["Literal"].as_str().unwrap()), o => s.push_str(&format!("?{o}")) }
    }
    format!("{s:?}")
}

/// policy id -> canonical residual condition ("true"/"false" for decided, "error" for error).
pub fn canonical_residuals(schema: &Schema, ps: &PolicySet, sc: &Scenario) -> BTreeMap<String, String> {
    let pes = partial_entities(schema, &sc.res_attrs);
    let req = preq(schema, sc.action);
    let resp = ps.tpe(&req, &pes, schema).expect("tpe");
    let mut m = BTreeMap::new();
    for p in resp.policies() {
        let j = p.to_json().expect("to_json");
        let body = &j["conditions"][0]["body"];
        m.insert(p.id().to_string(), canon(body));
    }
    m
}
