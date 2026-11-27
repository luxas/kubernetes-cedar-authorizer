//! Policy lints (R-9, R-11, T-6, T-10, D-11): small functions over Cedar EST JSON.
use cedar_policy::*;
use serde_json::Value;
use std::str::FromStr;

/// T-6 / `has`-guard lint: validate every policy on its own; returns (policy id, errors) for
/// the policies that do not validate (an unguarded optional access is the typical error). One
/// bad policy must not take the whole set down, so the webhook runs this at load time.
pub fn has_guard_lint(schema: &Schema, policies_text: &str) -> Vec<(String, Vec<String>)> {
    let mut bad = vec![];
    for (id, body) in crate::engine::split_policies(policies_text) {
        let mut ps = PolicySet::new();
        match Policy::parse(Some(PolicyId::new(&id)), body) {
            Ok(p) => { ps.add(p).unwrap(); }
            Err(e) => { bad.push((id, vec![format!("parse: {e}")])); continue; }
        }
        let r = Validator::new(schema.clone()).validate(&ps, ValidationMode::default());
        if !r.validation_passed() { bad.push((id, r.validation_errors().map(|e| e.to_string()).collect())); }
    }
    bad
}

fn walk(v: &Value, f: &mut impl FnMut(&str, &Value)) {
    match v {
        Value::Object(o) => for (k, x) in o { f(k, x); walk(x, f); },
        Value::Array(a) => for x in a { walk(x, f) },
        _ => {}
    }
}

const SAFE_OPS: &[&str] = &["Value", "Var", "Slot", "!", "==", "!=", "in", "<", "<=", ">", ">=", "&&", "||", "if-then-else", ".", "has",
    "like", "is", "contains", "containsAll", "containsAny", "isEmpty", "Set", "Record", "left", "right", "arg", "attr", "pattern", "if", "then", "else",
    "entity_type", "in_entity", "elements", "kind", "body", "type", "id", "__entity", "Literal", "Wildcard"];

/// R-11 / D-2 lint list: constructs that can raise a runtime error. Cedar skips an erroring
/// policy, so inside a `forbid` they silently turn a Deny into "not applicable" (T-10).
/// Returns the construct names found in `policy_json` (a full policy in EST JSON).
pub fn forbid_can_error(policy_json: &Value) -> Vec<String> {
    let mut found = vec![];
    for c in policy_json["conditions"].as_array().into_iter().flatten() {
        walk(&c["body"], &mut |k, _| match k {
            "+" | "-" | "*" => found.push(format!("arithmetic `{k}` (overflow)")),
            "neg" => found.push("negation (overflow)".into()),
            "getTag" => found.push("getTag (missing tag)".into()),
            "hasTag" => {}
            k if !SAFE_OPS.contains(&k) => found.push(format!("extension call `{k}`")),
            _ => {}
        });
    }
    found.sort();
    found.dedup();
    found
}

/// D-11: policies must never mention the synthetic resource uid and never compare `resource`
/// with an entity (the scope uses `resource is <type>`); the uid is an implementation artefact.
pub fn reserved_uid_lint(policy_json: &Value, reserved: &str) -> Vec<String> {
    let mut out = vec![];
    if policy_json["resource"]["op"] == "==" || policy_json["resource"]["op"] == "in" || policy_json["resource"]["op"] == "is" && policy_json["resource"]["in"].is_object() {
        out.push(format!("resource scope `{}` (use `resource is <type>`)", policy_json["resource"]["op"]));
    }
    let mut check = |k: &str, x: &Value| {
        if k == "__entity" && x["id"].as_str().map(|i| i == reserved || i.starts_with('@')).unwrap_or(false) {
            out.push(format!("entity literal {}::{}", x["type"], x["id"]));
        }
        if k == "==" || k == "!=" {
            for side in ["left", "right"] { if x[side]["Var"] == "resource" { out.push("`resource ==` comparison".into()); } }
        }
    };
    walk(policy_json, &mut check);
    out.sort();
    out.dedup();
    out
}

/// D-13: residuals are scope-less `when` clauses and must not mention `action`.
pub fn residual_mentions_action(residual_est_body: &Value) -> bool {
    let mut hit = false;
    walk(residual_est_body, &mut |k, x| { if k == "Var" && x == "action" { hit = true; } });
    hit
}

/// Parse text and give EST JSON (for the lint tests).
pub fn est(text: &str) -> Value {
    Policy::from_str(text).expect("policy").to_json().expect("json")
}
