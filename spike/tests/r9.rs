//! R-9: K8s `map[string]string` typing for `labels["x"]`.
//! A: record with declared keys. B: open record (`additionalAttributes`). C: set of {key,value} pairs.
use cedar_policy::*;
use serde_json::{json, Value};
use std::str::FromStr;

fn schema_json(labels_ty: Value) -> Value {
    json!({"": {
      "entityTypes": {
        "User": {"shape": {"type": "Record", "attributes": {"name": {"type": "String"}}}},
        "Res": {"shape": {"type": "Record", "attributes": {"request": {"type": "Record", "required": false, "attributes": {
            "labels": {"type": "Record", "required": false, "attributes": {}}}}}}}},
      "actions": {"Create": {"appliesTo": {"principalTypes": ["User"], "resourceTypes": ["Res"], "context": {"type": "Record", "attributes": {}}}}}}})
        .as_object().map(|_| {
            let mut v = json!({"": {
              "entityTypes": {
                "User": {"shape": {"type": "Record", "attributes": {"name": {"type": "String"}}}},
                "Res": {"shape": {"type": "Record", "attributes": {"request": {"type": "Record", "required": false, "attributes": {"labels": labels_ty}}}}}},
              "actions": {"Create": {"appliesTo": {"principalTypes": ["User"], "resourceTypes": ["Res"], "context": {"type": "Record", "attributes": {}}}}}}});
            v[""]["entityTypes"]["Res"]["shape"]["attributes"]["request"]["required"] = json!(false);
            v
        }).unwrap()
}

fn mk(labels_ty: Value) -> Schema { Schema::from_json_value(schema_json(labels_ty)).unwrap() }
fn valid(s: &Schema, pol: &str) -> Result<(), Vec<String>> {
    let ps = PolicySet::from_str(pol).unwrap();
    let r = Validator::new(s.clone()).validate(&ps, ValidationMode::default());
    if r.validation_passed() { Ok(()) } else { Err(r.validation_errors().map(|e| e.to_string()).collect()) }
}
fn entity_ok(s: &Schema, labels: Value) -> bool {
    Entities::from_json_value(json!([{"uid": {"type": "Res", "id": "r"}, "attrs": {"request": {"labels": labels}}, "parents": []}]), Some(s)).is_ok()
}

const INDEX: &str = r#"permit(principal, action, resource) when { resource has request && resource.request has labels && resource.request.labels has "team.example.com/owner" && resource.request.labels["team.example.com/owner"] == "alice" };"#;
const PLAIN: &str = r#"permit(principal, action, resource) when { resource has request && resource.request has labels && resource.request.labels has owner && resource.request.labels["owner"] == principal.name };"#;

const INDEX_GUARDED: &str = r#"permit(principal, action, resource) when { resource has request && resource.request has labels && resource.request.labels has "team.example.com/owner" && resource.request.labels["team.example.com/owner"] == "alice" };"#;
const INDEX_UNGUARDED: &str = r#"permit(principal, action, resource) when { resource has request && resource.request has labels && resource.request.labels["team.example.com/owner"] == "alice" };"#;

fn tpe_residual(s: &Schema, pol: &str, request: Value) -> String {
    let ps = PolicySet::from_str(pol).unwrap();
    let a = EntityUid::from_str("Action::\"Create\"").unwrap();
    let ctx = PartialContext::from_json_value(json!({}), &a, s).unwrap();
    let preq = PartialRequest::new(PartialEntityUid::from_concrete(EntityUid::from_str("User::\"alice\"").unwrap()), a, PartialEntityUid::from_concrete(EntityUid::from_str("Res::\"r\"").unwrap()), ctx, s).unwrap();
    let pes = PartialEntities::from_json_value(json!([
        {"uid": {"type": "User", "id": "alice"}, "attrs": {"name": "alice"}, "parents": []},
        {"uid": {"type": "Res", "id": "r"}, "attrs": {"request": request}, "parents": []}]), s).unwrap();
    let resp = ps.tpe(&preq, &pes, s).unwrap();
    let out = resp.policies().next().unwrap().to_string().replace('\n', " ");
    out
}
fn pm(a: &str) -> Value { json!({"__extn": {"fn": "partial", "arg": a}}) }

#[test]
fn variant_a_declared_keys() {
    let a = mk(json!({"type": "Record", "required": false, "attributes": {"owner": {"type": "String", "required": false},
        "team.example.com/owner": {"type": "String", "required": false}}}));
    assert!(valid(&a, PLAIN).is_ok());
    assert!(valid(&a, INDEX_GUARDED).is_ok());
    assert!(valid(&a, INDEX_UNGUARDED).is_err(), "optional label key needs a has guard");
    // a key that is NOT declared type-checks behind a `has` guard but can never be true (dead policy)
    let narrow = mk(json!({"type": "Record", "required": false, "attributes": {"owner": {"type": "String", "required": false}}}));
    assert!(valid(&narrow, INDEX_GUARDED).is_ok());
    assert!(valid(&narrow, INDEX_UNGUARDED).is_err());
    let r = tpe_residual(&narrow, INDEX_GUARDED, json!({"labels": pm("present")}));
    // observed at cedar 99a88d5: it does NOT fold to false; the residual keeps only the `has` test
    // (the `== "alice"` conjunct on the undeclared key is dropped). Under schema conformance the
    // `has` is false for every concrete labels record, so phase 2 still never matches.
    assert_eq!(r, r#"permit(principal, action, resource) when { Res::"r".request.labels has "team.example.com/owner" };"#);
    // control: the declared key stays residual
    let r = tpe_residual(&a, INDEX_GUARDED, json!({"labels": pm("present")}));
    assert!(r.contains("team.example.com/owner") && !r.contains("{ false }"), "{r}");
    // an object with an undeclared label key does NOT conform: phase 2 would fail closed on real objects
    assert!(entity_ok(&narrow, json!({"owner": "alice"})));
    assert!(!entity_ok(&narrow, json!({"owner": "alice", "app": "web"})), "undeclared label key must be rejected by entity validation");
    // so the converter must drop undeclared keys (spike::convert does, see r8 test) or the schema must declare them
}

#[test]
fn variant_b_open_record_is_unsupported_at_the_pin() {
    let r = Schema::from_json_value(schema_json(json!({"type": "Record", "required": false, "additionalAttributes": true, "attributes": {}})));
    let msg = format!("{:?}", r.err().expect("open records must be rejected at cedar 99a88d5"));
    assert!(msg.contains("OpenRecordsAndEntities"), "{msg}");
}

const PAIRS: &str = r#"permit(principal, action, resource) when { resource has request && resource.request has labels && resource.request.labels.contains({key: "owner", value: principal.name}) };"#;

#[test]
fn variant_c_set_of_key_value_pairs() {
    let pair = json!({"type": "Record", "attributes": {"key": {"type": "String"}, "value": {"type": "String"}}});
    let c = mk(json!({"type": "Set", "required": false, "element": pair}));
    assert!(valid(&c, PAIRS).is_ok());
    // any label set conforms (availability 100%)
    assert!(entity_ok(&c, json!([{"key": "owner", "value": "alice"}, {"key": "app", "value": "web"}, {"key": "x/y", "value": ""}])));
    // TPE keeps the contains test residual while `labels` is present, decides it once labels are known
    let r = tpe_residual(&c, PAIRS, json!({"labels": pm("present")}));
    assert!(r.contains("contains"), "{r}");
    assert!(tpe_residual(&c, PAIRS, json!({"labels": [{"key": "owner", "value": "alice"}]})).contains("{ true }"));
    assert!(tpe_residual(&c, PAIRS, json!({"labels": [{"key": "owner", "value": "bob"}]})).contains("{ false }"));
    // phase 2 on the JSON residual equals the original policy
    let ps = PolicySet::from_str(PAIRS).unwrap();
    let a = EntityUid::from_str("Action::\"Create\"").unwrap();
    let ctx = PartialContext::from_json_value(json!({}), &a, &c).unwrap();
    let preq = PartialRequest::new(PartialEntityUid::from_concrete(EntityUid::from_str("User::\"alice\"").unwrap()), a.clone(), PartialEntityUid::from_concrete(EntityUid::from_str("Res::\"r\"").unwrap()), ctx, &c).unwrap();
    let pes = PartialEntities::from_json_value(json!([
        {"uid": {"type": "User", "id": "alice"}, "attrs": {"name": "alice"}, "parents": []},
        {"uid": {"type": "Res", "id": "r"}, "attrs": {"request": pm("present")}, "parents": []}]), &c).unwrap();
    let resp = ps.tpe(&preq, &pes, &c).unwrap();
    let mut residual = PolicySet::new();
    for p in resp.residual_policies() { residual.add(Policy::from_json(Some(p.id().clone()), p.to_json().unwrap()).unwrap()).unwrap(); }
    let req = Request::new(EntityUid::from_str("User::\"alice\"").unwrap(), a, EntityUid::from_str("Res::\"r\"").unwrap(), Context::empty(), Some(&c)).unwrap();
    let mut seen = std::collections::BTreeSet::new();
    for labels in [json!([{"key": "owner", "value": "alice"}]), json!([{"key": "owner", "value": "bob"}]), json!([])] {
        let es = Entities::from_json_value(json!([
            {"uid": {"type": "User", "id": "alice"}, "attrs": {"name": "alice"}, "parents": []},
            {"uid": {"type": "Res", "id": "r"}, "attrs": {"request": {"labels": labels}}, "parents": []}]), Some(&c)).unwrap();
        let orig = Authorizer::new().is_authorized(&req, &ps, &es).decision();
        let got = Authorizer::new().is_authorized(&req, &residual, &es).decision();
        assert_eq!(orig, got);
        seen.insert(format!("{orig:?}"));
    }
    assert_eq!(seen.len(), 2, "both Allow and Deny must occur: {seen:?}");
}

