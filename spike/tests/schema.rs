use cedar_policy::*;
use spike::{engine::*, model::*};

#[test]
fn schema_and_policies_validate() {
    let (frag, _) = SchemaFragment::from_cedarschema_str(SCHEMA).expect("schema");
    let schema = Schema::from_schema_fragments([frag]).unwrap();
    let ps = policy_set_from(POLICIES);
    assert_eq!(ps.policies().count(), 11);
    let r = Validator::new(schema).validate(&ps, ValidationMode::default());
    assert!(r.validation_passed(), "{:?}", r.validation_errors().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn principal_ids_are_deterministic() {
    let u = serde_json::json!({"username": "alice", "groups": ["g"]});
    let a = principal(&u);
    let b = principal(&u);
    assert_eq!(a.id, b.id);
    assert_eq!(a.id.len(), 64); // sha256 hex of the username
    let with_uid = principal(&serde_json::json!({"username": "alice", "uid": "u-1"}));
    assert_eq!(with_uid.id, "u-1");
    assert_eq!(principal(&serde_json::json!({"username": "system:node:n1"})).ty, "k8s::Node");
    assert_eq!(principal(&serde_json::json!({"username": "system:serviceaccount:ns:sa"})).ty, "k8s::ServiceAccount");
}
