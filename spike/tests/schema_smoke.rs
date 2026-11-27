use cedar_policy::*;
use std::str::FromStr;
#[test]
fn schema_and_policies_validate() {
    let (frag, _) = SchemaFragment::from_cedarschema_str(spike::model::SCHEMA).expect("schema");
    println!("{}", frag.clone().to_json_value().unwrap());
    let schema = Schema::from_schema_fragments([frag]).unwrap();
    let ps = PolicySet::from_str(spike::model::POLICIES).expect("policies parse");
    let r = Validator::new(schema).validate(&ps, ValidationMode::default());
    for e in r.validation_errors() { println!("ERR {e}"); }
    for w in r.validation_warnings() { println!("WARN {w}"); }
    assert!(r.validation_passed());
}
