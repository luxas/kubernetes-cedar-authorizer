//! R-13 (prototype): conformance of the Kubernetes API fixtures (staging/src/k8s.io/api/testdata/HEAD,
//! fully populated objects) to Cedar types generated from the OpenAPI v3 documents.
use spike::r13::*;

fn available() -> bool { std::path::Path::new(&format!("{K8S}/api/openapi-spec/v3")).exists() }

fn read(p: &str) -> serde_json::Value { serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap() }

#[test]
fn r13_fixtures_conform_to_generated_types() {
    if !available() { eprintln!("SKIP r13: {K8S} not present"); return; }
    let rows: Vec<Row> = fixtures(true).iter().filter_map(|s| run(s)).collect();
    let n = rows.len();
    let ok = rows.iter().filter(|r| r.result.is_ok()).count();
    let no_drop = rows.iter().filter(|r| r.result.is_ok() && r.dropped == 0).count();
    let fails: Vec<_> = rows.iter().filter(|r| r.result.is_err()).map(|r| (r.stem.clone(), r.result.clone().unwrap_err())).collect();
    println!("R-13: {ok}/{n} fixtures conform (drop undeclared fields); {no_drop}/{n} conform without dropping anything; failures {fails:?}");
    assert!(n >= 60, "vacuity guard: only {n} fixtures resolved");
    assert!(ok * 100 >= n * 99, "R-13 threshold 99%: {ok}/{n} {fails:?}");
    // strict mode (fail closed on any undeclared field) would be unusable: managedFields.fieldsV1 etc.
    assert!(no_drop * 2 < n, "expected most real objects to carry opaque fields");
    assert!(rows.iter().map(|r| r.map_pairs).sum::<usize>() > 100);
}

#[test]
fn r13_controls_wrong_type_and_raw_objects_are_rejected() {
    if !available() { return; }
    use cedar_policy::*;
    use serde_json::json;
    use spike::{convert::*, openapi::*};
    let doc = read(&format!("{K8S}/api/openapi-spec/v3/apis__apps__v1_openapi.json"));
    let name = find_schema_name(&doc, "v1", "Deployment").unwrap();
    let (sj, _) = kind_schema(&doc, &name);
    let env = TypeEnv::from_schema_json(&sj);
    let ty = env.attr_ty("Res", "request").unwrap();
    let fx = format!("{K8S}/staging/src/k8s.io/api/testdata/HEAD/apps.v1.Deployment.json");
    let mut obj = read(&fx);
    assert!(convert(&ty, &obj, "request", &mut ConvStats::default()).is_ok());
    // control 1: a declared field of the wrong type fails the conversion (fail closed)
    obj["spec"]["replicas"] = json!("three");
    assert!(convert(&ty, &obj, "request", &mut ConvStats::default()).is_err());
    // control 2: the raw object (no schema-directed conversion) is rejected by Cedar's strict entity validation
    let schema = Schema::from_json_value(sj).unwrap();
    let raw = read(&fx);
    assert!(Entities::from_json_value(json!([{"uid": {"type": "Res", "id": "r"}, "attrs": {"request": raw}, "parents": []}]), Some(&schema)).is_err());
}
