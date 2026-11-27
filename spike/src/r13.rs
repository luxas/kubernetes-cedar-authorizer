//! R-13 measurement: how real(istic) Kubernetes objects conform to generated Cedar types.
use crate::{convert::*, openapi::*};
use cedar_policy::*;
use serde_json::{json, Value};

pub const K8S: &str = "/home/luxask/code/kubernetes";

#[derive(Debug)]
pub struct Row {
    pub stem: String,
    pub result: Result<(), String>,
    pub dropped: usize,
    pub coerced: usize,
    pub map_pairs: usize,
    pub gen: GenStats,
}

pub fn fixtures(stable_only: bool) -> Vec<String> {
    let dir = format!("{K8S}/staging/src/k8s.io/api/testdata/HEAD");
    let mut v: Vec<String> = std::fs::read_dir(&dir).map(|d| d.filter_map(|e| e.ok()).filter_map(|e| {
        let n = e.file_name().to_string_lossy().to_string();
        n.strip_suffix(".json").map(str::to_string)
    }).collect()).unwrap_or_default();
    v.sort();
    if stable_only { v.retain(|s| { let p: Vec<&str> = s.split('.').collect(); p.len() >= 3 && { let ver = p[p.len() - 2]; ver.starts_with('v') && ver[1..].chars().all(|c| c.is_ascii_digit()) } }); }
    v
}

pub fn run(stem: &str) -> Option<Row> {
    let (file, version, kind) = locate(stem)?;
    let doc_path = format!("{K8S}/api/openapi-spec/v3/{file}");
    let doc: Value = serde_json::from_str(&std::fs::read_to_string(&doc_path).ok()?).ok()?;
    let name = find_schema_name(&doc, &version, &kind)?;
    let obj: Value = serde_json::from_str(&std::fs::read_to_string(format!("{K8S}/staging/src/k8s.io/api/testdata/HEAD/{stem}.json")).ok()?).ok()?;
    let (sj, gen) = kind_schema(&doc, &name);
    let env = TypeEnv::from_schema_json(&sj);
    let schema = match Schema::from_json_value(sj.clone()) { Ok(s) => s, Err(e) => return Some(Row { stem: stem.into(), result: Err(format!("schema: {e}")), dropped: 0, coerced: 0, map_pairs: 0, gen }) };
    let ty = env.attr_ty("Res", "request").ok()?;
    let mut stats = ConvStats::default();
    let result = convert(&ty, &obj, "request", &mut stats).map_err(|e| format!("convert: {e}")).and_then(|c| {
        let attrs = json!({"request": c});
        Entities::from_json_value(json!([{"uid": {"type": "Res", "id": "r"}, "attrs": attrs, "parents": []}]), Some(&schema)).map(|_| ()).map_err(|e| format!("entity: {e}"))
    });
    Some(Row { stem: stem.into(), result, dropped: stats.dropped.len(), coerced: stats.coerced.len(), map_pairs: stats.map_pairs.len(), gen })
}
