//! Runs the R-12 shape corpus end to end: SAR -> phase 1 -> phase 2 vs the original policies.
use crate::engine::*;
use cedar_policy::*;
use serde_json::Value;

pub fn load() -> Vec<Value> {
    let p = concat!(env!("CARGO_MANIFEST_DIR"), "/../conformance/shapes.json");
    let v: Value = serde_json::from_str(&std::fs::read_to_string(p).expect("shapes.json")).unwrap();
    v["shapes"].as_array().unwrap().clone()
}

#[derive(Debug)]
pub struct ReqReport {
    pub ar_uid: String,
    pub baseline: Class,
    pub phase2: Result<Class, String>,
    /// `TpeResponse::reauthorize` with the real action (R-7): Err = consistency or validation error
    pub reauthorize: Result<Class, String>,
    /// plain `Authorizer` over `policy_set()` of the residuals with the real action
    pub plain_residual_set: Class,
    /// `TpeResponse::reauthorize` with the placeholder action (expected to fail: C2 evidence)
    pub reauthorize_placeholder: Result<Class, String>,
    pub dropped_fields: Vec<String>,
}

#[derive(Debug)]
pub struct ShapeReport {
    pub id: String,
    pub outcome: Outcome,
    pub phase1: Phase1,
    pub requests: Vec<ReqReport>,
    pub expect: Vec<Class>,
}

pub fn parse_class(s: &str) -> Class {
    match s { "Allow" => Class::Allow, "Deny" => Class::Deny, "NoOpinion" => Class::NoOpinion, o => panic!("class {o}") }
}

pub fn outcome_kind(o: &Outcome) -> String {
    match o {
        Outcome::Unconditional(c) => format!("{c:?}"),
        Outcome::Conditional { deny, allow } => format!("Conditional(deny={}, allow={})", deny.len(), allow.len()),
        Outcome::FailClosed { class, .. } => format!("FailClosed({class:?})"),
    }
}

pub fn run_shape(e: &Engine, shape: &Value, name_source: NameSource) -> Result<ShapeReport, String> {
    let attrs = Attrs::from_sar(&shape["sar"]);
    if shape["outOfScope"].as_bool().unwrap_or(false) {
        let p1 = e.phase1(&attrs).map_err(|x| x.0)?;
        return Ok(ShapeReport { id: shape["id"].as_str().unwrap().into(), outcome: p1.outcome.clone(), phase1: p1, requests: vec![], expect: vec![] });
    }
    let ars: Vec<Value> = shape["admissionRequests"].as_array().unwrap().clone();
    let mut concretes = Vec::new();
    for ar in &ars { concretes.push(e.concrete(ar, name_source).map_err(|x| x.0)?); }
    let verb = attrs.verb.clone();
    let (p1, extra) = e.phase1_with(&attrs, |resp| {
        concretes.iter().map(|c| {
            let real = Request::new(c.principal_uid.clone(), Engine::action_uid_pub(&verb), c.resource_uid.clone(), Context::empty(), Some(&e.schema)).unwrap();
            let ph = Request::new(c.principal_uid.clone(), Engine::action_uid_pub("evaluate"), c.resource_uid.clone(), Context::empty(), Some(&e.schema)).unwrap();
            let re = resp.reauthorize(&real, &c.entities).map(|r| classify(&r)).map_err(|x| format!("{x:?}"));
            let rp = resp.reauthorize(&ph, &c.entities).map(|r| classify(&r)).map_err(|x| format!("{x:?}"));
            let plain = classify(&Authorizer::new().is_authorized(&real, &resp.policy_set(), &c.entities));
            (re, rp, plain)
        }).collect::<Vec<_>>()
    }).map_err(|x| x.0)?;
    let mut reqs = Vec::new();
    for (i, c) in concretes.iter().enumerate() {
        let (re, rp, plain) = match &extra {
            Some(v) => v[i].clone(),
            None => (Ok(Class::NoOpinion), Ok(Class::NoOpinion), Class::NoOpinion),
        };
        reqs.push(ReqReport {
            ar_uid: ars[i]["uid"].as_str().unwrap().into(),
            baseline: e.baseline(c, &verb).map_err(|x| x.0)?,
            phase2: e.phase2(&p1.outcome, c).map_err(|x| x.0),
            reauthorize: re, plain_residual_set: plain, reauthorize_placeholder: rp,
            dropped_fields: c.stats.dropped.clone(),
        });
    }
    Ok(ShapeReport {
        id: shape["id"].as_str().unwrap().into(), outcome: p1.outcome.clone(), phase1: p1, requests: reqs,
        expect: shape["expect"].as_array().unwrap().iter().map(|x| parse_class(x.as_str().unwrap())).collect(),
    })
}
