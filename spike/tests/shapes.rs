//! R-12: every shape: phase 2 over the JSON conditions == original policies on concrete data
//! == hand-written expectation, plus mutation checks proving the comparison is not vacuous.
use spike::{engine::*, shapes::*};

fn all(e: &Engine, ns: NameSource) -> Vec<(serde_json::Value, Result<ShapeReport, String>)> {
    load().into_iter().map(|s| { let r = run_shape(e, &s, ns); (s, r) }).collect()
}

#[test]
fn every_shape_phase2_equals_baseline_and_expectation() {
    let e = Engine::new();
    let mut compared = 0;
    let (mut cond, mut uncond) = (0, 0);
    for (s, r) in all(&e, NameSource::Plan) {
        let r = r.unwrap_or_else(|m| panic!("{}: {m}", s["id"]));
        match &r.outcome { Outcome::Conditional { .. } => cond += 1, Outcome::Unconditional(_) => uncond += 1, o => panic!("{}: fail closed {o:?}", r.id) }
        assert_eq!(r.requests.len(), r.expect.len(), "{}", r.id);
        for (i, q) in r.requests.iter().enumerate() {
            assert_eq!(q.baseline, r.expect[i], "{} #{i}: baseline vs hand expectation", r.id);
            assert_eq!(q.phase2.as_ref().unwrap(), &q.baseline, "{} #{i}: phase 2 vs original policies", r.id);
            // R-7: TpeResponse::reauthorize and a plain Authorizer over the residual set agree
            assert_eq!(q.reauthorize.as_ref().unwrap(), &q.baseline, "{} #{i}: reauthorize", r.id);
            assert_eq!(q.plain_residual_set, q.baseline, "{} #{i}: plain residual set", r.id);
            compared += 1;
        }
    }
    println!("requests compared: {compared}, conditional shapes: {cond}, unconditional: {uncond}");
    assert!(compared >= 20, "vacuity guard: only {compared} requests compared");
    assert!(cond >= 15 && uncond >= 3, "vacuity guard: cond {cond} uncond {uncond}");
    // the corpus must exercise all three classes on conditional outcomes
    let mut seen = std::collections::BTreeSet::new();
    for (_, r) in all(&e, NameSource::Plan) { for q in r.unwrap().requests { seen.insert(q.baseline); } }
    assert_eq!(seen.len(), 3);
}

#[test]
fn out_of_scope_shape_is_unconditional_no_opinion() {
    let e = Engine::new();
    let s = load().into_iter().find(|s| s["id"] == "create-secret-out-of-scope").unwrap();
    let r = run_shape(&e, &s, NameSource::Plan).unwrap();
    assert!(matches!(r.outcome, Outcome::Unconditional(Class::NoOpinion)));
}

#[test]
fn placeholder_action_breaks_reauthorize_c2() {
    // C2 (review B): TpeResponse::reauthorize needs the real action; AdmissionRequest has none.
    let e = Engine::new();
    let mut n = 0;
    for (_, r) in all(&e, NameSource::Plan) {
        let r = r.unwrap();
        if let Outcome::Conditional { .. } = r.outcome {
            for q in &r.requests {
                let err = q.reauthorize_placeholder.as_ref().unwrap_err();
                assert!(err.contains("InconsistentAction"), "{err}");
                n += 1;
            }
        }
    }
    assert!(n >= 15);
}

// ---- mutations: each must be detected, otherwise the comparison above proves nothing ----

fn mismatches_with(e: &Engine, mutate: impl Fn(&Outcome) -> Outcome) -> Vec<String> {
    let mut bad = vec![];
    for s in load() {
        let attrs = Attrs::from_sar(&s["sar"]);
        if resource_type(&attrs.group, &attrs.resource, &attrs.subresource).is_none() { continue; }
        let p1 = e.phase1(&attrs).unwrap();
        let m = mutate(&p1.outcome);
        for ar in s["admissionRequests"].as_array().unwrap() {
            let c = e.concrete(ar, NameSource::Plan).unwrap();
            if e.phase2(&m, &c).unwrap() != e.baseline(&c, &attrs.verb).unwrap() { bad.push(format!("{}:{}", s["id"].as_str().unwrap(), ar["uid"])); }
        }
    }
    bad
}

#[test]
fn mutation_dropping_deny_conditions_is_detected() {
    let bad = mismatches_with(&Engine::new(), |o| match o {
        Outcome::Conditional { allow, .. } => Outcome::Conditional { deny: vec![], allow: allow.clone() },
        o => o.clone() });
    assert!(bad.iter().any(|b| b.contains("update-cm-finalizer")), "{bad:?}");
    assert!(bad.iter().any(|b| b.contains("patch-pod-node-moved")), "{bad:?}");
    assert!(bad.len() >= 4, "{bad:?}");
}

#[test]
fn mutation_dropping_allow_conditions_is_detected() {
    let bad = mismatches_with(&Engine::new(), |o| match o {
        Outcome::Conditional { deny, .. } => Outcome::Conditional { deny: deny.clone(), allow: vec![] },
        o => o.clone() });
    assert!(bad.len() >= 8, "{bad:?}");
}

#[test]
fn mutation_flipping_unconditional_is_detected() {
    let bad = mismatches_with(&Engine::new(), |o| match o {
        Outcome::Unconditional(Class::Allow) => Outcome::Unconditional(Class::NoOpinion),
        o => o.clone() });
    assert!(bad.iter().any(|b| b.contains("delete-cm-masters")), "{bad:?}");
}

#[test]
fn mutation_wrong_name_source_is_detected_by_expectation() {
    // plan 3.2: name on create comes from object.metadata.name; AdmissionRequest.name is empty.
    let e = Engine::new();
    let s = load().into_iter().find(|s| s["id"] == "create-cm-generatename").unwrap();
    let r = run_shape(&e, &s, NameSource::AdmissionName).unwrap();
    assert_eq!(r.requests[0].baseline, Class::NoOpinion);
    assert_ne!(r.requests[0].baseline, r.expect[0], "the AdmissionRequest.name mutation must contradict the expectation");
    let ok = run_shape(&e, &s, NameSource::Plan).unwrap();
    assert_eq!(ok.requests[0].baseline, ok.expect[0]);
}

#[test]
fn mutation_kind_version_instead_of_request_kind_fails_closed() {
    let e = Engine::new();
    let s = load().into_iter().find(|s| s["id"] == "create-widget-multiversion").unwrap();
    let mut ar = s["admissionRequests"][0].clone();
    assert_eq!(ar["kind"]["version"], "v1");
    assert_eq!(ar["requestKind"]["version"], "v1beta1");
    // an apiserver that sent the object in the storage version instead of the request version
    ar["object"]["apiVersion"] = serde_json::json!("example.com/v1");
    assert!(e.concrete(&ar, NameSource::Plan).is_err());
}

#[test]
fn mutation_patch_not_in_update_group_changes_decision() {
    // D-13: without the action group, a patch no longer matches `action in Action::"update"`.
    let broken = spike::model::SCHEMA.replace(r#"action "patch" in ["update"]"#, r#"action "patch""#);
    assert_ne!(broken, spike::model::SCHEMA);
    let e = Engine::with(&broken, spike::model::POLICIES);
    let s = load().into_iter().find(|s| s["id"] == "patch-pod-node-ok").unwrap();
    let r = run_shape(&e, &s, NameSource::Plan).unwrap();
    assert_eq!(r.requests[0].baseline, Class::NoOpinion);
    assert_ne!(r.requests[0].baseline, r.expect[0]);
}
