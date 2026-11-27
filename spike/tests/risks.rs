//! R-1..R-3, R-6..R-8, R-11 of docs/tpe-risk-report.md re-run against the pinned SHAs
//! (cedar 99a88d5), with the lints of R-9/R-11. Each risk has a positive check and a control.
use cedar_policy::*;
use serde_json::{json, Value};
use spike::{audit::*, engine::*, lint, model, shapes};
use std::str::FromStr;

fn owner_residual(action: &str, res_attrs: Value) -> String {
    let s = schema();
    let ps = kep5();
    let sc = Scenario { name: "x", action: Box::leak(action.to_string().into_boxed_str()), res_attrs };
    canonical_residuals(&s, &ps, &sc).remove("owner").unwrap()
}
fn base(request: Value) -> Value { json!({"name": pm("unknown"), "request": request, "stored": pm("absent")}) }
const DEEP: &str = r#"(== (. (. (. (. Res::"r1" request) metadata) labels) owner) "alice")"#;

#[test]
fn r1_deep_paths_stay_residual_and_fold_when_decided() {
    // request present: nothing below it is known, the whole guarded path stays residual
    let r = owner_residual("Create", base(pm("present")));
    assert!(r.contains(DEEP) && r.contains("(has (. Res::\"r1\" request) metadata)"), "{r}");
    // labels present: guards on request/metadata/labels are decided away
    let r = owner_residual("Create", base(json!({"metadata": {"labels": pm("present")}})));
    assert_eq!(r, format!("(and (has (. (. (. Res::\"r1\" request) metadata) labels) owner) {DEEP})"));
    // leaf known to equal / differ / be absent
    assert_eq!(owner_residual("Create", base(json!({"metadata": {"labels": {"owner": "alice"}}}))), "true");
    assert_eq!(owner_residual("Create", base(json!({"metadata": {"labels": {"owner": "bob"}}}))), "false");
    assert_eq!(owner_residual("Create", base(json!({"metadata": {"labels": {"owner": pm("absent")}}}))), "false");
    assert_eq!(owner_residual("Create", base(json!({"metadata": {"labels": pm("absent")}}))), "false");
    // control: leaf present but unknown value keeps only the comparison
    assert_eq!(owner_residual("Create", base(json!({"metadata": {"labels": {"owner": pm("present")}}}))), DEEP);
}

#[test]
fn r2_absent_prunes_and_unknown_does_not() {
    let s = schema();
    let ps = kep5();
    let get = |res: Value, action: &'static str| canonical_residuals(&s, &ps, &Scenario { name: "x", action, res_attrs: res });
    // update on a delete-like request: request absent kills every request-guarded policy
    let d = get(json!({"name": "n", "request": pm("absent"), "stored": pm("present")}), "Update");
    assert_eq!(d["owner"], "false");
    assert_eq!(d["finalizer"], "false");
    // create: stored absent prunes node-bound and unchanged
    let c = get(json!({"name": pm("unknown"), "request": pm("present"), "stored": pm("absent")}), "Update");
    assert_eq!(c["nodebound"], "false");
    assert_eq!(c["unchanged"], "false");
    // control: stored unknown keeps them residual
    let u = get(json!({"name": pm("unknown"), "request": pm("present"), "stored": pm("unknown")}), "Update");
    assert!(u["nodebound"].starts_with("(and"), "{}", u["nodebound"]);
    assert!(u["unchanged"].starts_with("(and"), "{}", u["unchanged"]);
}

#[test]
fn r8_closed_record_footgun_and_partial_marker() {
    // T-7: a JSON record without markers is CLOSED: omitted optional attributes are absent
    let closed = owner_residual("Create", base(json!({"metadata": {"name": "x"}})));
    assert_eq!(closed, "false", "closed record must prune (omitted labels = absent)");
    // with a marker inside the record the unstated attributes stay unknown
    let partial = owner_residual("Create", base(json!({"metadata": {"name": pm("present")}})));
    assert!(partial.starts_with("(and (has (. (. Res::\"r1\" request) metadata) labels)"), "{partial}");
    // `present` on the object (what the plan emits for unknown request bodies) is safe
    assert!(owner_residual("Create", base(pm("present"))).contains(DEEP));
}

#[test]
fn r8_converter_drops_undeclared_fields_and_omits_absent_ones() {
    let e = Engine::new();
    let ar = json!({"uid": "u", "kind": {"group": "", "version": "v1", "kind": "ConfigMap"}, "resource": {"group": "", "version": "v1", "resource": "configmaps"},
      "requestKind": {"group": "", "version": "v1", "kind": "ConfigMap"}, "requestResource": {"group": "", "version": "v1", "resource": "configmaps"},
      "name": "n", "namespace": "ns", "operation": "CREATE", "userInfo": {"username": "alice", "groups": []}, "dryRun": false,
      "object": {"apiVersion": "v1", "kind": "ConfigMap", "metadata": {"name": "n", "uid": "xyz", "labels": {"owner": "alice", "other": "x"}}, "data": {"a": "b"}},
      "oldObject": null});
    let c = e.concrete(&ar, NameSource::Plan).unwrap();
    // labels.other, metadata.uid and data.a are not declared: dropped (policies cannot see them)
    assert!(c.stats.dropped.iter().any(|d| d == "request.metadata.labels.other"), "{:?}", c.stats.dropped);
    assert!(c.stats.dropped.iter().any(|d| d == "request.metadata.uid"));
    assert!(c.stats.dropped.iter().any(|d| d == "request.data.a"));
    // a declared field of the wrong JSON type fails closed
    let mut bad = ar.clone();
    bad["object"]["metadata"]["labels"]["owner"] = json!(true);
    assert!(e.concrete(&bad, NameSource::Plan).is_err());
}

#[test]
fn r3_residual_sizes_and_condition_counts_over_the_shape_corpus() {
    let e = Engine::new();
    let (mut max_json, mut max_text, mut n, mut ratio_sum) = (0, 0, 0, 0.0);
    let mut over16 = 0;
    for s in shapes::load() {
        let r = shapes::run_shape(&e, &s, NameSource::Plan).unwrap();
        if let Outcome::Conditional { deny, allow } = &r.outcome { if deny.len() + allow.len() > 16 { over16 += 1; } }
        for x in &r.phase1.residuals {
            max_json = max_json.max(x.json_len); max_text = max_text.max(x.text_len); n += 1;
            ratio_sum += x.json_len as f64 / x.text_len as f64;
        }
    }
    println!("R-3: {n} residual policies, max text {max_text} B, max json {max_json} B, mean json/text {:.2}", ratio_sum / n as f64);
    assert!(n >= 30, "vacuity guard");
    assert!(max_json <= 2048, "R-3 threshold: <= 2 KiB per residual policy, got {max_json}");
    assert!(max_json < 10240);
    assert_eq!(over16, 0, "R-3 threshold: <= 16 conditions per decision");
}

#[test]
fn r6_error_node_frequency_over_all_attribute_shapes_is_zero_for_guarded_policies() {
    let e = Engine::new();
    let users = [json!({"username": "alice"}), json!({"username": "system:node:n1"}), json!({"username": "admin", "groups": ["system:masters"]}),
                 json!({"username": "system:serviceaccount:ns:sa", "uid": "u1"})];
    let resources = [("", "configmaps", ""), ("", "pods", ""), ("", "pods", "exec"), ("", "serviceaccounts", "token"), ("example.com", "widgets", "")];
    let (mut runs, mut residuals, mut with_error, mut exact_error, mut fail_closed) = (0, 0, 0, 0, 0);
    for u in &users { for (g, r, sub) in resources { for verb in ["create", "update", "patch", "delete", "deletecollection"] { for name in ["", "n"] {
        let a = Attrs { verb: verb.into(), group: g.into(), version: "v1".into(), resource: r.into(), subresource: sub.into(), name: name.into(), namespace: "ns".into(), user: u.clone() };
        let p = e.phase1(&a).unwrap();
        runs += 1; residuals += p.residuals.len();
        with_error += p.residuals.iter().filter(|x| x.has_error_node).count();
        exact_error += p.counts.ep + p.counts.ef;
        if matches!(p.outcome, Outcome::FailClosed { .. }) { fail_closed += 1; }
    } } } }
    println!("R-6: {runs} phase-1 runs, {residuals} residual policies, {with_error} with an error node, {exact_error} exactly `error`, {fail_closed} fail-closed");
    assert!(runs >= 200 && residuals >= 100, "vacuity guard");
    assert_eq!(with_error, 0);
    assert_eq!(exact_error, 0);
    assert_eq!(fail_closed, 0);
}

#[test]
fn r6_control_a_forbid_that_can_error_produces_an_error_node_and_fails_closed() {
    let extra = r#"

@id("err-forbid")
forbid(principal, action in k8s::Action::"create", resource is core::ConfigMap)
when { resource has request && resource.request has metadata && resource.request has apiVersion && 1 + 9223372036854775807 > 0 };
"#;
    let e = Engine::with(model::SCHEMA, &format!("{}{extra}", model::POLICIES));
    let s = shapes::load().into_iter().find(|s| s["id"] == "create-cm-owner").unwrap();
    let a = Attrs::from_sar(&s["sar"]);
    let p = e.phase1(&a).unwrap();
    assert!(p.residuals.iter().any(|x| x.policy_id == "err-forbid" && x.has_error_node), "{:?}", p.residuals);
    // fail closed: a conditional Deny exists, so the FailureDecision is Deny (never Allow)
    assert!(matches!(p.outcome, Outcome::FailClosed { class: Class::Deny, .. }), "{:?}", p.outcome);
    assert!(!p.plain_residual_set_json_roundtrip);
}

#[test]
fn r7_plain_authorizer_equals_reauthorize_on_audit_scenarios() {
    let s = schema();
    let ps = kep5();
    let sc = &scenarios()[1]; // update: name known, request present, stored unknown
    let pes = partial_entities(&s, &sc.res_attrs);
    let preq = preq(&s, sc.action);
    let resp = ps.tpe(&preq, &pes, &s).unwrap();
    let act = EntityUid::from_str("Action::\"Update\"").unwrap();
    let req = Request::new(EntityUid::from_str("User::\"alice\"").unwrap(), act, EntityUid::from_str("Res::\"r1\"").unwrap(), Context::empty(), Some(&s)).unwrap();
    let mk = |request: Value, stored: Option<Value>| {
        let mut a = json!({"name": "settings", "request": request});
        if let Some(st) = stored { a["stored"] = st; }
        Entities::from_json_value(json!([
            {"uid": {"type": "User", "id": "alice"}, "attrs": {"name": "alice", "nodeName": "n1"}, "parents": []},
            {"uid": {"type": "Res", "id": "r1"}, "attrs": a, "parents": []}]), Some(&s)).unwrap()
    };
    let cases = vec![
        mk(json!({"metadata": {"labels": {"owner": "alice"}}}), None),
        mk(json!({"metadata": {"labels": {"owner": "bob"}}}), None),
        mk(json!({"metadata": {"finalizers": ["protected"], "labels": {"owner": "alice"}}}), None),
        mk(json!({"spec": {"nodeName": "n2"}}), Some(json!({"spec": {"nodeName": "n1"}}))),
        mk(json!({"spec": {"nodeName": "n1"}}), Some(json!({"spec": {"nodeName": "n1"}}))),
    ];
    let (mut agree, mut classes) = (0, std::collections::BTreeSet::new());
    for es in &cases {
        let a = classify(&resp.reauthorize(&req, es).unwrap());
        let b = classify(&Authorizer::new().is_authorized(&req, &resp.policy_set(), es));
        let c = classify(&Authorizer::new().is_authorized(&req, &ps, es));
        assert_eq!(a, b); assert_eq!(b, c);
        classes.insert(a); agree += 1;
    }
    assert_eq!(agree, 5);
    assert!(classes.len() >= 3, "vacuity guard: classes {classes:?}");
    // the consistency check that reauthorize adds and the plain authorizer lacks (T-5): stored present
    // although TPE said ... here `stored` was unknown so any is consistent; with `absent` it must fail
    let pes2 = partial_entities(&s, &json!({"name": "settings", "request": pm("present"), "stored": pm("absent")}));
    let resp2 = ps.tpe(&preq, &pes2, &s).unwrap();
    let inconsistent = mk(json!({"metadata": {}}), Some(json!({"spec": {"nodeName": "n1"}})));
    assert!(resp2.reauthorize(&req, &inconsistent).is_err(), "reauthorize must reject stored present vs partial absent");
    // while the plain authorizer happily evaluates it (so evaluateConditions needs its own consistency story)
    let _ = Authorizer::new().is_authorized(&req, &resp2.policy_set(), &inconsistent);
}

#[test]
fn r11_forbid_error_lint_flags_the_known_constructs_and_not_the_kep_forbids() {
    let flagged = |body: &str| lint::forbid_can_error(&lint::est(&format!("forbid(principal, action, resource) when {{ {body} }};")));
    assert!(flagged("1 + 2 > 0").iter().any(|f| f.contains("arithmetic")));
    assert!(flagged("1 * 2 > 0").iter().any(|f| f.contains("arithmetic")));
    assert!(flagged("1 - 2 > 0").iter().any(|f| f.contains("arithmetic")));
    assert!(flagged("-context.n > 0").iter().any(|f| f.contains("negation")));
    assert!(flagged("decimal(\"1.0\").lessThan(decimal(\"2.0\"))").iter().any(|f| f.contains("extension")));
    assert!(flagged("ip(\"1.2.3.4\").isIpv4()").iter().any(|f| f.contains("extension")));
    assert!(flagged("principal.hasTag(\"a\") && principal.getTag(\"a\") == \"x\"").iter().any(|f| f.contains("getTag")));
    // controls: the KEP forbids use only has/./==/!=/contains/like and are not flagged
    for (id, body) in split_policies(spike::audit::KEP5).into_iter().chain(split_policies(model::POLICIES)) {
        let est = lint::est(&body);
        if est["effect"] == "forbid" { assert!(lint::forbid_can_error(&est).is_empty(), "{id}: {:?}", lint::forbid_can_error(&est)); }
    }
}

#[test]
fn has_guard_lint_isolates_the_bad_policy() {
    let (frag, _) = SchemaFragment::from_cedarschema_str(model::SCHEMA).unwrap();
    let schema = Schema::from_schema_fragments([frag]).unwrap();
    let bad = r#"

@id("unguarded")
permit(principal, action in k8s::Action::"create", resource is core::ConfigMap)
when { resource.request.metadata.labels.owner == principal.name };
"#;
    let mixed = format!("{}{bad}", model::POLICIES);
    let found = lint::has_guard_lint(&schema, &mixed);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].0, "unguarded");
    assert!(found[0].1.iter().any(|e| e.contains("optional") || e.contains("attribute")), "{found:?}");
    assert!(lint::has_guard_lint(&schema, model::POLICIES).is_empty());
    // T-6 demonstration: TPE over the whole mixed set refuses everything
    let ps = policy_set_from(&mixed);
    let e = Engine::with(model::SCHEMA, &mixed);
    let s = shapes::load().into_iter().find(|s| s["id"] == "create-cm-owner").unwrap();
    assert!(e.phase1(&Attrs::from_sar(&s["sar"])).is_err(), "one invalid policy fails the whole TPE call");
    assert_eq!(ps.policies().count(), 12);
}

#[test]
fn reserved_uid_and_action_lints() {
    let ok = lint::est(r#"permit(principal, action, resource is core::ConfigMap) when { resource has name };"#);
    assert!(lint::reserved_uid_lint(&ok, model::RESERVED_UID).is_empty());
    let scope = lint::est(r#"permit(principal, action, resource == core::ConfigMap::"@conditional-request");"#);
    assert!(!lint::reserved_uid_lint(&scope, model::RESERVED_UID).is_empty());
    let lit = lint::est(r#"permit(principal, action, resource is core::ConfigMap) when { core::ConfigMap::"@conditional-request" has name };"#);
    assert!(lint::reserved_uid_lint(&lit, model::RESERVED_UID).iter().any(|m| m.contains("entity literal")));
    let cmp = lint::est(r#"permit(principal, action, resource is core::ConfigMap) when { resource == core::ConfigMap::"x" };"#);
    assert!(lint::reserved_uid_lint(&cmp, model::RESERVED_UID).iter().any(|m| m.contains("resource ==")));
    // no shipped policy trips the lint
    for (id, body) in split_policies(model::POLICIES) { assert!(lint::reserved_uid_lint(&lint::est(&body), model::RESERVED_UID).is_empty(), "{id}"); }
    // D-13: residuals of the corpus never mention `action`
    let e = Engine::new();
    for s in shapes::load() {
        let r = shapes::run_shape(&e, &s, NameSource::Plan).unwrap();
        if let Outcome::Conditional { deny, allow } = &r.outcome {
            for c in deny.iter().chain(allow) { assert!(!lint::residual_mentions_action(&c.json["conditions"][0]["body"]), "{}", c.policy_id); }
        }
    }
    // control: the lint does fire on an action-mentioning body
    assert!(lint::residual_mentions_action(&lint::est(r#"permit(principal, action, resource) when { action == Action::"x" };"#)["conditions"][0]["body"]));
}
