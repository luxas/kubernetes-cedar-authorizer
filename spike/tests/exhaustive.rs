//! Exhaustive small-domain differential: phase 2 over JSON conditions == original policies,
//! for every combination of verb x principal x owner/finalizer/name/nodeName variants.
use serde_json::{json, Value};
use spike::engine::*;

fn cm(name: &str, owner: Option<&str>, fin: bool) -> Value {
    let mut md = json!({"name": name, "namespace": "team-a"});
    if let Some(o) = owner { md["labels"] = json!({"owner": o}); }
    if fin { md["finalizers"] = json!(["example.com/protected"]); }
    json!({"apiVersion": "v1", "kind": "ConfigMap", "metadata": md})
}
fn pod(node: Option<&str>) -> Value {
    let mut spec = json!({"containers": []});
    if let Some(n) = node { spec["nodeName"] = json!(n); }
    json!({"apiVersion": "v1", "kind": "Pod", "metadata": {"name": "p", "namespace": "default"}, "spec": spec})
}
fn users() -> Vec<Value> {
    vec![json!({"username": "alice", "groups": ["system:authenticated"]}),
         json!({"username": "system:node:node-1", "groups": ["system:nodes"]}),
         json!({"username": "admin", "groups": ["system:masters"]}),
         json!({"username": "system:serviceaccount:team-a:builder", "uid": "uid-sa", "groups": []})]
}
fn op(verb: &str, has_old: bool) -> &'static str {
    match verb { "create" => "CREATE", "update" | "patch" => if has_old { "UPDATE" } else { "CREATE" }, _ => "DELETE" }
}

fn check(e: &Engine, verb: &str, resource: &str, kind: &str, user: &Value, name: &str, obj: Option<Value>, old: Option<Value>, stats: &mut (usize, usize, usize)) {
    let sar_name = if verb == "create" || verb == "deletecollection" { "" } else { name };
    let ns = if resource == "pods" { "default" } else { "team-a" };
    let attrs = Attrs { verb: verb.into(), group: "".into(), version: "v1".into(), resource: resource.into(), subresource: "".into(), name: sar_name.into(), namespace: ns.into(), user: user.clone() };
    let ar_name = if verb == "create" { "" } else { name };
    let ar = json!({"uid": "u", "kind": {"group": "", "version": "v1", "kind": kind}, "resource": {"group": "", "version": "v1", "resource": resource},
        "requestKind": {"group": "", "version": "v1", "kind": kind}, "requestResource": {"group": "", "version": "v1", "resource": resource},
        "name": ar_name, "namespace": ns, "operation": op(verb, old.is_some()), "userInfo": user, "object": obj, "oldObject": old, "dryRun": false});
    let p1 = e.phase1(&attrs).unwrap();
    let c = e.concrete(&ar, NameSource::Plan).unwrap();
    let want = e.baseline(&c, verb).unwrap();
    let got = e.phase2(&p1.outcome, &c).unwrap();
    assert_eq!(got, want, "verb={verb} user={user} name={name} ar={ar} outcome={:?}", p1.outcome);
    stats.0 += 1;
    match want { Class::Allow => stats.1 += 1, Class::Deny => stats.2 += 1, _ => {} }
}

#[test]
fn configmap_and_pod_small_domain() {
    let e = Engine::new();
    let mut stats = (0usize, 0usize, 0usize);
    let owners = [None, Some("alice"), Some("bob"), Some("admin"), Some("system:serviceaccount:team-a:builder")];
    for user in users() {
        for name in ["safe-1", "keep-1", "x"] {
            for o_new in owners { for o_old in owners { for fin in [false, true] {
                let new = cm(name, o_new, fin);
                let old = cm(name, o_old, false);
                check(&e, "create", "configmaps", "ConfigMap", &user, name, Some(new.clone()), None, &mut stats);
                check(&e, "update", "configmaps", "ConfigMap", &user, name, Some(new.clone()), Some(old.clone()), &mut stats);
                check(&e, "patch", "configmaps", "ConfigMap", &user, name, Some(new.clone()), Some(old.clone()), &mut stats);
                check(&e, "update", "configmaps", "ConfigMap", &user, name, Some(new), None, &mut stats); // update-to-create
                check(&e, "delete", "configmaps", "ConfigMap", &user, name, None, Some(old.clone()), &mut stats);
                check(&e, "deletecollection", "configmaps", "ConfigMap", &user, name, None, Some(old), &mut stats);
            } } }
        }
        for n_new in [None, Some("node-1"), Some("node-2")] { for n_old in [None, Some("node-1"), Some("node-2")] {
            for verb in ["update", "patch"] {
                check(&e, verb, "pods", "Pod", &user, "p", Some(pod(n_new)), Some(pod(n_old)), &mut stats);
            }
            check(&e, "delete", "pods", "Pod", &user, "p", None, Some(pod(n_old)), &mut stats);
        } }
    }
    println!("requests compared: {} (Allow {}, Deny {})", stats.0, stats.1, stats.2);
    assert!(stats.0 > 3000, "vacuity guard");
    assert!(stats.1 > 100 && stats.2 > 100, "both Allow and Deny must be exercised");
}
