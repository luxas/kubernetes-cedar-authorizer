#!/usr/bin/env python3
"""Generate conformance/shapes.json (R-12). Hand-built from the KEP ACR example
(kubernetes review/kep.md "Example ACR request") and the integration tests in
test/integration/apiserver/conditionalauthorization. Run: python3 conformance/gen_shapes.py"""
import json, pathlib

def user(name, groups=("system:authenticated",), uid="", extra=None):
    u = {"username": name, "groups": list(groups)}
    if uid: u["uid"] = uid
    if extra: u["extra"] = extra
    return u

def sar(u, verb, group, version, resource, sub="", name="", ns=""):
    ra = {"verb": verb, "group": group, "version": version, "resource": resource}
    if sub: ra["subresource"] = sub
    if name: ra["name"] = name
    if ns: ra["namespace"] = ns
    return {"user": u, "resourceAttributes": ra}

def ar(uid, op, u, group, version, kind, resource, name="", ns="", sub="", obj=None, old=None,
       dry=False, req_version=None, opts_kind=None, kgroup=None):
    kg = group if kgroup is None else kgroup
    rv = req_version or version
    a = {"uid": uid,
         "kind": {"group": kg, "version": version, "kind": kind},
         "resource": {"group": group, "version": version, "resource": resource},
         "requestKind": {"group": kg, "version": rv, "kind": kind},
         "requestResource": {"group": group, "version": rv, "resource": resource},
         "name": name, "namespace": ns, "operation": op, "userInfo": u,
         "object": obj, "oldObject": old, "dryRun": dry}
    if sub:
        a["subResource"] = sub; a["requestSubResource"] = sub
    if opts_kind: a["options"] = {"apiVersion": "meta.k8s.io/v1", "kind": opts_kind}
    return a

def cm(name=None, ns="team-a", owner=None, fin=None, gen=None, data=None, extra_labels=None):
    md = {}
    if name is not None: md["name"] = name
    if gen: md["generateName"] = gen
    if ns: md["namespace"] = ns
    labels = {}
    if owner: labels["owner"] = owner
    if extra_labels: labels.update(extra_labels)
    if labels: md["labels"] = labels
    if fin: md["finalizers"] = fin
    o = {"apiVersion": "v1", "kind": "ConfigMap", "metadata": md}
    if data is not None: o["data"] = data
    return o

def pod(name, node, ns="default"):
    return {"apiVersion": "v1", "kind": "Pod", "metadata": {"name": name, "namespace": ns},
            "spec": {"nodeName": node, "containers": [{"name": "app", "image": "x"}]}}

def widget(name, owner, ver, ns="team-a"):
    return {"apiVersion": f"example.com/{ver}", "kind": "Widget",
            "metadata": {"name": name, "namespace": ns, "labels": {"owner": owner}},
            "spec": {"size": 3}}

alice = user("alice")
sa_user = user("system:serviceaccount:team-a:builder", ("system:serviceaccounts", "system:serviceaccounts:team-a", "system:authenticated"), uid="3f2a9c1e-0000-4000-8000-000000000001")
node1 = user("system:node:node-1", ("system:nodes", "system:authenticated"))
S = []
def shape(id, desc, s, ars, expect, **notes):
    S.append({"id": id, "description": desc, "sar": s, "admissionRequests": ars, "expect": expect, **notes})

shape("create-cm-owner", "plain create, name in body, owner label == requester (KEP example shape)",
  sar(alice, "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-01", "CREATE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      obj=cm("settings", owner="alice", data={"mode": "fast"}), opts_kind="CreateOptions")],
  ["Allow"])
shape("create-cm-generatename", "create with generateName: name unknown at authorization time, generated name present in object at admission; AdmissionRequest.name is empty",
  sar(alice, "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-02", "CREATE", alice, "", "v1", "ConfigMap", "configmaps", name="", ns="team-a",
      obj=cm("safe-x7k2p", gen="safe-"), opts_kind="CreateOptions")],
  ["Allow"], note="name must come from object.metadata.name (plan 3.2, review B I4)")
shape("create-cm-generatename-unresolved", "generateName not yet applied: no name anywhere (if admission ran before name generation)",
  sar(alice, "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-03", "CREATE", alice, "", "v1", "ConfigMap", "configmaps", name="", ns="team-a",
      obj=cm(None, gen="safe-"), opts_kind="CreateOptions")],
  ["NoOpinion"], note="name-prefix policy does not apply when the name is absent")
shape("create-sa-token", "create serviceaccounts/token: name in URL, body is TokenRequest, no stored object",
  sar(alice, "create", "", "v1", "serviceaccounts", sub="token", name="builder", ns="team-a"),
  [ar("u-04", "CREATE", alice, "", "v1", "TokenRequest", "serviceaccounts", kgroup="authentication.k8s.io", name="builder", ns="team-a", sub="token",
      obj={"apiVersion": "authentication.k8s.io/v1", "kind": "TokenRequest",
           "metadata": {"name": "builder", "namespace": "team-a"},
           "spec": {"audiences": ["api"], "expirationSeconds": 3600}}, opts_kind="CreateOptions")],
  ["Allow"], note="admission kind/resource group differ from the SAR group ('' vs authentication.k8s.io)")
shape("connect-pods-exec", "create pods/exec (POST connect): operation CONNECT, object PodExecOptions, oldObject null",
  sar(alice, "create", "", "v1", "pods", sub="exec", name="web-0", ns="default"),
  [ar("u-05", "CONNECT", alice, "", "v1", "PodExecOptions", "pods", name="web-0", ns="default", sub="exec",
      obj={"apiVersion": "v1", "kind": "PodExecOptions", "stdin": True, "stdout": True,
           "container": "debug", "command": ["sh"]})],
  ["Allow"], note="operation CONNECT; verb is create")
shape("update-cm", "update, owner unchanged",
  sar(alice, "update", "", "v1", "configmaps", name="settings", ns="team-a"),
  [ar("u-06", "UPDATE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      obj=cm("settings", owner="alice", data={"mode": "slow"}), old=cm("settings", owner="alice", data={"mode": "fast"}), opts_kind="UpdateOptions")],
  ["Allow"])
shape("update-cm-finalizer", "update adds the protected finalizer: conditional forbid fires",
  sar(alice, "update", "", "v1", "configmaps", name="settings", ns="team-a"),
  [ar("u-07", "UPDATE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      obj=cm("settings", owner="alice", fin=["example.com/protected"]), old=cm("settings", owner="alice"), opts_kind="UpdateOptions")],
  ["Deny"])
shape("update-to-create", "update that turns into create: operation CREATE, oldObject null (secondary create check is unconditional in v1.38)",
  sar(alice, "update", "", "v1", "configmaps", name="new-one", ns="team-a"),
  [ar("u-08", "CREATE", alice, "", "v1", "ConfigMap", "configmaps", name="new-one", ns="team-a",
      obj=cm("new-one", owner="alice"), opts_kind="UpdateOptions")],
  ["Allow"], note="verb update, operation CREATE: action cannot be recovered from the AdmissionRequest")
shape("patch-pod-node-ok", "patch by node principal on a pod bound to it, nodeName unchanged",
  sar(node1, "patch", "", "v1", "pods", name="web-0", ns="default"),
  [ar("u-09", "UPDATE", node1, "", "v1", "Pod", "pods", name="web-0", ns="default",
      obj=pod("web-0", "node-1"), old=pod("web-0", "node-1"), opts_kind="PatchOptions")],
  ["Allow"], note="verb patch, operation UPDATE; action patch must be in group update")
shape("patch-pod-node-moved", "patch by node principal changes spec.nodeName: sensitive-field forbid fires",
  sar(node1, "patch", "", "v1", "pods", name="web-0", ns="default"),
  [ar("u-10", "UPDATE", node1, "", "v1", "Pod", "pods", name="web-0", ns="default",
      obj=pod("web-0", "node-2"), old=pod("web-0", "node-1"), opts_kind="PatchOptions")],
  ["Deny"])
shape("delete-cm", "delete: no object, stored object visible",
  sar(alice, "delete", "", "v1", "configmaps", name="settings", ns="team-a"),
  [ar("u-11", "DELETE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      old=cm("settings", owner="alice"), opts_kind="DeleteOptions")],
  ["Allow"])
shape("deletecollection-cm", "deletecollection over two objects: name unknown at authorization, one DELETE admission per object",
  sar(alice, "deletecollection", "", "v1", "configmaps", ns="team-a"),
  [ar("u-12a", "DELETE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      old=cm("settings", owner="alice"), opts_kind="DeleteOptions"),
   ar("u-12b", "DELETE", alice, "", "v1", "ConfigMap", "configmaps", name="keep-1", ns="team-a",
      old=cm("keep-1", owner="alice"), opts_kind="DeleteOptions")],
  ["Allow", "Deny"], note="action deletecollection must be in group delete")
shape("create-cm-dryrun", "dryRun=true is not visible to policies; owner is bob so no permit applies",
  sar(alice, "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-13", "CREATE", alice, "", "v1", "ConfigMap", "configmaps", name="settings", ns="team-a",
      obj=cm("settings", owner="bob"), dry=True, opts_kind="CreateOptions")],
  ["NoOpinion"])
shape("create-widget-multiversion", "CRD served in v1beta1 and v1 (storage v1): request kind is v1beta1, converted kind is v1",
  sar(alice, "create", "example.com", "v1beta1", "widgets", ns="team-a"),
  [ar("u-14", "CREATE", alice, "example.com", "v1", "Widget", "widgets", name="w1", ns="team-a",
      obj=widget("w1", "alice", "v1beta1"), req_version="v1beta1", opts_kind="CreateOptions")],
  ["Allow"], note="object is in the request version (requestKind), not the storage version (kind)")
shape("create-cm-serviceaccount", "ServiceAccount principal with uid; principal type derived from the username prefix",
  sar(sa_user, "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-15", "CREATE", sa_user, "", "v1", "ConfigMap", "configmaps", name="s", ns="team-a",
      obj=cm("s", owner="system:serviceaccount:team-a:builder"), opts_kind="CreateOptions")],
  ["Allow"])
shape("create-cm-user-no-uid-extra", "user without uid and with extra: principal id is a hash of the username",
  sar(user("bob", extra={"scopes": ["a", "b"]}), "create", "", "v1", "configmaps", ns="team-a"),
  [ar("u-16", "CREATE", user("bob", extra={"scopes": ["a", "b"]}), "", "v1", "ConfigMap", "configmaps", name="mine", ns="team-a",
      obj=cm("mine", owner="bob"), opts_kind="CreateOptions")],
  ["Allow"])

out = pathlib.Path(__file__).with_name("shapes.json")
out.write_text(json.dumps({"version": 1, "shapes": S}, indent=1) + "\n")
print(len(S), "shapes ->", out)
