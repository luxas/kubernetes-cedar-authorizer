//! Hand-written K8s-flavoured Cedar schema and the KEP-style policies used by the spike.
//! Decisions applied: D-12 (deterministic principal ids, labels as records, no entity-typed
//! attributes besides principal and the synthetic resource), D-13 (patch in update,
//! deletecollection in delete), D-11 (one reserved resource uid per resource type),
//! optional record-typed `request`/`stored` (T-8), `name` optional (unknown on create).

/// Reserved synthetic id of the single resource entity (never a valid Kubernetes name).
pub const RESERVED_UID: &str = "@conditional-request";

pub const SCHEMA: &str = r#"
namespace meta {
  // R-9 variant A: map[string]string as a record with declared keys.
  type Labels = { owner?: String, tier?: String };
  type ObjectMeta = {
    name?: String, generateName?: String, namespace?: String,
    labels?: Labels, finalizers?: Set<String>
  };
}
namespace k8s {
  entity User = { name: String, groups: Set<String> };
  entity ServiceAccount = { name: String, groups: Set<String>, namespace: String, saName: String };
  entity Node = { name: String, groups: Set<String>, nodeName: String };
  action "create", "update", "delete", "evaluate" appliesTo {
    principal: [User, ServiceAccount, Node],
    resource: [core::ConfigMap, core::Pod, core::PodExec, core::ServiceAccountToken, example::Widget],
    context: {}
  };
  action "patch" in ["update"] appliesTo {
    principal: [User, ServiceAccount, Node],
    resource: [core::ConfigMap, core::Pod, core::PodExec, core::ServiceAccountToken, example::Widget],
    context: {}
  };
  action "deletecollection" in ["delete"] appliesTo {
    principal: [User, ServiceAccount, Node],
    resource: [core::ConfigMap, core::Pod, core::PodExec, core::ServiceAccountToken, example::Widget],
    context: {}
  };
}
namespace core {
  type ConfigMapObj = { apiVersion?: String, kind?: String, metadata?: meta::ObjectMeta, data?: { mode?: String } };
  type PodObj = { apiVersion?: String, kind?: String, metadata?: meta::ObjectMeta, spec?: { nodeName?: String } };
  entity ConfigMap = {
    apiGroup: String, resource: String, subresource?: String, namespace?: String, name?: String,
    request?: ConfigMapObj, stored?: ConfigMapObj
  };
  entity Pod = {
    apiGroup: String, resource: String, subresource?: String, namespace?: String, name?: String,
    request?: PodObj, stored?: PodObj
  };
  // create on a subresource: request is the kind of the subresource body, no stored object (S-10).
  entity PodExec = {
    apiGroup: String, resource: String, subresource?: String, namespace?: String, name?: String,
    request?: { apiVersion?: String, kind?: String, container?: String, command?: Set<String>, stdin?: Bool, stdout?: Bool }
  };
  entity ServiceAccountToken = {
    apiGroup: String, resource: String, subresource?: String, namespace?: String, name?: String,
    request?: { apiVersion?: String, kind?: String, metadata?: meta::ObjectMeta,
                spec?: { audiences?: Set<String>, expirationSeconds?: Long } }
  };
}
namespace example {
  entity Widget = {
    apiGroup: String, resource: String, subresource?: String, namespace?: String, name?: String,
    request?: { apiVersion?: String, kind?: String, metadata?: meta::ObjectMeta, spec?: { size?: Long } },
    stored?:  { apiVersion?: String, kind?: String, metadata?: meta::ObjectMeta, spec?: { size?: Long } }
  };
}
"#;

/// Nine policies: the five KEP-style ones of PLAN stage 1 (owner-label, sensitive-unchanged,
/// name-prefix, finalizer, node-bound) plus four that cover the remaining shapes.
/// Every optional access is `has`-guarded (T-6). No policy mentions the resource uid.
pub const POLICIES: &str = r#"
@id("owner-label")
permit(principal, action in [k8s::Action::"create", k8s::Action::"update"], resource is core::ConfigMap)
when { resource has request && resource.request has metadata && resource.request.metadata has labels
       && resource.request.metadata.labels has owner
       && resource.request.metadata.labels.owner == principal.name };

@id("sensitive-unchanged")
forbid(principal, action in k8s::Action::"update", resource is core::Pod)
when { resource has stored && resource.stored has spec && resource.stored.spec has nodeName
       && resource has request && resource.request has spec && resource.request.spec has nodeName
       && resource.stored.spec.nodeName != resource.request.spec.nodeName };

@id("name-prefix")
permit(principal, action in k8s::Action::"create", resource is core::ConfigMap)
when { resource has name && resource.name like "safe-*" };

@id("finalizer")
forbid(principal, action in [k8s::Action::"create", k8s::Action::"update"], resource is core::ConfigMap)
when { resource has request && resource.request has metadata && resource.request.metadata has finalizers
       && resource.request.metadata.finalizers.contains("example.com/protected") }
unless { principal.groups.contains("system:masters") };

@id("node-bound")
permit(principal is k8s::Node, action in k8s::Action::"update", resource is core::Pod)
when { resource has stored && resource.stored has spec && resource.stored.spec has nodeName
       && resource.stored.spec.nodeName == principal.nodeName };

@id("delete-owner")
permit(principal, action in k8s::Action::"delete", resource is core::ConfigMap)
when { resource has stored && resource.stored has metadata && resource.stored.metadata has labels
       && resource.stored.metadata.labels has owner
       && resource.stored.metadata.labels.owner == principal.name };

@id("delete-keep")
forbid(principal, action in k8s::Action::"delete", resource is core::ConfigMap)
when { resource has name && resource.name like "keep-*" };

@id("token-audience")
permit(principal, action in k8s::Action::"create", resource is core::ServiceAccountToken)
when { resource has request && resource.request has spec && resource.request.spec has audiences
       && resource.request.spec.audiences.contains("api") };

@id("exec-container")
permit(principal, action in k8s::Action::"create", resource is core::PodExec)
when { resource has request && resource.request has container && resource.request.container == "debug" };

@id("widget-owner")
permit(principal, action in [k8s::Action::"create", k8s::Action::"update"], resource is example::Widget)
when { resource has request && resource.request has metadata && resource.request.metadata has labels
       && resource.request.metadata.labels has owner
       && resource.request.metadata.labels.owner == principal.name };
"#;
