//! Pure core of the Kubernetes Cedar authorizer.
//!
//! No I/O. All Cedar-facing code lives in [`cedar_adapter`], the only module that
//! names `cedar_policy` items (Lean counterpart: `CedarK8s/Adapter.lean`).

pub mod cedar_adapter;
