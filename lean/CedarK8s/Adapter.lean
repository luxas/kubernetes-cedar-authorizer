import Cedar.TPE
import Cedar.Thm.TPE

/-!
# CedarK8s.Adapter

The ONLY file in this package that imports `Cedar.TPE` / `Cedar.Thm.TPE`. Everything else in
`CedarK8s` goes through the names re-exported here, so a change in the pinned Cedar API
touches one file. Rust counterpart: `crates/core/src/cedar_adapter.rs`.
-/

namespace CedarK8s.Adapter

/-- Cedar's partial (type-aware) authorizer. -/
abbrev tpeIsAuthorized := @Cedar.TPE.isAuthorized

/-- Re-authorize a residual response against concrete data. -/
abbrev reauthorize := @Cedar.TPE.Response.reauthorize

end CedarK8s.Adapter
