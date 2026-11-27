//! The ONLY module in `kca-core` that names `cedar_policy` items.
//!
//! Lean: `CedarK8s.Adapter`.

use cedar_policy::PolicySet;

/// Number of policies in a parsed policy set. Exercises the pinned Cedar dependency.
pub fn policy_count(src: &str) -> Result<usize, String> {
    let ps: PolicySet = src.parse().map_err(|e| format!("{e}"))?;
    Ok(ps.policies().count())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_policies() {
        assert_eq!(policy_count("permit(principal, action, resource);"), Ok(1));
        assert!(policy_count("not cedar").is_err());
    }
}
