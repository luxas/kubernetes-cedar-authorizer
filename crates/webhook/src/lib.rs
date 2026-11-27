//! Webhook server (stub; stage 5c).

/// Crate name, used by the skeleton test.
pub fn name() -> &'static str {
    "kca-webhook"
}

#[cfg(test)]
mod tests {
    #[test]
    fn name_is_stable() {
        assert_eq!(super::name(), "kca-webhook");
    }
}
