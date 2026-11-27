/-!
# `filters/featuregate.lean`  —  no Go file counterpart

The `ConditionalAuthorization` feature gate is not one Go file: its off-switches are spread
over eight places (`review/properties.md` §K, P-80). This module collects them into one
record so the composition "gate off ⇒ no conditional authorization" can be stated. Each
field is the Bool a Go `if utilfeature.DefaultFeatureGate.Enabled(...)` switch computes;
the other inputs (wiring, presence of config/fields) are `Wiring`. Paths are relative to the
repo root; `S/` = `staging/src/k8s.io/apiserver/`.
-/

namespace featuregate

/-- Non-gate inputs to the eight switches. -/
structure Wiring where
  /-- `c.Authorization.ConditionalAuthorizationRequestClassifier != nil` (`S/pkg/server/config.go:1077`). -/
  classifierSet : Bool
  /-- `c.Authorization.ConditionsEnforcerPluginEnabled` (`config.go:1077`). -/
  enforcerPluginEnabled : Bool
  /-- An `authorizationConditionsReviewer` is passed to the webhook constructor (`webhook.go:152`). -/
  conditionsReviewerPassed : Bool
  /-- `configuredAuthorizer.Webhook.ConditionsReview != nil` (`pkg/kubeapiserver/authorizer/reload.go:190`). -/
  conditionsReviewConfigured : Bool
  /-- Informer factory and client are non-nil (`authorization_conditions.go:54-59`). -/
  builtinBuilderInputsPresent : Bool
  /-- A posted SAR carries `spec.authorizationOptions`. -/
  sarAuthorizationOptionsPosted : Bool
  /-- A posted SAR uses any of the new gated fields (DV `ifDisabled`). -/
  sarNewFieldsPosted : Bool

/-- The eight gate-dependent switches of P-80 (a)–(h). -/
structure GateSwitches where
  /-- (a) `WithConditionsAwareAuthorization` installed instead of the legacy filter
  (`S/pkg/server/config.go:1077-1087`). -/
  conditionsAwareFilterInstalled : Bool
  /-- (b) Enforcer `Handles` / `Validate` active (`conditionsenforcer.go:74-82`). -/
  enforcerActive : Bool
  /-- (c) Webhook `authorizationConditionsReviewer` set, hence `authorizationOptions`
  advertised (`S/plugin/pkg/authorizer/webhook/webhook.go:152-157`). -/
  webhookConditionsReviewerSet : Bool
  /-- (d) Builtin CEL builder non-nil (`pkg/kubeapiserver/authorizer/reload.go:188-211`). -/
  builtinBuilderSet : Bool
  /-- (e) Posted SAR `spec.authorizationOptions` kept, so `ConditionsAwareAuthorize` may be
  used (`pkg/registry/authorization/subjectaccessreview/rest.go:78-80`, `helpers.go:252-254`). -/
  sarAuthorizationOptionsKept : Bool
  /-- (f) A `conditionsReview` authorizer config is rejected
  (`S/pkg/apis/apiserver/validation/validation.go:759-761`). -/
  conditionsReviewConfigRejected : Bool
  /-- (g) A SAR using the new fields is rejected by declarative validation `ifDisabled`
  (`staging/src/k8s.io/api/authorization/v1/zz_generated.validations.go:1114-1124`). -/
  sarNewFieldsRejected : Bool
  /-- (h) matchConditions CEL declares `request.authorizationOptions`
  (`S/pkg/authorization/cel/compile.go:218`). -/
  matchConditionsDeclaresAuthorizationOptions : Bool

/-- Switch values as the Go code computes them from the gate and the wiring. -/
def GateSwitches.of (gateOn : Bool) (w : Wiring) : GateSwitches where
  conditionsAwareFilterInstalled := gateOn && w.classifierSet && w.enforcerPluginEnabled
  enforcerActive := gateOn
  webhookConditionsReviewerSet := gateOn && w.conditionsReviewerPassed
  builtinBuilderSet := gateOn && w.conditionsReviewConfigured && w.builtinBuilderInputsPresent
  sarAuthorizationOptionsKept := gateOn && w.sarAuthorizationOptionsPosted
  conditionsReviewConfigRejected := !gateOn && w.conditionsReviewConfigured
  sarNewFieldsRejected := !gateOn && w.sarNewFieldsPosted
  matchConditionsDeclaresAuthorizationOptions := gateOn

/-- The eight gate-off consequences of P-80. -/
def GateOffConsequences (w : Wiring) (s : GateSwitches) : Prop :=
  s.conditionsAwareFilterInstalled = false                              -- (a) legacy filter
  ∧ s.enforcerActive = false                                            -- (b) enforcer no-op
  ∧ s.webhookConditionsReviewerSet = false                              -- (c) nothing advertised
  ∧ s.builtinBuilderSet = false                                         -- (d) no builtin builder
  ∧ s.sarAuthorizationOptionsKept = false                               -- (e) SAR ⇒ Authorize only
  ∧ (w.conditionsReviewConfigured = true → s.conditionsReviewConfigRejected = true)  -- (f)
  ∧ (w.sarNewFieldsPosted = true → s.sarNewFieldsRejected = true)       -- (g)
  ∧ s.matchConditionsDeclaresAuthorizationOptions = false               -- (h)

/-- P-80. "Gate off ⇒ no conditional decision is produced, advertised or evaluated in
production": with `gateOn = false` all eight switches are off by definition, for any wiring.
(The model only composes the switches; that each Go switch reads the gate as stated is the
per-file citation in the field docs.) -/
theorem P_80_gate_off (w : Wiring) : GateOffConsequences w (GateSwitches.of false w) := by
  simp [GateOffConsequences, GateSwitches.of]

/-! ### P-81 (negative, documented only)

P-81 "Gate off ⇒ no new code path is reachable" -- status: does NOT hold (benign).
`WebhookAuthorizer.Authorize` (`S/plugin/pkg/authorizer/webhook/webhook.go:255-270`) has no gate
check, so it is NOT one of the `GateSwitches` above: a webhook that returns an unrequested
`status.conditionalDecision` reaches the decode-and-fold-down branch (`webhook.go:264-267`) even
with the gate off, and `allowed = true ∧ conditionalDecision` yields
`FailureDecision(…) + error` (⇒ 500) where 1.37 returned Allow. `denied = true` still wins
(`webhook.go:262-263`). The legacy `Authorize` model and its fold-down theorem live in
`webhook/webhook.lean`; this module deliberately contains no switch for it. -/

end featuregate
