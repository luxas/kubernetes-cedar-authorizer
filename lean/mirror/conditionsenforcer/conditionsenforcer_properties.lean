import conditionsenforcer.conditionsenforcer

/-!
# `conditionsenforcer/conditionsenforcer_properties.lean`

Properties of the filter → enforcer pipeline from `review/properties.md` §I and §K:
P-64, P-65, P-66, P-69, P-70, P-80(a,b), P-82, the end-to-end safety theorem, P-68 (axiom,
false on HEAD) and P-72 (negative, with the surviving clamp guarantee).
-/

namespace conditionsenforcer

open authorizer filters

/-! ## Helper lemmas -/

theorem fromParts_IsAllow (t : Decision × String × Option Err) :
    (fromParts t).IsAllow = true ↔ t.1 = .Allow := by
  obtain ⟨d, r, e⟩ := t
  cases d <;> simp [fromParts, ConditionsAwareDecisionFromParts, ConditionsAwareDecision.IsAllow]

theorem fromParts_PD_Allow (t : Decision × String × Option Err) :
    (fromParts t).PossibleDecisions.Has .Allow = true ↔ t.1 = .Allow := by
  obtain ⟨d, r, e⟩ := t
  cases d <;> simp [fromParts, ConditionsAwareDecisionFromParts,
    ConditionsAwareDecision.PossibleDecisions, DecisionSet.singleton, DecisionSet.Has]

theorem fromParts_Error (t : Decision × String × Option Err) :
    (fromParts t).Error = t.2.2 := by
  obtain ⟨d, r, e⟩ := t
  cases d <;> rfl

theorem fromParts_IsUnconditional (t : Decision × String × Option Err) :
    (fromParts t).IsUnconditional = true := by
  obtain ⟨d, r, e⟩ := t
  cases d <;> rfl

/-- The return guard: an accepted `Allow` came from the evaluator and was possible. -/
theorem guard_allow (z : Authorizer) (d : ConditionsAwareDecision) (data : ConditionsData)
    (h : (evaluateWithReturnGuard z d data).1 = .Allow) :
    (z.EvaluateConditions d data).1 = .Allow ∧ d.PossibleDecisions.Has .Allow = true := by
  unfold evaluateWithReturnGuard at h
  split at h
  rename_i r rs e heq
  split at h
  · simp at h
  · rename_i hpd
    simp at h hpd
    subst h
    simp [heq, hpd]

/-- Core lemma for P-66 / P-72: acceptance by `ValidateWith ev` (gate on). -/
theorem validateWith_admitted (ev : Authorizer → Authorizer) (ctx : Context)
    (x : Except Err ConditionsData)
    (h : ({ featureEnabled := some true } : conditionsEnforcer).ValidateWith ev ctx x = .admitted) :
    ∃ z d, ctx = some (z, d) ∧
      (d.IsAllow = true ∨
        (d.PossibleDecisions.Has .Allow = true ∧
          ∃ data, x = .ok data ∧ ((ev z).EvaluateConditions d data).1 = .Allow)) := by
  unfold conditionsEnforcer.ValidateWith at h
  simp only [ConditionallyAuthorizedDecisionFrom] at h
  cases ctx with
  | none => simp at h
  | some t =>
    obtain ⟨z, d⟩ := t
    refine ⟨z, d, rfl, ?_⟩
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at h
    split at h
    · simp at h
    · split at h
      · exact Or.inl (by assumption)
      · right
        cases x with
        | error e => simp at h
        | ok data =>
          simp only at h
          generalize hr : evaluateWithReturnGuard (ev z) d data = r at h
          obtain ⟨dec, rs, e⟩ := r
          simp only at h
          split at h
          · rename_i hdec
            have := guard_allow (ev z) d data (by rw [hr]; exact hdec)
            exact ⟨this.2, data, rfl, this.1⟩
          · split at h <;> simp at h

/-! ## P-64 -/

/-- **P-64** The filter lets a request proceed iff it can still become allowed:
`next` is called iff `allow d ∨ A ∈ PD(d)` (fresh request context). -/
theorem P_64_filter_next_iff (z : Authorizer) (cl : ConditionalAuthorizationRequestClassifier)
    (a : Attributes) :
    (∃ c, withConditionsAwareAuthorization z cl none a = .next c) ↔
      ((conditionsAwareDecisionFor z cl a).IsAllow = true ∨
        (conditionsAwareDecisionFor z cl a).PossibleDecisions.Has .Allow = true) := by
  unfold withConditionsAwareAuthorization
  simp only [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom]
  generalize conditionsAwareDecisionFor z cl a = d
  by_cases h1 : d.IsAllow = true
  · simp [h1]
  · by_cases h2 : d.PossibleDecisions.Has .Allow = true
    · simp [h1, h2]
    · simp only [h1, h2, ite_false, Bool.false_eq_true, false_or]
      split <;> simp

/-- **P-64** (otherwise branch): `¬allow d ∧ A ∉ PD(d)` ⇒ 500 if `err(d) ≠ nil`, else 403.
(The HTTP-code half is `P_70_filter_codes`.) Legacy filter: `next` iff `Authorize = Allow`. -/
theorem P_64_legacy_next_iff (gateOn : Bool) (z : Authorizer) (a : Attributes) :
    (∃ c, withAuthorization gateOn z none a = .next c) ↔ (z.Authorize a).1 = .Allow := by
  unfold withAuthorization
  obtain ⟨d, r, e⟩ := z.Authorize a
  simp only [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom]
  by_cases hd : d = .Allow
  · cases gateOn <;> simp [hd]
  · simp only [hd, ite_false]
    split <;> simp [hd]

/-! ## P-65 -/

/-- **P-65** Exactly one (authorizer, decision) tuple in the context; a second attach fails. -/
theorem P_65_second_attach_fails (t : Authorizer × ConditionsAwareDecision)
    (z : Authorizer) (d : ConditionsAwareDecision) :
    ∃ e, WithConditionallyAuthorizedDecision (some t) z d = .error e := by
  simp [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom]

/-- **P-65** (conditions-aware filter, which exists only with the gate on): a request that
proceeds carries exactly the tuple `(z, d)`, and attaching again fails. -/
theorem P_65_conditionsAware_one_tuple (z : Authorizer)
    (cl : ConditionalAuthorizationRequestClassifier) (a : Attributes) (c : Context)
    (h : withConditionsAwareAuthorization z cl none a = .next c) :
    c = some (z, conditionsAwareDecisionFor z cl a) ∧
      ∀ z' d', ∃ e, WithConditionallyAuthorizedDecision c z' d' = .error e := by
  unfold withConditionsAwareAuthorization at h
  simp only [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom] at h
  have hc : c = some (z, conditionsAwareDecisionFor z cl a) := by
    split at h
    · simp at h; exact h.symm
    · split at h
      · simp at h; exact h.symm
      · split at h <;> simp at h
  subst hc
  exact ⟨rfl, fun z' d' => P_65_second_attach_fails _ z' d'⟩

/-- **P-65** (legacy filter, gate on): an Allow attaches `(AuthorizerFunc(Authorize), allow)`
(`authorization.go:71,101-110`), and attaching again fails. -/
theorem P_65_legacy_one_tuple (z : Authorizer) (a : Attributes) (c : Context)
    (h : withAuthorization true z none a = .next c) :
    c = some (AuthorizerFunc z.Authorize,
              ConditionsAwareDecisionAllow (z.Authorize a).2.1 (z.Authorize a).2.2) ∧
      ∀ z' d', ∃ e, WithConditionallyAuthorizedDecision c z' d' = .error e := by
  unfold withAuthorization at h
  generalize ht : z.Authorize a = t at h ⊢
  obtain ⟨d, r, e⟩ := t
  simp only [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom] at h
  have hc : c = some (AuthorizerFunc z.Authorize, ConditionsAwareDecisionAllow r e) := by
    split at h
    · simp at h; exact h.symm
    · split at h <;> simp at h
  subst hc
  exact ⟨rfl, fun z' d' => P_65_second_attach_fails _ z' d'⟩

/-- **P-65** (consequence of `P_65_legacy_one_tuple`): the legacy-attached tuple is an
unconditional Allow, so `AuthorizerFunc.EvaluateConditions` is unreachable from the
enforcer (`conditionsenforcer.go:97`). -/
theorem P_65_legacy_tuple_is_allow (z : Authorizer) (a : Attributes) (c : Context)
    (h : withAuthorization true z none a = .next c) :
    ∃ z' d, c = some (z', d) ∧ d.IsAllow = true :=
  ⟨_, _, (P_65_legacy_one_tuple z a c h).1, rfl⟩

/-- **P-65** (pipeline form): gate on, fresh context, whichever filter is installed — a
request that proceeds carries exactly one tuple, and a second attach fails. -/
theorem P_65_one_tuple (cfg : Config) (a : Attributes) (c : Context)
    (hg : cfg.gateOn = true) (h : Filter cfg none a = .next c) :
    (∃ z d, c = some (z, d)) ∧ ∀ z' d', ∃ e, WithConditionallyAuthorizedDecision c z' d' = .error e := by
  obtain ⟨g, cl, en, z⟩ := cfg
  simp only at hg
  subst hg
  unfold Filter at h
  cases cl with
  | none =>
    simp [Config.usesConditionsAwareFilter, WithAuthorization] at h
    have := P_65_legacy_one_tuple z a c h
    exact ⟨⟨_, _, this.1⟩, this.2⟩
  | some cl =>
    cases en with
    | false =>
      simp [Config.usesConditionsAwareFilter, WithAuthorization] at h
      have := P_65_legacy_one_tuple z a c h
      exact ⟨⟨_, _, this.1⟩, this.2⟩
    | true =>
      simp [Config.usesConditionsAwareFilter] at h
      have := P_65_conditionsAware_one_tuple z cl a c h
      exact ⟨⟨_, _, this.1⟩, this.2⟩

/-! ## P-66 -/

/-- **P-66** Enforcer acceptance implies an Allow: gate on ∧ `Validate = nil` ⇒
`allow d ∨ (r = A ∧ A ∈ PD(d))` where `r = z.EvaluateConditions(d, x)` and `(z, d)` is the
context tuple. -/
theorem P_66_validate_admitted (ctx : Context) (x : Except Err ConditionsData)
    (h : ({ featureEnabled := some true } : conditionsEnforcer).Validate ctx x = .admitted) :
    ∃ z d, ctx = some (z, d) ∧
      (d.IsAllow = true ∨
        ((∃ data, x = .ok data ∧ (z.EvaluateConditions d data).1 = .Allow) ∧
          d.PossibleDecisions.Has .Allow = true)) := by
  obtain ⟨z, d, hc, hd⟩ := validateWith_admitted id ctx x h
  refine ⟨z, d, hc, ?_⟩
  rcases hd with hd | ⟨hpd, hr⟩
  · exact Or.inl hd
  · exact Or.inr ⟨hr, hpd⟩

/-- **P-66** Missing tuple ⇒ error (gate on). -/
theorem P_66_missing_tuple (x : Except Err ConditionsData) :
    ({ featureEnabled := some true } : conditionsEnforcer).Validate none x = .internal500 := by
  simp [conditionsEnforcer.Validate, conditionsEnforcer.ValidateWith,
    ConditionallyAuthorizedDecisionFrom]

/-- **P-66** `Handles(op)` is constant in the operation (all ops incl. CONNECT). -/
theorem P_66_handles_constant (c : conditionsEnforcer) (op op' : String) :
    c.Handles op = c.Handles op' := rfl

/-- **P-66** Return guard: `r ∉ PD(d) ⇒ (Deny, err)`. Together: the guarded result is in
`PD(d)`, or it is `Deny` carrying an error (terminal 500 via P-70). -/
theorem P_66_return_guard (z : Authorizer) (d : ConditionsAwareDecision) (data : ConditionsData) :
    d.PossibleDecisions.Has (evaluateWithReturnGuard z d data).1 = true ∨
      ((evaluateWithReturnGuard z d data).1 = .Deny ∧
        (evaluateWithReturnGuard z d data).2.2.isSome = true) := by
  unfold evaluateWithReturnGuard
  obtain ⟨r, rs, e⟩ := z.EvaluateConditions d data
  simp only
  split
  · right; simp
  · left; rename_i h; simpa using h

/-! ## P-69 -/

/-- **P-69** Unclassified requests never carry a conditional decision:
`¬classifier(a) ⇒ d = FromParts(z.Authorize(a))` ⇒ `uncond d`. -/
theorem P_69_unclassified_unconditional (z : Authorizer)
    (cl : ConditionalAuthorizationRequestClassifier) (a : Attributes) (h : cl a = false) :
    conditionsAwareDecisionFor z cl a = fromParts (z.Authorize a) ∧
      (conditionsAwareDecisionFor z cl a).IsUnconditional = true := by
  simp [conditionsAwareDecisionFor, h, fromParts_IsUnconditional]

/-! ## P-70 -/

/-- **P-70** HTTP code of a final non-Allow, conditions-aware filter (fresh context):
`¬allow d ∧ A ∉ PD(d)`: `err ≠ nil ↦ 500`, `err = nil ↦ 403`. -/
theorem P_70_filter_codes (z : Authorizer) (cl : ConditionalAuthorizationRequestClassifier)
    (a : Attributes)
    (h1 : (conditionsAwareDecisionFor z cl a).IsAllow = false)
    (h2 : (conditionsAwareDecisionFor z cl a).PossibleDecisions.Has .Allow = false) :
    ((conditionsAwareDecisionFor z cl a).Error.isSome = true →
        withConditionsAwareAuthorization z cl none a = .internal500) ∧
      ((conditionsAwareDecisionFor z cl a).Error = none →
        withConditionsAwareAuthorization z cl none a = .forbidden403) := by
  unfold withConditionsAwareAuthorization
  simp only [WithConditionallyAuthorizedDecision, ConditionallyAuthorizedDecisionFrom]
  generalize conditionsAwareDecisionFor z cl a = d at *
  refine ⟨fun he => by simp [h1, h2, he], fun he => by simp [h1, h2, he]⟩

/-- **P-70** HTTP code, legacy filter: `Authorize ≠ Allow`: `err ≠ nil ↦ 500`, else 403. -/
theorem P_70_legacy_codes (gateOn : Bool) (z : Authorizer) (ctx : Context) (a : Attributes)
    (h : (z.Authorize a).1 ≠ .Allow) :
    ((z.Authorize a).2.2.isSome = true → withAuthorization gateOn z ctx a = .internal500) ∧
      ((z.Authorize a).2.2 = none → withAuthorization gateOn z ctx a = .forbidden403) := by
  unfold withAuthorization
  generalize z.Authorize a = t at h ⊢
  obtain ⟨d, r, e⟩ := t
  simp only at h ⊢
  refine ⟨fun he => by simp [h, he], fun he => by simp [h, he]⟩

/-- **P-70** HTTP code, enforcer: for a conditional decision with `A ∈ PD(d)` that reaches
evaluation, a guarded result `r ≠ A` maps `e ≠ nil ↦ 500`, `e = nil ↦ 403`; `r = A` admits
regardless of `e` ("Allow ignores e"). -/
theorem P_70_enforcer_codes (z : Authorizer) (d : ConditionsAwareDecision) (data : ConditionsData)
    (hu : d.IsUnconditional = false) (hpd : d.PossibleDecisions.Has .Allow = true) :
    let r := evaluateWithReturnGuard z d data
    let V := ({ featureEnabled := some true } : conditionsEnforcer).Validate (some (z, d)) (.ok data)
    (r.1 = .Allow → V = .admitted) ∧
      (r.1 ≠ .Allow → r.2.2.isSome = true → V = .internal500) ∧
      (r.1 ≠ .Allow → r.2.2 = none → V = .forbidden403) := by
  simp only [ConditionsAwareDecision.IsUnconditional, Bool.or_eq_false_iff] at hu
  obtain ⟨⟨hA, hD⟩, hN⟩ := hu
  simp only [conditionsEnforcer.Validate, conditionsEnforcer.ValidateWith,
    ConditionallyAuthorizedDecisionFrom, id]
  refine ⟨fun h => by simp [hA, hD, hN, hpd, h], fun h he => by simp [hA, hD, hN, hpd, h, he],
    fun h he => by simp [hA, hD, hN, hpd, h, he]⟩

/-! ## §K Feature gate -/

/-- **P-82** Gate on without the enforcer plugin (or without a classifier) ⇒ legacy filter. -/
theorem P_82_no_enforcer_legacy (cfg : Config) (hg : cfg.gateOn = true)
    (h : cfg.classifier = none ∨ cfg.enforcerEnabled = false) :
    Filter cfg = WithAuthorization true cfg.authorizer := by
  obtain ⟨g, cl, en, z⟩ := cfg
  simp only at hg h ⊢
  subst hg
  funext ctx a
  rcases h with h | h
  · subst h; simp [Filter, Config.usesConditionsAwareFilter]
  · subst h; cases cl <;> simp [Filter, Config.usesConditionsAwareFilter]

/-- **P-80(a)** Gate off ⇒ legacy filter installed (and it never attaches a tuple). -/
theorem P_80a_gate_off_legacy (cfg : Config) (hg : cfg.gateOn = false) :
    Filter cfg = WithAuthorization false cfg.authorizer ∧
      ∀ ctx a c, Filter cfg ctx a = .next c → c = ctx := by
  obtain ⟨g, cl, en, z⟩ := cfg
  simp only at hg ⊢
  subst hg
  have hF : Filter ⟨false, cl, en, z⟩ = WithAuthorization false z := by
    funext ctx a; cases cl <;> simp [Filter, Config.usesConditionsAwareFilter]
  refine ⟨hF, fun ctx a c h => ?_⟩
  rw [hF] at h
  unfold WithAuthorization withAuthorization at h
  obtain ⟨d, r, e⟩ := z.Authorize a
  simp only at h
  split at h
  · simp at h; exact h.symm
  · split at h <;> simp at h

/-- **P-80(b)** Gate off ⇒ enforcer `Handles = false` and `Validate` is a no-op. -/
theorem P_80b_gate_off_enforcer (cfg : Config) (hg : cfg.gateOn = false) :
    (∀ op, cfg.enforcer.Handles op = false) ∧
      ∀ ctx x, cfg.enforcer.Validate ctx x = .admitted := by
  simp [Config.enforcer, conditionsEnforcer.InspectFeatureGates, conditionsEnforcer.Handles,
    conditionsEnforcer.Validate, conditionsEnforcer.ValidateWith, hg]

/-! ## End-to-end safety -/

/-- Filter `next` ⇒ either an unconditional Allow decision, or the conditions-aware filter
is installed and the context holds `(cfg.authorizer, d)` with `A ∈ PD(d)`. -/
theorem filter_next_cases (cfg : Config) (ctx : Context) (a : Attributes) (c : Context)
    (h : Filter cfg ctx a = .next c) :
    (filterDecision cfg a).IsAllow = true ∨
      (cfg.gateOn = true ∧ cfg.enforcerEnabled = true ∧
        c = some (cfg.authorizer, filterDecision cfg a) ∧
        (filterDecision cfg a).PossibleDecisions.Has .Allow = true) := by
  obtain ⟨g, cl, en, z⟩ := cfg
  have legacy : ∀ g', withAuthorization g' z ctx a = .next c →
      (fromParts (z.Authorize a)).IsAllow = true := by
    intro g' h
    rw [fromParts_IsAllow]
    unfold withAuthorization at h
    generalize z.Authorize a = t at h ⊢
    obtain ⟨d, r, e⟩ := t
    simp only at h ⊢
    by_cases hd : d = .Allow
    · exact hd
    · simp only [hd, ite_false] at h; split at h <;> simp at h
  cases cl with
  | none =>
    left
    simp [Filter, filterDecision, Config.usesConditionsAwareFilter, WithAuthorization] at h ⊢
    exact legacy g h
  | some cl =>
    cases g <;> cases en <;>
      simp [Filter, filterDecision, Config.usesConditionsAwareFilter, WithAuthorization] at h ⊢
    · exact legacy _ h
    · exact legacy _ h
    · exact legacy _ h
    · -- conditions-aware filter installed
      cases ctx with
      | some t =>
        simp [withConditionsAwareAuthorization, WithConditionallyAuthorizedDecision,
          ConditionallyAuthorizedDecisionFrom] at h
      | none =>
        have h1 := (P_65_conditionsAware_one_tuple z cl a c h).1
        have h2 := (P_64_filter_next_iff z cl a).1 ⟨c, h⟩
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · by_cases hA : (conditionsAwareDecisionFor z cl a).IsAllow = true
          · exact Or.inl hA
          · exact Or.inr ⟨h1, h2⟩

/-- **End-to-end safety.** For ANY authorizer `z` (arbitrary functions), ANY configuration,
ANY incoming context and ANY request: if the pipeline admits, then either the filter
decision was an unconditional Allow, or `A ∈ PD(d)` and the enforcer obtained `Allow` from
`z.EvaluateConditions(d, x)` with `z` the authoring authorizer. No path admits a request
whose decision could not be Allow. Assumes the enforcer is reached (`P_68_enforcer_runs`). -/
theorem end_to_end_safety (cfg : Config) (ctx : Context) (a : Attributes)
    (x : Except Err ConditionsData) (h : Outcome cfg ctx a x = .admitted) :
    (filterDecision cfg a).IsAllow = true ∨
      ((filterDecision cfg a).PossibleDecisions.Has .Allow = true ∧
        ∃ data, x = .ok data ∧
          (cfg.authorizer.EvaluateConditions (filterDecision cfg a) data).1 = .Allow) := by
  unfold Outcome at h
  split at h
  · rename_i c hf
    rcases filter_next_cases cfg ctx a c hf with hA | ⟨hg, he, hc, hpd⟩
    · exact Or.inl hA
    · simp only [he, ite_true] at h
      have hEn : cfg.enforcer = { featureEnabled := some true } := by
        simp [Config.enforcer, conditionsEnforcer.InspectFeatureGates, hg]
      rw [hEn, hc] at h
      obtain ⟨z, d, hzd, hd⟩ := P_66_validate_admitted _ x h
      simp only [Option.some.injEq, Prod.mk.injEq] at hzd
      obtain ⟨rfl, rfl⟩ := hzd
      rcases hd with hd | ⟨hr, _⟩
      · exact Or.inl hd
      · exact Or.inr ⟨hpd, hr⟩
  · simp at h
  · simp at h

/-! ## P-68 (axiom, false on HEAD) -/

/-- What the real kube-apiserver does with a request, including paths outside the modelled
filter → admission pipeline (aggregated-API proxying, the unsafe corrupt-object delete). -/
opaque ServedOutcome : Config → Context → Attributes → Except Err ConditionsData → AdmissionOutcome

/-- **P-68** A request classified conditional cannot complete without the enforcer:
with the conditions-aware filter installed and `classifier(a) = true`, the served outcome is
the modelled filter → enforcer `Outcome`.

-- status: does NOT hold on HEAD. This is an environment assumption, recorded as a named
`Prop` that dependent theorems take as an explicit hypothesis (never as an axiom, since it
is false on HEAD). Counterexamples on HEAD
(`review/properties.md` P-68): (1) aggregated APIs — the classifier has no "served locally"
check (`pkg/controlplane/apiserver/config.go:299-321`), so a conditional allow passes the
filter and the aggregator proxies without kube-apiserver admission
(`kube-aggregator/pkg/apiserver/handler_proxy.go`); (2) unsafe corrupt-object delete —
`ignoreStoreReadErrorWithClusterBreakingPotential` uses the corrupt-object deleter, which
skips `deleteValidation` (`S/pkg/endpoints/handlers/delete.go:157-169`).
`end_to_end_safety` is about `Outcome`, i.e. it ASSUMES the enforcer is reached; only
`served_safety_classified` transports it to `ServedOutcome`, under this hypothesis. -/
def P_68_enforcer_runs (cfg : Config) (ctx : Context) (a : Attributes) (x : Except Err ConditionsData)
    (cl : ConditionalAuthorizationRequestClassifier) : Prop :=
  cfg.usesConditionsAwareFilter = true → cfg.classifier = some cl → cl a = true →
    ServedOutcome cfg ctx a x = Outcome cfg ctx a x

/-- End-to-end safety for served classified requests; depends on the (false on HEAD)
hypothesis `P_68_enforcer_runs`. -/
theorem served_safety_classified (cfg : Config) (ctx : Context) (a : Attributes)
    (x : Except Err ConditionsData) (cl : ConditionalAuthorizationRequestClassifier)
    (h68 : P_68_enforcer_runs cfg ctx a x cl)
    (hu : cfg.usesConditionsAwareFilter = true) (hc : cfg.classifier = some cl) (ha : cl a = true)
    (h : ServedOutcome cfg ctx a x = .admitted) :
    (filterDecision cfg a).IsAllow = true ∨
      ((filterDecision cfg a).PossibleDecisions.Has .Allow = true ∧
        ∃ data, x = .ok data ∧
          (cfg.authorizer.EvaluateConditions (filterDecision cfg a) data).1 = .Allow) := by
  rw [h68 hu hc ha] at h
  exact end_to_end_safety cfg ctx a x h

/-! ## P-72 (does NOT hold; the clamp survives) -/

/-- **P-72** The evaluating authorizer is the authoring authorizer.

-- status: does NOT hold. The context stores the reloadable wrapper, whose
`EvaluateConditions` loads the current chain independently of the one that authored `d`
(`pkg/kubeapiserver/authorizer/reload.go:93-99`). Modelled by `ValidateWith ev`: the
evaluating authorizer is `ev z`, not `z`. Counterexample (for any `data`): `d` a conditions
map with one allow and one deny condition; `z` evaluates to Allow, the reloaded `z'` to Deny;
`Validate` admits, `ValidateWith (fun _ => z')` answers 403. -/
theorem P_72_evaluator_may_differ (data : ConditionsData) :
    ¬ ∀ (ev : Authorizer → Authorizer) (ctx : Context) (x : Except Err ConditionsData),
      ({ featureEnabled := some true } : conditionsEnforcer).ValidateWith ev ctx x =
        ({ featureEnabled := some true } : conditionsEnforcer).Validate ctx x := by
  intro hall
  let d : ConditionsAwareDecision :=
    .conditionsMap { denyConditions := [default], allowConditions := [default] }
  let mk : Decision → Authorizer := fun r =>
    { Authorize := fun _ => (.NoOpinion, "", none)
      ConditionsAwareAuthorize := fun _ => d
      EvaluateConditions := fun _ _ => (r, "", none) }
  have h0 := hall (fun _ => mk .Deny) (some (mk .Allow, d)) (.ok data)
  have h1 : ({ featureEnabled := some true } : conditionsEnforcer).ValidateWith (fun _ => mk .Deny)
      (some (mk .Allow, d)) (.ok data) = .forbidden403 := rfl
  have h2 : ({ featureEnabled := some true } : conditionsEnforcer).Validate
      (some (mk .Allow, d)) (.ok data) = .admitted := rfl
  rw [h1, h2] at h0
  cases h0

/-- **P-72** (surviving guarantee): whatever authorizer evaluates (`ev` arbitrary, e.g. a
reload in between), the pipeline admits only an unconditional Allow or a conditional `d`
with `A ∈ PD(d)` for which the EVALUATING authorizer returned Allow — the clamp keeps the
result in `PD(d)`; nothing else about the authored decision survives. -/
theorem P_72_clamp_survives_reload (cfg : Config) (ev : Authorizer → Authorizer)
    (ctx : Context) (a : Attributes) (x : Except Err ConditionsData)
    (h : OutcomeReloaded cfg ev ctx a x = .admitted) :
    (filterDecision cfg a).IsAllow = true ∨
      ((filterDecision cfg a).PossibleDecisions.Has .Allow = true ∧
        ∃ data, x = .ok data ∧
          ((ev cfg.authorizer).EvaluateConditions (filterDecision cfg a) data).1 = .Allow) := by
  unfold OutcomeReloaded at h
  split at h
  · rename_i c hf
    rcases filter_next_cases cfg ctx a c hf with hA | ⟨hg, he, hc, hpd⟩
    · exact Or.inl hA
    · simp only [he, ite_true] at h
      have hEn : cfg.enforcer = { featureEnabled := some true } := by
        simp [Config.enforcer, conditionsEnforcer.InspectFeatureGates, hg]
      rw [hEn, hc] at h
      obtain ⟨z, d, hzd, hd⟩ := validateWith_admitted ev _ x h
      simp only [Option.some.injEq, Prod.mk.injEq] at hzd
      obtain ⟨rfl, rfl⟩ := hzd
      rcases hd with hd | ⟨_, hr⟩
      · exact Or.inl hd
      · exact Or.inr ⟨hpd, hr⟩
  · simp at h
  · simp at h

/-- **P-72** (clamp, per evaluation): for any evaluating authorizer, the guarded result lies
in `PD(d)` or is the fail-closed `(Deny, err)`. -/
theorem P_72_guard_in_PD (z' : Authorizer) (d : ConditionsAwareDecision) (data : ConditionsData) :
    d.PossibleDecisions.Has (evaluateWithReturnGuard z' d data).1 = true ∨
      ((evaluateWithReturnGuard z' d data).1 = .Deny ∧
        (evaluateWithReturnGuard z' d data).2.2.isSome = true) :=
  P_66_return_guard z' d data

end conditionsenforcer
