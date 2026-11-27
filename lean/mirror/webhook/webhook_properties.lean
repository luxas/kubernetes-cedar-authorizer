import webhook.webhook

/-!
# `webhook/webhook_properties.lean`  ↔  `plugin/pkg/authorizer/webhook/webhook*_test.go`

Properties of the webhook authorizer from `review/properties.md` §G (P-49 … P-52) and §D
(P-26, P-32), plus the documented legacy-path divergence (P-69 / P-K5 / shipped.md §3.1).
-/

namespace webhook

open authorizer
open WebhookAuthorizer

/-! ### Helpers -/

/-- `FailureDecision` is never `Allow` (`conditions.go:224-229`). -/
theorem FailureDecision_ne_Allow (d : ConditionsAwareDecision) : d.FailureDecision ≠ .Allow := by
  unfold ConditionsAwareDecision.FailureDecision
  split <;> intro h <;> cases h

/-- `FailureDecision ∈ {Deny, NoOpinion}`. -/
theorem FailureDecision_cases (d : ConditionsAwareDecision) :
    d.FailureDecision = .Deny ∨ d.FailureDecision = .NoOpinion := by
  unfold ConditionsAwareDecision.FailureDecision
  split <;> simp

/-- The failure decision is unconditional. -/
theorem conditionsAwareFailureDecision_unconditional (w : WebhookAuthorizer) (e : Option Err) :
    (w.conditionsAwareFailureDecision e).IsUnconditional = true := by
  unfold conditionsAwareFailureDecision
  split <;> rfl

/-- The order `N < D` on failure decisions (`properties.md` §1.1), reflexive. -/
def failLe (a b : Decision) : Prop := a = b ∨ (a = .NoOpinion ∧ b = .Deny)

/-! ### P-49 -/

/-- **P-49 (legacy path)** "status.conditionalDecision ≠ nil ⇒ Authorize ∈ {(D, _, nil) if denied,
(FD(dec cd), _, err≠nil) otherwise}" — the precise shape (the `both` case is `(D, _, err)`). -/
theorem P_49_legacy_shape (w : WebhookAuthorizer) (s : SubjectAccessReviewStatus) (d : ConditionsAwareDecision)
    (hcd : s.ConditionalDecision = some d) :
    let r := w.Authorize (.ok true) (.ok s)
    (s.Denied = true ∧ s.Allowed = true ∧ r = (.Deny, s.Reason, some errBothAllowDeny))
    ∨ (s.Denied = true ∧ s.Allowed = false ∧ r = (.Deny, s.Reason, none))
    ∨ (s.Denied = false ∧ r = (d.FailureDecision, s.Reason, some errUnrequestedConditional)) := by
  simp only [Authorize, authorizeStatus, hcd]
  cases hD : s.Denied <;> cases hA : s.Allowed <;> simp

/-- **P-49 (legacy path)** "An unrequested conditional answer never becomes Allow." -/
theorem P_49_legacy_conditional_not_allow (w : WebhookAuthorizer) (s : SubjectAccessReviewStatus)
    (hcd : s.ConditionalDecision ≠ none) :
    (w.Authorize (.ok true) (.ok s)).1 ≠ .Allow := by
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hcd
  rcases P_49_legacy_shape w s d hd with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h]
  · intro h'; cases h'
  · intro h'; cases h'
  · exact FailureDecision_ne_Allow d

/-- **P-49 (legacy path)** "in particular allowed = true ∧ cd ≠ nil ⇒ ¬A" (for every match
and transport outcome, given a well-formed failure policy). -/
theorem P_49_legacy_allowed_and_conditional_not_allow (w : WebhookAuthorizer) (hw : w.WF)
    (m : Except Err Bool) (sar : Except Err SubjectAccessReviewStatus)
    (hsar : ∀ s, sar = .ok s → s.Allowed = true ∧ s.ConditionalDecision ≠ none) :
    (w.Authorize m sar).1 ≠ .Allow := by
  unfold Authorize
  match m, sar, hsar with
  | .error _, _, _ => exact hw
  | .ok false, _, _ => intro h; cases h
  | .ok true, .error _, _ => exact hw
  | .ok true, .ok s, h =>
    have := P_49_legacy_conditional_not_allow w s (h s rfl).2
    simpa [Authorize] using this

/-- **P-49 (CAA path without reviewer)** "cd ≠ nil fails CombinedValidateSubjectAccessReviewCreate
⇒ failPol(err) ∈ {deny, noOp}" (the `both` case is caught first, `webhook.go:322-324`). -/
theorem P_49_caa_no_reviewer (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (hv : ValidRejectsUnrequested w valid) (s : SubjectAccessReviewStatus)
    (hr : w.hasReviewer = false) (hcd : s.ConditionalDecision ≠ none) (hboth : ¬(s.Denied = true ∧ s.Allowed = true)) :
    w.conditionsAwareStatus valid s = w.conditionsAwareFailureDecision (some errValidation) := by
  have hval := hv s hr hcd
  unfold conditionsAwareStatus
  have : (s.Denied && s.Allowed) = false := by
    cases hD : s.Denied <;> cases hA : s.Allowed <;> simp_all
  simp [this, hval]

/-! ### P-50 -/

/-- **P-50** "CAA returns a conditional decision only when conditions were requested."
`¬uncond(webhook.CAA(a)) ⇒ reviewer ≠ nil`. -/
theorem P_50_conditional_requires_reviewer (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (hv : ValidRejectsUnrequested w valid) (m : Except Err Bool)
    (sar : Bool → Except Err SubjectAccessReviewStatus)
    (hc : (w.ConditionsAwareAuthorize valid m sar).IsUnconditional = false) :
    w.hasReviewer = true := by
  cases hr : w.hasReviewer
  · exfalso
    revert hc
    unfold ConditionsAwareAuthorize
    split
    · simp [conditionsAwareFailureDecision_unconditional]
    · simp [ConditionsAwareDecision.IsUnconditional, ConditionsAwareDecision.IsNoOpinion]
    · split
      · simp [conditionsAwareFailureDecision_unconditional]
      · rename_i s _
        unfold conditionsAwareStatus
        by_cases hb : (s.Denied && s.Allowed) = true
        · simp [hb, ConditionsAwareDecision.IsUnconditional, ConditionsAwareDecision.IsDeny]
        · simp only [hb]
          by_cases hval : valid s = true
          · have hcd : s.ConditionalDecision = none := by
              cases h : s.ConditionalDecision with
              | none => rfl
              | some _ =>
                have := hv s hr (by simp [h]); simp_all
            simp [hval, hcd]
            split
            · simp [ConditionsAwareDecision.IsUnconditional, ConditionsAwareDecision.IsDeny]
            · cases s.Allowed <;> simp [ConditionsAwareDecision.IsUnconditional,
                ConditionsAwareDecision.IsAllow, ConditionsAwareDecision.IsNoOpinion]
          · simp [hval, conditionsAwareFailureDecision_unconditional]
  · rfl

/-! ### P-51 -/

/-- **P-51** "Malformed responses on the CAA path follow failurePolicy, not the response's deny
intent": a status failing validation yields `failPol(err)` even when `denied = true` —
provided it is not the `allowed ∧ denied` status, which is intercepted before validation
(`webhook.go:322-324`). -/
theorem P_51_invalid_follows_failurePolicy (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (s : SubjectAccessReviewStatus) (hval : valid s = false) (hboth : ¬(s.Denied = true ∧ s.Allowed = true)) :
    w.conditionsAwareStatus valid s = w.conditionsAwareFailureDecision (some errValidation) := by
  unfold conditionsAwareStatus
  have : (s.Denied && s.Allowed) = false := by
    cases hD : s.Denied <;> cases hA : s.Allowed <;> simp_all
  simp [this, hval]

/-- **P-51, deny-intent case**: under `failurePolicy: NoOpinion`, an invalid status with
`denied = true` (and `allowed = false`) yields NoOpinion. -/
theorem P_51_denied_invalid_noOpinion (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (s : SubjectAccessReviewStatus) (hval : valid s = false) (hD : s.Denied = true) (hA : s.Allowed = false)
    (hpol : w.decisionOnError = .NoOpinion) :
    w.conditionsAwareStatus valid s = .noOpinion "failed closed" (some errValidation) := by
  rw [P_51_invalid_follows_failurePolicy w valid s hval (by simp [hA])]
  simp [conditionsAwareFailureDecision, hpol]

-- status: does NOT hold (unrestricted form)
/-- **P-51 without the `both` exclusion does NOT hold**: "response fails validation ⇒ result
`failPol(err)`". Counterexample: `failurePolicy = NoOpinion`, status `allowed = denied = true`
(which validation rejects, `validation.go:93-96`): the result is `deny(reason, err)`
(`webhook.go:322-324`), not `noOpinion("failed closed", err)`. Benign (more restrictive). -/
theorem P_51_unrestricted_does_not_hold :
    ¬ ∀ (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool) (s : SubjectAccessReviewStatus),
        valid s = false → ∃ e, w.conditionsAwareStatus valid s = w.conditionsAwareFailureDecision e := by
  intro h
  let w : WebhookAuthorizer :=
    { decisionOnError := .NoOpinion, hasReviewer := true, builtin := none, acr := fun _ _ => none }
  let s : SubjectAccessReviewStatus := { Allowed := true, Denied := true }
  obtain ⟨e, he⟩ := h w (fun _ => false) s rfl
  simp [w, s, conditionsAwareStatus, conditionsAwareFailureDecision] at he

/-! ### P-52 -/

/-- **P-52** "`webhookEvaluateConditions` returns a possible decision or the failure decision":
result ∈ `PD(d')` and is the webhook's own answer, or `= (FD d', "failed closed", err≠nil)`. -/
theorem P_52_possible_or_failure (w : WebhookAuthorizer) (d : ConditionsAwareDecision) (x : ConditionsData) :
    let r := w.webhookEvaluateConditions d x
    (w.hasReviewer = true ∧ w.acr d x = some r ∧ d.PossibleDecisions.Has r.1 = true)
    ∨ (r.1 = d.FailureDecision ∧ r.2.1 = "failed closed" ∧ r.2.2.isSome = true) := by
  simp only [webhookEvaluateConditions]
  cases hr : w.hasReviewer
  · simp
  · cases ha : w.acr d x with
    | none => simp
    | some r =>
      by_cases hp : d.PossibleDecisions.Has r.1 = true
      · simp [hp]
      · simp [hp]

/-- **P-52** "never A unless A ∈ PD(d') and the webhook said A". -/
theorem P_52_allow_only_if_possible_and_said (w : WebhookAuthorizer) (d : ConditionsAwareDecision)
    (x : ConditionsData) (h : (w.webhookEvaluateConditions d x).1 = .Allow) :
    d.PossibleDecisions.Has .Allow = true ∧ ∃ rs ee, w.acr d x = some (.Allow, rs, ee) := by
  rcases P_52_possible_or_failure w d x with ⟨_, ha, hp⟩ | ⟨hf, _, _⟩
  · rw [h] at hp
    refine ⟨hp, (w.webhookEvaluateConditions d x).2.1, (w.webhookEvaluateConditions d x).2.2, ?_⟩
    rw [ha, ← h]
  · exact absurd (hf ▸ h) (FailureDecision_ne_Allow d)

/-! ### P-32 -/

/-- **P-32 (first part)** "The webhook never feeds builtin errors into partial evaluation":
`p_b(c) ∈ {T, F, U}`. -/
theorem P_32_builtin_oracle_no_error (b : Condition → ConditionEvaluationResult) (c : Condition) :
    (builtinOracle b c).IsError = false := by
  unfold builtinOracle
  split <;> simp_all [ConditionEvaluationResult.IsError]

/-- **P-32 (second part)** "if peval(d, p_b) is unconditional, no ACR is sent": the result is
`UnconditionalPartsOrError` of the refined decision. -/
theorem P_32_unconditional_refined_no_acr (w : WebhookAuthorizer) (d : ConditionsAwareDecision)
    (x : ConditionsData) (hd : d.IsUnconditional = false)
    (hu : (w.tryEvaluateUsingBuiltins d).IsUnconditional = true) :
    w.EvaluateConditions d (some x) = (w.tryEvaluateUsingBuiltins d).UnconditionalPartsOrError := by
  simp [EvaluateConditions, hd, hu]

/-- **P-32 (second part, extensional form)**: in that case the ACR oracle is irrelevant. -/
theorem P_32_unconditional_refined_acr_irrelevant (w : WebhookAuthorizer) (d : ConditionsAwareDecision)
    (x : ConditionsData) (hd : d.IsUnconditional = false)
    (hu : (w.tryEvaluateUsingBuiltins d).IsUnconditional = true)
    (acr' : ConditionsAwareDecision → ConditionsData → Option (Decision × String × Option Err)) :
    ({ w with acr := acr' } : WebhookAuthorizer).EvaluateConditions d (some x) = w.EvaluateConditions d (some x) := by
  have hu' : (({ w with acr := acr' } : WebhookAuthorizer).tryEvaluateUsingBuiltins d).IsUnconditional = true := by
    simpa [tryEvaluateUsingBuiltins] using hu
  rw [P_32_unconditional_refined_no_acr _ d x hd hu', P_32_unconditional_refined_no_acr w d x hd hu]
  rfl

/-- **P-32 (third part)** "otherwise the ACR carries peval(d, p_b) and its answer is clamped to
PD(peval(d, p_b))": `EvaluateConditions` delegates the refined (not the original) decision. -/
theorem P_32_conditional_refined_sent (w : WebhookAuthorizer) (d : ConditionsAwareDecision)
    (x : ConditionsData) (hd : d.IsUnconditional = false)
    (hu : (w.tryEvaluateUsingBuiltins d).IsUnconditional = false) :
    w.EvaluateConditions d (some x) = w.webhookEvaluateConditions (w.tryEvaluateUsingBuiltins d) x := by
  simp [EvaluateConditions, hd, hu]

/-! ### P-26 -/

/-- **P-25 (hypothesis)** "partial evaluation never grows PD", for one decision and oracle.
Proved (for WF decisions) by the wave-2 evaluate properties. It is a per-instance hypothesis,
not a global axiom, because it is FALSE for non-WF unions: `union [("", allow)]` has
`PD = {A}`, but re-adding the child under the invalid name `""` makes `ToDecision` fail closed
to `noOpinion`, `PD = {N}` (`conditionsunion.go:58-84,135-145`). -/
def P_25_hyp (d : ConditionsAwareDecision) (p : MaybeEvaluateConditionFunc) : Prop :=
  (PartiallyEvaluateConditionsAwareDecision d p).PossibleDecisions.Subset d.PossibleDecisions

/-- Generic form: PD inclusion ⇒ FD can only drop (`N < D`). -/
theorem failLe_of_subset (d d' : ConditionsAwareDecision) (h : d'.PossibleDecisions.Subset d.PossibleDecisions) :
    failLe d'.FailureDecision d.FailureDecision := by
  unfold failLe ConditionsAwareDecision.FailureDecision
  by_cases h' : d'.PossibleDecisions.Has .Deny = true
  · simp [h', h .Deny h']
  · by_cases h2 : d.PossibleDecisions.Has .Deny = true <;> simp [h', h2]

/-- **P-26** "FailureDecision can only drop, from Deny to NoOpinion": `FD(peval(d,p_b)) ≤ FD(d)`
for the decision the webhook refines in-process, under `P_25_hyp` for the builtin oracle. -/
theorem P_26_failure_decision_drops (w : WebhookAuthorizer) (d : ConditionsAwareDecision)
    (hP25 : ∀ b, w.builtin = some b → P_25_hyp d (builtinOracle b)) :
    failLe (w.tryEvaluateUsingBuiltins d).FailureDecision d.FailureDecision := by
  unfold tryEvaluateUsingBuiltins
  cases hb : w.builtin with
  | none => exact Or.inl rfl
  | some b => exact failLe_of_subset _ _ (hP25 b hb)

/-! ### Divergence: legacy path errors on unrequested conditional answers -/

/-- **P-69 / P-K5 / shipped.md §3.1 (documented divergence from the KEP)**: on the legacy
`Authorize` path, an unrequested conditional answer that is not an explicit deny fails closed
WITH a non-nil error (`webhook.go:264-267`), so the filter answers 500, not 403 (P-70). The KEP
(`kep.md:890-892`) only says "fails closed". -/
theorem P_69_legacy_unrequested_conditional_errors (w : WebhookAuthorizer) (s : SubjectAccessReviewStatus)
    (hcd : s.ConditionalDecision ≠ none) (hD : s.Denied = false) :
    (w.Authorize (.ok true) (.ok s)).2.2.isSome = true
    ∧ (w.Authorize (.ok true) (.ok s)).1 ≠ .Allow := by
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hcd
  refine ⟨?_, P_49_legacy_conditional_not_allow w s hcd⟩
  simp [Authorize, authorizeStatus, hd, hD]

end webhook
