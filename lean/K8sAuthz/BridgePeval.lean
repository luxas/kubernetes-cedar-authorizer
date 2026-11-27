import K8sAuthz.Bridge

/-!
# `K8sAuthz.BridgePeval`: A-3, `peval_is_refinement`

The mirror's `PartiallyEvaluateConditionsAwareDecision` is a `Refines` step sequence of the
spec core (`K8sAuthz.Refines`): for a well-formed decision `d`, a total oracle `o` and a partial
oracle `p ⊑ o` that returns no errors,
`Refines (mapOracle o) (toCAD (peval d p)) (toCAD d)`.

The error-free premise and well-formedness (valid distinct union names) are the hypotheses; the
mirror's counterexamples (`P_27_counterexample`, `P_25_needs_WF`) show neither can be dropped.
-/

namespace K8sAuthz.Bridge

open authorizer K8sAuthz

/-! ### Lifting steps through union cells -/

theorem step_from_list {o : CM → Dec} {x y : CAD CM} (h : Step o x y) (hx : isList x = true) :
    isList y = true ∨ ∃ d, y = .un d := by
  cases h with
  | resolve => simp [isList] at hx
  | shrink => simp [isList] at hx
  | head => exact Or.inl hx
  | tail _ hl => exact Or.inl (by simpa [isList] using hl)
  | trunc => exact Or.inl rfl
  | norm => exact Or.inr ⟨_, rfl⟩

theorem tail_lift {o : CM → Dec} (n : String) (c : CAD CM) {r r' : CAD CM} (h : Steps o r r')
    (hr : isList r = true) (hl : isList r' = true) : Steps o (.ucons n c r) (.ucons n c r') := by
  induction h with
  | refl => exact Steps.refl _
  | cons s rest ih =>
    rcases step_from_list s hr with hy | ⟨d, hd⟩
    · exact Steps.cons (Step.tail s hy) (ih hy hl)
    · subst hd
      have := steps_un rest
      subst this; simp [isList] at hl

theorem head_lift {o : CM → Dec} (n : String) (r : CAD CM) {c c' : CAD CM} (h : Steps o c c') :
    Steps o (.ucons n c r) (.ucons n c' r) := by
  induction h with
  | refl => exact Steps.refl _
  | cons s rest ih => exact Steps.cons (Step.head s) ih

theorem prefix_lift {o : CM → Dec} (pre : List (String × ConditionsAwareDecision))
    {x y : List (String × ConditionsAwareDecision)} (h : Steps o (toCADList x) (toCADList y)) :
    Steps o (toCADList (pre ++ x)) (toCADList (pre ++ y)) := by
  induction pre with
  | nil => exact h
  | cons p r ih =>
    obtain ⟨n, c⟩ := p
    exact tail_lift n (toCAD c) ih (isList_toCADList _) (isList_toCADList _)

theorem steps_trans' {o : CM → Dec} {x y z : CAD CM} (h1 : Steps o x y) (h2 : Steps o y z) :
    Steps o x z := Steps.trans h1 h2

theorem clamp_map {o : MaybeEvaluateConditionFunc} (ho : o.Total) (m : CM) :
    clamp (!m.denyConditions.isEmpty) (!m.allowConditions.isEmpty) (mapOracle o m) = mapOracle o m := by
  have := sem_toCAD ho (.conditionsMap m)
  simpa [toCAD, sem, mapOracle] using this

theorem pmap_shape (m : CM) (p : MaybeEvaluateConditionFunc) :
    (∃ r e, pmap m p = .deny r e) ∨ (∃ r e, pmap m p = .allow r e) ∨
    (∃ r e, pmap m p = .noOpinion r e) ∨ ∃ m', pmap m p = .conditionsMap m' := by
  obtain ⟨D, N, A⟩ := m
  have mk : ∀ D N A : List Condition,
      (∃ r e, ConditionsAwareDecisionConditionsMap D N A = .noOpinion r e) ∨
      (∃ r e, ConditionsAwareDecisionConditionsMap D N A = .deny r e) ∨
      ∃ m', ConditionsAwareDecisionConditionsMap D N A = .conditionsMap m' := by
    intro D N A
    rcases mkMap_cases D N A with h | ⟨r, e, h⟩
    · exact Or.inr (Or.inr ⟨_, h⟩)
    · rw [h]; split
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  rcases pmap_cases D N A p with ⟨-, r, h'⟩ | ⟨-, -, e, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, r, h'⟩ | ⟨-, -, -, e, h'⟩
    | ⟨-, -, -, -, h'⟩ | ⟨-, -, -, r, h'⟩ | ⟨-, -, -, -, e, h'⟩ | ⟨-, -, -, -, -, h'⟩ | ⟨-, -, -, h'⟩ <;>
    rw [h']
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · rcases mk (unevOf D p) N A with ⟨r, e, h⟩ | ⟨r, e, h⟩ | ⟨m', h⟩ <;> rw [h] <;> simp
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · rcases mk [] (unevOf N p) A with ⟨r, e, h⟩ | ⟨r, e, h⟩ | ⟨m', h⟩ <;> rw [h] <;> simp
  · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · rcases mk [] [] (unevOf A p) with ⟨r, e, h⟩ | ⟨r, e, h⟩ | ⟨m', h⟩ <;> rw [h] <;> simp
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))

theorem pd_map_deny (m : CM) :
    (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Has .Deny = !m.denyConditions.isEmpty := by
  cases hD : m.denyConditions <;> cases hA : m.allowConditions <;>
    simp [ConditionsAwareDecision.PossibleDecisions, authorizer.ConditionsMap.PossibleDecisions,
      DecisionSet.Has, DecisionSet.singleton, DecisionSet.Insert, hD, hA]

theorem pd_map_allow (m : CM) :
    (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Has .Allow = !m.allowConditions.isEmpty := by
  cases hD : m.denyConditions <;> cases hA : m.allowConditions <;>
    simp [ConditionsAwareDecision.PossibleDecisions, authorizer.ConditionsMap.PossibleDecisions,
      DecisionSet.Has, DecisionSet.singleton, DecisionSet.Insert, hD, hA]

/-- A-3 for a map: the mirror's `pmap` is one `resolve` or `shrink` step. -/
theorem pmap_refines {o p : MaybeEvaluateConditionFunc} (ho : o.Total) (hpo : p ⊑ o)
    (hp : ∀ c, (p c).IsError = false) {m : CM} (hm : m.WF) :
    Steps (mapOracle o) (toCAD (.conditionsMap m)) (toCAD (pmap m p)) := by
  have hsem := authorizer.P_27_map hm hpo ho hp
  have hcl := clamp_map ho m
  rcases pmap_shape m p with ⟨r, e, h⟩ | ⟨r, e, h⟩ | ⟨r, e, h⟩ | ⟨m', h⟩
  all_goals rw [h] at hsem ⊢
  · refine Steps.cons ?_ (Steps.refl _)
    have := Step.resolve (o := mapOracle o) (!m.denyConditions.isEmpty) (!m.allowConditions.isEmpty) m
    have e : mapOracle o m = .deny := by unfold mapOracle; rw [← hsem]; rfl
    rw [hcl, e] at this
    exact this
  · refine Steps.cons ?_ (Steps.refl _)
    have := Step.resolve (o := mapOracle o) (!m.denyConditions.isEmpty) (!m.allowConditions.isEmpty) m
    have e : mapOracle o m = .allow := by unfold mapOracle; rw [← hsem]; rfl
    rw [hcl, e] at this
    exact this
  · refine Steps.cons ?_ (Steps.refl _)
    have := Step.resolve (o := mapOracle o) (!m.denyConditions.isEmpty) (!m.allowConditions.isEmpty) m
    have e : mapOracle o m = .noOp := by unfold mapOracle; rw [← hsem]; rfl
    rw [hcl, e] at this
    exact this
  · refine Steps.cons ?_ (Steps.refl _)
    have hw' : (ConditionsAwareDecision.conditionsMap m').WF := by
      have := authorizer.peval_WF (ConditionsAwareDecision.WF.conditionsMap m hm) p
      rwa [authorizer.peval_map, h] at this
    have hm' : m'.WF := by cases hw' with | conditionsMap _ h => exact h
    have hsub := authorizer.P_25_map m p
    rw [h] at hsub
    have hcl' := clamp_map ho m'
    refine Step.shrink _ _ m _ _ m' ?_ ?_ ?_ ?_
    · obtain ⟨_, _, h3, _⟩ := hm'
      rcases h3 with h | h <;> simp [h, List.isEmpty_iff]
    · intro hd
      have := hsub .Deny (by rw [pd_map_deny]; exact hd)
      rwa [pd_map_deny] at this
    · intro ha
      have := hsub .Allow (by rw [pd_map_allow]; exact ha)
      rwa [pd_map_allow] at this
    · rw [hcl, hcl']
      have := congrArg toDec hsem
      simpa [mapOracle] using this

end K8sAuthz.Bridge
