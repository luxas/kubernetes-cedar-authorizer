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

/-! ### The union loop -/

open ConditionsAwareDecisionUnion in
theorem loopB_inner_of_cua (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) (u : ConditionsAwareDecisionUnion) (ct : Bool),
      u.containsUnconditionalAllowOrDeny = true → (loopB p l u ct).inner = u.inner
  | [], u, ct, _ => rfl
  | (n, c) :: rest, u, ct, hu => by
    have hnoop : ∀ d, u.Add n d = u := fun d => P_33_add_noop u n d hu
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte, hnoop]
      split
      · rfl
      · exact loopB_inner_of_cua p rest u _ hu
    · simp only [loopB, ↓reduceIte, hnoop]
      exact loopB_inner_of_cua p rest u _ hu

open ConditionsAwareDecisionUnion in
/-- Once a builder has stopped (its last child contains an unconditional Allow/Deny), the
remaining children are dropped: a `trunc` step. -/
theorem trunc_steps {o : CM → Dec} {u : ConditionsAwareDecisionUnion}
    (hr : Reachable ConditionsAwareDecision.WF u) (hu : u.containsUnconditionalAllowOrDeny = true)
    (l : List (String × ConditionsAwareDecision)) :
    Steps o (toCADList (u.inner ++ l)) (toCADList u.inner) := by
  have hi := hr.inv
  have hgo : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go u.inner = true := by
    rw [← hi.cua]; exact hu
  have hne : u.inner ≠ [] := by
    intro h0; rw [h0] at hgo; simp [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go] at hgo
  have hsplit := List.dropLast_concat_getLast hne
  obtain ⟨c, hc, hcc⟩ := (ConditionsAwareDecision.go_iff _).1 hgo
  have hlast : (u.inner.getLast hne).2.ContainsUnconditionalAllowOrDeny = true := by
    rw [← hsplit] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · rw [hi.dropLast c hc] at hcc; exact absurd hcc (by decide)
    · exact hcc
  generalize u.inner.getLast hne = q at hlast hsplit
  obtain ⟨k, c0⟩ := q
  rw [← hsplit, List.append_assoc]
  have hcua : cua (toCAD c0) = true := by rw [(pd_cua_toCAD c0).2]; exact hlast
  have := prefix_lift (o := o) u.inner.dropLast
    (x := (k, c0) :: l) (y := [(k, c0)]) (Steps.cons (Step.trunc hcua) (Steps.refl _))
  simpa using this

open ConditionsAwareDecisionUnion in
theorem loop_steps {o : MaybeEvaluateConditionFunc} {p : MaybeEvaluateConditionFunc} :
    ∀ (l : List (String × ConditionsAwareDecision)) (u : ConditionsAwareDecisionUnion) (ct : Bool),
      Reachable ConditionsAwareDecision.WF u →
      (∀ x ∈ l, ConditionsAwareDecision.WF x.2 ∧
          Steps (mapOracle o) (toCAD x.2) (toCAD (peval x.2 p))) →
      Steps (mapOracle o) (toCADList (u.inner ++ l)) (toCADList (loopB p l u ct).inner)
  | [], u, ct, _, _ => by simpa [loopB] using Steps.refl _
  | (n, c) :: rest, u, ct, hr, hl => by
    by_cases hu : u.containsUnconditionalAllowOrDeny = true
    · rw [loopB_inner_of_cua p _ u ct hu]
      exact trunc_steps hr hu _
    · have hu' : u.containsUnconditionalAllowOrDeny = false := by simpa using hu
      have hinner : ∀ d, (u.Add n d).inner = u.inner ++ [(n, d)] :=
        fun d => (Add_of_not_cua u n d hu').1
      have hc := hl (n, c) (by simp)
      have hrest : ∀ x ∈ rest, ConditionsAwareDecision.WF x.2 ∧
          Steps (mapOracle o) (toCAD x.2) (toCAD (peval x.2 p)) :=
        fun x hx => hl x (by simp [hx])
      cases ct
      · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
        have hrA : Reachable ConditionsAwareDecision.WF (u.Add n (peval c p)) :=
          .add _ _ hr (authorizer.peval_WF hc.1 p)
        have h1 : Steps (mapOracle o) (toCADList (u.inner ++ (n, c) :: rest))
            (toCADList (u.inner ++ (n, peval c p) :: rest)) :=
          prefix_lift u.inner (head_lift n _ hc.2)
        split
        · rename_i hcua
          refine Steps.trans h1 ?_
          rw [hinner]
          have hcua' : cua (toCAD (peval c p)) = true := by rw [(pd_cua_toCAD _).2]; exact hcua
          exact prefix_lift u.inner (x := (n, peval c p) :: rest) (y := [(n, peval c p)])
            (Steps.cons (Step.trunc hcua') (Steps.refl _))
        · refine Steps.trans h1 ?_
          have := loop_steps rest (u.Add n (peval c p)) (!(peval c p).IsUnconditional) hrA hrest
          rw [hinner] at this
          simpa using this
      · simp only [loopB, ↓reduceIte]
        have hrA : Reachable ConditionsAwareDecision.WF (u.Add n c) := .add _ _ hr hc.1
        have := loop_steps rest (u.Add n c) true hrA hrest
        rw [hinner] at this
        simpa using this

theorem toDS_theOnly (s : DecisionSet) (x : authorizer.Decision) (h : s.theOnly = some x) :
    (toDS s).theOnly = some (toDec x) := by
  rcases s with ⟨dd, aa, nn⟩
  revert h
  cases dd <;> cases aa <;> cases nn <;> cases x <;>
    simp [DecisionSet.theOnly, DecisionSet.Len, toDS, DS.theOnly, toDec]

open ConditionsAwareDecisionUnion in
theorem toDecision_cases (u : ConditionsAwareDecisionUnion) (he : u.errs = []) :
    u.ToDecision = .union u.inner ∨
    ∃ only r e, u.PossibleDecisions.theOnly = some only ∧
      u.ToDecision = ConditionsAwareDecisionFromParts only r e := by
  unfold ToDecision
  simp only [he, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  cases hT : u.PossibleDecisions.theOnly with
  | none => exact Or.inl rfl
  | some only => exact Or.inr ⟨only, _, _, rfl, rfl⟩

theorem toCAD_fromParts (x : authorizer.Decision) (r : String) (e : Option Err) :
    toCAD (ConditionsAwareDecisionFromParts x r e) = .un (toDec x) := by
  cases x <;> rfl

/-- **A-3 (`peval_is_refinement`)**: for a well-formed decision `d`, a total oracle `o`, and a
partial oracle `p ⊑ o` that returns no errors, the mirror's partial evaluation of `d` under `p`
is a refinement of `d` in the spec's sense (a sequence of agreeing steps), w.r.t. the oracle on
maps induced by `o`. -/
theorem peval_is_refinement {o p : MaybeEvaluateConditionFunc} (ho : o.Total) (hpo : p ⊑ o)
    (hp : ∀ c, (p c).IsError = false) {d : ConditionsAwareDecision}
    (hw : ConditionsAwareDecision.WF d) :
    Refines (mapOracle o) (toCAD (peval d p)) (toCAD d) := by
  unfold Refines
  induction d using authorizer.CAD_induct with
  | hdeny r e => simpa using Steps.refl (toCAD (ConditionsAwareDecision.deny r e))
  | hallow r e => simpa using Steps.refl (toCAD (ConditionsAwareDecision.allow r e))
  | hnoOp r e => simpa using Steps.refl (toCAD (ConditionsAwareDecision.noOpinion r e))
  | hmap m =>
    cases hw with
    | conditionsMap _ hm =>
      rw [authorizer.peval_map]
      exact pmap_refines ho hpo hp hm
  | hunion l ih =>
    cases hw with
    | union _ hne hv hnd hwc hdl hlen =>
      rw [authorizer.peval_union']
      have hr := loopB_reachable (P := ConditionsAwareDecision.WF) p l {} false
        .empty (fun x hx => ⟨hwc x hx, authorizer.peval_WF (hwc x hx) p⟩)
      have hs := loop_steps (o := o) (p := p) l {} false .empty
        (fun x hx => ⟨hwc x hx, ih x hx (hwc x hx)⟩)
      have he := authorizer.loopB_errs p l {} false rfl hnd hv (by simp)
      simp only [List.nil_append] at hs
      rcases toDecision_cases _ he with h | ⟨only, r, e, ho', h⟩
      · rw [h]; exact hs
      · rw [h, toCAD_fromParts]
        refine Steps.trans hs (Steps.cons (Step.norm ?_ ?_) (Steps.refl _))
        · exact isUn_toCADList _
        · have hpd := (pd_cua_toCAD (.union (loopB p l {} false).inner)).1
          have e2 := hr.PD_eq
          rw [← e2] at hpd
          have : pd (toCADList (loopB p l {} false).inner) = toDS (loopB p l {} false).PossibleDecisions := hpd
          rw [this]
          exact toDS_theOnly _ _ ho'


end K8sAuthz.Bridge
