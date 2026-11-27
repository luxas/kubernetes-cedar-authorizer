import authorizer.evaluate_internal_properties

/-!
# `authorizer/evaluate_properties.lean`  ↔  `pkg/authorization/authorizer/evaluate_test.go`

Tree-level partial-evaluation properties of `review/properties.md` Part 2 §D and §E about
`PartiallyEvaluateConditionsAwareDecision` (`evaluate.go:235-282`), abbreviated `peval`, and
the reference semantics `refSem` (§1.7): P-19 (tree), P-20 (chain), P-25 (+ negative), P-26,
P-27 (+ counterexamples), P-28, P-30, P-31, P-37, P-38. Consistency `p ⊑ o` is defined in
`evaluate_internal_properties.lean`.

Method: `CAD_induct` is structural induction over the nested tree with a hypothesis for
every child; `loopB` is the builder at which the Go loop calls `ToDecision` (`loop_eq`), and
every union result is analysed through it (`loopB_reachable`, `loopB_errs`, `loopB_PD`,
`loopB_seq`, `loopB_total_singleton`, `loopB_names`, `loopB_rerun`).

Summary of what needs well-formedness:
* hold for ALL trees: P-19 (tree), P-30, P-31 (exact equality, any oracle), P-37 (total
  oracle), P-38 (reachable builder without name errors, any children).
* need WF (only for the union names: a re-`Add` under an invalid/duplicate name fails the
  union closed): P-25, P-26, P-27, P-28 (decision part). `P_25_needs_WF` is the
  counterexample. P-27 additionally needs `∀ c, p c ∉ E` (`P_27_counterexample`).
-/

namespace authorizer
open DecisionSet ConditionsAwareDecision ConditionEvaluationResult ConditionsAwareDecisionUnion

/-! ## Induction principle and unfolding -/

section induct
variable {motive : ConditionsAwareDecision → Prop}
  (hdeny : ∀ r e, motive (.deny r e)) (hallow : ∀ r e, motive (.allow r e))
  (hnoOp : ∀ r e, motive (.noOpinion r e)) (hmap : ∀ m, motive (.conditionsMap m))
  (hunion : ∀ l, (∀ x ∈ l, motive x.2) → motive (.union l))
include hdeny hallow hnoOp hmap hunion

mutual
/-- Structural induction over the nested tree, with the hypothesis for every child. -/
theorem CAD_induct : ∀ d, motive d
  | .deny r e => hdeny r e
  | .allow r e => hallow r e
  | .noOpinion r e => hnoOp r e
  | .conditionsMap m => hmap m
  | .union l => hunion l (CAD_induct_list l)
theorem CAD_induct_list : ∀ l : List (String × ConditionsAwareDecision), ∀ x ∈ l, motive x.2
  | [] => by simp
  | (_, c) :: rest => by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact CAD_induct c
    · exact CAD_induct_list rest x hx
end
end induct


/-- Short name for `PartiallyEvaluateConditionsAwareDecision` (`evaluate.go:235`). -/
abbrev peval := PartiallyEvaluateConditionsAwareDecision

@[simp] theorem peval_deny (r e p) : peval (.deny r e) p = .deny r e := by
  simp [peval, PartiallyEvaluateConditionsAwareDecision]
@[simp] theorem peval_allow (r e p) : peval (.allow r e) p = .allow r e := by
  simp [peval, PartiallyEvaluateConditionsAwareDecision]
@[simp] theorem peval_noOpinion (r e p) : peval (.noOpinion r e) p = .noOpinion r e := by
  simp [peval, PartiallyEvaluateConditionsAwareDecision]
@[simp] theorem peval_map (m p) : peval (.conditionsMap m) p = pmap m p := by
  simp [peval, PartiallyEvaluateConditionsAwareDecision]
theorem peval_union (l p) : peval (.union l) p = PartiallyEvaluateConditionsAwareDecision.loop p l {} false := by
  simp [peval, PartiallyEvaluateConditionsAwareDecision]

/-- The builder state at which `PartiallyEvaluateConditionsAwareDecision.loop` calls `ToDecision`
(`evaluate.go:248-277`). -/
def loopB (p : MaybeEvaluateConditionFunc) :
    List (String × ConditionsAwareDecision) → ConditionsAwareDecisionUnion → Bool → ConditionsAwareDecisionUnion
  | [], chain, _ => chain
  | (name, sub) :: rest, chain, collectTail =>
    if collectTail then loopB p rest (chain.Add name sub) true
    else
      let evaluated := peval sub p
      let chain := chain.Add name evaluated
      if evaluated.ContainsUnconditionalAllowOrDeny then chain
      else loopB p rest chain (!evaluated.IsUnconditional)

theorem loop_eq (p : MaybeEvaluateConditionFunc) : ∀ l chain ct,
    PartiallyEvaluateConditionsAwareDecision.loop p l chain ct = (loopB p l chain ct).ToDecision
  | [], chain, ct => by simp [PartiallyEvaluateConditionsAwareDecision.loop, loopB]
  | (n, c) :: rest, chain, ct => by
    cases ct
    · simp only [PartiallyEvaluateConditionsAwareDecision.loop, loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · exact loop_eq p rest _ _
    · simp only [PartiallyEvaluateConditionsAwareDecision.loop, loopB, ↓reduceIte]
      exact loop_eq p rest _ _

theorem peval_union' (l : List (String × ConditionsAwareDecision)) (p : MaybeEvaluateConditionFunc) :
    peval (.union l) p = (loopB p l {} false).ToDecision := by
  rw [peval_union, loop_eq]

/-! ## Builder `Add` lemmas -/

theorem Add_inner (u : ConditionsAwareDecisionUnion) (n : String) (d : ConditionsAwareDecision) :
    (u.Add n d).inner = if u.containsUnconditionalAllowOrDeny then u.inner else u.inner ++ [(n, d)] := by
  cases h : u.containsUnconditionalAllowOrDeny
  · simp [(Add_of_not_cua u n d h).1]
  · simp [P_33_add_noop u n d h]

theorem Add_flag (u : ConditionsAwareDecisionUnion) (n : String) (d : ConditionsAwareDecision) :
    (u.Add n d).containsUnconditionalAllowOrDeny = (u.containsUnconditionalAllowOrDeny || d.ContainsUnconditionalAllowOrDeny) := by
  cases h : u.containsUnconditionalAllowOrDeny
  · simp [(Add_of_not_cua u n d h).2.1]
  · simp [P_33_add_noop u n d h, h]

/-- A name check that passes: non-empty, DNS-1123, not yet used ⇒ no error is recorded. -/
theorem Add_errs_nil (u : ConditionsAwareDecisionUnion) (n : String) (d : ConditionsAwareDecision)
    (he : u.errs = []) (h1 : n.length ≠ 0) (h2 : IsDNS1123Subdomain n = true) (h3 : n ∉ u.inner.map Prod.fst) :
    (u.Add n d).errs = [] := by
  cases h : u.containsUnconditionalAllowOrDeny
  · refine ((Add_of_not_cua u n d h).2.2.2).2 ⟨he, h1, ?_, h2⟩
    simp only [hasConditionalAuthorizerName, List.any_eq_false, beq_iff_eq]
    intro x hx hxn; exact h3 (List.mem_map.2 ⟨x, hx, hxn⟩)
  · rw [P_33_add_noop u n d h]; exact he

/-! ## `PossibleDecisions` of a union, membership form -/

theorem PD_union_Has_iff (l : List (String × ConditionsAwareDecision)) (y : Decision) :
    (ConditionsAwareDecision.union l).PossibleDecisions.Has y = true ↔
      (y = .NoOpinion ∧ ContainsUnconditionalAllowOrDeny.go l = false)
      ∨ (y ≠ .NoOpinion ∧ (PossibleDecisions.subPD l).Has y = true) := by
  rw [PD_union_Has]
  cases hg : ContainsUnconditionalAllowOrDeny.go l <;> by_cases hy : y = .NoOpinion <;> simp [hy]

/-! ## P-37 -/

theorem refSem_seq_cons (o : MaybeEvaluateConditionFunc) (n : String) (c : ConditionsAwareDecision) l :
    refSem.seq o ((n, c) :: l) = if refSem o c = .NoOpinion then refSem.seq o l else refSem o c := by
  simp only [refSem.seq]; split <;> simp_all

theorem refSem_union (o : MaybeEvaluateConditionFunc) (l : List (String × ConditionsAwareDecision)) :
    refSem o (.union l) = refSem.seq o l := by simp [refSem]

theorem seq_mem (o : MaybeEvaluateConditionFunc) : ∀ l : List (String × ConditionsAwareDecision),
    (∀ x ∈ l, x.2.PossibleDecisions.Has (refSem o x.2) = true) →
      (ConditionsAwareDecision.union l).PossibleDecisions.Has (refSem.seq o l) = true
  | [], _ => rfl
  | (n, c) :: rest, h => by
    have hc := h (n, c) (by simp)
    have ih := seq_mem o rest (fun x hx => h x (by simp [hx]))
    rw [refSem_seq_cons]
    rw [PD_union_Has_iff] at ih ⊢
    split
    · rename_i hN
      simp only at hc
      rw [hN, P_35_noOpinion_possible_iff] at hc
      simp only [Bool.not_eq_true'] at hc
      simp only [go_cons, hc, Bool.false_or, subPD_cons, Has_union, Bool.or_eq_true]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr ⟨ih.1, Or.inr ih.2⟩
    · rename_i hN
      exact Or.inr ⟨hN, by simp [hc]⟩

/-- **P-37 Soundness of PD for every decision.** `∀ total o. ⟦d⟧ₒ ∈ PD(d)`. Holds for EVERY
tree (no well-formedness needed): maps by P-18, unions because `seq` either returns some
child's non-N result, or N when every child is N, in which case (P-35 + IH) no child contains
an unconditional Allow/Deny and `N ∈ PD(union)`. -/
theorem P_37_refSem_mem_PD {o : MaybeEvaluateConditionFunc} (ho : o.Total) (d : ConditionsAwareDecision) :
    d.PossibleDecisions.Has (refSem o d) = true := by
  induction d using CAD_induct with
  | hdeny => rfl
  | hallow => rfl
  | hnoOp => rfl
  | hmap m =>
    obtain ⟨-, x, hx, hm⟩ := P_18_dec_mem_PD m ho
    rw [pmap_total m ho] at hx
    rw [refSem_map ho]; injection hx with hx; rw [hx]; exact hm
  | hunion l ih => rw [refSem_union]; exact seq_mem o l ih

/-- A decision containing an unconditional Allow/Deny never means NoOpinion (P-35 + P-37). -/
theorem refSem_ne_N_of_cua {o : MaybeEvaluateConditionFunc} (ho : o.Total) {d : ConditionsAwareDecision}
    (h : d.ContainsUnconditionalAllowOrDeny = true) : refSem o d ≠ .NoOpinion := by
  intro hN
  have := P_37_refSem_mem_PD ho d
  rw [hN, P_35_noOpinion_possible_iff, h] at this
  exact absurd this (by decide)


/-! ## The partial-evaluation loop -/

abbrev ReachableAny := ConditionsAwareDecisionUnion.Reachable (fun _ => True)

theorem Subset.refl' (s : DecisionSet) : s.Subset s := fun _ h => h
theorem Subset.trans' {s t u : DecisionSet} (h1 : s.Subset t) (h2 : t.Subset u) : s.Subset u :=
  fun y hy => h2 y (h1 y hy)

theorem PD_FromParts (x : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts x r e).PossibleDecisions = .singleton x := by
  cases x <;> rfl

theorem refSem_FromParts (o : MaybeEvaluateConditionFunc) (x : Decision) (r : String) (e : Option Err) :
    refSem o (ConditionsAwareDecisionFromParts x r e) = x := by
  cases x <;> rfl

/-- The loop's builder is reachable whenever the original and evaluated children satisfy `P`. -/
theorem loopB_reachable {P : ConditionsAwareDecision → Prop} (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct,
      ConditionsAwareDecisionUnion.Reachable P chain → (∀ x ∈ l, P x.2 ∧ P (peval x.2 p)) →
      ConditionsAwareDecisionUnion.Reachable P (loopB p l chain ct)
  | [], chain, ct, hr, _ => hr
  | (n, c) :: rest, chain, ct, hr, hl => by
    have hc := hl (n, c) (by simp)
    have hrest : ∀ x ∈ rest, P x.2 ∧ P (peval x.2 p) := fun x hx => hl x (by simp [hx])
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · exact .add _ _ hr hc.2
      · exact loopB_reachable p rest _ _ (.add _ _ hr hc.2) hrest
    · simp only [loopB, ↓reduceIte]
      exact loopB_reachable p rest _ _ (.add _ _ hr hc.1) hrest

/-- With valid, distinct names (as in a WF union), the loop records no name error. -/
theorem loopB_errs (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct,
      chain.errs = [] → (l.map Prod.fst).Nodup →
      (∀ x ∈ l, x.1.length ≠ 0 ∧ IsDNS1123Subdomain x.1 = true) →
      (∀ x ∈ chain.inner, x.1 ∉ l.map Prod.fst) → (loopB p l chain ct).errs = []
  | [], chain, ct, he, _, _, _ => he
  | (n, c) :: rest, chain, ct, he, hnd, hv, hdis => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hn := hv (n, c) (by simp)
    have hrest : ∀ x ∈ rest, x.1.length ≠ 0 ∧ IsDNS1123Subdomain x.1 = true := fun x hx => hv x (by simp [hx])
    have hnot : n ∉ chain.inner.map Prod.fst := by
      intro h; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h; exact hdis x hx (by simp)
    have step : ∀ d, (chain.Add n d).errs = [] ∧ ∀ x ∈ (chain.Add n d).inner, x.1 ∉ rest.map Prod.fst := by
      intro d
      refine ⟨Add_errs_nil chain n d he hn.1 hn.2 hnot, ?_⟩
      intro x hx
      rw [Add_inner] at hx
      split at hx
      · exact fun h => hdis x hx (by simp [h])
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact fun h => hdis x hx (by simp [h])
        · exact hnd.1
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · exact (step _).1
      · exact loopB_errs p rest _ _ (step _).1 hnd.2 hrest (step _).2
    · simp only [loopB, ↓reduceIte]
      exact loopB_errs p rest _ _ (step _).1 hnd.2 hrest (step _).2

/-- `ToDecision` never leaves `PD(union inner)` when no name error was recorded. -/
theorem PD_ToDecision_subset {P} {u : ConditionsAwareDecisionUnion}
    (hr : ConditionsAwareDecisionUnion.Reachable P u) (he : u.errs = []) :
    u.ToDecision.PossibleDecisions.Subset (ConditionsAwareDecision.union u.inner).PossibleDecisions := by
  unfold ToDecision
  simp only [he, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i x hx
    rw [PD_FromParts, ← hr.PD_eq, ← (theOnly_eq_some_iff _ _).1 hx]
    exact Subset.refl' _
  · exact Subset.refl' _

/-! ### PD comparison of child lists -/

/-- `l₁` can only yield what `l₂` can: children's PDs included and N removed in `l₁` whenever
it is removed in `l₂`. -/
def PDle (l₁ l₂ : List (String × ConditionsAwareDecision)) : Prop :=
  (PossibleDecisions.subPD l₁).Subset (PossibleDecisions.subPD l₂)
  ∧ (ContainsUnconditionalAllowOrDeny.go l₂ = true → ContainsUnconditionalAllowOrDeny.go l₁ = true)

theorem PDle.PD {l₁ l₂ : List (String × ConditionsAwareDecision)} (h : PDle l₁ l₂) :
    (ConditionsAwareDecision.union l₁).PossibleDecisions.Subset (ConditionsAwareDecision.union l₂).PossibleDecisions := by
  intro y hy
  rw [PD_union_Has_iff] at hy ⊢
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    cases h3 : ContainsUnconditionalAllowOrDeny.go l₂
    · rfl
    · rw [h.2 h3] at h2; exact absurd h2 (by decide)
  · exact Or.inr ⟨h1, h.1 y h2⟩

theorem PDle.refl (l : List (String × ConditionsAwareDecision)) : PDle l l := ⟨Subset.refl' _, id⟩
theorem PDle.trans {a b c : List (String × ConditionsAwareDecision)} (h1 : PDle a b) (h2 : PDle b c) : PDle a c :=
  ⟨Subset.trans' h1.1 h2.1, fun h => h1.2 (h2.2 h)⟩

theorem PDle_prefix {A : List (String × ConditionsAwareDecision)} (B : List (String × ConditionsAwareDecision))
    (h : ContainsUnconditionalAllowOrDeny.go A = true) : PDle A (A ++ B) :=
  ⟨fun y hy => by rw [subPD_append]; simp [hy], fun _ => h⟩

theorem PDle_drop {A : List (String × ConditionsAwareDecision)} (x) (B : List (String × ConditionsAwareDecision))
    (h : ContainsUnconditionalAllowOrDeny.go A = true) : PDle (A ++ B) (A ++ x :: B) := by
  obtain ⟨n, c⟩ := x
  refine ⟨fun y hy => ?_, fun _ => by rw [go_append, h]; rfl⟩
  rw [subPD_append] at hy ⊢
  simp only [Has_union, Bool.or_eq_true, subPD_cons] at hy ⊢
  rcases hy with hy | hy <;> simp [hy]

theorem cua_of_PD_subset {c c' : ConditionsAwareDecision} (h : c'.PossibleDecisions.Subset c.PossibleDecisions)
    (hc : c.ContainsUnconditionalAllowOrDeny = true) : c'.ContainsUnconditionalAllowOrDeny = true := by
  cases h' : c'.ContainsUnconditionalAllowOrDeny
  · have hN : c'.PossibleDecisions.Has .NoOpinion = true := by rw [P_35_noOpinion_possible_iff, h']; rfl
    have := h _ hN
    rw [P_35_noOpinion_possible_iff, hc] at this; exact absurd this (by decide)
  · rfl

theorem PDle_replace (A B : List (String × ConditionsAwareDecision)) (n : String) {c c' : ConditionsAwareDecision}
    (h : c'.PossibleDecisions.Subset c.PossibleDecisions) : PDle (A ++ (n, c') :: B) (A ++ (n, c) :: B) := by
  refine ⟨fun y hy => ?_, fun hg => ?_⟩
  · rw [subPD_append] at hy ⊢
    simp only [Has_union, Bool.or_eq_true, subPD_cons] at hy ⊢
    rcases hy with hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inl (h y hy))
    · exact Or.inr (Or.inr hy)
  · rw [go_append, go_cons] at hg ⊢
    simp only [Bool.or_eq_true] at hg ⊢
    rcases hg with hg | hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl (cua_of_PD_subset h hg))
    · exact Or.inr (Or.inr hg)

/-- The loop's final children list is `PDle` the input list. -/
theorem loopB_PD (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct, ReachableAny chain →
      (∀ x ∈ l, (peval x.2 p).PossibleDecisions.Subset x.2.PossibleDecisions) →
      PDle (loopB p l chain ct).inner (chain.inner ++ l)
  | [], chain, ct, _, _ => by simpa [loopB] using PDle.refl _
  | (n, c) :: rest, chain, ct, hr, hl => by
    have hc := hl (n, c) (by simp)
    have hrest := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hflag := hr.cua_eq
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i hcua
        rw [Add_inner]
        split
        · rename_i hf; rw [hflag] at hf; exact PDle_prefix _ hf
        · rw [List.append_cons chain.inner]
          refine PDle.trans (PDle_prefix rest ?_) ?_
          · simp only [go_append, go_cons, go_nil, hcua]; simp
          · simpa using PDle_replace chain.inner rest n hc
      · refine PDle.trans (loopB_PD p rest _ _ (.add _ _ hr trivial) hrest) ?_
        rw [Add_inner]
        split
        · rename_i hf; rw [hflag] at hf; exact PDle_drop _ _ hf
        · simpa using PDle_replace chain.inner rest n hc
    · simp only [loopB, ↓reduceIte]
      refine PDle.trans (loopB_PD p rest _ _ (.add _ _ hr trivial) hrest) ?_
      rw [Add_inner]
      split
      · rename_i hf; rw [hflag] at hf; exact PDle_drop _ _ hf
      · simpa using PDle.refl _


/-! ### Reference-semantics comparison of child lists -/

theorem seq_append_of_ne (o : MaybeEvaluateConditionFunc) :
    ∀ (A B : List (String × ConditionsAwareDecision)), refSem.seq o A ≠ .NoOpinion →
      refSem.seq o (A ++ B) = refSem.seq o A
  | [], _, h => absurd rfl h
  | (n, c) :: rest, B, h => by
    simp only [List.cons_append, refSem_seq_cons] at h ⊢
    split
    · rename_i hc; rw [if_pos hc] at h; exact seq_append_of_ne o rest B h
    · rfl

theorem seq_ne_N_of_go {o : MaybeEvaluateConditionFunc} (ho : o.Total) {A : List (String × ConditionsAwareDecision)}
    (h : ContainsUnconditionalAllowOrDeny.go A = true) : refSem.seq o A ≠ .NoOpinion := by
  rw [← refSem_union]; exact refSem_ne_N_of_cua ho (d := .union A) h

theorem seq_replace (o : MaybeEvaluateConditionFunc) (B : List (String × ConditionsAwareDecision)) (n : String)
    {c c' : ConditionsAwareDecision} (h : refSem o c' = refSem o c) :
    ∀ A : List (String × ConditionsAwareDecision),
      refSem.seq o (A ++ (n, c') :: B) = refSem.seq o (A ++ (n, c) :: B)
  | [] => by simp [refSem_seq_cons, h]
  | (m, d) :: rest => by simp only [List.cons_append, refSem_seq_cons, seq_replace o B n h rest]

/-- The loop's final children list has the same reference meaning as the input list, provided
each child keeps its meaning under partial evaluation. -/
theorem loopB_seq {o : MaybeEvaluateConditionFunc} (ho : o.Total) (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct, ReachableAny chain →
      (∀ x ∈ l, refSem o (peval x.2 p) = refSem o x.2) →
      refSem.seq o (loopB p l chain ct).inner = refSem.seq o (chain.inner ++ l)
  | [], chain, ct, _, _ => by simp [loopB]
  | (n, c) :: rest, chain, ct, hr, hl => by
    have hc := hl (n, c) (by simp)
    have hrest := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hflag := hr.cua_eq
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i hcua
        rw [Add_inner]
        split
        · rename_i hf; rw [hflag] at hf
          exact (seq_append_of_ne o _ _ (seq_ne_N_of_go ho hf)).symm
        · have hg : ContainsUnconditionalAllowOrDeny.go (chain.inner ++ [(n, peval c p)]) = true := by
            simp only [go_append, go_cons, go_nil, hcua]; simp
          rw [← seq_append_of_ne o _ rest (seq_ne_N_of_go ho hg), List.append_assoc]
          exact seq_replace o rest n hc chain.inner
      · rw [loopB_seq ho p rest _ _ (.add _ _ hr trivial) hrest, Add_inner]
        split
        · rename_i hf; rw [hflag] at hf
          rw [seq_append_of_ne o _ _ (seq_ne_N_of_go ho hf), seq_append_of_ne o _ _ (seq_ne_N_of_go ho hf)]
        · rw [List.append_assoc]; exact seq_replace o rest n hc chain.inner
    · simp only [loopB, ↓reduceIte]
      rw [loopB_seq ho p rest _ _ (.add _ _ hr trivial) hrest, Add_inner]
      split
      · rename_i hf; rw [hflag] at hf
        rw [seq_append_of_ne o _ _ (seq_ne_N_of_go ho hf), seq_append_of_ne o _ _ (seq_ne_N_of_go ho hf)]
      · simp

/-! ## P-38 -/

/-- **P-38 Folding preserves the outcome.** For a builder reachable from `{}` by `Add` with no
recorded name error, `∀ total o. ⟦toDecision(B)⟧ₒ = seq(B.inner)`: the fold fires only on a
singleton `PD_B = {X}` and then `seq(inner) = X` for every `o` (P-37). Holds for ANY children
(well-formedness of the children is not needed); `B.inner` omits the no-op `Add`s after a
cua child, which `seq` never reaches. -/
theorem P_38_fold_preserves_refSem {P} {u : ConditionsAwareDecisionUnion}
    (hr : ConditionsAwareDecisionUnion.Reachable P u) (he : u.errs = [])
    {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    refSem o u.ToDecision = refSem.seq o u.inner := by
  unfold ToDecision
  simp only [he, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i x hx
    rw [refSem_FromParts]
    have hm := P_37_refSem_mem_PD ho (.union u.inner)
    rw [← hr.PD_eq, (theOnly_eq_some_iff _ _).1 hx, refSem_union, Has_singleton] at hm
    exact (of_decide_eq_true hm).symm
  · exact refSem_union o _

/-- **P-38** in the catalogue form: children all WF. -/
theorem P_38_WF {u : ConditionsAwareDecisionUnion}
    (hr : ConditionsAwareDecisionUnion.Reachable ConditionsAwareDecision.WF u) (he : u.errs = [])
    {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    refSem o u.ToDecision = refSem.seq o u.inner :=
  P_38_fold_preserves_refSem hr he ho

/-! ## Union case of the tree theorems -/

/-- Partial evaluation of a union whose names are valid and distinct keeps the reference meaning,
if every child does. -/
theorem refSem_peval_union {o : MaybeEvaluateConditionFunc} (ho : o.Total) (p : MaybeEvaluateConditionFunc)
    (l : List (String × ConditionsAwareDecision))
    (hn : ∀ x ∈ l, x.1.length ≠ 0 ∧ IsDNS1123Subdomain x.1 = true) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ x ∈ l, refSem o (peval x.2 p) = refSem o x.2) :
    refSem o (peval (.union l) p) = refSem o (.union l) := by
  rw [peval_union', refSem_union]
  have hr : ReachableAny (loopB p l {} false) :=
    loopB_reachable p l {} false .empty (fun _ _ => ⟨trivial, trivial⟩)
  have he := loopB_errs p l {} false rfl hnd hn (by simp)
  rw [P_38_fold_preserves_refSem hr he ho, loopB_seq ho p l {} false .empty hl]
  rfl

theorem PD_peval_union (p : MaybeEvaluateConditionFunc) (l : List (String × ConditionsAwareDecision))
    (hn : ∀ x ∈ l, x.1.length ≠ 0 ∧ IsDNS1123Subdomain x.1 = true) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ x ∈ l, (peval x.2 p).PossibleDecisions.Subset x.2.PossibleDecisions) :
    (peval (.union l) p).PossibleDecisions.Subset (ConditionsAwareDecision.union l).PossibleDecisions := by
  rw [peval_union']
  have hr : ReachableAny (loopB p l {} false) :=
    loopB_reachable p l {} false .empty (fun _ _ => ⟨trivial, trivial⟩)
  have he := loopB_errs p l {} false rfl hnd hn (by simp)
  exact Subset.trans' (PD_ToDecision_subset hr he) (by simpa using (loopB_PD p l {} false .empty hl).PD)

/-! ## P-25 -/

/-- **P-25 Monotone refinement: partial evaluation never grows PD.**
`∀ WF d, ∀p. PD(peval(d,p)) ⊆ PD(d)` — no consistency or no-error premise. WF is needed only
for the union names (re-`Add` must not record name errors; see `P_25_needs_WF`). -/
theorem P_25_monotone {d : ConditionsAwareDecision} (hw : d.WF) (p : MaybeEvaluateConditionFunc) :
    (peval d p).PossibleDecisions.Subset d.PossibleDecisions := by
  induction d using CAD_induct with
  | hdeny => exact Subset.refl' _
  | hallow => exact Subset.refl' _
  | hnoOp => exact Subset.refl' _
  | hmap m => rw [peval_map]; exact P_25_map m p
  | hunion l ih =>
    cases hw with
    | union _ _ hn hnd hwc _ _ => exact PD_peval_union p l hn hnd (fun x hx => ih x hx (hwc x hx))

/-- **P-25 does NOT hold without well-formedness.** The (non-WF) union `[("", allow)]` is
re-`Add`ed under the invalid empty name; the builder records an error and fails closed to
`FD_B = N` (`PD_B = {A}`), so `PD(peval) = {N} ⊄ {A} = PD(d)`. -/
theorem P_25_needs_WF :
    ¬ ∀ (d : ConditionsAwareDecision) (p : MaybeEvaluateConditionFunc),
        (peval d p).PossibleDecisions.Subset d.PossibleDecisions := by
  -- status: does NOT hold for arbitrary trees (holds for WF, see `P_25_monotone`)
  intro h
  have h1 := h (.union [("", .allow "" none)]) (fun _ => .unevaluatable)
  have e : peval (.union [("", .allow "" none)]) (fun _ => .unevaluatable)
      = (({} : ConditionsAwareDecisionUnion).Add "" (.allow "" none)).ToDecision := by
    rw [peval_union']; rfl
  have hno := P_34_allow_with_empty_name_becomes_noOpinion "" none
  rw [← e] at hno
  have hN : (peval (.union [("", .allow "" none)]) (fun _ => .unevaluatable)).PossibleDecisions.Has .NoOpinion = true := by
    revert hno; cases peval (.union [("", .allow "" none)]) (fun _ => .unevaluatable) <;>
      simp [IsNoOpinion, ConditionsAwareDecision.PossibleDecisions]
  have := h1 _ hN
  exact absurd this (by decide)

/-! ## P-26 -/

/-- **P-26 FailureDecision can only drop, from Deny to NoOpinion** (`N < D`): for WF `d`,
`FD(peval(d,p)) = D ⇒ FD(d) = D`. Corollary of P-25 and P-5. -/
theorem P_26_failureDecision_drops {d : ConditionsAwareDecision} (hw : d.WF) (p : MaybeEvaluateConditionFunc)
    (h : (peval d p).FailureDecision = .Deny) : d.FailureDecision = .Deny := by
  rw [(P_5_failureDecision_spec _).2] at h ⊢
  exact P_25_monotone hw p _ h

/-- **P-26** contrapositive form: an original NoOpinion failure decision stays NoOpinion. -/
theorem P_26_failureDecision_le {d : ConditionsAwareDecision} (hw : d.WF) (p : MaybeEvaluateConditionFunc)
    (h : d.FailureDecision = .NoOpinion) : (peval d p).FailureDecision = .NoOpinion := by
  rcases (P_5_failureDecision_spec (peval d p)).1 with h' | h'
  · rw [P_26_failureDecision_drops hw p h'] at h; exact absurd h (by decide)
  · exact h'


/-! ## P-19 (tree form) -/

theorem ToDecision_uncond_of_singleton {u : ConditionsAwareDecisionUnion} {x : Decision}
    (h : u.PossibleDecisions = .singleton x) : u.ToDecision.IsUnconditional = true := by
  unfold ToDecision
  split
  · exact FromParts_IsUnconditional _ _ _
  · rw [(theOnly_eq_some_iff _ _).2 h]; exact FromParts_IsUnconditional _ _ _

/-- With a total oracle the loop never enters tail mode and its builder has a singleton PD:
all children before the stopping one are NoOpinion, the stopping one (if any) is Allow/Deny. -/
theorem loopB_total_singleton {o : MaybeEvaluateConditionFunc} :
    ∀ (l : List (String × ConditionsAwareDecision)) (chain : ConditionsAwareDecisionUnion),
      chain.containsUnconditionalAllowOrDeny = false →
      chain.subDecisionsPossibleDecisions.Has .Deny = false →
      chain.subDecisionsPossibleDecisions.Has .Allow = false →
      (∀ x ∈ l, (peval x.2 o).IsUnconditional = true) →
      ∃ x, (loopB o l chain false).PossibleDecisions = .singleton x
  | [], chain, hf, hD, hA, _ => by
    refine ⟨.NoOpinion, ext_Has fun y => ?_⟩
    simp only [loopB, ConditionsAwareDecisionUnion.PossibleDecisions,
      ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, hf, Bool.false_eq_true, ↓reduceIte]
    cases y <;> simp [hD, hA]
  | (n, c) :: rest, chain, hf, hD, hA, hl => by
    have hc := hl (n, c) (by simp)
    obtain ⟨e1, e2, e3, -⟩ := Add_of_not_cua chain n (peval c o) hf
    simp only at hc
    simp only [loopB, Bool.false_eq_true, ↓reduceIte]
    cases hev : peval c o with
    | allow r e =>
      rw [hev] at e2 e3
      refine ⟨.Allow, ext_Has fun y => ?_⟩
      simp only [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny, ↓reduceIte, ConditionsAwareDecisionUnion.PossibleDecisions,
        ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, e2, e3]
      cases y <;> simp [hD, hA, ConditionsAwareDecision.PossibleDecisions]
    | deny r e =>
      rw [hev] at e2 e3
      refine ⟨.Deny, ext_Has fun y => ?_⟩
      simp only [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny, ↓reduceIte, ConditionsAwareDecisionUnion.PossibleDecisions,
        ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, e2, e3]
      cases y <;> simp [hD, hA, ConditionsAwareDecision.PossibleDecisions]
    | noOpinion r e =>
      rw [hev] at e2 e3
      simp only [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny, Bool.false_eq_true, ↓reduceIte, IsUnconditional, IsAllow,
        IsDeny, IsNoOpinion, Bool.or_true, Bool.not_true]
      exact loopB_total_singleton rest _ e2 (by simp [e3, hD, ConditionsAwareDecision.PossibleDecisions])
        (by simp [e3, hA, ConditionsAwareDecision.PossibleDecisions]) (fun x hx => hl x (by simp [hx]))
    | conditionsMap m => rw [hev] at hc; simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at hc
    | union l' => rw [hev] at hc; simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at hc

/-- **P-19 (tree form) Totality.** `∀ total o. uncond(peval(d,o))`, for EVERY tree (no
well-formedness needed: even a union failing closed on a name error is unconditional). -/
theorem P_19_tree_total_unconditional {o : MaybeEvaluateConditionFunc} (ho : o.Total) (d : ConditionsAwareDecision) :
    (peval d o).IsUnconditional = true := by
  induction d using CAD_induct with
  | hdeny => rfl
  | hallow => rfl
  | hnoOp => rfl
  | hmap m => rw [peval_map]; exact P_19_total_unconditional m ho
  | hunion l ih =>
    rw [peval_union']
    obtain ⟨x, hx⟩ := loopB_total_singleton (o := o) l {} rfl rfl rfl ih
    exact ToDecision_uncond_of_singleton hx

/-! ## P-28 (tree form) -/

theorem refSem_of_dec? (o : MaybeEvaluateConditionFunc) {d : ConditionsAwareDecision} {x : Decision}
    (h : d.dec? = some x) : refSem o d = x := by
  cases d <;> simp_all [dec?, refSem]

theorem dec?_of_uncond (o : MaybeEvaluateConditionFunc) {d : ConditionsAwareDecision}
    (h : d.IsUnconditional = true) : d.dec? = some (refSem o d) := by
  cases d <;> simp_all [dec?, refSem, IsUnconditional, IsAllow, IsDeny, IsNoOpinion]

/-- `⟦peval(d,o)⟧ₒ = ⟦d⟧ₒ` for a total `o` (WF needed for the union names). -/
theorem refSem_peval_total {o : MaybeEvaluateConditionFunc} (ho : o.Total) {d : ConditionsAwareDecision}
    (hw : d.WF) : refSem o (peval d o) = refSem o d := by
  induction d using CAD_induct with
  | hdeny => rfl
  | hallow => rfl
  | hnoOp => rfl
  | hmap m => rw [peval_map, refSem_of_dec? o (pmap_total m ho), refSem_map ho]
  | hunion l ih =>
    cases hw with
    | union _ _ hn hnd hwc _ _ => exact refSem_peval_union ho o l hn hnd (fun x hx => ih x hx (hwc x hx))

/-- **P-28 Partial evaluation with a total oracle is full evaluation.**
`∀ WF d, total o. uncond(peval(d,o)) ∧ dec(peval(d,o)) = ⟦d⟧ₒ`. (Unconditionality holds for
every tree, P-19; the decision equation needs WF union names — without them the builder
fails closed, e.g. `[("", allow)]` becomes NoOpinion while `⟦·⟧ = A`.) -/
theorem P_28_total_is_full {o : MaybeEvaluateConditionFunc} (ho : o.Total) {d : ConditionsAwareDecision}
    (hw : d.WF) : (peval d o).IsUnconditional = true ∧ (peval d o).dec? = some (refSem o d) := by
  have hu := P_19_tree_total_unconditional ho d
  exact ⟨hu, by rw [dec?_of_uncond o hu, refSem_peval_total ho hw]⟩

/-- **P-28 does NOT hold without well-formedness** (the catalogue states it for all `d`): the
non-WF union `[("", allow)]` partially evaluates, under any total oracle, to a fail-closed
NoOpinion (name error, `FD_B = N`), while `⟦d⟧ₒ = A`. -/
theorem P_28_needs_WF :
    ¬ ∀ (d : ConditionsAwareDecision) (o : MaybeEvaluateConditionFunc), o.Total →
        (peval d o).dec? = some (refSem o d) := by
  -- status: does NOT hold for arbitrary trees (holds for WF, see `P_28_total_is_full`)
  intro h
  let o : MaybeEvaluateConditionFunc := fun _ => .false_
  have ho : o.Total := fun _ => by simp [o]
  have h1 := h (.union [("", .allow "" none)]) o ho
  have e : peval (.union [("", .allow "" none)]) o
      = (({} : ConditionsAwareDecisionUnion).Add "" (.allow "" none)).ToDecision := by
    rw [peval_union']; rfl
  have hno := P_34_allow_with_empty_name_becomes_noOpinion "" none
  rw [← e] at hno
  have hr : refSem o (.union [("", .allow "" none)]) = .Allow := rfl
  rw [hr] at h1
  revert hno h1; cases peval (.union [("", .allow "" none)]) o <;> simp [IsNoOpinion, dec?]

/-! ## P-27 -/

/-- **P-27 Confluence: partial-then-full equals full — with an exact precondition.**
`∀ WF d, p ⊑ o, total o. (∀c. p(c) ∉ E) ⇒ ⟦peval(d,p)⟧ₒ = ⟦d⟧ₒ`. The no-error premise cannot
be dropped (`P_27_counterexample`). -/
theorem P_27_confluence {d : ConditionsAwareDecision} (hw : d.WF) {p o : MaybeEvaluateConditionFunc}
    (hpo : p ⊑ o) (ho : o.Total) (hp : ∀ c, (p c).IsError = false) :
    refSem o (peval d p) = refSem o d := by
  induction d using CAD_induct with
  | hdeny => rfl
  | hallow => rfl
  | hnoOp => rfl
  | hmap m => cases hw with | conditionsMap _ hm => rw [peval_map]; exact P_27_map hm hpo ho hp
  | hunion l ih =>
    cases hw with
    | union _ _ hn hnd hwc _ _ => exact refSem_peval_union ho p l hn hnd (fun x hx => ih x hx (hwc x hx))

/-- The P-27 counterexample oracles: `p(a1) = o(a1) = E`, `p(a2) = U`, `o(a2) = T`, `F` elsewhere. -/
def cexP (a1 a2 : Condition) (e : Err) : MaybeEvaluateConditionFunc :=
  fun c => if c = a1 then .error e else if c = a2 then .unevaluatable else .false_
def cexO (a1 a2 : Condition) (e : Err) : MaybeEvaluateConditionFunc :=
  fun c => if c = a1 then .error e else if c = a2 then .true_ else .false_

/-- **P-27 counterexample without the no-error premise** (`properties.md` P-27, verified against
`evaluate.go:173-187`). `m = ([], [], [a1, a2])`, `p(a1) = o(a1) = E`, `p(a2) = U`, `o(a2) = T`:
full evaluation meets `a1` (E, collected) then `a2` (T) ⇒ Allow; partial evaluation returns
`errs = [a1]`, `unev = [a2]`, and errors win over unevaluatable (`:182`) ⇒ NoOpinion.
The map is WF whenever `a1`, `a2` are valid (`IsDomainPrefixedKey` is opaque, hence the
hypotheses). -/
theorem P_27_counterexample (a1 a2 : Condition) (e : Err) (hid : a1.ID ≠ a2.ID) :
    ((a1.valid = true → a2.valid = true →
        (ConditionsAwareDecision.conditionsMap ⟨[], [], [a1, a2]⟩).WF))
    ∧ cexP a1 a2 e ⊑ cexO a1 a2 e ∧ (cexO a1 a2 e).Total
    ∧ refSem (cexO a1 a2 e) (peval (.conditionsMap ⟨[], [], [a1, a2]⟩) (cexP a1 a2 e)) = .NoOpinion
    ∧ refSem (cexO a1 a2 e) (.conditionsMap ⟨[], [], [a1, a2]⟩) = .Allow := by
  have hne : a2 ≠ a1 := fun h => hid (by rw [h])
  refine ⟨fun h1 h2 => .conditionsMap _ ⟨by simp [ConditionsMap.Length], by simp [ConditionsMap.Length, MaxConditionsPerMap],
    Or.inr (by simp), ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [ConditionsMap.all] using hid
  · intro x hx; simp [ConditionsMap.all] at hx; rcases hx with rfl | rfl <;> assumption
  · intro c; by_cases h1 : c = a1 <;> by_cases h2 : c = a2 <;> simp [cexP, cexO, h1, h2, hne]
  · intro c; by_cases h1 : c = a1 <;> by_cases h2 : c = a2 <;> simp [cexO, h1, h2, hne]
  · rw [peval_map]
    obtain ⟨err, h⟩ := pmap_A_E (A := [a1, a2]) (p := cexP a1 a2 e)
      (by simp [anyT, cexP, hne, IsTrue]) (by simp [anyE, cexP, IsError])
    rw [h]; rfl
  · rw [refSem_map (by intro c; by_cases h1 : c = a1 <;> by_cases h2 : c = a2 <;> simp [cexO, h1, h2, hne])]
    simp [decSpec, anyT, anyE, cexO, hne, IsTrue]

/-- **P-27 the no-error premise is necessary** (WF form): as soon as two valid conditions with
distinct IDs exist, confluence fails for some WF map. -/
theorem P_27_needs_no_error_premise (hex : ∃ a1 a2 : Condition, a1.valid = true ∧ a2.valid = true ∧ a1.ID ≠ a2.ID) :
    ¬ ∀ (d : ConditionsAwareDecision) (p o : MaybeEvaluateConditionFunc),
        d.WF → p ⊑ o → o.Total → refSem o (peval d p) = refSem o d := by
  -- status: does NOT hold without `∀ c, p c ∉ E`
  obtain ⟨a1, a2, h1, h2, hid⟩ := hex
  intro h
  obtain ⟨hw, hpo, ho, hl, hr⟩ := P_27_counterexample a1 a2 "e" hid
  have := h (.conditionsMap ⟨[], [], [a1, a2]⟩) _ _ (hw h1 h2) hpo ho
  rw [hl, hr] at this; exact absurd this (by decide)

/-- **P-27 the no-error premise is necessary** (unconditional form, over arbitrary trees). -/
theorem P_27_needs_no_error_premise' :
    ¬ ∀ (d : ConditionsAwareDecision) (p o : MaybeEvaluateConditionFunc),
        p ⊑ o → o.Total → refSem o (peval d p) = refSem o d := by
  -- status: does NOT hold without `∀ c, p c ∉ E`
  intro h
  obtain ⟨-, hpo, ho, hl, hr⟩ := P_27_counterexample { ID := "a" } { ID := "b" } "e" (by decide)
  have := h (.conditionsMap ⟨[], [], [{ ID := "a" }, { ID := "b" }]⟩) _ _ hpo ho
  rw [hl, hr] at this; exact absurd this (by decide)

/-- **P-27 error-component counterexample** (Deny phase): `D = [d1, d2]`, `p(d1) = E`,
`p(d2) = U`, `o(d2) = T`: partial gives `deny(err)`, full gives `deny(nil)` — same decision,
different error, which the enforcer turns into 500 vs 403 (`conditionsenforcer.go:126-141`). -/
theorem P_27_error_component_counterexample (d1 d2 : Condition) (e : Err) (hid : d1.ID ≠ d2.ID) :
    (∃ err, peval (.conditionsMap ⟨[d1, d2], [], []⟩) (cexP d1 d2 e) = .deny evaluationErrorsReason (some err))
    ∧ (∃ r, pmap ⟨[d1, d2], [], []⟩ (cexO d1 d2 e) = .deny r none) := by
  have hne : d2 ≠ d1 := fun h => hid (by rw [h])
  refine ⟨?_, pmap_D_T (by simp [anyT, cexO, hne, IsTrue])⟩
  rw [peval_map]
  exact pmap_D_E (by simp [anyT, cexP, hne, IsTrue]) (by simp [anyE, cexP, IsError])


/-! ## Well-formedness is preserved -/

/-- Partial evaluation maps WF decisions to WF decisions (map results go through the smart
constructor, unions through the builder). -/
theorem peval_WF {d : ConditionsAwareDecision} (hw : d.WF) (p : MaybeEvaluateConditionFunc) : (peval d p).WF := by
  induction d using CAD_induct with
  | hdeny => exact hw
  | hallow => exact hw
  | hnoOp => exact hw
  | hmap m =>
    rw [peval_map]
    obtain ⟨D, N, A⟩ := m
    rcases pmap_cases D N A p with ⟨-, r, h'⟩ | ⟨-, -, e, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, r, h'⟩ | ⟨-, -, -, e, h'⟩
      | ⟨-, -, -, -, h'⟩ | ⟨-, -, -, r, h'⟩ | ⟨-, -, -, -, e, h'⟩ | ⟨-, -, -, -, -, h'⟩ | ⟨-, -, -, h'⟩ <;>
      rw [h'] <;> first | exact WF_mkMap _ _ _ | constructor
  | hunion l ih =>
    cases hw with
    | union _ _ _ _ hwc _ _ =>
      rw [peval_union']
      exact WF_ToDecision (loopB_reachable p l {} false .empty
        (fun x hx => ⟨hwc x hx, ih x hx (hwc x hx)⟩))

/-! ## P-30 -/

theorem loopB_stuck (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct,
      chain.containsUnconditionalAllowOrDeny = true → loopB p l chain ct = chain
  | [], _, _, _ => rfl
  | (n, c) :: rest, chain, ct, h => by
    have hA : ∀ d, chain.Add n d = chain := fun d => P_33_add_noop chain n d h
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte, hA]
      split
      · rfl
      · exact loopB_stuck p rest _ _ h
    · simp only [loopB, ↓reduceIte, hA]; exact loopB_stuck p rest _ _ h

theorem loopB_names (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain ct, ReachableAny chain →
      ((loopB p l chain ct).inner.map Prod.fst = chain.inner.map Prod.fst ++ l.map Prod.fst)
      ∨ (ContainsUnconditionalAllowOrDeny.go (loopB p l chain ct).inner = true
          ∧ ((loopB p l chain ct).inner.map Prod.fst).IsPrefix (chain.inner.map Prod.fst ++ l.map Prod.fst))
  | [], chain, ct, _ => Or.inl (by simp [loopB])
  | (n, c) :: rest, chain, ct, hr => by
    have hflag := hr.cua_eq
    by_cases hf : chain.containsUnconditionalAllowOrDeny = true
    · rw [loopB_stuck p _ chain ct hf]
      exact Or.inr ⟨hflag ▸ hf, List.prefix_append _ _⟩
    have hf' : chain.containsUnconditionalAllowOrDeny = false := by simpa using hf
    have hin : ∀ d, (chain.Add n d).inner = chain.inner ++ [(n, d)] := fun d => (Add_of_not_cua chain n d hf').1
    have step : ∀ d, ((loopB p rest (chain.Add n d) true).inner.map Prod.fst = chain.inner.map Prod.fst ++ ((n, c) :: rest).map Prod.fst)
        ∨ (ContainsUnconditionalAllowOrDeny.go (loopB p rest (chain.Add n d) true).inner = true
          ∧ ((loopB p rest (chain.Add n d) true).inner.map Prod.fst).IsPrefix
              (chain.inner.map Prod.fst ++ ((n, c) :: rest).map Prod.fst)) := by
      intro d
      rcases loopB_names p rest (chain.Add n d) true (.add _ _ hr trivial) with h | ⟨h1, h2⟩
      · left; rw [h, hin]; simp
      · right; refine ⟨h1, ?_⟩; rw [hin] at h2; simpa using h2
    have step' : ∀ d b, ((loopB p rest (chain.Add n d) b).inner.map Prod.fst = chain.inner.map Prod.fst ++ ((n, c) :: rest).map Prod.fst)
        ∨ (ContainsUnconditionalAllowOrDeny.go (loopB p rest (chain.Add n d) b).inner = true
          ∧ ((loopB p rest (chain.Add n d) b).inner.map Prod.fst).IsPrefix
              (chain.inner.map Prod.fst ++ ((n, c) :: rest).map Prod.fst)) := by
      intro d b
      rcases loopB_names p rest (chain.Add n d) b (.add _ _ hr trivial) with h | ⟨h1, h2⟩
      · left; rw [h, hin]; simp
      · right; refine ⟨h1, ?_⟩; rw [hin] at h2; simpa using h2
    cases ct
    · simp only [loopB, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i hcua
        right
        rw [hin]
        refine ⟨by rw [go_append]; simp [hcua], ?_⟩
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩)
      · exact step' _ _
    · simp only [loopB, ↓reduceIte]; exact step _

/-- **P-30 Order and names are preserved; truncation only after a cua child.**
If `peval(union l, p)` stays a union `l'`, the name sequence of `l'` is a prefix of the name
sequence of `l`, and if it is a proper prefix then the last child of `l'` contains an
unconditional Allow/Deny (`evaluate.go:253,263,266-268`). All trees. -/
theorem P_30_names_prefix (l l' : List (String × ConditionsAwareDecision)) (p : MaybeEvaluateConditionFunc)
    (h : peval (.union l) p = .union l') :
    (l'.map Prod.fst).IsPrefix (l.map Prod.fst)
    ∧ (l'.map Prod.fst ≠ l.map Prod.fst → ∃ x, l'.getLast? = some x ∧ x.2.ContainsUnconditionalAllowOrDeny = true) := by
  rw [peval_union'] at h
  have hr : ReachableAny (loopB p l {} false) :=
    loopB_reachable p l {} false .empty (fun _ _ => ⟨trivial, trivial⟩)
  obtain ⟨hl', -, -, -, -, hlast⟩ := P_36_union_shape hr h
  subst hl'
  rcases loopB_names p l {} false .empty with h1 | ⟨h1, h2⟩
  · simp only [List.map_nil, List.nil_append] at h1
    exact ⟨by rw [h1]; exact List.prefix_refl _, fun hne => absurd h1 hne⟩
  · simp only [List.map_nil, List.nil_append] at h2
    exact ⟨h2, fun _ => hlast h1⟩


/-! ## P-31 -/

theorem loopB_tail (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain,
      loopB p l chain true = l.foldl (fun u x => u.Add x.1 x.2) chain
  | [], _ => rfl
  | (n, c) :: rest, chain => by simp only [loopB, ↓reduceIte]; exact loopB_tail p rest _

/-- Folding `Add` over `L` appends exactly the children `K` that were not no-ops, and folding
over `K` alone gives the same builder. -/
theorem foldl_Add_trace : ∀ (L : List (String × ConditionsAwareDecision)) (u : ConditionsAwareDecisionUnion),
    ∃ K, (L.foldl (fun u x => u.Add x.1 x.2) u).inner = u.inner ++ K
      ∧ K.foldl (fun u x => u.Add x.1 x.2) u = L.foldl (fun u x => u.Add x.1 x.2) u
  | [], u => ⟨[], by simp, rfl⟩
  | x :: L, u => by
    simp only [List.foldl_cons]
    by_cases hf : u.containsUnconditionalAllowOrDeny = true
    · rw [P_33_add_noop u x.1 x.2 hf]; exact foldl_Add_trace L u
    · have hf' : u.containsUnconditionalAllowOrDeny = false := by simpa using hf
      obtain ⟨K, h1, h2⟩ := foldl_Add_trace L (u.Add x.1 x.2)
      refine ⟨x :: K, ?_, by simpa using h2⟩
      rw [h1, (Add_of_not_cua u x.1 x.2 hf').1]; simp

theorem peval_FromParts (x : Decision) (r : String) (e : Option Err) (p : MaybeEvaluateConditionFunc) :
    peval (ConditionsAwareDecisionFromParts x r e) p = ConditionsAwareDecisionFromParts x r e := by
  cases x <;> simp [ConditionsAwareDecisionFromParts]

/-- Re-running the loop on its own output children rebuilds the same builder. -/
theorem loopB_rerun (p : MaybeEvaluateConditionFunc) :
    ∀ (l : List (String × ConditionsAwareDecision)) chain,
      chain.containsUnconditionalAllowOrDeny = false →
      (∀ x ∈ l, peval (peval x.2 p) p = peval x.2 p) →
      ∃ T, (loopB p l chain false).inner = chain.inner ++ T ∧ loopB p T chain false = loopB p l chain false
  | [], chain, _, _ => ⟨[], by simp [loopB], rfl⟩
  | (n, c) :: rest, chain, hf, hl => by
    have hc := hl (n, c) (by simp)
    simp only at hc
    obtain ⟨e1, e2, -, -⟩ := Add_of_not_cua chain n (peval c p) hf
    have first : ∀ T, loopB p ((n, peval c p) :: T) chain false
        = if (peval c p).ContainsUnconditionalAllowOrDeny then chain.Add n (peval c p)
          else loopB p T (chain.Add n (peval c p)) (!(peval c p).IsUnconditional) := by
      intro T; simp only [loopB, Bool.false_eq_true, ↓reduceIte, hc]
    simp only [loopB, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hcua
      exact ⟨[(n, peval c p)], e1, by rw [first]; simp [hcua]⟩
    · rename_i hcua
      have hf2 : (chain.Add n (peval c p)).containsUnconditionalAllowOrDeny = false := by simpa [e2] using hcua
      cases hu : (peval c p).IsUnconditional
      · simp only [Bool.not_false]
        rw [loopB_tail]
        obtain ⟨K, h1, h2⟩ := foldl_Add_trace rest (chain.Add n (peval c p))
        refine ⟨(n, peval c p) :: K, by rw [h1, e1]; simp, ?_⟩
        rw [first]; simp [hcua, hu, loopB_tail, h2]
      · simp only [Bool.not_true]
        obtain ⟨T', h1, h2⟩ := loopB_rerun p rest _ hf2 (fun x hx => hl x (by simp [hx]))
        refine ⟨(n, peval c p) :: T', by rw [h1, e1]; simp, ?_⟩
        rw [first]; simp [hcua, hu, h2]

/-- **P-31 Idempotence.** `peval(peval(d,p),p) = peval(d,p)` — exact equality, for EVERY tree
and ANY oracle (stronger than the catalogue's `≅`): an unconditional result is returned
unchanged; a refined map contains only unevaluatable conditions in its first non-empty phase
(`P_31_map`); a union result is rebuilt child by child into the same builder
(`loopB_rerun`). -/
theorem P_31_idempotent (d : ConditionsAwareDecision) (p : MaybeEvaluateConditionFunc) :
    peval (peval d p) p = peval d p := by
  induction d using CAD_induct with
  | hdeny => rfl
  | hallow => rfl
  | hnoOp => rfl
  | hmap m =>
    rw [peval_map]
    cases h : pmap m p with
    | deny => rfl
    | allow => rfl
    | noOpinion => rfl
    | conditionsMap m' => rw [peval_map]; exact P_31_map m m' p h
    | union l' =>
      exfalso
      obtain ⟨D, N, A⟩ := m
      rcases pmap_cases D N A p with ⟨-, r, h'⟩ | ⟨-, -, e, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, r, h'⟩ | ⟨-, -, -, e, h'⟩
        | ⟨-, -, -, -, h'⟩ | ⟨-, -, -, r, h'⟩ | ⟨-, -, -, -, e, h'⟩ | ⟨-, -, -, -, -, h'⟩ | ⟨-, -, -, h'⟩ <;>
        rw [h'] at h <;> (try simp at h) <;>
        (rcases mkMap_cases _ _ _ with h'' | ⟨_, _, h''⟩ <;> rw [h''] at h <;> (try simp at h) <;>
          split at h <;> simp at h)
  | hunion l ih =>
    rw [peval_union']
    obtain ⟨T, h1, h2⟩ := loopB_rerun p l {} rfl ih
    simp only [List.nil_append] at h1
    rcases ToDecision_cases (loopB p l {} false) with ⟨x, r, e, h⟩ | ⟨-, -, h⟩ <;> rw [h]
    · exact peval_FromParts x r e p
    · rw [peval_union', h1, h2, h, h1]


/-! ## P-20 (chain form, remark) -/

/-- **P-20 (chain form)** In `seq(l)`, if `⟦cᵢ⟧ ≠ N` and every earlier child is `N`, the
result is `⟦cᵢ⟧` (`union.go:152-155,170-172`). -/
theorem P_20_chain_first_non_N (o : MaybeEvaluateConditionFunc) (n : String) (c : ConditionsAwareDecision)
    (B : List (String × ConditionsAwareDecision)) (hc : refSem o c ≠ .NoOpinion) :
    ∀ A : List (String × ConditionsAwareDecision), (∀ x ∈ A, refSem o x.2 = .NoOpinion) →
      refSem.seq o (A ++ (n, c) :: B) = refSem o c
  | [], _ => by simp [refSem_seq_cons, hc]
  | (m, d) :: rest, h => by
    have hd := h (m, d) (by simp)
    simp only at hd
    simp only [List.cons_append, refSem_seq_cons, hd, ↓reduceIte]
    exact P_20_chain_first_non_N o n c B hc rest (fun x hx => h x (by simp [hx]))

/-- **P-20 (chain form)** "a true Deny dominates every Allow" is NOT a property of the chain:
an earlier Allow wins over a later Deny (by design, `kep.md:861-869`). -/
theorem P_20_chain_earlier_allow_wins (o : MaybeEvaluateConditionFunc) (r r' : String) (e e' : Option Err) :
    refSem.seq o [("a", .allow r e), ("b", .deny r' e')] = .Allow := rfl
  -- status: absolute "Deny dominates every Allow" does NOT hold for the chain (by design)

end authorizer