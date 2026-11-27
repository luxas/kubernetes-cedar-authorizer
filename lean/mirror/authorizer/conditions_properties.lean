import authorizer.conditions

/-!
# `authorizer/conditions_properties.lean`  ↔  `pkg/authorization/authorizer/conditions_test.go`
(and the map half of `conditionsmap_test.go`)

Core algebra of `ConditionsAwareDecision`: properties P-1, P-3, P-4 (WF form), P-5, P-6,
P-9, P-13, P-14, P-15, P-35 of `review/properties.md` Part 2 §A, §B, §E, plus the helper
lemmas the other property files rely on (`DecisionSet` simp set, `subPD`/`go`
membership characterisations, `validateConditions` success lemma) and the
well-formedness predicate `ConditionsAwareDecision.WF` (= "producible by the public
constructors", `properties.md` §1.3).

Summary of what needs WF:
* hold for ALL trees: P-1, P-3, P-5, P-6 (`FD ≠ Allow` part), P-9, P-13, P-14, P-15
  (the PD equation), P-35.
* need well-formedness: P-4 (`IsUnconditional ↔ Len = 1`), P-6 (`FD ∈ PD` for non-allow
  decisions), P-15 (`2 ≤ Len`, needs `ConditionsMap.WF`). The negations for arbitrary
  trees are stated with counterexamples.
-/

namespace authorizer

/-! ## `DecisionSet` simp set -/

namespace DecisionSet

@[simp] theorem Has_empty (y : Decision) : empty.Has y = false := by cases y <;> rfl

@[simp] theorem Has_singleton (x y : Decision) : (singleton x).Has y = decide (y = x) := by
  cases x <;> cases y <;> rfl

@[simp] theorem Has_Insert (s : DecisionSet) (x y : Decision) :
    (s.Insert x).Has y = (decide (y = x) || s.Has y) := by
  cases x <;> cases y <;> simp [Insert, Has]

@[simp] theorem Has_Delete (s : DecisionSet) (x y : Decision) :
    (s.Delete x).Has y = (!decide (y = x) && s.Has y) := by
  cases x <;> cases y <;> simp [Delete, Has]

@[simp] theorem Has_union (s t : DecisionSet) (y : Decision) :
    (s.union t).Has y = (s.Has y || t.Has y) := by
  cases y <;> rfl

/-- Extensionality: a `DecisionSet` is determined by its membership function. -/
theorem ext_Has {s t : DecisionSet} (h : ∀ y, s.Has y = t.Has y) : s = t := by
  have h1 := h .Deny; have h2 := h .Allow; have h3 := h .NoOpinion
  cases s; cases t; simp_all [Has]

/-- `Len` in terms of membership. -/
theorem Len_eq (s : DecisionSet) :
    s.Len = (if s.Has .Deny then 1 else 0) + (if s.Has .Allow then 1 else 0)
      + (if s.Has .NoOpinion then 1 else 0) := rfl

theorem Len_le_three (s : DecisionSet) : s.Len ≤ 3 := by
  rcases s with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide

/-- `0 < Len` iff some member. -/
theorem Len_pos_iff (s : DecisionSet) : 0 < s.Len ↔ ∃ y, s.Has y = true := by
  rcases s with ⟨a, b, c⟩
  constructor
  · intro h
    cases a <;> cases b <;> cases c <;> simp_all [Len] <;>
      first | exact ⟨.Deny, rfl⟩ | exact ⟨.Allow, rfl⟩ | exact ⟨.NoOpinion, rfl⟩
  · rintro ⟨y, hy⟩
    cases y <;> simp_all [Has, Len] <;> (cases a <;> cases b <;> cases c <;> simp_all)

@[simp] theorem Len_singleton (x : Decision) : (singleton x).Len = 1 := by cases x <;> rfl

/-- `theOnly` is `none` exactly when `Len ≠ 1`. -/
theorem theOnly_eq_none_iff (s : DecisionSet) : s.theOnly = none ↔ s.Len ≠ 1 := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- `theOnly s = some x` iff `s = {x}`. -/
theorem theOnly_eq_some_iff (s : DecisionSet) (x : Decision) :
    s.theOnly = some x ↔ s = singleton x := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases x <;> decide

/-- `Len = 1` iff the set is a singleton. -/
theorem Len_eq_one_iff (s : DecisionSet) : s.Len = 1 ↔ ∃ x, s = singleton x := by
  constructor
  · intro h
    cases ho : s.theOnly with
    | none => exact absurd h ((theOnly_eq_none_iff s).1 ho)
    | some x => exact ⟨x, (theOnly_eq_some_iff s x).1 ho⟩
  · rintro ⟨x, rfl⟩; exact Len_singleton x

/-- `Len ≥ 2` follows from two distinct members. -/
theorem two_le_Len {s : DecisionSet} {x y : Decision} (hxy : x ≠ y)
    (hx : s.Has x = true) (hy : s.Has y = true) : 2 ≤ s.Len := by
  rcases s with ⟨a, b, c⟩
  cases x <;> cases y <;> simp_all [Has, Len] <;> (cases a <;> cases b <;> cases c <;> simp_all)

/-- A set of size ≥ 2 without `Deny` contains `NoOpinion`. -/
theorem has_N_of_two_le_Len_of_not_D {s : DecisionSet} (h2 : 2 ≤ s.Len)
    (hD : s.Has .Deny = false) : s.Has .NoOpinion = true := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> simp_all [Has, Len]

end DecisionSet

open DecisionSet

/-! ## `ConditionsMap` PD and FD -/

namespace ConditionsMap

@[simp] theorem PD_Has_NoOpinion (m : authorizer.ConditionsMap) :
    m.PossibleDecisions.Has .NoOpinion = true := by
  unfold PossibleDecisions; split <;> split <;> simp

@[simp] theorem PD_Has_Allow (m : authorizer.ConditionsMap) :
    m.PossibleDecisions.Has .Allow = decide (m.allowConditions ≠ []) := by
  unfold PossibleDecisions
  cases hA : m.allowConditions <;> cases hD : m.denyConditions <;> simp

@[simp] theorem PD_Has_Deny (m : authorizer.ConditionsMap) :
    m.PossibleDecisions.Has .Deny = decide (m.denyConditions ≠ []) := by
  unfold PossibleDecisions
  cases hA : m.allowConditions <;> cases hD : m.denyConditions <;> simp

/-- P-5 for the map (`conditionsmap.go:50-56`). -/
theorem FailureDecision_spec (m : authorizer.ConditionsMap) :
    (m.FailureDecision = .Deny ∨ m.FailureDecision = .NoOpinion)
    ∧ (m.FailureDecision = .Deny ↔ m.PossibleDecisions.Has .Deny = true) := by
  unfold FailureDecision; split <;> simp_all

end ConditionsMap

namespace ConditionsAwareDecision

/-! ## Membership characterisations for the union helpers -/

/-- `ContainsUnconditionalAllowOrDeny.go l` iff some child contains an unconditional Allow/Deny. -/
theorem go_iff (l : List (String × ConditionsAwareDecision)) :
    ContainsUnconditionalAllowOrDeny.go l = true ↔
      ∃ c ∈ l, c.2.ContainsUnconditionalAllowOrDeny = true := by
  induction l with
  | nil => simp [ContainsUnconditionalAllowOrDeny.go]
  | cons p rest ih =>
    obtain ⟨n, c⟩ := p
    simp [ContainsUnconditionalAllowOrDeny.go, ih]

theorem go_eq_false_iff (l : List (String × ConditionsAwareDecision)) :
    ContainsUnconditionalAllowOrDeny.go l = false ↔
      ∀ c ∈ l, c.2.ContainsUnconditionalAllowOrDeny = false := by
  rw [← Bool.not_eq_true, go_iff]; simp

@[simp] theorem go_nil : ContainsUnconditionalAllowOrDeny.go [] = false := rfl

@[simp] theorem go_cons (n : String) (c : ConditionsAwareDecision) l :
    ContainsUnconditionalAllowOrDeny.go ((n, c) :: l) =
      (c.ContainsUnconditionalAllowOrDeny || ContainsUnconditionalAllowOrDeny.go l) := rfl

theorem go_append (l l' : List (String × ConditionsAwareDecision)) :
    ContainsUnconditionalAllowOrDeny.go (l ++ l') =
      (ContainsUnconditionalAllowOrDeny.go l || ContainsUnconditionalAllowOrDeny.go l') := by
  induction l with
  | nil => simp
  | cons p rest ih => obtain ⟨n, c⟩ := p; simp [ih, Bool.or_assoc]

/-- `Has x (subPD l) ↔ ∃ c ∈ l, c.2.PossibleDecisions.Has x`. -/
theorem subPD_Has (l : List (String × ConditionsAwareDecision)) (x : Decision) :
    (PossibleDecisions.subPD l).Has x = true ↔
      ∃ c ∈ l, c.2.PossibleDecisions.Has x = true := by
  induction l with
  | nil => simp [PossibleDecisions.subPD]
  | cons p rest ih =>
    obtain ⟨n, c⟩ := p
    simp [PossibleDecisions.subPD, ih]

@[simp] theorem subPD_nil : PossibleDecisions.subPD [] = .empty := rfl

@[simp] theorem subPD_cons (n : String) (c : ConditionsAwareDecision) l :
    PossibleDecisions.subPD ((n, c) :: l) = c.PossibleDecisions.union (PossibleDecisions.subPD l) := rfl

theorem subPD_append (l l' : List (String × ConditionsAwareDecision)) :
    PossibleDecisions.subPD (l ++ l') =
      (PossibleDecisions.subPD l).union (PossibleDecisions.subPD l') := by
  apply ext_Has; intro y
  induction l with
  | nil => simp
  | cons p rest ih => obtain ⟨n, c⟩ := p; simp [ih, Bool.or_assoc]

/-- Unfolding of `PossibleDecisions` on a union, membership form. -/
theorem PD_union_Has (l : List (String × ConditionsAwareDecision)) (x : Decision) :
    (ConditionsAwareDecision.union l).PossibleDecisions.Has x =
      (if ContainsUnconditionalAllowOrDeny.go l then
        (!decide (x = .NoOpinion) && (decide (x = .NoOpinion) || (PossibleDecisions.subPD l).Has x))
      else (decide (x = .NoOpinion) || (PossibleDecisions.subPD l).Has x)) := by
  simp only [PossibleDecisions]
  split <;> simp

/-! ## P-1 -/

/-- **P-1 Zero value is Deny.** `CAD{} = deny("", nil)`, `PD = {D}`, `FD = D`. -/
theorem P_1_zero_is_deny :
    zero = .deny "" none ∧ zero.PossibleDecisions = .singleton .Deny
    ∧ zero.FailureDecision = .Deny ∧ zero.IsDeny = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## P-35 (the NoOpinion lemma) — holds for ALL trees -/

/-- **P-35 NoOpinion is possible iff no unconditional Allow/Deny is contained.**
`N ∈ PD(d) ⟺ ¬cua(d)`. Holds for EVERY tree (no well-formedness needed): it is a direct
consequence of the PD clauses, the union clause removing `N` exactly when `go l`. This
discharges the `TODO: (formally) verify this` at `conditionsunion.go:165`. -/
theorem P_35_noOpinion_possible_iff (d : ConditionsAwareDecision) :
    d.PossibleDecisions.Has .NoOpinion = !d.ContainsUnconditionalAllowOrDeny := by
  cases d with
  | deny => rfl
  | allow => rfl
  | noOpinion => rfl
  | conditionsMap m => simp [PossibleDecisions, ContainsUnconditionalAllowOrDeny]
  | union l =>
    rw [PD_union_Has]; simp only [ContainsUnconditionalAllowOrDeny]
    cases ContainsUnconditionalAllowOrDeny.go l <;> simp

/-! ## P-3 -/

mutual
/-- A decision containing an unconditional Allow/Deny can yield Allow or Deny (all trees). -/
theorem cua_has_allow_or_deny : (d : ConditionsAwareDecision) →
    d.ContainsUnconditionalAllowOrDeny = true →
      (d.PossibleDecisions.Has .Allow = true ∨ d.PossibleDecisions.Has .Deny = true)
  | .deny _ _, _ => Or.inr rfl
  | .allow _ _, _ => Or.inl rfl
  | .noOpinion _ _, h => by simp [ContainsUnconditionalAllowOrDeny] at h
  | .conditionsMap _, h => by simp [ContainsUnconditionalAllowOrDeny] at h
  | .union l, h => by
    simp only [ContainsUnconditionalAllowOrDeny] at h
    have := cua_has_allow_or_deny_go l h
    rw [PD_union_Has, PD_union_Has, h]
    simp_all
/-- List half of `cua_has_allow_or_deny`. -/
theorem cua_has_allow_or_deny_go : (l : List (String × ConditionsAwareDecision)) →
    ContainsUnconditionalAllowOrDeny.go l = true →
      ((PossibleDecisions.subPD l).Has .Allow = true ∨ (PossibleDecisions.subPD l).Has .Deny = true)
  | [], h => by simp at h
  | (_, c) :: rest, h => by
    simp only [go_cons, Bool.or_eq_true] at h
    simp only [subPD_cons, Has_union, Bool.or_eq_true]
    rcases h with h | h
    · rcases cua_has_allow_or_deny c h with h' | h' <;> simp [h']
    · rcases cua_has_allow_or_deny_go rest h with h' | h' <;> simp [h']
end

/-- **P-3 PD is a non-empty subset of {D,A,N}.** `∅ ≠ PD(d) ⊆ {D,A,N}`. Holds for EVERY
tree. `⊆ {D,A,N}` is free (`DecisionSet` has exactly three members); non-emptiness:
either `N ∈ PD` or (P-35) `cua d`, and then `A` or `D ∈ PD`. -/
theorem P_3_possibleDecisions_nonempty (d : ConditionsAwareDecision) :
    ∃ x, d.PossibleDecisions.Has x = true := by
  cases h : d.ContainsUnconditionalAllowOrDeny
  · exact ⟨.NoOpinion, by rw [P_35_noOpinion_possible_iff, h]; rfl⟩
  · rcases cua_has_allow_or_deny d h with h' | h'
    · exact ⟨_, h'⟩
    · exact ⟨_, h'⟩

theorem P_3_Len_pos (d : ConditionsAwareDecision) : 1 ≤ d.PossibleDecisions.Len :=
  (Len_pos_iff _).2 (P_3_possibleDecisions_nonempty d)

theorem P_3_Len_le_three (d : ConditionsAwareDecision) : d.PossibleDecisions.Len ≤ 3 :=
  Len_le_three _

/-! ## P-5 -/

/-- **P-5 FailureDecision is D or N, and D iff D is possible.** Holds for EVERY tree
(definitional, `conditions.go:224-229`). -/
theorem P_5_failureDecision_spec (d : ConditionsAwareDecision) :
    (d.FailureDecision = .Deny ∨ d.FailureDecision = .NoOpinion)
    ∧ (d.FailureDecision = .Deny ↔ d.PossibleDecisions.Has .Deny = true) := by
  unfold FailureDecision; split <;> simp_all

/-! ## P-9 -/

/-- **P-9 Splitters, unconditional input.** `uncond d ⇒ OrError(d) = OrFailClosed(d) = (dec d, r, e)`.
All trees. -/
theorem P_9_splitters_unconditional (d : ConditionsAwareDecision) (h : d.IsUnconditional = true) :
    ∃ x, d.dec? = some x ∧ d.UnconditionalPartsOrError = (x, d.Reason, d.Error)
      ∧ d.UnconditionalPartsOrFailClosed = (x, d.Reason, d.Error) := by
  cases d <;> simp_all [IsUnconditional, IsAllow, IsDeny, IsNoOpinion, dec?,
    UnconditionalPartsOrError, UnconditionalPartsOrFailClosed, Reason, Error]

/-- **P-9 Splitters, conditional input.** `¬uncond d ⇒ OrError(d) = (FD d, _, err≠nil) ∧
OrFailClosed(d) = (FD d, r≠"", nil)`, and neither ever yields Allow. All trees. -/
theorem P_9_splitters_conditional (d : ConditionsAwareDecision) (h : d.IsUnconditional = false) :
    d.UnconditionalPartsOrError.1 = d.FailureDecision
    ∧ d.UnconditionalPartsOrError.2.2.isSome = true
    ∧ d.UnconditionalPartsOrFailClosed.1 = d.FailureDecision
    ∧ d.UnconditionalPartsOrFailClosed.2.2 = none
    ∧ d.UnconditionalPartsOrFailClosed.2.1 ≠ ""
    ∧ d.UnconditionalPartsOrError.1 ≠ .Allow
    ∧ d.UnconditionalPartsOrFailClosed.1 ≠ .Allow := by
  have hfd : d.FailureDecision ≠ .Allow := by
    rcases (P_5_failureDecision_spec d).1 with h' | h' <;> rw [h'] <;> decide
  cases d with
  | deny => simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at h
  | allow => simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at h
  | noOpinion => simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at h
  | conditionsMap m =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, hfd, hfd⟩
    simp only [UnconditionalPartsOrFailClosed]
    rcases (P_5_failureDecision_spec (.conditionsMap m)).1 with h' | h' <;> rw [h'] <;> decide
  | union l =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, hfd, hfd⟩
    simp only [UnconditionalPartsOrFailClosed]
    rcases (P_5_failureDecision_spec (.union l)).1 with h' | h' <;> rw [h'] <;> decide

end ConditionsAwareDecision

/-! ## `validateConditions` and the map smart constructor (§B) -/

/-- Success of `validateConditions seen l` (`conditionsmap.go:187-220`): every condition is
valid, the IDs of `l` are pairwise distinct and disjoint from `seen`, and the returned
`seenIDs` is `seen` extended with the IDs of `l` (most recent first). -/
theorem validateConditions_ok : ∀ (seen : List String) (l : List Condition) (s : List String),
    validateConditions seen l = .ok s →
      (∀ x ∈ l, x.valid = true) ∧ (l.map Condition.ID).Nodup
      ∧ (∀ x ∈ l, x.ID ∉ seen) ∧ s = (l.map Condition.ID).reverse ++ seen
  | seen, [], s, h => by
    simp [validateConditions] at h; subst h; simp
  | seen, c :: rest, s, h => by
    simp only [validateConditions] at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    rename_i h1 h2 h3 h4 h5
    obtain ⟨iv, ind, ins, ies⟩ := validateConditions_ok _ rest s h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [Condition.valid]
        simp_all
        exact (Classical.em _).elim Or.inl (fun hc => Or.inr (h4 hc))
      · exact iv x hx
    · simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ind⟩
      rintro ⟨y, hy, hyc⟩
      exact ins y hy (by simp [hyc])
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using h1
      · have := ins x hx; simp at this; exact this.2
    · simp [ies]

/-- Branch structure of the map constructor: either the map itself, or an unconditional
decision whose variant is `deny` iff `denyConditions ≠ []` (`conditionsmap.go:140-162`). -/
theorem mkMap_cases (D N A : List Condition) :
    ConditionsAwareDecisionConditionsMap D N A = .conditionsMap ⟨D, N, A⟩
    ∨ ∃ r e, ConditionsAwareDecisionConditionsMap D N A =
        (if D = [] then .noOpinion r e else .deny r e) := by
  have fc : ∀ err : Err,
      (if D.length > 0 then ConditionsAwareDecision.deny "failed closed" (some err)
        else .noOpinion "failed closed" (some err))
      = if D = [] then .noOpinion "failed closed" (some err) else .deny "failed closed" (some err) := by
    intro err; cases D <;> simp
  unfold ConditionsAwareDecisionConditionsMap
  simp only
  split
  · rename_i h0
    have : D = [] := by cases D <;> simp_all
    exact Or.inr ⟨_, _, by rw [ite_eq_left_of_eq_true _ _ (eq_true this)]⟩
  split
  · exact Or.inr ⟨_, _, fc _⟩
  split
  · rename_i h0
    have : D = [] := by cases D <;> simp_all
    exact Or.inr ⟨_, _, by rw [ite_eq_left_of_eq_true _ _ (eq_true this)]⟩
  split
  · exact Or.inr ⟨_, _, fc _⟩
  split
  · exact Or.inr ⟨_, _, fc _⟩
  split
  · exact Or.inr ⟨_, _, fc _⟩
  · exact Or.inl rfl

/-- Success characterisation of the map constructor. -/
theorem mkMap_eq_conditionsMap {D N A : List Condition} {m : ConditionsMap}
    (h : ConditionsAwareDecisionConditionsMap D N A = .conditionsMap m) :
    m = ⟨D, N, A⟩ ∧ D.length + N.length + A.length ≠ 0
    ∧ D.length + N.length + A.length ≤ MaxConditionsPerMap ∧ (D ≠ [] ∨ A ≠ [])
    ∧ ∃ s1 s2 s3, validateConditions [] D = .ok s1 ∧ validateConditions s1 N = .ok s2
        ∧ validateConditions s2 A = .ok s3 := by
  unfold ConditionsAwareDecisionConditionsMap at h
  simp only at h
  split at h; · simp at h
  split at h; · split at h <;> simp at h
  split at h; · simp at h
  rename_i h0 h1 h2
  split at h; · split at h <;> simp at h
  rename_i s1 e1
  split at h; · split at h <;> simp at h
  rename_i s2 e2
  split at h; · split at h <;> simp at h
  rename_i s3 e3
  simp at h
  refine ⟨h.symm, by simpa using h0, by omega, ?_, s1, s2, s3, e1, e2, e3⟩
  cases D <;> cases A <;> simp_all

/-- **P-13 A constructed map is well-formed.** `mkMap(D,N,A) = map m ⇒ WFMap(m)` and
`m = (D,N,A)`. All inputs. -/
theorem P_13_mkMap_WF {D N A : List Condition} {m : ConditionsMap}
    (h : ConditionsAwareDecisionConditionsMap D N A = .conditionsMap m) :
    m = ⟨D, N, A⟩ ∧ m.WF := by
  obtain ⟨rfl, h0, h1, h2, s1, s2, s3, e1, e2, e3⟩ := mkMap_eq_conditionsMap h
  obtain ⟨vD, nD, -, rfl⟩ := validateConditions_ok _ _ _ e1
  obtain ⟨vN, nN, dN, rfl⟩ := validateConditions_ok _ _ _ e2
  obtain ⟨vA, nA, dA, -⟩ := validateConditions_ok _ _ _ e3
  refine ⟨rfl, by simp [ConditionsMap.Length]; omega, by simpa [ConditionsMap.Length] using h1, h2, ?_, ?_⟩
  · simp only [ConditionsMap.all, List.map_append, List.nodup_append]
    refine ⟨⟨nD, nN, ?_⟩, nA, ?_⟩
    · intro a ha b hb hab; subst hab
      simp only [List.mem_map] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha; obtain ⟨y, hy, hxy⟩ := hb
      exact dN y hy (by simp [hxy]; exact ⟨x, hx, rfl⟩)
    · intro a ha b hb hab; subst hab
      simp only [List.mem_append, List.mem_map] at ha hb
      obtain ⟨y, hy, hyb⟩ := hb
      apply dA y hy
      rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · simp [hyb]; exact Or.inr ⟨x, hx, rfl⟩
      · simp [hyb]; exact Or.inl ⟨x, hx, rfl⟩
  · intro x hx
    simp only [ConditionsMap.all, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact vD x hx
    · exact vN x hx
    · exact vA x hx

/-- **P-14 The constructor never yields Allow.** All inputs. -/
theorem P_14_mkMap_ne_allow (D N A : List Condition) (r : String) (e : Option Err) :
    ConditionsAwareDecisionConditionsMap D N A ≠ .allow r e := by
  rcases mkMap_cases D N A with h | ⟨r', e', h⟩ <;> rw [h]
  · simp
  · split <;> simp

/-- **P-14 fallbacks are fail-closed by effect.** A non-map result is `noOpinion` or
`deny`, and it is `deny` iff `denyConditions ≠ []`. All inputs. -/
theorem P_14_mkMap_fallback (D N A : List Condition)
    (h : (ConditionsAwareDecisionConditionsMap D N A).IsConditionsMap = false) :
    ((ConditionsAwareDecisionConditionsMap D N A).IsDeny = true ↔ D ≠ [])
    ∧ ((ConditionsAwareDecisionConditionsMap D N A).IsNoOpinion = true ↔ D = []) := by
  rcases mkMap_cases D N A with h' | ⟨r', e', h'⟩ <;> rw [h'] at h ⊢
  · simp [ConditionsAwareDecision.IsConditionsMap] at h
  · by_cases hD : D = [] <;>
      simp [hD, ConditionsAwareDecision.IsDeny, ConditionsAwareDecision.IsNoOpinion]

/-- **P-14** no conditions ⇒ `noOpinion` with a non-nil error (`conditionsmap.go:150-153`). -/
theorem P_14_mkMap_empty :
    ∃ e, ConditionsAwareDecisionConditionsMap [] [] [] = .noOpinion "no conditions" (some e) :=
  ⟨_, rfl⟩

/-- **P-14** NoOpinion-only inputs fold to `noOpinion(…, nil)` WITHOUT validating the
conditions (`conditionsmap.go:160-162` precedes `:164`): invalid or duplicate conditions
are silently accepted. -/
theorem P_14_mkMap_noOpinion_only_skips_validation (N : List Condition)
    (h1 : N ≠ []) (h2 : N.length ≤ MaxConditionsPerMap) :
    ConditionsAwareDecisionConditionsMap [] N [] =
      .noOpinion "only NoOpinion conditions always evaluate to NoOpinion" none := by
  unfold ConditionsAwareDecisionConditionsMap
  have : N.length ≠ 0 := by cases N <;> simp_all
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using this)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp

namespace ConditionsAwareDecision

/-! ## P-15 -/

/-- **P-15 PD of a map.** `PD(map(D,N,A)) = {N} ∪ {A | A≠[]} ∪ {D | D≠[]}`. All maps. -/
theorem P_15_map_PD (m : authorizer.ConditionsMap) :
    (ConditionsAwareDecision.conditionsMap m).PossibleDecisions =
      { deny := decide (m.denyConditions ≠ []), allow := decide (m.allowConditions ≠ []),
        noOpinion := true } := by
  apply ext_Has; intro y
  cases y <;> simp only [PossibleDecisions, ConditionsMap.PD_Has_Deny, ConditionsMap.PD_Has_Allow,
    ConditionsMap.PD_Has_NoOpinion] <;> rfl

/-- **P-15 maps are never foldable.** `WFMap m ⇒ |PD| ≥ 2` (needs the `D ≠ [] ∨ A ≠ []`
part of `WFMap`; the empty map `{}` has `PD = {N}`). -/
theorem P_15_map_Len (m : authorizer.ConditionsMap) (h : m.WF) :
    2 ≤ (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Len := by
  rcases h.2.2.1 with h' | h'
  · exact two_le_Len (x := .NoOpinion) (y := .Deny) (by decide)
      (by simp [PossibleDecisions]) (by simp [PossibleDecisions, h'])
  · exact two_le_Len (x := .NoOpinion) (y := .Allow) (by decide)
      (by simp [PossibleDecisions]) (by simp [PossibleDecisions, h'])

/-- **P-15** for constructor outputs. -/
theorem P_15_mkMap_Len {D N A : List Condition} {m : authorizer.ConditionsMap}
    (h : ConditionsAwareDecisionConditionsMap D N A = .conditionsMap m) :
    2 ≤ (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Len :=
  P_15_map_Len m (P_13_mkMap_WF h).2

/-- **P-15 negative for arbitrary maps**: the (non-constructible) empty map has `|PD| = 1`. -/
theorem P_15_map_Len_not_all_maps :
    ¬ ∀ m : authorizer.ConditionsMap, 2 ≤ (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Len := by
  intro h; have := h {}; simp [P_15_map_PD, Len] at this

/-! ## Well-formedness -/

/-- `WF d` (`properties.md` §1.3, "producible by the public constructors"): unconditional
leaves; maps satisfying `ConditionsMap.WF` (`mkMap`, P-13); unions satisfying `WFUnion`
(what `ToDecision` emits, see `conditionsunion_properties.lean`). -/
inductive WF : ConditionsAwareDecision → Prop
  | deny (r : String) (e : Option Err) : WF (.deny r e)
  | allow (r : String) (e : Option Err) : WF (.allow r e)
  | noOpinion (r : String) (e : Option Err) : WF (.noOpinion r e)
  | conditionsMap (m : authorizer.ConditionsMap) : m.WF → WF (.conditionsMap m)
  | union (l : List (String × ConditionsAwareDecision)) :
      l ≠ [] →
      (∀ p ∈ l, p.1.length ≠ 0 ∧ IsDNS1123Subdomain p.1 = true) →
      (l.map Prod.fst).Nodup →
      (∀ p ∈ l, WF p.2) →
      (∀ p ∈ l.dropLast, p.2.ContainsUnconditionalAllowOrDeny = false) →
      2 ≤ (ConditionsAwareDecision.union l).PossibleDecisions.Len →
      WF (.union l)

theorem WF_of_FromParts (x : Decision) (r : String) (e : Option Err) :
    WF (ConditionsAwareDecisionFromParts x r e) := by
  cases x
  · exact .deny r e
  · exact .allow r e
  · exact .noOpinion r e

/-- The map constructor only produces WF decisions. -/
theorem WF_mkMap (D N A : List Condition) : WF (ConditionsAwareDecisionConditionsMap D N A) := by
  cases h : ConditionsAwareDecisionConditionsMap D N A with
  | deny => exact .deny _ _
  | allow => exact .allow _ _
  | noOpinion => exact .noOpinion _ _
  | conditionsMap m => exact .conditionsMap m (P_13_mkMap_WF h).2
  | union l => rcases mkMap_cases D N A with h' | ⟨_, _, h'⟩ <;> rw [h'] at h
               · simp at h
               · split at h <;> simp at h

/-- WF conditional decisions have `|PD| ≥ 2`. -/
theorem WF_conditional_Len {d : ConditionsAwareDecision} (hw : WF d) (hc : d.IsUnconditional = false) :
    2 ≤ d.PossibleDecisions.Len := by
  cases hw with
  | conditionsMap m hm => exact P_15_map_Len m hm
  | union l _ _ _ _ _ hl => exact hl
  | _ => simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at hc

/-! ## P-4 -/

/-- **P-4 Unconditional ⟺ singleton PD**, for WF decisions. -/
theorem P_4_unconditional_iff_singleton {d : ConditionsAwareDecision} (hw : WF d) :
    d.IsUnconditional = true ↔ d.PossibleDecisions.Len = 1 := by
  cases hu : d.IsUnconditional
  · have := WF_conditional_Len hw hu; simp; omega
  · cases d <;> simp_all [IsUnconditional, IsAllow, IsDeny, IsNoOpinion, PossibleDecisions]

/-- **P-4 negative for arbitrary trees**: the empty union (never emitted, `ToDecision` folds
it to `noOpinion`) is conditional with `|PD| = 1`. -/
theorem P_4_not_all_trees :
    ¬ ∀ d : ConditionsAwareDecision, d.IsUnconditional = true ↔ d.PossibleDecisions.Len = 1 := by
  -- status: does NOT hold for arbitrary trees (holds for WF, see `P_4_unconditional_iff_singleton`)
  intro h
  have := (h (.union [])).2 rfl
  simp [IsUnconditional, IsAllow, IsDeny, IsNoOpinion] at this

/-! ## P-6 -/

/-- **P-6 FailureDecision is never Allow.** All trees. -/
theorem P_6_failureDecision_ne_allow (d : ConditionsAwareDecision) : d.FailureDecision ≠ .Allow := by
  rcases (P_5_failureDecision_spec d).1 with h | h <;> rw [h] <;> decide

/-- **P-6 FD ∈ PD** for a non-allow decision, under the hypothesis
`2 ≤ |PD| ∨ IsConditionsMap ∨ IsUnconditional` (which every WF decision satisfies). -/
theorem P_6_failureDecision_mem_of (d : ConditionsAwareDecision) (hna : d.IsAllow = false)
    (h : 2 ≤ d.PossibleDecisions.Len ∨ d.IsConditionsMap = true ∨ d.IsUnconditional = true) :
    d.PossibleDecisions.Has d.FailureDecision = true := by
  unfold FailureDecision
  split
  · assumption
  · rename_i hD
    simp only [Bool.not_eq_true] at hD
    rcases h with h | h | h
    · exact has_N_of_two_le_Len_of_not_D h hD
    · cases d <;> simp_all [IsConditionsMap, PossibleDecisions]
    · cases d <;> simp_all [IsUnconditional, IsAllow, IsDeny, IsNoOpinion, PossibleDecisions]

/-- **P-6 FD ∈ PD** for every WF decision other than `allow`. -/
theorem P_6_failureDecision_mem_WF {d : ConditionsAwareDecision} (hw : WF d) (hna : d.IsAllow = false) :
    d.PossibleDecisions.Has d.FailureDecision = true := by
  apply P_6_failureDecision_mem_of d hna
  cases hu : d.IsUnconditional
  · exact Or.inl (WF_conditional_Len hw hu)
  · exact Or.inr (Or.inr rfl)

/-- **P-6** `FD(allow) = N ∉ PD(allow)`. -/
theorem P_6_failureDecision_allow (r : String) (e : Option Err) :
    (ConditionsAwareDecision.allow r e).FailureDecision = .NoOpinion
    ∧ (ConditionsAwareDecision.allow r e).PossibleDecisions.Has .NoOpinion = false := ⟨rfl, rfl⟩

/-- **P-6 negative for arbitrary trees**: the (non-WF, `|PD| = 1`) union `[("a", allow)]`
is not `allow`, yet `FD = N ∉ PD = {A}`. -/
theorem P_6_not_all_trees :
    ¬ ∀ d : ConditionsAwareDecision, d.IsAllow = false →
        d.PossibleDecisions.Has d.FailureDecision = true := by
  -- status: does NOT hold for arbitrary trees (holds for WF, see `P_6_failureDecision_mem_WF`)
  intro h
  have := h (.union [("a", .allow "" none)]) rfl
  simp [FailureDecision, ContainsUnconditionalAllowOrDeny, PossibleDecisions.subPD,
    PossibleDecisions] at this

end ConditionsAwareDecision

end authorizer
