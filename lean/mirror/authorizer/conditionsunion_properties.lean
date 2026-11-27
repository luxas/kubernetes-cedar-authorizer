import authorizer.conditionsunion
import authorizer.conditions_properties

/-!
# `authorizer/conditionsunion_properties.lean`  ↔  `pkg/authorization/authorizer/conditionsunion_test.go`

Union-builder properties of `review/properties.md` Part 2 §E: P-33, P-34, P-36, P-4 (for
builder outputs), the builder invariants (the cached `containsUnconditionalAllowOrDeny`
and `subDecisionsPossibleDecisions` agree with the child list), and well-formedness of
`ToDecision` outputs.

"Reachable" builders are those obtained from `{}` by a sequence of `Add` calls
(`ConditionsAwareDecisionUnion.Reachable P`, where `P` constrains the added children);
this is the only way to obtain a builder outside package `authorizer` (fields
unexported, `conditionsunion.go:37-56`).

Summary of what needs reachability:
* ALL builders (any field values): P-33, P-34 (the `ToDecision` equation and its
  unconditionality), P-5 / P-35 for the builder.
* reachable builders: the cache invariants, `PD_B = PD(union inner)`, P-36, P-4 for
  `ToDecision`; reachable with WF children: `WF (ToDecision u)`.
-/

namespace authorizer

open DecisionSet ConditionsAwareDecision

namespace ConditionsAwareDecisionUnion

/-! ## Reachable builders -/

/-- Builders obtained from the zero value `{}` by `Add` calls whose children satisfy `P`. -/
inductive Reachable (P : ConditionsAwareDecision → Prop) : ConditionsAwareDecisionUnion → Prop
  | empty : Reachable P {}
  | add {u : ConditionsAwareDecisionUnion} (n : String) (d : ConditionsAwareDecision) :
      Reachable P u → P d → Reachable P (u.Add n d)

/-- The builder obtained by `Add`ing a history of named children in order. -/
def build (h : List (String × ConditionsAwareDecision)) : ConditionsAwareDecisionUnion :=
  h.foldl (fun u p => u.Add p.1 p.2) {}

theorem Reachable_foldl {P : ConditionsAwareDecision → Prop} :
    ∀ (h : List (String × ConditionsAwareDecision)) (u : ConditionsAwareDecisionUnion),
      Reachable P u → (∀ p ∈ h, P p.2) → Reachable P (h.foldl (fun u p => u.Add p.1 p.2) u)
  | [], _, hu, _ => hu
  | p :: rest, u, hu, hP =>
    Reachable_foldl rest _ (.add p.1 p.2 hu (hP p (by simp)))
      (fun q hq => hP q (by simp [hq]))

theorem Reachable_build {P : ConditionsAwareDecision → Prop} (h : List (String × ConditionsAwareDecision))
    (hP : ∀ p ∈ h, P p.2) : Reachable P (build h) :=
  Reachable_foldl h {} .empty hP

theorem Reachable.mono {P Q : ConditionsAwareDecision → Prop} (hPQ : ∀ d, P d → Q d)
    {u : ConditionsAwareDecisionUnion} (h : Reachable P u) : Reachable Q u := by
  induction h with
  | empty => exact .empty
  | add n d _ hd ih => exact .add n d ih (hPQ d hd)

/-! ## P-33 -/

/-- **P-33 `add` is a no-op after a child containing an unconditional Allow/Deny.**
`B.flag ⇒ add(B, n, d) = B` — no change to inner, errs, PD, and no name validation.
All builders. -/
theorem P_33_add_noop (u : ConditionsAwareDecisionUnion) (n : String) (d : ConditionsAwareDecision)
    (h : u.ContainsUnconditionalAllowOrDeny = true) : u.Add n d = u := by
  simp [Add, h]

/-- `Add` when the flag is not yet set. -/
theorem Add_of_not_cua (u : ConditionsAwareDecisionUnion) (n : String) (d : ConditionsAwareDecision)
    (h : u.containsUnconditionalAllowOrDeny = false) :
    (u.Add n d).inner = u.inner ++ [(n, d)]
    ∧ (u.Add n d).containsUnconditionalAllowOrDeny = d.ContainsUnconditionalAllowOrDeny
    ∧ (u.Add n d).subDecisionsPossibleDecisions = u.subDecisionsPossibleDecisions.union d.PossibleDecisions
    ∧ ((u.Add n d).errs = [] ↔
        u.errs = [] ∧ n.length ≠ 0 ∧ u.hasConditionalAuthorizerName n = false
          ∧ IsDNS1123Subdomain n = true) := by
  have hc : u.ContainsUnconditionalAllowOrDeny = false := h
  refine ⟨by simp [Add, hc], by simp [Add, hc, h], by simp [Add, hc], ?_⟩
  by_cases h1 : n.length = 0 <;> by_cases h2 : u.hasConditionalAuthorizerName n = true <;>
    by_cases h3 : IsDNS1123Subdomain n = true <;> simp_all [Add]

/-! ## Builder invariants -/

/-- Invariants of reachable builders. -/
structure Inv (P : ConditionsAwareDecision → Prop) (u : ConditionsAwareDecisionUnion) : Prop where
  /-- the cached flag is `go inner` (`conditionsunion.go:75-77`). -/
  cua : u.containsUnconditionalAllowOrDeny = ContainsUnconditionalAllowOrDeny.go u.inner
  /-- the cached set is `subPD inner` (`conditionsunion.go:80-83`). -/
  sub : u.subDecisionsPossibleDecisions = PossibleDecisions.subPD u.inner
  /-- only the last child may contain an unconditional Allow/Deny (`:59-61`). -/
  dropLast : ∀ p ∈ u.inner.dropLast, p.2.ContainsUnconditionalAllowOrDeny = false
  /-- every child satisfies `P`. -/
  children : ∀ p ∈ u.inner, P p.2
  /-- without errors, names are non-empty, DNS-1123 and pairwise distinct (`:63-72`). -/
  names : u.errs = [] →
    (∀ p ∈ u.inner, p.1.length ≠ 0 ∧ IsDNS1123Subdomain p.1 = true) ∧ (u.inner.map Prod.fst).Nodup

theorem Reachable.inv {P : ConditionsAwareDecision → Prop} {u : ConditionsAwareDecisionUnion}
    (h : Reachable P u) : Inv P u := by
  induction h with
  | empty =>
    exact ⟨rfl, rfl, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩
  | @add u n d _ hd ih =>
    cases hf : u.containsUnconditionalAllowOrDeny
    · obtain ⟨e1, e2, e3, e4⟩ := Add_of_not_cua u n d hf
      have hgo : ContainsUnconditionalAllowOrDeny.go u.inner = false := ih.cua ▸ hf
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e1, e2, go_append, hgo]; simp
      · rw [e1, e3, subPD_append, ih.sub]
        apply ext_Has; intro y; simp
      · rw [e1, List.dropLast_concat]; exact (go_eq_false_iff _).1 hgo
      · rw [e1]; intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact ih.children p hp
        · exact hd
      · intro he
        obtain ⟨he, hn1, hn2, hn3⟩ := e4.1 he
        obtain ⟨ihn, ihd⟩ := ih.names he
        rw [e1]
        refine ⟨?_, ?_⟩
        · intro p hp
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact ihn p hp
          · exact ⟨hn1, hn3⟩
        · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
            List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
            List.mem_singleton, true_and]
          refine ⟨ihd, ?_⟩
          intro a ha b hb; subst hb
          simp only [hasConditionalAuthorizerName, List.any_eq_false, beq_iff_eq] at hn2
          simp only [List.mem_map] at ha
          obtain ⟨p, hp, rfl⟩ := ha
          exact hn2 p hp
    · have hc : u.ContainsUnconditionalAllowOrDeny = true := hf
      rw [P_33_add_noop u n d hc]
      exact ⟨ih.cua, ih.sub, ih.dropLast, ih.children, ih.names⟩

/-- **Builder cache invariant**: `containsUnconditionalAllowOrDeny = go inner`. -/
theorem Reachable.cua_eq {P} {u : ConditionsAwareDecisionUnion} (h : Reachable P u) :
    u.containsUnconditionalAllowOrDeny = ContainsUnconditionalAllowOrDeny.go u.inner := h.inv.cua

/-- **Builder cache invariant**: `subDecisionsPossibleDecisions = subPD inner`. -/
theorem Reachable.sub_eq {P} {u : ConditionsAwareDecisionUnion} (h : Reachable P u) :
    u.subDecisionsPossibleDecisions = PossibleDecisions.subPD u.inner := h.inv.sub

/-- `PD_B = PD(union inner)` for reachable builders. -/
theorem Reachable.PD_eq {P} {u : ConditionsAwareDecisionUnion} (h : Reachable P u) :
    u.PossibleDecisions = (ConditionsAwareDecision.union u.inner).PossibleDecisions := by
  have i := h.inv
  unfold ConditionsAwareDecisionUnion.PossibleDecisions ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny
  rw [i.cua, i.sub]
  simp only [ConditionsAwareDecision.PossibleDecisions]

/-- `FD_B = FD(union inner)` for reachable builders. -/
theorem Reachable.FD_eq {P} {u : ConditionsAwareDecisionUnion} (h : Reachable P u) :
    u.FailureDecision = (ConditionsAwareDecision.union u.inner).FailureDecision := by
  unfold ConditionsAwareDecisionUnion.FailureDecision ConditionsAwareDecision.FailureDecision
  rw [h.PD_eq]

/-- `cua_B = cua(union inner)` for reachable builders. -/
theorem Reachable.ContainsUnconditionalAllowOrDeny_eq {P} {u : ConditionsAwareDecisionUnion}
    (h : Reachable P u) :
    u.ContainsUnconditionalAllowOrDeny = (ConditionsAwareDecision.union u.inner).ContainsUnconditionalAllowOrDeny :=
  h.inv.cua

/-! ## P-5 / P-35 for the builder (all builders) -/

/-- **P-5 (builder)** `FD_B ∈ {D,N}` and `FD_B = D ⟺ D ∈ PD_B` (`conditionsunion.go:98-103`). -/
theorem P_5_builder_failureDecision_spec (u : ConditionsAwareDecisionUnion) :
    (u.FailureDecision = .Deny ∨ u.FailureDecision = .NoOpinion)
    ∧ (u.FailureDecision = .Deny ↔ u.PossibleDecisions.Has .Deny = true) := by
  unfold FailureDecision; split <;> simp_all

/-- **P-35 (builder)** `N ∈ PD_B ⟺ ¬flag`, for every builder state. -/
theorem P_35_builder_noOpinion_possible_iff (u : ConditionsAwareDecisionUnion) :
    u.PossibleDecisions.Has .NoOpinion = !u.ContainsUnconditionalAllowOrDeny := by
  unfold PossibleDecisions; split <;> simp_all

/-! ## P-34 -/

theorem FromParts_ne_union (x : Decision) (r : String) (e : Option Err)
    (l : List (String × ConditionsAwareDecision)) : ConditionsAwareDecisionFromParts x r e ≠ .union l := by
  cases x <;> simp [ConditionsAwareDecisionFromParts]

theorem FromParts_IsUnconditional (x : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts x r e).IsUnconditional = true := by
  cases x <;> rfl

/-- **P-34 Name validation fails the whole union closed.**
`B.errs ≠ [] ⇒ toDecision(B) = FromParts(FD_B, "failed closed", agg errs)`. All builders. -/
theorem P_34_errs_fail_closed (u : ConditionsAwareDecisionUnion) (h : u.errs ≠ []) :
    u.ToDecision = ConditionsAwareDecisionFromParts u.FailureDecision "failed closed" (aggregate u.errs) := by
  have : (u.errs.length != 0) = true := by cases he : u.errs <;> simp_all
  simp [ToDecision, this]

/-- **P-34** with errors, `ToDecision` is unconditional, and never Allow. All builders. -/
theorem P_34_errs_unconditional (u : ConditionsAwareDecisionUnion) (h : u.errs ≠ []) :
    u.ToDecision.IsUnconditional = true ∧ u.ToDecision.IsAllow = false := by
  rw [P_34_errs_fail_closed u h]
  refine ⟨FromParts_IsUnconditional _ _ _, ?_⟩
  rcases (P_5_builder_failureDecision_spec u).1 with h' | h' <;> rw [h'] <;> rfl

/-- **P-34 note** (`properties.md` P-34/P-42): a bad name on an `allow` child turns the
whole decision into `noOpinion` + error, because `PD_B = {A}` gives `FD_B = N`. -/
theorem P_34_allow_with_empty_name_becomes_noOpinion (r : String) (e : Option Err) :
    (({} : ConditionsAwareDecisionUnion).Add "" (.allow r e)).ToDecision.IsNoOpinion = true := by
  have hne : (({} : ConditionsAwareDecisionUnion).Add "" (.allow r e)).errs ≠ [] := by
    intro h
    have := ((Add_of_not_cua {} "" (.allow r e) rfl).2.2.2).1 h
    simp at this
  rw [P_34_errs_fail_closed _ hne]
  have hfd : (({} : ConditionsAwareDecisionUnion).Add "" (.allow r e)).FailureDecision = .NoOpinion := by
    rfl
  rw [hfd]; rfl

/-! ## P-36 -/

/-- `ToDecision` is either an unconditional `FromParts` or `.union inner`. All builders. -/
theorem ToDecision_cases (u : ConditionsAwareDecisionUnion) :
    (∃ x r e, u.ToDecision = ConditionsAwareDecisionFromParts x r e)
    ∨ (u.errs = [] ∧ u.PossibleDecisions.theOnly = none ∧ u.ToDecision = .union u.inner) := by
  unfold ToDecision
  split
  · exact Or.inl ⟨_, _, _, rfl⟩
  · rename_i h
    split
    · exact Or.inl ⟨_, _, _, rfl⟩
    · rename_i hn
      refine Or.inr ⟨?_, hn, rfl⟩
      cases he : u.errs <;> simp_all

/-- **P-36 Shape of an emitted union.** For a reachable builder, `ToDecision = union l` ⇒
`l = inner`, no errors, `l ≠ []`, `|PD| ≥ 2`, no child before the last contains an
unconditional Allow/Deny, and if the union contains one then the last child does. -/
theorem P_36_union_shape {P} {u : ConditionsAwareDecisionUnion} (hr : Reachable P u)
    {l : List (String × ConditionsAwareDecision)} (h : u.ToDecision = .union l) :
    l = u.inner ∧ u.errs = [] ∧ l ≠ []
    ∧ 2 ≤ (ConditionsAwareDecision.union l).PossibleDecisions.Len
    ∧ (∀ p ∈ l.dropLast, p.2.ContainsUnconditionalAllowOrDeny = false)
    ∧ ((ConditionsAwareDecision.union l).ContainsUnconditionalAllowOrDeny = true →
        ∃ p, l.getLast? = some p ∧ p.2.ContainsUnconditionalAllowOrDeny = true) := by
  rcases ToDecision_cases u with ⟨x, r, e, h'⟩ | ⟨he, hn, h'⟩
  · rw [h'] at h; exact absurd h (FromParts_ne_union _ _ _ _)
  rw [h'] at h; injection h with h; subst h
  have hlen : (ConditionsAwareDecision.union u.inner).PossibleDecisions.Len ≠ 1 := by
    rw [← hr.PD_eq]; exact (theOnly_eq_none_iff _).1 hn
  have h2 : 2 ≤ (ConditionsAwareDecision.union u.inner).PossibleDecisions.Len := by
    have := P_3_Len_pos (.union u.inner); omega
  have hne : u.inner ≠ [] := by
    intro h0; rw [h0] at hlen; exact hlen rfl
  refine ⟨rfl, he, hne, h2, hr.inv.dropLast, ?_⟩
  intro hc
  simp only [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny] at hc
  obtain ⟨c, hc, hcc⟩ := (go_iff _).1 hc
  refine ⟨u.inner.getLast hne, List.getLast?_eq_some_getLast hne, ?_⟩
  have hsplit := List.dropLast_concat_getLast hne
  rw [← hsplit] at hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · rw [hr.inv.dropLast c hc] at hcc; exact absurd hcc (by decide)
  · exact hcc

/-! ## P-4 for builder outputs -/

/-- **P-4 (ToDecision)** for a reachable builder, `IsUnconditional ⟺ |PD| = 1`. -/
theorem P_4_ToDecision_unconditional_iff {P} {u : ConditionsAwareDecisionUnion} (hr : Reachable P u) :
    u.ToDecision.IsUnconditional = true ↔ u.ToDecision.PossibleDecisions.Len = 1 := by
  rcases ToDecision_cases u with ⟨x, r, e, h'⟩ | ⟨_, _, h'⟩
  · rw [h']; cases x <;> simp [ConditionsAwareDecisionFromParts, IsUnconditional, IsDeny,
      IsAllow, IsNoOpinion, ConditionsAwareDecision.PossibleDecisions]
  · have := (P_36_union_shape hr h').2.2.2.1
    rw [h']; simp [IsUnconditional, IsDeny, IsAllow, IsNoOpinion]; omega

/-- **P-4 (map constructor)** `IsUnconditional ⟺ |PD| = 1` for every `mkMap` output. -/
theorem P_4_mkMap_unconditional_iff (D N A : List Condition) :
    (ConditionsAwareDecisionConditionsMap D N A).IsUnconditional = true
      ↔ (ConditionsAwareDecisionConditionsMap D N A).PossibleDecisions.Len = 1 :=
  P_4_unconditional_iff_singleton (WF_mkMap D N A)

/-! ## Well-formedness of `ToDecision` -/

/-- `ToDecision` of a reachable builder whose children are all WF is WF. No extra
hypothesis is needed. -/
theorem WF_ToDecision {u : ConditionsAwareDecisionUnion} (hr : Reachable ConditionsAwareDecision.WF u) :
    ConditionsAwareDecision.WF u.ToDecision := by
  rcases ToDecision_cases u with ⟨x, r, e, h'⟩ | ⟨he, _, h'⟩
  · rw [h']; exact WF_of_FromParts x r e
  · obtain ⟨-, -, hne, h2, hdl, -⟩ := P_36_union_shape hr h'
    obtain ⟨hn, hnd⟩ := hr.inv.names he
    rw [h']
    exact .union _ hne hn hnd hr.inv.children hdl h2

/-- `ToDecision` of a reachable builder whose children are arbitrary (possibly non-WF) is
WF except for the children: the emitted union satisfies every `WFUnion` clause but
`∀ i. WF cᵢ`. -/
theorem ToDecision_union_WF_except_children {P} {u : ConditionsAwareDecisionUnion} (hr : Reachable P u)
    {l : List (String × ConditionsAwareDecision)} (h : u.ToDecision = .union l) :
    l ≠ [] ∧ (∀ p ∈ l, p.1.length ≠ 0 ∧ IsDNS1123Subdomain p.1 = true) ∧ (l.map Prod.fst).Nodup
    ∧ (∀ p ∈ l.dropLast, p.2.ContainsUnconditionalAllowOrDeny = false)
    ∧ 2 ≤ (ConditionsAwareDecision.union l).PossibleDecisions.Len := by
  obtain ⟨rfl, he, hne, h2, hdl, -⟩ := P_36_union_shape hr h
  obtain ⟨hn, hnd⟩ := hr.inv.names he
  exact ⟨hne, hn, hnd, hdl, h2⟩

/-- `build` of WF children is WF. -/
theorem WF_build_ToDecision (h : List (String × ConditionsAwareDecision))
    (hP : ∀ p ∈ h, ConditionsAwareDecision.WF p.2) : ConditionsAwareDecision.WF (build h).ToDecision :=
  WF_ToDecision (Reachable_build h hP)

end ConditionsAwareDecisionUnion

end authorizer
