import union.union

/-!
# `union/union_properties.lean`  ↔  `pkg/authorization/union/union_test.go`

Properties P-41, P-42, P-44, P-45, P-46, P-47 of `review/properties.md` §F.
-/

namespace union

open authorizer

/-! ### Small facts about `DecisionSet`, `PossibleDecisions`, `FromParts` -/

theorem DecisionSet.Has_union (s t : DecisionSet) (d : Decision) :
    (s.union t).Has d = (s.Has d || t.Has d) := by
  cases d <;> rfl

theorem DecisionSet.Has_Delete_ne (s : DecisionSet) (d x : Decision) (h : x ≠ d) :
    (s.Delete d).Has x = s.Has x := by
  cases d <;> cases x <;> simp_all [DecisionSet.Delete, DecisionSet.Has]

theorem DecisionSet.Has_Delete_self (s : DecisionSet) (d : Decision) :
    (s.Delete d).Has d = false := by
  cases d <;> rfl

theorem DecisionSet.Has_singleton (d x : Decision) :
    (DecisionSet.singleton d).Has x = decide (x = d) := by
  cases d <;> cases x <;> rfl

/-- A set with at least two members contains Deny or NoOpinion. -/
theorem DecisionSet.Len_two (s : DecisionSet) (h : 2 ≤ s.Len) :
    s.Has .Deny = true ∨ s.Has .NoOpinion = true := by
  obtain ⟨d, a, n⟩ := s
  cases d <;> cases a <;> cases n <;> simp_all [DecisionSet.Len, DecisionSet.Has]

/-- `FailureDecision` is a member whenever Deny or NoOpinion is. -/
theorem FD_mem (s : DecisionSet) (h : s.Has .Deny = true ∨ s.Has .NoOpinion = true) :
    s.Has (if s.Has .Deny then .Deny else .NoOpinion) = true := by
  cases hd : s.Has .Deny <;> simp_all

theorem ConditionsMap.PD_has_N (m : ConditionsMap) : m.PossibleDecisions.Has .NoOpinion = true := by
  unfold ConditionsMap.PossibleDecisions
  split <;> split <;> rfl

theorem FromParts_dec (d : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts d r e).dec? = some d := by
  cases d <;> rfl

theorem FromParts_Error (d : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts d r e).Error = e := by
  cases d <;> rfl

theorem cua_union (l : List (String × ConditionsAwareDecision)) :
    (ConditionsAwareDecision.union l).ContainsUnconditionalAllowOrDeny
      = ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l := by
  simp [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]

theorem PD_union (l : List (String × ConditionsAwareDecision)) :
    (ConditionsAwareDecision.union l).PossibleDecisions =
      (if ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l
       then ((DecisionSet.singleton .NoOpinion).union
              (ConditionsAwareDecision.PossibleDecisions.subPD l)).Delete .NoOpinion
       else (DecisionSet.singleton .NoOpinion).union
              (ConditionsAwareDecision.PossibleDecisions.subPD l)) := by
  simp [ConditionsAwareDecision.PossibleDecisions]

theorem cua_go_exists (l : List (String × ConditionsAwareDecision))
    (h : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l = true) :
    ∃ p ∈ l, p.2.ContainsUnconditionalAllowOrDeny = true := by
  induction l with
  | nil => simp [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go] at h
  | cons p rest ih =>
    obtain ⟨n, c⟩ := p
    simp only [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨(n, c), by simp, h⟩
    · obtain ⟨q, hq, hq'⟩ := ih h
      exact ⟨q, by simp [hq], hq'⟩

theorem subPD_has (l : List (String × ConditionsAwareDecision)) (p : String × ConditionsAwareDecision)
    (hp : p ∈ l) (x : Decision) (hx : p.2.PossibleDecisions.Has x = true) :
    (ConditionsAwareDecision.PossibleDecisions.subPD l).Has x = true := by
  induction l with
  | nil => simp at hp
  | cons q rest ih =>
    obtain ⟨n, c⟩ := q
    simp only [ConditionsAwareDecision.PossibleDecisions.subPD, DecisionSet.Has_union, Bool.or_eq_true]
    rcases List.mem_cons.mp hp with h | h
    · subst h; exact Or.inl hx
    · exact Or.inr (ih h)

/-- P-35 (one direction, locally re-proved): a decision containing an unconditional
Allow/Deny cannot evaluate to NoOpinion. -/
theorem cua_no_N (c : ConditionsAwareDecision) (h : c.ContainsUnconditionalAllowOrDeny = true) :
    c.PossibleDecisions.Has .NoOpinion = false := by
  cases c with
  | deny => rfl
  | allow => rfl
  | noOpinion => simp [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny] at h
  | conditionsMap => simp [ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny] at h
  | union l =>
    rw [cua_union] at h
    rw [PD_union]
    simp only [h, ↓reduceIte]
    exact DecisionSet.Has_Delete_self _ _

/-! ### P-44: `EvaluateConditions` is clamped into PD -/

/-- The hypothesis P-44 needs about each union-typed child: its `PossibleDecisions` has at
least two members (part of `WFUnion`, `properties.md` §1.3). Without it the clamp fallback
`FailureDecision(c)` can itself lie outside `PD(c)` (see `P_44_needs_child_WF`). -/
def ChildWF (c : ConditionsAwareDecision) : Prop :=
  c.IsUnion = true → 2 ≤ c.PossibleDecisions.Len

/-- Clamp lemma (`union.go:160-165`): whatever the sub-authorizers do, each child result is
in `PD(child)`, provided a union child is well formed. -/
theorem evalChild_mem (h : unionAuthzHandler) (n : String) (c : ConditionsAwareDecision)
    (data : ConditionsData) (hc : ChildWF c) :
    c.PossibleDecisions.Has (h.evalChild n c data).1 = true := by
  have clamp : ∀ (c : ConditionsAwareDecision),
      (c.PossibleDecisions.Has .Deny = true ∨ c.PossibleDecisions.Has .NoOpinion = true) →
      c.PossibleDecisions.Has (h.evaluateAndClamp n c data).1 = true := by
    intro c hfd
    unfold unionAuthzHandler.evaluateAndClamp
    simp only
    split
    · assumption
    · exact FD_mem _ hfd
  cases c with
  | deny => rfl
  | allow => rfl
  | noOpinion => rfl
  | conditionsMap m => exact clamp _ (Or.inr (ConditionsMap.PD_has_N m))
  | union l => exact clamp _ (DecisionSet.Len_two _ (hc rfl))

/-- Shape of the `EvaluateConditions` loop result: either NoOpinion with every child
NoOpinion, or the (non-NoOpinion) result of some child. -/
theorem evaluateLoop_shape (h : unionAuthzHandler) (data : ConditionsData)
    (l : List (String × ConditionsAwareDecision)) (es : List Err) (rs : List String) :
    ((evaluateLoop h data l es rs).1 = .NoOpinion ∧
        ∀ p ∈ l, (h.evalChild p.1 p.2 data).1 = .NoOpinion) ∨
      ∃ p ∈ l, (evaluateLoop h data l es rs).1 = (h.evalChild p.1 p.2 data).1 ∧
        (h.evalChild p.1 p.2 data).1 ≠ .NoOpinion := by
  induction l generalizing es rs with
  | nil => left; simp [evaluateLoop]
  | cons p rest ih =>
    obtain ⟨n, c⟩ := p
    unfold evaluateLoop
    generalize hr : h.evalChild n c data = r
    obtain ⟨d, r', e⟩ := r
    cases d with
    | Allow => right; exact ⟨(n, c), by simp, by simp [hr], by simp [hr]⟩
    | Deny => right; exact ⟨(n, c), by simp, by simp [hr], by simp [hr]⟩
    | NoOpinion =>
      simp only
      rcases ih (appendErr es e) (appendReason rs n r') with ⟨h1, h2⟩ | ⟨q, hq, h1, h2⟩
      · left
        refine ⟨h1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq; simp [hr]
        · exact h2 q hq
      · right; exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- **P-44** `EvaluateConditions` is clamped into PD and never fails open.
"∀ WF union u, ∀ sub-authorizers (arbitrary, possibly adversarial).
dec(EvaluateConditions(u,x)) ∈ PD(u)". The handler `h` is arbitrary: its chain and
routing table may hold any functions. The WF part used is `ChildWF` on each child. -/
theorem P_44_EvaluateConditions_in_PD (h : unionAuthzHandler)
    (l : List (String × ConditionsAwareDecision)) (data : ConditionsData)
    (hwf : ∀ p ∈ l, ChildWF p.2) :
    (ConditionsAwareDecision.union l).PossibleDecisions.Has
      (h.EvaluateConditions (.union l) data).1 = true := by
  simp only [unionAuthzHandler.EvaluateConditions, ConditionsAwareDecision.IsUnion,
    Bool.not_true, Bool.false_eq_true, ite_false, ConditionsAwareDecision.UnionedDecisions]
  rcases evaluateLoop_shape h data l [] [] with ⟨h1, h2⟩ | ⟨p, hp, h1, h2⟩
  · rw [h1]
    -- no child contains an unconditional Allow/Deny, else it could not have returned N
    have hcua : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l = false := by
      cases hg : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l with
      | false => rfl
      | true =>
        obtain ⟨q, hq, hq'⟩ := cua_go_exists l hg
        have hm := evalChild_mem h q.1 q.2 data (hwf q hq)
        rw [h2 q hq, cua_no_N _ hq'] at hm
        exact absurd hm (by decide)
    rw [PD_union, hcua]
    simp [DecisionSet.Has_union, DecisionSet.Has_singleton]
  · rw [h1]
    have hm := evalChild_mem h p.1 p.2 data (hwf p hp)
    have hs := subPD_has l p hp _ hm
    rw [PD_union]
    split
    · rw [DecisionSet.Has_Delete_ne _ _ _ h2, DecisionSet.Has_union, hs, Bool.or_true]
    · rw [DecisionSet.Has_union, hs, Bool.or_true]

/-- P-44 corollary (fail-closed): a non-union input yields `FailureDecision`, never Allow;
a union input yields Allow only if Allow is possible. -/
theorem P_44_never_allow_unless_possible (h : unionAuthzHandler) (u : ConditionsAwareDecision)
    (data : ConditionsData) (hwf : ∀ p ∈ u.UnionedDecisions, ChildWF p.2)
    (hA : (h.EvaluateConditions u data).1 = .Allow) :
    u.IsUnion = true ∧ u.PossibleDecisions.Has .Allow = true := by
  cases u with
  | union l =>
    refine ⟨rfl, ?_⟩
    have := P_44_EvaluateConditions_in_PD h l data hwf
    rwa [hA] at this
  | _ =>
    simp only [unionAuthzHandler.EvaluateConditions, ConditionsAwareDecision.IsUnion,
      Bool.not_false, ite_true, ConditionsAwareDecision.FailureDecision] at hA
    split at hA <;> cases hA

/-- P-44 counterpart: the `ChildWF` hypothesis is needed. A union whose only child is the
non-WF union `[("y", allow)]` (PD = {Allow}, FD = NoOpinion): with that child's authorizer
missing, the clamp fallback is `NoOpinion ∉ PD(u) = {Allow}`. Fail-closed, but outside PD.
-- status: does NOT hold without WF of nested union children. -/
theorem P_44_needs_child_WF (data : ConditionsData) :
    let u := ConditionsAwareDecision.union [("x", .union [("y", .allow "" none)])]
    let h : unionAuthzHandler := { chain := [], nameToAuthorizer := [] }
    (h.EvaluateConditions u data).1 = .NoOpinion ∧ u.PossibleDecisions.Has .NoOpinion = false := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### P-41: with only unconditional leaves, CAA agrees with Authorize on the decision -/

/-- A chain name accepted by the builder's `Add` (`conditionsunion.go:63-72`). DNS-1123 is
opaque in the model, so non-emptiness is stated separately (in Go it is implied). -/
def NameValid (n : String) : Prop := n.length ≠ 0 ∧ IsDNS1123Subdomain n = true

/-- P-10 shape: the conditions-aware method is `FromParts ∘ Authorize`. -/
def LegacyLifted (z : Authorizer) : Prop :=
  ∀ a, z.ConditionsAwareAuthorize a =
    ConditionsAwareDecisionFromParts (z.Authorize a).1 (z.Authorize a).2.1 (z.Authorize a).2.2

/-- Loop invariant of `caaLoop` while every child so far was NoOpinion. -/
structure Inv41 (B : ConditionsAwareDecisionUnion) (pre : List String) : Prop where
  errs : B.errs = []
  flag : B.containsUnconditionalAllowOrDeny = false
  sd : B.subDecisionsPossibleDecisions.deny = false
  sa : B.subDecisionsPossibleDecisions.allow = false
  names : B.inner.map (·.1) = pre

theorem PD_FromParts (d : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts d r e).PossibleDecisions = .singleton d := by
  cases d <;> rfl

theorem cua_FromParts (d : Decision) (r : String) (e : Option Err) :
    (ConditionsAwareDecisionFromParts d r e).ContainsUnconditionalAllowOrDeny = (d != .NoOpinion) := by
  cases d <;> rfl

theorem theOnly_singleton (d : Decision) : (DecisionSet.singleton d).theOnly = some d := by
  cases d <;> rfl

/-- `ToDecision` on an error-free builder with a singleton PD folds to that decision. -/
theorem ToDecision_dec (B : ConditionsAwareDecisionUnion) (herr : B.errs = []) (X : Decision)
    (hpd : B.PossibleDecisions = .singleton X) : B.ToDecision.dec? = some X := by
  unfold ConditionsAwareDecisionUnion.ToDecision
  simp only [herr, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hpd,
    theOnly_singleton]
  exact FromParts_dec _ _ _

theorem hasName_false (B : ConditionsAwareDecisionUnion) (pre : List String)
    (hn : B.inner.map (·.1) = pre) (n : String) (hnot : n ∉ pre) :
    B.hasConditionalAuthorizerName n = false := by
  unfold ConditionsAwareDecisionUnion.hasConditionalAuthorizerName
  rw [List.any_eq_false]
  intro x hx hb
  apply hnot
  rw [← hn]
  have : x.1 = n := by simpa using hb
  exact List.mem_map.mpr ⟨x, hx, this⟩

/-- One `Add` of a valid, fresh name onto an invariant-satisfying builder. -/
theorem Add_lifted (B : ConditionsAwareDecisionUnion) (pre : List String) (hinv : Inv41 B pre)
    (n : String) (hn : NameValid n) (hnot : n ∉ pre) (d : Decision) (r : String) (e : Option Err) :
    B.Add n (ConditionsAwareDecisionFromParts d r e) =
      { inner := B.inner ++ [(n, ConditionsAwareDecisionFromParts d r e)]
        errs := []
        containsUnconditionalAllowOrDeny := (d != .NoOpinion)
        subDecisionsPossibleDecisions := B.subDecisionsPossibleDecisions.union (.singleton d) } := by
  unfold ConditionsAwareDecisionUnion.Add
  have hh := hasName_false B pre hinv.names n hnot
  simp [ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, hinv.flag, hinv.errs, hh,
    hn.1, hn.2, cua_FromParts, PD_FromParts]

theorem PD_inv (B : ConditionsAwareDecisionUnion) (pre : List String) (hinv : Inv41 B pre) :
    B.PossibleDecisions = .singleton .NoOpinion := by
  unfold ConditionsAwareDecisionUnion.PossibleDecisions
  have hd := hinv.sd
  have ha := hinv.sa
  simp only [ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, hinv.flag,
    Bool.false_eq_true, ↓reduceIte]
  revert hd ha
  cases B.subDecisionsPossibleDecisions
  intro hd ha
  simp_all [DecisionSet.union, DecisionSet.singleton]

theorem PD_after_decide (s : DecisionSet) (hd : s.deny = false) (ha : s.allow = false)
    (X : Decision) (hX : X ≠ .NoOpinion) :
    (((DecisionSet.singleton .NoOpinion).union (s.union (.singleton X))).Delete .NoOpinion)
      = .singleton X := by
  obtain ⟨d, a, n⟩ := s
  simp at hd ha
  subst hd ha
  cases X <;> simp_all [DecisionSet.union, DecisionSet.singleton, DecisionSet.Delete]

theorem caaLoop_dec (a : Attributes) (rest : List NamedAuthorizer) :
    ∀ (B : ConditionsAwareDecisionUnion) (pre : List String) (es : List Err) (rs : List String),
    Inv41 B pre → (pre ++ rest.map (·.AuthorizerName)).Nodup →
    (∀ z ∈ rest, NameValid z.AuthorizerName ∧ LegacyLifted z.Authorizer) →
    (caaLoop a rest B).dec? = some (authorizeLoop a rest es rs).1 := by
  induction rest with
  | nil =>
    intro B pre es rs hinv _ _
    simp only [caaLoop, authorizeLoop]
    exact ToDecision_dec B hinv.errs _ (PD_inv B pre hinv)
  | cons z rest ih =>
    intro B pre es rs hinv hnd hall
    obtain ⟨hnv, hlift⟩ := hall z (by simp)
    have hnot : z.AuthorizerName ∉ pre := by
      intro hm
      simp [List.nodup_append] at hnd
      exact (hnd.2.2 _ hm).1 rfl
    have hnd' : ((pre ++ [z.AuthorizerName]) ++ rest.map (·.AuthorizerName)).Nodup := by
      simpa using hnd
    have hall' : ∀ y ∈ rest, NameValid y.AuthorizerName ∧ LegacyLifted y.Authorizer :=
      fun y hy => hall y (List.mem_cons_of_mem _ hy)
    unfold caaLoop authorizeLoop
    rw [hlift a]
    generalize z.Authorizer.Authorize a = t
    obtain ⟨d, r, e⟩ := t
    simp only
    rw [Add_lifted B pre hinv _ hnv hnot]
    have hsd := hinv.sd
    have hsa := hinv.sa
    cases d with
    | Allow =>
      simp only [cua_FromParts, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ↓reduceIte]
      apply ToDecision_dec _ rfl
      exact PD_after_decide _ hsd hsa _ (by decide)
    | Deny =>
      simp only [cua_FromParts, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        ↓reduceIte]
      apply ToDecision_dec _ rfl
      exact PD_after_decide _ hsd hsa _ (by decide)
    | NoOpinion =>
      simp only [cua_FromParts, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      apply ih _ (pre ++ [z.AuthorizerName]) _ _ _ hnd' hall'
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · simp [DecisionSet.union, DecisionSet.singleton, hsd]
      · simp [DecisionSet.union, DecisionSet.singleton, hsa]
      · simp [hinv.names]

/-- **P-41** "With only unconditional leaves, `CAA` agrees with legacy `Authorize` on the
decision — not on reason or error. Formal: let `zᵢ.CAA = FromParts ∘ zᵢ.Authorize` (P-10)
and all names DNS-1123 and distinct. Then `dec(CAA(chain,a)) = dec(Authorize(chain,a))`."
(Decision component only; reasons/errors differ, see properties.md table.) -/
theorem P_41_CAA_agrees_with_Authorize (h : unionAuthzHandler) (a : Attributes)
    (hvalid : ∀ z ∈ h.chain, NameValid z.AuthorizerName ∧ LegacyLifted z.Authorizer)
    (hdistinct : (h.chain.map (·.AuthorizerName)).Nodup) :
    (h.ConditionsAwareAuthorize a).dec? = some (h.Authorize a).1 := by
  unfold unionAuthzHandler.ConditionsAwareAuthorize unionAuthzHandler.Authorize
  exact caaLoop_dec a h.chain {} [] [] [] ⟨rfl, rfl, rfl, rfl, rfl⟩ (by simpa using hdistinct) hvalid

/-! ### P-42: `New` accepts names that make every conditions-aware request fail -/

theorem caaLoop_single (a : Attributes) (n : String) (z : Authorizer) :
    caaLoop a [⟨n, z⟩] {} = (({} : ConditionsAwareDecisionUnion).Add n (z.ConditionsAwareAuthorize a)).ToDecision := by
  unfold caaLoop
  simp only
  split <;> rfl

/-- **P-42** "`union.New` accepts names that make every conditions-aware request fail.
`union.New` succeeds iff names are non-empty and distinct; `add` additionally needs
DNS-1123. So ∃ chain accepted by `New` such that ∀a. CAA(chain,a) is a fail-closed
decision with error; for a first authorizer that Allows, `PD_B = {A}` ⇒ result
`noOp("failed closed", err)`."
-- status: does NOT hold (the desirable "New-valid ⇒ CAA well-behaved").
`IsDNS1123Subdomain` is opaque, so the counterexample is parametric in any non-empty name
it rejects (e.g. `"Node_Authz"` in Go). The legacy `Authorize` on the same chain allows. -/
theorem P_42_New_accepts_non_DNS1123 (n : String) (hn : n.length ≠ 0)
    (hdns : IsDNS1123Subdomain n = false) (z : Authorizer) :
    ∃ h, New [⟨n, z⟩] = .ok h ∧ h.chain = [⟨n, z⟩] ∧
      ∀ a,
        (h.ConditionsAwareAuthorize a).Error.isSome = true ∧
        (h.ConditionsAwareAuthorize a).dec? ≠ some .Allow ∧
        (∀ r e, z.ConditionsAwareAuthorize a = .allow r e →
          (h.Authorize a).1 = .Allow ∨ ¬ LegacyLifted z) ∧
        (∀ r e, z.ConditionsAwareAuthorize a = .allow r e →
          ∃ err, h.ConditionsAwareAuthorize a = .noOpinion "failed closed" (some err)) := by
  refine ⟨{ chain := [⟨n, z⟩], nameToAuthorizer := [(n, z)] }, ?_, rfl, ?_⟩
  · simp [New, buildNameToAuthorizer, lookup, hn]
  · intro a
    have hcaa : ({ chain := [⟨n, z⟩], nameToAuthorizer := [(n, z)] } : unionAuthzHandler).ConditionsAwareAuthorize a
        = (({} : ConditionsAwareDecisionUnion).Add n (z.ConditionsAwareAuthorize a)).ToDecision :=
      caaLoop_single a n z
    rw [hcaa]
    have herrs : (({} : ConditionsAwareDecisionUnion).Add n (z.ConditionsAwareAuthorize a)).errs
        = ["invalid authorizerName"] := by
      simp [ConditionsAwareDecisionUnion.Add, ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny,
        ConditionsAwareDecisionUnion.hasConditionalAuthorizerName, hn, hdns]
    have htd : ∀ B : ConditionsAwareDecisionUnion, B.errs = ["invalid authorizerName"] →
        B.ToDecision = ConditionsAwareDecisionFromParts B.FailureDecision "failed closed"
          (aggregate ["invalid authorizerName"]) := by
      intro B hB
      simp [ConditionsAwareDecisionUnion.ToDecision, hB]
    rw [htd _ herrs, FromParts_Error, FromParts_dec]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [ConditionsAwareDecisionUnion.FailureDecision]
      split <;> simp
    · intro r e hz
      by_cases hl : LegacyLifted z
      · left
        have := hl a
        rw [hz] at this
        simp only [unionAuthzHandler.Authorize, authorizeLoop]
        generalize hA : z.Authorize a = t at this
        obtain ⟨d, r', e'⟩ := t
        cases d <;> simp_all [ConditionsAwareDecisionFromParts]
      · exact Or.inr hl
    · intro r e hz
      refine ⟨String.intercalate ", " ["invalid authorizerName"], ?_⟩
      rw [hz]
      rfl

/-! ### P-45: `EvaluateConditions` stops at the first Allow/Deny -/

/-- **P-45** "children after the first `{A,D}` result are not passed to their authorizer."
Stated extensionally: once a child yields Allow/Deny after a NoOpinion prefix, the loop's
result is exactly that child's result, whatever the remaining children `post` are (so
their sub-authorizers, reached only via `evalChild`, cannot influence it). -/
theorem P_45_EvaluateConditions_short_circuit (h : unionAuthzHandler) (data : ConditionsData)
    (pre : List (String × ConditionsAwareDecision)) (n : String) (c : ConditionsAwareDecision)
    (post : List (String × ConditionsAwareDecision))
    (hpre : ∀ p ∈ pre, (h.evalChild p.1 p.2 data).1 = .NoOpinion)
    (hc : (h.evalChild n c data).1 ≠ .NoOpinion) :
    ∀ es rs, evaluateLoop h data (pre ++ (n, c) :: post) es rs = h.evalChild n c data := by
  induction pre with
  | nil =>
    intro es rs
    simp only [List.nil_append, evaluateLoop]
    generalize h.evalChild n c data = t at hc ⊢
    obtain ⟨d, r, e⟩ := t
    cases d <;> simp_all
  | cons p rest ih =>
    intro es rs
    obtain ⟨m, c'⟩ := p
    have hp := hpre (m, c') (by simp)
    simp only [List.cons_append, evaluateLoop]
    generalize h.evalChild m c' data = t at hp ⊢
    obtain ⟨d, r, e⟩ := t
    simp at hp
    subst hp
    exact ih (fun q hq => hpre q (List.mem_cons_of_mem _ hq)) _ _

/-! ### P-46: routing is single-level by name -/

/-- **P-46** "for child `(n, c)`, the evaluator is `nameToAuthorizer[n]` of *this* union
instance": the per-child result depends on the routing table only through `lookup … n`. -/
theorem P_46_routing_by_name (h h' : unionAuthzHandler) (n : String) (c : ConditionsAwareDecision)
    (data : ConditionsData)
    (hl : lookup h.nameToAuthorizer n = lookup h'.nameToAuthorizer n) :
    h.evalChild n c data = h'.evalChild n c data := by
  have he : ∀ c, h.evaluateConditions n c data = h'.evaluateConditions n c data := by
    intro c
    unfold unionAuthzHandler.evaluateConditions
    rw [hl]
  cases c <;> simp only [unionAuthzHandler.evalChild, unionAuthzHandler.evaluateAndClamp, he]

/-- P-46 "nested unions are delegated whole": a union child is handed, unchanged, to the
named authorizer (then clamped). -/
theorem P_46_nested_delegated_whole (h : unionAuthzHandler) (n : String)
    (l : List (String × ConditionsAwareDecision)) (data : ConditionsData) (z : Authorizer)
    (hz : lookup h.nameToAuthorizer n = some z)
    (hpd : (ConditionsAwareDecision.union l).PossibleDecisions.Has
      (z.EvaluateConditions (.union l) data).1 = true) :
    h.evalChild n (.union l) data = z.EvaluateConditions (.union l) data := by
  simp [unionAuthzHandler.evalChild, unionAuthzHandler.evaluateAndClamp,
    unionAuthzHandler.evaluateConditions, hz, hpd]

theorem lookup_append (m : List (String × Authorizer)) (k : String) (v : Authorizer) (n : String) :
    lookup (m ++ [(k, v)]) n = (lookup m n).or (if k = n then some v else none) := by
  unfold lookup
  rw [List.find?_append]
  cases m.find? (fun p => p.1 == n) with
  | some x => simp
  | none => by_cases hk : k = n <;> simp [hk]

theorem buildNameToAuthorizer_lookup (rest : List NamedAuthorizer) :
    ∀ (m m' : List (String × Authorizer)), buildNameToAuthorizer rest m = .ok m' →
      ∀ n, lookup m' n =
        (lookup m n).or ((rest.find? (fun z => z.AuthorizerName == n)).map (·.Authorizer)) := by
  induction rest with
  | nil => intro m m' hb n; simp [buildNameToAuthorizer] at hb; subst hb; simp
  | cons z rest ih =>
    intro m m' hb n
    unfold buildNameToAuthorizer at hb
    split at hb
    · cases hb
    · split at hb
      · cases hb
      · rename_i _ hfresh
        rw [ih _ _ hb n, lookup_append]
        by_cases hk : z.AuthorizerName = n
        · subst hk
          simp at hfresh
          simp [hfresh]
        · simp [hk]

/-- P-46 for a handler built by `New`: `nameToAuthorizer[n]` is the authorizer of the
chain entry named `n`. -/
theorem P_46_New_lookup (chain : List NamedAuthorizer) (h : unionAuthzHandler)
    (hN : New chain = .ok h) (n : String) :
    lookup h.nameToAuthorizer n =
      (chain.find? (fun z => z.AuthorizerName == n)).map (·.Authorizer) := by
  unfold New at hN
  split at hN
  · cases hN
  · rename_i m hb
    cases hN
    rw [buildNameToAuthorizer_lookup chain [] m hb n]
    simp [lookup]

/-! ### P-47: NoOpinion errors propagate -/

theorem aggregate_isSome (es : List Err) (h : es ≠ []) : (aggregate es).isSome = true := by
  cases es with
  | nil => exact absurd rfl h
  | cons => rfl

theorem appendErr_ne (es : List Err) (e : Option Err) (h : es ≠ []) : appendErr es e ≠ [] := by
  cases e <;> simp [appendErr, h]

theorem evaluateLoop_err_kept (h : unionAuthzHandler) (data : ConditionsData)
    (l : List (String × ConditionsAwareDecision)) :
    ∀ es rs, es ≠ [] → (evaluateLoop h data l es rs).1 = .NoOpinion →
      (evaluateLoop h data l es rs).2.2.isSome = true := by
  induction l with
  | nil => intro es rs hes _; exact aggregate_isSome es hes
  | cons p rest ih =>
    intro es rs hes hN
    obtain ⟨n, c⟩ := p
    simp only [evaluateLoop] at hN ⊢
    generalize h.evalChild n c data = t at hN ⊢
    obtain ⟨d, r, e⟩ := t
    cases d with
    | Allow => simp at hN
    | Deny => simp at hN
    | NoOpinion => exact ih _ _ (appendErr_ne es e hes) hN

/-- **P-47** "if `EvaluateConditions` returns N and some N child carried an error, the
returned error is non-nil (`union.go:176-185`)." -/
theorem P_47_NoOpinion_errors_propagate (h : unionAuthzHandler)
    (l : List (String × ConditionsAwareDecision)) (data : ConditionsData)
    (hN : (h.EvaluateConditions (.union l) data).1 = .NoOpinion)
    (hex : ∃ p ∈ l, (h.evalChild p.1 p.2 data).1 = .NoOpinion ∧
      (h.evalChild p.1 p.2 data).2.2.isSome = true) :
    (h.EvaluateConditions (.union l) data).2.2.isSome = true := by
  simp only [unionAuthzHandler.EvaluateConditions, ConditionsAwareDecision.IsUnion,
    Bool.not_true, Bool.false_eq_true, ite_false, ConditionsAwareDecision.UnionedDecisions] at hN ⊢
  suffices key : ∀ es rs, (evaluateLoop h data l es rs).1 = .NoOpinion →
      (evaluateLoop h data l es rs).2.2.isSome = true from key [] [] hN
  clear hN
  induction l with
  | nil => obtain ⟨p, hp, _⟩ := hex; simp at hp
  | cons q rest ih =>
    intro es rs hN
    obtain ⟨p, hp, hpN, hpE⟩ := hex
    obtain ⟨n, c⟩ := q
    simp only [evaluateLoop] at hN ⊢
    rcases List.mem_cons.mp hp with hq | hq
    · subst hq
      simp only at hpN hpE
      generalize h.evalChild n c data = t at hN hpN hpE ⊢
      obtain ⟨d, r, e⟩ := t
      simp at hpN
      subst hpN
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hpE
      exact evaluateLoop_err_kept h data rest _ _ (by simp [appendErr]) hN
    · generalize h.evalChild n c data = t at hN ⊢
      obtain ⟨d, r, e⟩ := t
      cases d with
      | Allow => simp at hN
      | Deny => simp at hN
      | NoOpinion => exact ih ⟨p, hq, hpN, hpE⟩ _ _ hN

end union
