import encoding.encoding

/-!
# `encoding/encoding_properties.lean`  ↔  `pkg/apis/authorization/v1/encoding_test.go`

Properties P-56, P-57, P-58 of `review/properties.md` §G (encode/decode of
`ConditionsAwareDecision` on the v1 wire).

Notation: `enc` = `v1.FromAuthorizerConditionsAwareDecision`,
`dec v fc` = `v1.ToAuthorizerConditionsAwareDecision v fc`.

**P-16 (not modelled, comment only).** "Wire validation does not imply constructibility":
`∃ v. DV(v) ∧ ¬isMap(dec v)` for `type = ConditionsMap`. Declarative validation (`DV`,
`staging/src/k8s.io/api/authorization/v1/zz_generated.validations.go`) is not modelled.
Its counterexamples are exactly the decoder-side facts below and in P-57: empty lists
(`P_57_map_all_empty`), NoOpinion-only lists (`P_57_map_noOpinion_only`), 129–384
conditions (DV limits 128 per list, the constructor 128 in total) and the same ID in two
lists (DV checks uniqueness per list, the constructor across lists). -- status: does NOT
hold (as a desirable implication); not stated as a theorem because `DV` is not modelled.
-/

namespace v1

open authorizer (Err)

local notation "enc" => FromAuthorizerConditionsAwareDecision
local notation "dec" => ToAuthorizerConditionsAwareDecision

/-! ## P-58 -/

/-- **P-58 The decoder is total and fails closed.** "`∀v. dec(v, fc)` returns without
panicking". In Lean totality is free; stated as: for every `v` the decoder returns. -/
theorem P_58_decoder_total (v : ConditionsAwareDecision) (fc : Err → authorizer.ConditionsAwareDecision) :
    ∃ d, dec v fc = d := ⟨_, rfl⟩

/-- **P-58** "unknown type ⇒ `fc(err)`". -/
theorem P_58_unknown_failClosed (s : String) (dn nn an : Option UnconditionalDecision)
    (cm : Option ConditionsMap) (u : List NamedConditionsAwareDecision)
    (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (.mk (.unknown s) dn nn an cm u) fc =
      fc s!"unrecognized ConditionsAwareDecision.type=\"{s}\"" := rfl

/-- **P-58** "invalid maps ⇒ constructor fail-closed …, independent of failurePolicy":
for `type = ConditionsMap` the result does not depend on `fc`. -/
theorem P_58_map_independent_of_failClosed (dn nn an : Option UnconditionalDecision)
    (cm : Option ConditionsMap) (u : List NamedConditionsAwareDecision)
    (fc fc' : Err → authorizer.ConditionsAwareDecision) :
    dec (.mk .ConditionsMap dn nn an cm u) fc = dec (.mk .ConditionsMap dn nn an cm u) fc' := by
  cases cm <;> rfl

/-- **P-58** (via P-14) a `type = ConditionsMap` value never decodes to Allow. -/
theorem P_58_map_never_allow (dn nn an : Option UnconditionalDecision)
    (cm : Option ConditionsMap) (u : List NamedConditionsAwareDecision)
    (fc : Err → authorizer.ConditionsAwareDecision) :
    (dec (.mk .ConditionsMap dn nn an cm u) fc).IsAllow = false := by
  cases cm <;>
  simp only [ToAuthorizerConditionsAwareDecision, authorizer.ConditionsAwareDecisionConditionsMap] <;>
  repeat (first | split | rfl)

/-! ## P-56, unconditional variants -/

/-- The error normalisation of a round trip: a non-nil error whose `Error()` is `""` is
encoded as `evaluationError: ""` and decodes to `nil` (`encoding.go:33-35,111`). -/
def normErr (e : Option Err) : Option Err := if errString e = "" then none else e

theorem normErr_eq_self (e : Option Err) (h : e ≠ some "") : normErr e = e := by
  cases e <;> simp_all [normErr, errString]

theorem UnconditionalEvaluationError_enc (r : String) (e : Option Err) :
    UnconditionalEvaluationError (some { Reason := r, EvaluationError := errString e }) = normErr e := by
  cases e <;> simp [UnconditionalEvaluationError, normErr, errString] <;> split <;> simp_all

/-- **P-56 (Deny)** "`dec(enc(d), fc) ≅ d`" with the stated loss: `dec(enc(deny r e)) =
deny r (normErr e)`. -/
theorem P_56_roundtrip_deny (r : String) (e : Option Err) (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (enc (.deny r e)) fc = .deny r (normErr e) := by
  simp [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ToAuthorizerConditionsAwareDecision, UnconditionalReason, UnconditionalEvaluationError_enc]

/-- **P-56 (Allow)**. -/
theorem P_56_roundtrip_allow (r : String) (e : Option Err) (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (enc (.allow r e)) fc = .allow r (normErr e) := by
  simp [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ToAuthorizerConditionsAwareDecision, UnconditionalReason, UnconditionalEvaluationError_enc]

/-- **P-56 (NoOpinion)**. -/
theorem P_56_roundtrip_noOpinion (r : String) (e : Option Err) (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (enc (.noOpinion r e)) fc = .noOpinion r (normErr e) := by
  simp [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ToAuthorizerConditionsAwareDecision, UnconditionalReason, UnconditionalEvaluationError_enc]

/-- **P-56 (unconditional, exact)**: when the error is not `some ""`, the round trip is the
identity. -/
theorem P_56_roundtrip_unconditional_exact (d : authorizer.ConditionsAwareDecision)
    (hu : d.IsUnconditional = true) (he : d.Error ≠ some "")
    (fc : Err → authorizer.ConditionsAwareDecision) : dec (enc d) fc = d := by
  cases d with
  | deny r e => rw [P_56_roundtrip_deny, normErr_eq_self e he]
  | allow r e => rw [P_56_roundtrip_allow, normErr_eq_self e he]
  | noOpinion r e => rw [P_56_roundtrip_noOpinion, normErr_eq_self e he]
  | conditionsMap _ => simp [authorizer.ConditionsAwareDecision.IsUnconditional,
      authorizer.ConditionsAwareDecision.IsAllow, authorizer.ConditionsAwareDecision.IsDeny,
      authorizer.ConditionsAwareDecision.IsNoOpinion] at hu
  | union _ => simp [authorizer.ConditionsAwareDecision.IsUnconditional,
      authorizer.ConditionsAwareDecision.IsAllow, authorizer.ConditionsAwareDecision.IsDeny,
      authorizer.ConditionsAwareDecision.IsNoOpinion] at hu

/-- **P-56, the exception** ("a non-nil error whose `Error()` is `""` decodes to nil"): the
round trip is NOT the identity on `deny r (some "")` (likewise allow/noOpinion).
-- status: does NOT hold for this input (documented loss). -/
theorem P_56_roundtrip_empty_error_lost (r : String) (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (enc (.deny r (some ""))) fc = .deny r none := by
  rw [P_56_roundtrip_deny]; rfl

/-! ## P-56, maps -/

/-- `toAuthorizerConditions ∘ fromAuthorizerConditions = id` (`encoding.go:96-107,154-163`;
the `EvaluateFunc` loss is outside the model). -/
theorem toAuthorizerConditions_from (l : List authorizer.Condition) :
    toAuthorizerConditions (fromAuthorizerConditions l) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [toAuthorizerConditions, fromAuthorizerConditions, List.map_map] at ih ⊢
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨rfl, ih⟩

/-- `validateConditions` accepts a list of valid conditions whose IDs are distinct and
fresh w.r.t. `seenIDs`, and returns the extended `seenIDs`. -/
theorem validateConditions_ok (l : List authorizer.Condition) (seen : List String)
    (hv : ∀ c ∈ l, c.valid = true) (hnd : (l.map (·.ID)).Nodup)
    (hfresh : ∀ c ∈ l, c.ID ∉ seen) :
    authorizer.validateConditions seen l = .ok ((l.map (·.ID)).reverse ++ seen) := by
  induction l generalizing seen with
  | nil => rfl
  | cons c rest ih =>
    have hc := hv c (List.mem_cons_self ..)
    simp only [authorizer.Condition.valid, Bool.and_eq_true, decide_eq_true_eq,
      Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    have hcs : seen.contains c.ID = false := by
      have := hfresh c (List.mem_cons_self ..)
      simpa [List.contains_iff_mem] using this
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih' := ih (c.ID :: seen) (fun x hx => hv x (List.mem_cons_of_mem _ hx)) hnd.2
      (by
        intro x hx hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact hnd.1 (h ▸ List.mem_map_of_mem hx)
        · exact hfresh x (List.mem_cons_of_mem _ hx) h)
    have h3' : (c.CondType.length != 0 && !authorizer.IsDomainPrefixedKey c.CondType) = false := by
      rcases h3 with h | h <;> simp [h]
    simp only [authorizer.validateConditions, hcs, h1, Bool.not_true, h3']
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.not_lt.mpr h2, Nat.not_lt.mpr h4, ih']
    simp

/-- The map smart constructor accepts every well-formed map unchanged
(`conditionsmap.go:138-185`, converse direction of P-13). -/
theorem ConditionsAwareDecisionConditionsMap_of_WF (m : authorizer.ConditionsMap) (h : m.WF) :
    authorizer.ConditionsAwareDecisionConditionsMap m.denyConditions m.noOpinionConditions
      m.allowConditions = .conditionsMap m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [authorizer.ConditionsMap.Length, authorizer.MaxConditionsPerMap] at h1 h2
  simp only [authorizer.ConditionsMap.all, List.map_append, List.nodup_append] at h4
  obtain ⟨⟨hD, hN, hDN⟩, hA, hDNA⟩ := h4
  have hvD : ∀ c ∈ m.denyConditions, c.valid = true := fun c hc => h5 c (by simp [authorizer.ConditionsMap.all, hc])
  have hvN : ∀ c ∈ m.noOpinionConditions, c.valid = true := fun c hc => h5 c (by simp [authorizer.ConditionsMap.all, hc])
  have hvA : ∀ c ∈ m.allowConditions, c.valid = true := fun c hc => h5 c (by simp [authorizer.ConditionsMap.all, hc])
  have v1 := validateConditions_ok m.denyConditions [] hvD hD (by simp)
  have v2 := validateConditions_ok m.noOpinionConditions
    ((m.denyConditions.map (·.ID)).reverse ++ []) hvN hN (by
    intro c hc hmem
    simp only [List.append_nil, List.mem_reverse] at hmem
    exact hDN _ hmem _ (List.mem_map_of_mem hc) rfl)
  have v3 := validateConditions_ok m.allowConditions
    ((m.noOpinionConditions.map (·.ID)).reverse ++ ((m.denyConditions.map (·.ID)).reverse ++ [])) hvA hA (by
    intro c hc hmem
    simp only [List.mem_append, List.mem_reverse, List.append_nil] at hmem
    rcases hmem with hmem | hmem
    · exact hDNA _ (List.mem_append_right _ hmem) _ (List.mem_map_of_mem hc) rfl
    · exact hDNA _ (List.mem_append_left _ hmem) _ (List.mem_map_of_mem hc) rfl)
  have hz : (m.denyConditions.length + m.noOpinionConditions.length + m.allowConditions.length == 0) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have hbig : ¬ (m.denyConditions.length + m.noOpinionConditions.length + m.allowConditions.length > 128) := by
    omega
  have hno : (m.denyConditions.length == 0 && m.allowConditions.length == 0) = false := by
    rcases h3 with h | h <;> simp [h]
  unfold authorizer.ConditionsAwareDecisionConditionsMap
  simp only [hz, authorizer.MaxConditionsPerMap, hbig, hno, v1, v2, v3,
    Bool.false_eq_true, ↓reduceIte]

/-- **P-56 (map)** "map — `mkMap` re-validates the same lists (WF ⇒ accepted, P-13)":
`m.WF ⇒ dec(enc(conditionsMap m)) = conditionsMap m` (for every `fc`). -/
theorem P_56_roundtrip_map (m : authorizer.ConditionsMap) (h : m.WF)
    (fc : Err → authorizer.ConditionsAwareDecision) :
    dec (enc (.conditionsMap m)) fc = .conditionsMap m := by
  simp only [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ToAuthorizerConditionsAwareDecision, toAuthorizerConditions_from,
    authorizer.ConditionsMap.DenyConditions, authorizer.ConditionsMap.NoOpinionConditions,
    authorizer.ConditionsMap.AllowConditions]
  exact ConditionsAwareDecisionConditionsMap_of_WF m h

/-! ## P-56, unions -/

section union

theorem DecisionSet.union_empty (s : authorizer.DecisionSet) : s.union .empty = s := by
  cases s; simp [authorizer.DecisionSet.union, authorizer.DecisionSet.empty]

theorem DecisionSet.empty_union (s : authorizer.DecisionSet) : authorizer.DecisionSet.empty.union s = s := by
  cases s; simp [authorizer.DecisionSet.union, authorizer.DecisionSet.empty]

theorem DecisionSet.union_assoc (s t w : authorizer.DecisionSet) :
    (s.union t).union w = s.union (t.union w) := by
  cases s; cases t; cases w; simp [authorizer.DecisionSet.union, Bool.or_assoc]

/-- "no child before the last has `cua`" (`WFUnion`, `properties.md` §1.3; `conditionsunion.go:59-61`). -/
def NoCuaBeforeLast : List (String × authorizer.ConditionsAwareDecision) → Prop
  | [] => True
  | [_] => True
  | (_, c) :: rest@(_ :: _) => c.ContainsUnconditionalAllowOrDeny = false ∧ NoCuaBeforeLast rest

/-- Decoding the encoded children re-adds them to the builder one by one; under the WFUnion
name and cua hypotheses every `Add` appends and records no error. -/
theorem decode_go_encode_go (fc : Err → authorizer.ConditionsAwareDecision)
    (l : List (String × authorizer.ConditionsAwareDecision)) (u : authorizer.ConditionsAwareDecisionUnion)
    (hflag : u.containsUnconditionalAllowOrDeny = false)
    (hrt : ∀ p ∈ l, dec (enc p.2) fc = p.2)
    (hne : ∀ p ∈ l, p.1 ≠ "")
    (hdns : ∀ p ∈ l, authorizer.IsDNS1123Subdomain p.1 = true)
    (hnd : ((u.inner ++ l).map Prod.fst).Nodup)
    (hcua : NoCuaBeforeLast l) :
    ToAuthorizerConditionsAwareDecision.go fc (FromAuthorizerConditionsAwareDecision.go l) u =
      { inner := u.inner ++ l, errs := u.errs,
        containsUnconditionalAllowOrDeny := authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l,
        subDecisionsPossibleDecisions :=
          u.subDecisionsPossibleDecisions.union (authorizer.ConditionsAwareDecision.PossibleDecisions.subPD l) } := by
  induction l generalizing u with
  | nil =>
    cases u
    simp_all [ToAuthorizerConditionsAwareDecision.go, FromAuthorizerConditionsAwareDecision.go,
      authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go,
      authorizer.ConditionsAwareDecision.PossibleDecisions.subPD, DecisionSet.union_empty]
  | cons p rest ih =>
    obtain ⟨n, c⟩ := p
    have hc : dec (enc c) fc = c := hrt (n, c) (List.mem_cons_self ..)
    have hn : n ≠ "" := hne (n, c) (List.mem_cons_self ..)
    have hd : authorizer.IsDNS1123Subdomain n = true := hdns (n, c) (List.mem_cons_self ..)
    have hfresh : u.hasConditionalAuthorizerName n = false := by
      simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
      obtain ⟨_, _, hdisj⟩ := hnd
      simp only [authorizer.ConditionsAwareDecisionUnion.hasConditionalAuthorizerName,
        List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hdisj _ (List.mem_map_of_mem hx) n (List.mem_cons_self ..) heq
    have hadd : u.Add n c =
        { inner := u.inner ++ [(n, c)], errs := u.errs,
          containsUnconditionalAllowOrDeny := c.ContainsUnconditionalAllowOrDeny,
          subDecisionsPossibleDecisions := u.subDecisionsPossibleDecisions.union c.PossibleDecisions } := by
      simp [authorizer.ConditionsAwareDecisionUnion.Add,
        authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny, hflag, hfresh, hd, hn]
    simp only [FromAuthorizerConditionsAwareDecision.go, ToAuthorizerConditionsAwareDecision.go, hc, hadd]
    cases rest with
    | nil =>
      simp [ToAuthorizerConditionsAwareDecision.go, FromAuthorizerConditionsAwareDecision.go,
        authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go,
        authorizer.ConditionsAwareDecision.PossibleDecisions.subPD, DecisionSet.union_empty]
    | cons q rest' =>
      simp only [NoCuaBeforeLast] at hcua
      obtain ⟨hc0, hcua'⟩ := hcua
      rw [ih]
      · simp [authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go,
          hc0, authorizer.ConditionsAwareDecision.PossibleDecisions.subPD,
          DecisionSet.union_assoc]
      · exact hc0
      · exact fun p hp => hrt p (List.mem_cons_of_mem _ hp)
      · exact fun p hp => hne p (List.mem_cons_of_mem _ hp)
      · exact fun p hp => hdns p (List.mem_cons_of_mem _ hp)
      · simpa using hnd
      · exact hcua'

/-- `ToDecision` (`conditionsunion.go:135-185`) emits the union unchanged when there are no
name errors and `|PD| ≥ 2`. -/
theorem ToDecision_noFold (u : authorizer.ConditionsAwareDecisionUnion) (he : u.errs = [])
    (h : 2 ≤ u.PossibleDecisions.Len) : u.ToDecision = .union u.inner := by
  have h1 : u.PossibleDecisions.Len ≠ 1 := by omega
  unfold authorizer.ConditionsAwareDecisionUnion.ToDecision
  simp [he, authorizer.DecisionSet.theOnly, h1]

/-- **P-56 (union)** "union — re-`add` of valid distinct names in the same order (no cua
before the last child, P-36), then `toDecision` sees the same PD (≥2) and does not fold."
Hypotheses mirror `WFUnion` / P-36: non-empty, names non-empty, distinct and DNS-1123, no
`cua` child before the last, `|PD| ≥ 2`, and every child round-trips (the induction
hypothesis). -/
theorem P_56_roundtrip_union (fc : Err → authorizer.ConditionsAwareDecision)
    (l : List (String × authorizer.ConditionsAwareDecision))
    (_hk : l ≠ [])
    (hne : ∀ p ∈ l, p.1 ≠ "")
    (hdns : ∀ p ∈ l, authorizer.IsDNS1123Subdomain p.1 = true)
    (hnd : (l.map Prod.fst).Nodup)
    (hcua : NoCuaBeforeLast l)
    (hPD : 2 ≤ (authorizer.ConditionsAwareDecision.union l).PossibleDecisions.Len)
    (hrt : ∀ p ∈ l, dec (enc p.2) fc = p.2) :
    dec (enc (.union l)) fc = .union l := by
  have hgo := decode_go_encode_go fc l {} rfl hrt hne hdns (by simpa using hnd) hcua
  simp only [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ToAuthorizerConditionsAwareDecision]
  rw [hgo, ToDecision_noFold _ rfl]
  · simp
  · simpa [authorizer.ConditionsAwareDecisionUnion.PossibleDecisions,
      authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny,
      authorizer.ConditionsAwareDecision.PossibleDecisions, DecisionSet.empty_union] using hPD

/-! ## P-56, all well-formed decisions -/

/-- The precondition of the exact round trip: `WF` of `properties.md` §1.3 (maps `WFMap`,
unions `WFUnion`, recursively) plus the error normalisation side condition
(every unconditional leaf's error is not `some ""`, see `P_56_roundtrip_empty_error_lost`). -/
def RoundTripWF : authorizer.ConditionsAwareDecision → Prop
  | .deny _ e | .allow _ e | .noOpinion _ e => e ≠ some ""
  | .conditionsMap m => m.WF
  | .union l =>
    l ≠ [] ∧ (∀ p ∈ l, p.1 ≠ "") ∧ (∀ p ∈ l, authorizer.IsDNS1123Subdomain p.1 = true)
    ∧ (l.map Prod.fst).Nodup ∧ NoCuaBeforeLast l
    ∧ 2 ≤ (authorizer.ConditionsAwareDecision.union l).PossibleDecisions.Len ∧ go l
where
  go : List (String × authorizer.ConditionsAwareDecision) → Prop
    | [] => True
    | (_, c) :: rest => RoundTripWF c ∧ go rest

mutual
/-- **P-56 Encode-decode round trip for every WF CAD.** "`∀ WF d. dec(enc(d), fc) ≅ d`".
In the model `≅` is equality (conditions keep `(id, expr, type, desc)`; the lost
`EvaluateFunc` is not modelled), under `RoundTripWF`, i.e. WF plus "no error is `some \"\"`". -/
theorem P_56_roundtrip (fc : Err → authorizer.ConditionsAwareDecision) :
    (d : authorizer.ConditionsAwareDecision) → RoundTripWF d → dec (enc d) fc = d
  | .deny r e, h => by rw [P_56_roundtrip_deny, normErr_eq_self e h]
  | .allow r e, h => by rw [P_56_roundtrip_allow, normErr_eq_self e h]
  | .noOpinion r e, h => by rw [P_56_roundtrip_noOpinion, normErr_eq_self e h]
  | .conditionsMap m, h => P_56_roundtrip_map m h fc
  | .union l, h => by
    simp only [RoundTripWF] at h
    obtain ⟨hk, hne, hdns, hnd, hcua, hPD, hgo⟩ := h
    exact P_56_roundtrip_union fc l hk hne hdns hnd hcua hPD (P_56_roundtrip_list fc l hgo)

/-- List part of `P_56_roundtrip`. -/
theorem P_56_roundtrip_list (fc : Err → authorizer.ConditionsAwareDecision) :
    (l : List (String × authorizer.ConditionsAwareDecision)) → RoundTripWF.go l →
      ∀ p ∈ l, dec (enc p.2) fc = p.2
  | [], _ => fun _ hp => absurd hp List.not_mem_nil
  | (_, c) :: rest, h => fun p hp => by
    simp only [RoundTripWF.go] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact P_56_roundtrip fc c h.1
    · exact P_56_roundtrip_list fc rest h.2 p hp
end

end union

/-! ## P-57 (negative theorems: `enc(dec(v)) ≠ v`) -/

theorem enc_Type_ne_unknown (d : authorizer.ConditionsAwareDecision) (s : String) :
    (enc d).«Type» ≠ .unknown s := by
  cases d <;> simp [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
    ConditionsAwareDecision.«Type»]

/-- **P-57** class "`type=ConditionsMap` with all-empty lists": decodes to
`noOpinion "no conditions" err`, re-encoded as `type=NoOpinion`.
-- status: does NOT hold (round trip `enc ∘ dec = id`) -/
theorem P_57_map_all_empty (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .ConditionsMap (ConditionsMap := some {})
    enc (dec v fc) ≠ v := by
  intro v h
  have hT : (enc (dec v fc)).«Type» = .NoOpinion := rfl
  rw [h] at hT; cases hT

/-- **P-57** class "`type=ConditionsMap` with nil map": decodes like the all-empty map.
-- status: does NOT hold -/
theorem P_57_map_nil (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .ConditionsMap
    enc (dec v fc) ≠ v := by
  intro v h
  have hT : (enc (dec v fc)).«Type» = .NoOpinion := rfl
  rw [h] at hT; cases hT

/-- **P-57** class "`type=ConditionsMap` with NoOpinion-only lists": decodes to
`noOpinion "only NoOpinion conditions …" nil` (without validation), re-encoded as
`type=NoOpinion`. -- status: does NOT hold -/
theorem P_57_map_noOpinion_only (c : Condition) (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .ConditionsMap (ConditionsMap := some { NoOpinionConditions := [c] })
    enc (dec v fc) ≠ v := by
  intro v h
  have hT : (enc (dec v fc)).«Type» = .NoOpinion := rfl
  rw [h] at hT; cases hT

theorem validateConditions_single_ok {seen s : List String} {x : authorizer.Condition}
    (h : authorizer.validateConditions seen [x] = .ok s) : s = x.ID :: seen := by
  simp only [authorizer.validateConditions] at h
  repeat' split at h
  all_goals simp_all

/-- **P-57** class "cross-list duplicate IDs": the same condition in `denyConditions` and
`allowConditions` decodes to a fail-closed `deny` (either the ID is invalid or it is a
duplicate), re-encoded as `type=Deny`. -- status: does NOT hold -/
theorem P_57_map_cross_list_duplicate (c : Condition) (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .ConditionsMap
      (ConditionsMap := some { DenyConditions := [c], AllowConditions := [c] })
    enc (dec v fc) ≠ v := by
  intro v h
  let c' : authorizer.Condition :=
    { ID := c.ID, Condition := c.Condition, CondType := c.CondType, Description := c.Description }
  have hT : (enc (dec v fc)).«Type» = .Deny := by
    show (enc (authorizer.ConditionsAwareDecisionConditionsMap [c'] [] [c'])).«Type» = .Deny
    unfold authorizer.ConditionsAwareDecisionConditionsMap
    simp only [List.length_cons, List.length_nil, authorizer.MaxConditionsPerMap]
    cases hv : authorizer.validateConditions [] [c'] with
    | error e => simp [FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
        ConditionsAwareDecision.«Type»]
    | ok s =>
      have := validateConditions_single_ok hv
      subst this
      have h2 : authorizer.validateConditions [c'.ID] [] = .ok [c'.ID] := rfl
      have h3 : authorizer.validateConditions [c'.ID] [c'] =
          .error s!"duplicate condition ID {c'.ID}" := by
        simp [authorizer.validateConditions]
      simp [h2, h3, FromAuthorizerConditionsAwareDecision, ConditionsAwareDecision.lit,
        ConditionsAwareDecision.«Type»]
  rw [h] at hT; cases hT

/-- **P-57** class "`type=Union` with empty list": decodes to the folded `noOpinion "" nil`,
re-encoded as `type=NoOpinion`. -- status: does NOT hold -/
theorem P_57_union_empty (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .Union
    enc (dec v fc) ≠ v := by
  intro v h
  have hT : (enc (dec v fc)).«Type» = .NoOpinion := rfl
  rw [h] at hT; cases hT

/-- **P-57** class "unknown `type`": whatever `fc` returns is re-encoded with one of the
five known types. -- status: does NOT hold -/
theorem P_57_unknown_type (s : String) (dn nn an : Option UnconditionalDecision)
    (cm : Option ConditionsMap) (u : List NamedConditionsAwareDecision)
    (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.mk (.unknown s) dn nn an cm u
    enc (dec v fc) ≠ v := by
  intro v h
  exact enc_Type_ne_unknown (dec v fc) s (congrArg ConditionsAwareDecision.«Type» h)

/-- **P-57** class "unconditional type with nil member pointer": re-encoded with a non-nil
empty member. -- status: does NOT hold -/
theorem P_57_unconditional_nil_member (fc : Err → authorizer.ConditionsAwareDecision) :
    let v := ConditionsAwareDecision.lit .Allow
    enc (dec v fc) ≠ v := by
  intro v h
  have hA : (enc (dec v fc)).Allow = some {} := rfl
  rw [h] at hA; cases hA

end v1
