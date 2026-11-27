import K8sAuthz.Spec
import authorizer.evaluate_properties

/-!
# `K8sAuthz.Bridge`: the spec core instantiated with the mirror's real types

`K8sAuthz.Spec` is proved over a generic condition-map type `M`. Here `M` is the mirror's
`authorizer.ConditionsMap` and `toCAD` translates a mirror `ConditionsAwareDecision` into the
spec's decision shape (`CAD ConditionsMap`). Reason/error strings are dropped; names are kept.

Bridge facts (no new axioms, no `sorry`): `pd_cua_toCAD`: the spec's `pd` and `cua` are the
mirror's `PossibleDecisions` and `ContainsUnconditionalAllowOrDeny` for every decision.
-/

namespace K8sAuthz.Bridge

open authorizer K8sAuthz

abbrev CM := authorizer.ConditionsMap

def toDec : authorizer.Decision → Dec
  | .Deny => .deny
  | .Allow => .allow
  | .NoOpinion => .noOp

def toDS (s : DecisionSet) : DS := ⟨s.allow, s.deny, s.noOpinion⟩

mutual
def toCAD : ConditionsAwareDecision → CAD CM
  | .deny _ _ => .un .deny
  | .allow _ _ => .un .allow
  | .noOpinion _ _ => .un .noOp
  | .conditionsMap m => .cond (!m.denyConditions.isEmpty) (!m.allowConditions.isEmpty) m
  | .union l => toCADList l
def toCADList : List (String × ConditionsAwareDecision) → CAD CM
  | [] => .unil
  | (n, c) :: r => .ucons n (toCAD c) (toCADList r)
end

theorem toDS_has (s : DecisionSet) (y : authorizer.Decision) :
    (toDS s).has (toDec y) = s.Has y := by
  cases y <;> rfl

theorem isList_toCADList (l : List (String × ConditionsAwareDecision)) :
    isList (toCADList l) = true := by
  induction l with
  | nil => rfl
  | cons p r ih => obtain ⟨n, c⟩ := p; simp [toCADList, isList, ih]

theorem sub_cua_list (l : List (String × ConditionsAwareDecision))
    (h : ∀ x ∈ l, pd (toCAD x.2) = toDS x.2.PossibleDecisions ∧
          cua (toCAD x.2) = x.2.ContainsUnconditionalAllowOrDeny) :
    (info (toCADList l)).sub = toDS (ConditionsAwareDecision.PossibleDecisions.subPD l) ∧
    (info (toCADList l)).cua = ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go l := by
  induction l with
  | nil =>
    simp [toCADList, info, toDS, DS.empty, ConditionsAwareDecision.PossibleDecisions.subPD,
      DecisionSet.empty, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go]
  | cons p r ihr =>
    obtain ⟨n, c⟩ := p
    have hc := h (n, c) (by simp)
    have hr := ihr (fun x hx => h x (by simp [hx]))
    have e1 : (info (toCAD c)).pd = toDS c.PossibleDecisions := hc.1
    have e2 : (info (toCAD c)).cua = c.ContainsUnconditionalAllowOrDeny := hc.2
    simp only [toCADList, info, hr.1, hr.2, ConditionsAwareDecision.PossibleDecisions.subPD,
      ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go, e1, e2]
    simp [DS.union, toDS, DecisionSet.union]

/-- The spec's `pd` and `cua` are the mirror's `PossibleDecisions` and
`ContainsUnconditionalAllowOrDeny`, for every decision. -/
theorem pd_cua_toCAD (d : ConditionsAwareDecision) :
    pd (toCAD d) = toDS d.PossibleDecisions ∧ cua (toCAD d) = d.ContainsUnconditionalAllowOrDeny := by
  induction d using authorizer.CAD_induct with
  | hdeny r e => simp [toCAD, pd, cua, info, toDS, DS.one, ConditionsAwareDecision.PossibleDecisions,
      DecisionSet.singleton, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]
  | hallow r e => simp [toCAD, pd, cua, info, toDS, DS.one, ConditionsAwareDecision.PossibleDecisions,
      DecisionSet.singleton, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]
  | hnoOp r e => simp [toCAD, pd, cua, info, toDS, DS.one, ConditionsAwareDecision.PossibleDecisions,
      DecisionSet.singleton, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]
  | hmap m =>
    refine ⟨?_, by simp [toCAD, cua, info, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]⟩
    simp only [toCAD, pd, info, toDS, ConditionsAwareDecision.PossibleDecisions,
      authorizer.ConditionsMap.PossibleDecisions, DecisionSet.singleton, DecisionSet.Insert]
    cases h1 : m.allowConditions <;> cases h2 : m.denyConditions <;> simp
  | hunion l ih =>
    have hk := sub_cua_list l ih
    refine ⟨?_, ?_⟩
    · show pd (toCADList l) = _
      cases l with
      | nil => rfl
      | cons p r =>
        obtain ⟨n, c⟩ := p
        have hk' := hk
        simp only [toCADList, info] at hk' ⊢
        simp only [pd, info, hk'.1, hk'.2, ConditionsAwareDecision.PossibleDecisions]
        cases hg : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.go ((n, c) :: r) <;>
          simp [toDS, DS.union, DecisionSet.union, DecisionSet.singleton, DecisionSet.Delete, hg]
    · simp only [toCAD, cua, ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny]
      exact hk.2

theorem FD_toCAD (d : ConditionsAwareDecision) : FD (toCAD d) = toDec d.FailureDecision := by
  unfold FD ConditionsAwareDecision.FailureDecision
  rw [(pd_cua_toCAD d).1]
  by_cases hd : d.PossibleDecisions.deny = true <;> simp [toDS, DecisionSet.Has, hd, toDec]

theorem isUn_toCADList (l : List (String × ConditionsAwareDecision)) : isUn (toCADList l) = false := by
  cases l with
  | nil => rfl
  | cons p r => rfl

theorem isUn_toCAD (d : ConditionsAwareDecision) : isUn (toCAD d) = d.IsUnconditional := by
  cases d with
  | union l => simpa [toCAD, ConditionsAwareDecision.IsUnconditional, ConditionsAwareDecision.IsAllow,
      ConditionsAwareDecision.IsDeny, ConditionsAwareDecision.IsNoOpinion] using isUn_toCADList l
  | _ => rfl

theorem wf_toCADList (l : List (String × ConditionsAwareDecision))
    (h : ∀ x ∈ l, wf (toCAD x.2) = true) : wf (toCADList l) = true := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨n, c⟩ := p
    simp [toCADList, wf, isList_toCADList, h (n, c) (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Mirror `WF` gives the spec's `wf`. -/
theorem wf_toCAD {d : ConditionsAwareDecision} (hw : authorizer.ConditionsAwareDecision.WF d) :
    wf (toCAD d) = true := by
  induction hw with
  | deny => rfl
  | allow => rfl
  | noOpinion => rfl
  | conditionsMap m hm =>
    obtain ⟨_, _, h3, _⟩ := hm
    simp only [toCAD, wf]
    rcases h3 with h | h <;> simp [h, List.isEmpty_iff]
  | union l _ _ _ hc _ _ ih =>
    exact wf_toCADList l (fun x hx => ih x hx)

/-- Mirror `WF` gives the spec's `good` (uses P-6). -/
theorem good_toCAD {d : ConditionsAwareDecision} (hw : authorizer.ConditionsAwareDecision.WF d) :
    good (toCAD d) = true := by
  have hwf := wf_toCAD hw
  unfold good
  rw [hwf, Bool.true_and, isUn_toCAD]
  cases hu : d.IsUnconditional with
  | true => rfl
  | false =>
    have hna : d.IsAllow = false := by
      cases d <;> simp_all [ConditionsAwareDecision.IsUnconditional, ConditionsAwareDecision.IsAllow,
        ConditionsAwareDecision.IsDeny, ConditionsAwareDecision.IsNoOpinion]
    have h := authorizer.ConditionsAwareDecision.P_6_failureDecision_mem_WF hw hna
    rw [FD_toCAD, (pd_cua_toCAD d).1]
    simpa [toDS_has] using h

/-- The oracle on condition maps induced by an oracle on conditions. -/
def mapOracle (o : MaybeEvaluateConditionFunc) : CM → Dec :=
  fun m => toDec (refSem o (.conditionsMap m))

theorem sem_toCADList (o : MaybeEvaluateConditionFunc) (l : List (String × ConditionsAwareDecision))
    (h : ∀ x ∈ l, sem (mapOracle o) (toCAD x.2) = toDec (refSem o x.2)) :
    sem (mapOracle o) (toCADList l) = toDec (refSem.seq o l) := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨n, c⟩ := p
    have hc := h (n, c) (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    rw [authorizer.refSem_seq_cons]
    simp only [toCADList, sem, hc, hr]
    cases hx : refSem o c <;> simp [toDec]

/-- The spec's reference fold is the mirror's `refSem` for a total oracle. -/
theorem sem_toCAD {o : MaybeEvaluateConditionFunc} (ho : o.Total) (d : ConditionsAwareDecision) :
    sem (mapOracle o) (toCAD d) = toDec (refSem o d) := by
  induction d using authorizer.CAD_induct with
  | hdeny r e => rfl
  | hallow r e => rfl
  | hnoOp r e => rfl
  | hmap m =>
    have hmem := authorizer.P_37_refSem_mem_PD ho (.conditionsMap m)
    have hp := (pd_cua_toCAD (.conditionsMap m)).1
    have hp2 := toDS_has (ConditionsAwareDecision.conditionsMap m).PossibleDecisions (refSem o (.conditionsMap m))
    rw [← hp, hmem] at hp2
    simp only [toCAD, sem, mapOracle]
    revert hp2
    generalize refSem o (.conditionsMap m) = r
    intro hp2
    simp only [toCAD, pd, info] at hp2
    cases r <;> simp_all [toDec, clamp, DS.has]
  | hunion l ih =>
    rw [authorizer.refSem_union]
    exact sem_toCADList o l ih

end K8sAuthz.Bridge
