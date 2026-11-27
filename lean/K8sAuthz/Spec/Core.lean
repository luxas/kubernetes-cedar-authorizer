/-! Toy model of ConditionsAwareDecision (Lean core only). Union = cons-list of (name, child). -/
namespace K8sAuthz

variable {M : Type}

inductive Dec | allow | deny | noOp deriving DecidableEq, Repr

structure DS where
  a : Bool
  d : Bool
  n : Bool
  deriving DecidableEq, Repr

def DS.has (s : DS) : Dec → Bool | .allow => s.a | .deny => s.d | .noOp => s.n
def DS.one : Dec → DS
  | .allow => ⟨true, false, false⟩ | .deny => ⟨false, true, false⟩ | .noOp => ⟨false, false, true⟩
def DS.union (s t : DS) : DS := ⟨s.a || t.a, s.d || t.d, s.n || t.n⟩
def DS.empty : DS := ⟨false, false, false⟩
def DS.theOnly (s : DS) : Option Dec :=
  match s.a, s.d, s.n with
  | true, false, false => some .allow
  | false, true, false => some .deny
  | false, false, true => some .noOp
  | _, _, _ => none

inductive CAD (M : Type) where
  | un (d : Dec)                          -- unconditional decision
  | cond (hd ha : Bool) (m : M)         -- a ConditionsMap: has Deny / Allow conditions
  | unil                                  -- empty union list
  | ucons (n : String) (c : CAD M) (r : CAD M) -- union = (name, child) :: rest
  deriving DecidableEq, Repr

structure Info where
  pd  : DS      -- PossibleDecisions
  sub : DS      -- union of children PDs (list tails)
  cua : Bool    -- ContainsUnconditionalAllowOrDeny

def info : CAD M → Info
  | .un d => ⟨DS.one d, DS.empty, d != .noOp⟩
  | .cond hd ha _ => ⟨⟨ha, hd, true⟩, DS.empty, false⟩
  | .unil => ⟨DS.one .noOp, DS.empty, false⟩
  | .ucons _ c r =>
    let ic := info c
    let ir := info r
    let sub := ic.pd.union ir.sub
    let cua := ic.cua || ir.cua
    ⟨⟨sub.a, sub.d, !cua⟩, sub, cua⟩

def pd (x : CAD M) : DS := (info x).pd
def cua (x : CAD M) : Bool := (info x).cua
def isUn : CAD M → Bool | .un _ => true | _ => false
def FD (x : CAD M) : Dec := if (pd x).d then .deny else .noOp
/-- the plan's `FoldDown` -/
def foldDown : CAD M → Dec | .un d => d | x => FD x

/-- builder invariants (the plan's L1 `WF`) -/
def isList : CAD M → Bool | .unil => true | .ucons _ _ r => isList r | _ => false
def wf : CAD M → Bool
  | .un _ => true
  | .cond hd ha _ => hd || ha
  | .unil => true
  | .ucons _ c r => wf c && isList r && wf r

def clamp (hd ha : Bool) : Dec → Dec
  | .deny => if hd then .deny else .noOp
  | .allow => if ha then .allow else .noOp
  | .noOp => .noOp

/-- reference semantics of a tree under a (total) oracle on condition ids -/
def sem (t : M → Dec) : CAD M → Dec
  | .un d => d
  | .cond hd ha m => clamp hd ha (t m)
  | .unil => .noOp
  | .ucons _ c r => if sem t c = .noOp then sem t r else sem t c

theorem has_one (d e : Dec) : (DS.one d).has e = decide (d = e) := by
  cases d <;> cases e <;> rfl

theorem cua_sem (t : M → Dec) : ∀ x : CAD M, wf x = true → cua x = true → sem t x ≠ .noOp := by
  intro x
  induction x with
  | un d => intro _ h; cases d <;> simp [cua, info] at h ⊢ <;> simp [sem]
  | cond hd ha m => intro _ h; simp [cua, info] at h
  | unil => intro _ h; simp [cua, info] at h
  | ucons n c r ihc ihr =>
    intro hw h
    simp [wf] at hw
    simp [cua, info] at h
    simp only [sem]
    by_cases hc : sem t c = .noOp
    · simp [hc]
      rcases h with h | h
      · exact absurd hc (ihc hw.1.1 (by simpa [cua] using h))
      · exact ihr hw.2 (by simpa [cua] using h)
    · simp [hc]

theorem pd_list : ∀ r : CAD M, isList r = true →
    pd r = ⟨(info r).sub.a, (info r).sub.d, !(info r).cua⟩ := by
  intro r
  induction r with
  | un d => intro h; simp [isList] at h
  | cond _ _ _ => intro h; simp [isList] at h
  | unil => intro _; simp [pd, info, DS.one, DS.empty]
  | ucons n c r _ ihr => intro _; simp [pd, info]

/-- P-37 soundness of PossibleDecisions (for well-formed trees) -/
theorem sem_mem (t : M → Dec) : ∀ x : CAD M, wf x = true → (pd x).has (sem t x) = true := by
  intro x
  induction x with
  | un d => intro _; cases d <;> simp [pd, info, sem, DS.has, DS.one]
  | cond hd ha m =>
    intro hw; simp [wf] at hw
    cases h : t m <;> cases hd <;> cases ha <;> simp_all [pd, info, sem, clamp, DS.has]
  | unil => intro _; simp [pd, info, sem, DS.has, DS.one]
  | ucons n c r ihc ihr =>
    intro hw
    simp only [wf, Bool.and_eq_true] at hw
    have h1 := ihc hw.1.1
    have h2 := ihr hw.2
    have e := pd_list r hw.1.2
    by_cases hc : sem t c = .noOp
    · have hnc : cua c = false := by
        cases h : cua c
        · rfl
        · exact absurd hc (cua_sem t c hw.1.1 h)
      have hsem : sem t (CAD.ucons n c r) = sem t r := by simp [sem, hc]
      rw [hsem]
      rw [e] at h2
      have hc' : (info c).cua = false := hnc
      simp only [pd, info, hc', Bool.false_or]
      generalize sem t r = v at h2 ⊢
      cases v <;> simp_all [DS.has, DS.union]
    · have hsem : sem t (CAD.ucons n c r) = sem t c := by simp [sem, hc]
      rw [hsem]
      simp only [pd, info]
      generalize hv : sem t c = v at h1 hc ⊢
      cases v <;> simp_all [DS.has, DS.union, pd]


/-! ## Partial evaluation as agreeing steps; `Refines` -/

theorem theOnly_has {s : DS} {d e : Dec} (h : s.theOnly = some d) (he : s.has e = true) : e = d := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all [DS.theOnly, DS.has]

inductive Step (o : M → Dec) : CAD M → CAD M → Prop
  /-- a map is fully evaluated under the oracle -/
  | resolve (hd ha : Bool) (m : M) : Step o (.cond hd ha m) (.un (clamp hd ha (o m)))
  /-- a map is replaced by a smaller map with the same reference value (Go: the unevaluated
  conditions are re-wrapped by `ConditionsAwareDecisionConditionsMap`; its possible effects
  can only shrink) -/
  | shrink (hd ha : Bool) (m : M) (hd' ha' : Bool) (m' : M) :
      (hd' || ha') = true → (hd' = true → hd = true) → (ha' = true → ha = true) →
      clamp hd' ha' (o m') = clamp hd ha (o m) →
      Step o (.cond hd ha m) (.cond hd' ha' m')
  /-- the tail of a union after a child that contains an unconditional Allow/Deny is dropped
  (Go: `chain.ToDecision()` right after `Add` of such a child) -/
  | trunc {n c r} : cua c = true → Step o (.ucons n c r) (.ucons n c .unil)
  | head {n c c' r} : Step o c c' → Step o (.ucons n c r) (.ucons n c' r)
  | tail {n c r r'} : Step o r r' → isList r' = true → Step o (.ucons n c r) (.ucons n c r')
  | norm {x d} : isUn x = false → (pd x).theOnly = some d → Step o x (.un d)

inductive Steps (o : M → Dec) : CAD M → CAD M → Prop
  | refl (x) : Steps o x x
  | cons {x y z} : Step o x y → Steps o y z → Steps o x z

/-- `Refines o x y`: `x` is obtained from `y` by agreeing partial evaluation under oracle `o`.
Reflexive-transitive by construction. -/
def Refines (o : M → Dec) (x y : CAD M) : Prop := Steps o y x

theorem Steps.trans {o : M → Dec} {x y z : CAD M} (h1 : Steps o x y) (h2 : Steps o y z) : Steps o x z := by
  induction h1 with
  | refl _ => exact h2
  | cons s _ ih => exact .cons s (ih h2)

/-- **A-3 (transitivity part): refining a refinement is a refinement.** Trivial: it is transitivity. -/
theorem refinement_closed {o : M → Dec} {x y z : CAD M} (h1 : Refines o x y) (h2 : Refines o y z) : Refines o x z :=
  Steps.trans h2 h1

theorem step_sem {o : M → Dec} {x y : CAD M} (h : Step o x y) :
    wf x = true → wf y = true ∧ sem o y = sem o x := by
  induction h with
  | resolve hd ha m => intro _; simp [wf, sem]
  | shrink hd ha m hd' ha' m' h1 _ _ h4 => intro _; exact ⟨by simpa [wf] using h1, by simp [sem, h4]⟩
  | trunc hc =>
    intro hw
    rename_i n c r
    simp only [wf, Bool.and_eq_true] at hw
    refine ⟨by simp [wf, isList, hw.1.1], ?_⟩
    have := cua_sem o c hw.1.1 hc
    simp [sem, this]
  | head hs ih =>
    intro hw
    simp only [wf, Bool.and_eq_true] at hw
    obtain ⟨h1, h2⟩ := ih hw.1.1
    simp only [wf, Bool.and_eq_true]
    refine ⟨⟨⟨h1, hw.1.2⟩, hw.2⟩, ?_⟩
    simp [sem, h2]
  | tail hs hl ih =>
    intro hw
    simp only [wf, Bool.and_eq_true] at hw
    obtain ⟨h1, h2⟩ := ih hw.2
    simp only [wf, Bool.and_eq_true]
    refine ⟨⟨⟨hw.1.1, hl⟩, h1⟩, ?_⟩
    simp [sem, h2]
  | norm hu ho =>
    intro hw
    rename_i x d
    refine ⟨rfl, ?_⟩
    exact (theOnly_has ho (sem_mem o x hw)).symm

/-- **P-27 / P-28 in the toy:** refinement preserves `sem` and `wf`. -/
theorem refines_sem {o : M → Dec} {x y : CAD M} (h : Refines o x y) :
    wf y = true → wf x = true ∧ sem o x = sem o y := by
  unfold Refines at h
  induction h with
  | refl _ => intro hw; exact ⟨hw, rfl⟩
  | cons s _ ih =>
    intro hw
    obtain ⟨h1, h2⟩ := step_sem s hw
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, h4.trans h2⟩



/-! ## Small facts about decisions and `good` -/

/-- Order `Deny < NoOpinion < Allow` (PLAN 3.1, clause S2). -/
def Dec.rank : Dec → Nat | .deny => 0 | .noOp => 1 | .allow => 2

/-- First non-`NoOpinion` of two decisions (the union fold). -/
def firstNo (x y : Dec) : Dec := if x = .noOp then y else x

/-- `good x`: `WF x` together with `FailureDecision x ∈ PossibleDecisions x` for conditional `x`
(PLAN 3.1; mirror `P_44_needs_child_WF`). -/
def good (x : CAD M) : Bool := wf x && (isUn x || (pd x).has (FD x))

theorem good_FD {x : CAD M} (h : good x = true) (hu : isUn x = false) : (pd x).has (FD x) = true := by
  simp [good, hu] at h; exact h.2

theorem FD_ne_allow (x : CAD M) : FD x ≠ .allow := by
  unfold FD; split <;> simp

theorem good_wf {x : CAD M} (h : good x = true) : wf x = true := by
  simp [good] at h; exact h.1

end K8sAuthz
