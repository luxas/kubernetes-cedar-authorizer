/-! Toy model of ConditionsAwareDecision (Lean core only). Union = cons-list of (name, child). -/
namespace K

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

inductive CAD
  | un (d : Dec)                          -- unconditional decision
  | cond (hd ha : Bool) (id : Nat)        -- a ConditionsMap: has Deny / Allow conditions
  | unil                                  -- empty union list
  | ucons (n : String) (c : CAD) (r : CAD) -- union = (name, child) :: rest
  deriving DecidableEq, Repr

structure Info where
  pd  : DS      -- PossibleDecisions
  sub : DS      -- union of children PDs (list tails)
  cua : Bool    -- ContainsUnconditionalAllowOrDeny

def info : CAD → Info
  | .un d => ⟨DS.one d, DS.empty, d != .noOp⟩
  | .cond hd ha _ => ⟨⟨ha, hd, true⟩, DS.empty, false⟩
  | .unil => ⟨DS.one .noOp, DS.empty, false⟩
  | .ucons _ c r =>
    let ic := info c
    let ir := info r
    let sub := ic.pd.union ir.sub
    let cua := ic.cua || ir.cua
    ⟨⟨sub.a, sub.d, !cua⟩, sub, cua⟩

def pd (x : CAD) : DS := (info x).pd
def cua (x : CAD) : Bool := (info x).cua
def isUn : CAD → Bool | .un _ => true | _ => false
def FD (x : CAD) : Dec := if (pd x).d then .deny else .noOp
/-- the plan's `FoldDown` -/
def foldDown : CAD → Dec | .un d => d | x => FD x

/-- builder invariants (the plan's L1 `WF`) -/
def isList : CAD → Bool | .unil => true | .ucons _ _ r => isList r | _ => false
def wf : CAD → Bool
  | .un _ => true
  | .cond hd ha _ => hd || ha
  | .unil => true
  | .ucons _ c r => wf c && isList r && wf r

def clamp (hd ha : Bool) : Dec → Dec
  | .deny => if hd then .deny else .noOp
  | .allow => if ha then .allow else .noOp
  | .noOp => .noOp

/-- reference semantics of a tree under a (total) oracle on condition ids -/
def sem (t : Nat → Dec) : CAD → Dec
  | .un d => d
  | .cond hd ha id => clamp hd ha (t id)
  | .unil => .noOp
  | .ucons _ c r => if sem t c = .noOp then sem t r else sem t c

theorem has_one (d e : Dec) : (DS.one d).has e = decide (d = e) := by
  cases d <;> cases e <;> rfl

theorem cua_sem (t : Nat → Dec) : ∀ x : CAD, wf x = true → cua x = true → sem t x ≠ .noOp := by
  intro x
  induction x with
  | un d => intro _ h; cases d <;> simp [cua, info] at h ⊢ <;> simp [sem]
  | cond hd ha id => intro _ h; simp [cua, info] at h
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

theorem pd_list : ∀ r : CAD, isList r = true →
    pd r = ⟨(info r).sub.a, (info r).sub.d, !(info r).cua⟩ := by
  intro r
  induction r with
  | un d => intro h; simp [isList] at h
  | cond _ _ _ => intro h; simp [isList] at h
  | unil => intro _; simp [pd, info, DS.one, DS.empty]
  | ucons n c r _ ihr => intro _; simp [pd, info]

/-- P-37 soundness of PossibleDecisions (for well-formed trees) -/
theorem sem_mem (t : Nat → Dec) : ∀ x : CAD, wf x = true → (pd x).has (sem t x) = true := by
  intro x
  induction x with
  | un d => intro _; cases d <;> simp [pd, info, sem, DS.has, DS.one]
  | cond hd ha id =>
    intro hw; simp [wf] at hw
    cases h : t id <;> cases hd <;> cases ha <;> simp_all [pd, info, sem, clamp, DS.has]
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

inductive Step (o : Nat → Dec) : CAD → CAD → Prop
  | resolve (hd ha : Bool) (id : Nat) : Step o (.cond hd ha id) (.un (clamp hd ha (o id)))
  | head {n c c' r} : Step o c c' → Step o (.ucons n c r) (.ucons n c' r)
  | tail {n c r r'} : Step o r r' → isList r' = true → Step o (.ucons n c r) (.ucons n c r')
  | norm {x d} : isUn x = false → (pd x).theOnly = some d → Step o x (.un d)

inductive Steps (o : Nat → Dec) : CAD → CAD → Prop
  | refl (x) : Steps o x x
  | cons {x y z} : Step o x y → Steps o y z → Steps o x z

/-- `Refines o x y`: `x` is obtained from `y` by agreeing partial evaluation under oracle `o`.
Reflexive-transitive by construction. -/
def Refines (o : Nat → Dec) (x y : CAD) : Prop := Steps o y x

theorem Steps.trans {o x y z} (h1 : Steps o x y) (h2 : Steps o y z) : Steps o x z := by
  induction h1 with
  | refl _ => exact h2
  | cons s _ ih => exact .cons s (ih h2)

/-- **A-3 (as stated): refining a refinement is a refinement.** Trivial: it is transitivity. -/
theorem refinement_closed {o x y z} (h1 : Refines o x y) (h2 : Refines o y z) : Refines o x z :=
  Steps.trans h2 h1

theorem step_sem {o : Nat → Dec} {x y : CAD} (h : Step o x y) :
    wf x = true → wf y = true ∧ sem o y = sem o x := by
  induction h with
  | resolve hd ha id => intro _; simp [wf, sem]
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
theorem refines_sem {o : Nat → Dec} {x y : CAD} (h : Refines o x y) :
    wf y = true → wf x = true ∧ sem o x = sem o y := by
  unfold Refines at h
  induction h with
  | refl _ => intro hw; exact ⟨hw, rfl⟩
  | cons s _ ih =>
    intro hw
    obtain ⟨h1, h2⟩ := step_sem s hw
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, h4.trans h2⟩


/-! ## World / Authorizer / Lawful / Guarded: the plan's definitions, literally -/

structure World where
  Attrs : Type
  Data : Type
  Consistent : Attrs → Data → Prop
  /-- NOT in the plan: the instance's own meaning of each condition on concrete data.
  Needed to define `Refines` ("an oracle that agrees with `full`"). -/
  truth : Data → Nat → Dec

structure Authorizer (W : World) where
  name : String
  authorize : W.Attrs → Dec            -- `.1` of the triple (reason / error projected away)
  caa : W.Attrs → CAD
  eval : CAD → W.Data → Dec

/-- PLAN section 3.1, L1-L5 as written. `Refines` is quantified over "an oracle that agrees with
`full`", read literally as `sem o (caa a) = full a d`. -/
structure LawfulPlan {W : World} (full : W.Attrs → W.Data → Dec) (A : Authorizer W) : Prop where
  L1 : ∀ a, wf (A.caa a) = true
  L2 : ∀ a, A.authorize a = foldDown (A.caa a)
  L3 : ∀ a d, W.Consistent a d → (pd (A.caa a)).has (full a d) = true
  L4 : ∀ a d, W.Consistent a d → ∀ o, sem o (A.caa a) = full a d →
         ∀ x, Refines o x (A.caa a) → A.eval x d = full a d
  L5 : ∀ a d, W.Consistent a d → isUn (A.caa a) = true → foldDown (A.caa a) = full a d

/-- PLAN G1, G2 as written (unconditional input -> Deny). -/
structure GuardedPlan {W : World} (A : Authorizer W) : Prop where
  G1c : ∀ x d, isUn x = false → (pd x).has (A.eval x d) = true
  G1u : ∀ x d, isUn x = true → A.eval x d = .deny
  G2  : ∀ x d, A.eval x d = .allow → (pd x).has .allow = true

/-- **FINDING 1.** `LawfulPlan` (via L4 at the reflexive refinement `x = caa a`) and `GuardedPlan`
(G1 unconditional clause) contradict each other as soon as some consistent `(a,d)` has an
unconditional non-Deny `full`. In particular A-8 (i) "always-NoOpinion is Lawful and Guarded"
is false. -/
theorem plan_lawful_guarded_clash {W : World} (full : W.Attrs → W.Data → Dec) (A : Authorizer W)
    (hL : LawfulPlan full A) (hG : GuardedPlan A) (a : W.Attrs) (d : W.Data)
    (hc : W.Consistent a d) (hu : isUn (A.caa a) = true) : full a d = .deny := by
  have h5 := hL.L5 a d hc hu
  have hsem : sem (fun _ => full a d) (A.caa a) = full a d := by
    revert hu h5; generalize A.caa a = x
    cases x <;> simp [isUn, foldDown, sem]
  have h4 := hL.L4 a d hc (fun _ => full a d) hsem (A.caa a) (Steps.refl _)
  rw [hG.G1u (A.caa a) d hu] at h4
  exact h4.symm

/-- counterexample world for A-8(i): one attribute, one datum, full = NoOpinion. -/
def W0 : World where
  Attrs := Unit
  Data := Unit
  Consistent _ _ := True
  truth _ _ := .noOp

def full0 : W0.Attrs → W0.Data → Dec := fun _ _ => .noOp

def A0 : Authorizer W0 where
  name := "never"
  authorize _ := .noOp
  caa _ := .un .noOp
  eval x _ := foldDown x

theorem A0_not_both : ¬ (LawfulPlan full0 A0 ∧ GuardedPlan A0) := by
  intro ⟨hL, hG⟩
  have := plan_lawful_guarded_clash full0 A0 hL hG () () trivial rfl
  exact absurd this (by decide)

/-- **FINDING 2.** `L4` with "any oracle agreeing with `full` at the root" is false for an authorizer
that evaluates with the *true* semantics of its conditions: two allow-conditions, truth (T,F), a
fake oracle (F,T) agrees at the root, refinement under the fake oracle then evaluates to NoOpinion. -/
def W1 : World where
  Attrs := Unit
  Data := Unit
  Consistent _ _ := True
  truth _ id := if id = 1 then .allow else .noOp

def full1 : W1.Attrs → W1.Data → Dec := fun _ _ => .allow

def dec2 : CAD := .ucons "a" (.cond false true 1) (.ucons "b" (.cond false true 2) .unil)

def A1 : Authorizer W1 where
  name := "two"
  authorize _ := .noOp
  caa _ := dec2
  eval x d := sem (W1.truth d) x          -- the natural, truthful evaluator

theorem L4_literal_false : ¬ (∀ o, sem o dec2 = full1 () () →
    ∀ x, Refines o x dec2 → A1.eval x () = full1 () ()) := by
  intro h
  let o : Nat → Dec := fun id => if id = 1 then .noOp else .allow
  have hs : sem o dec2 = full1 () () := by decide
  let x : CAD := .ucons "a" (.un .noOp) (.ucons "b" (.cond false true 2) .unil)
  have hr : Refines o x dec2 :=
    Steps.cons (Step.head (Step.resolve false true 1)) (Steps.refl _)
  have := h o hs x hr
  revert this; decide

/-! ## Proposed replacement: `Lawful*` -/

def good (x : CAD) : Bool := wf x && (isUn x || (pd x).has (FD x))

structure Lawful {W : World} (full : W.Attrs → W.Data → Dec) (A : Authorizer W) : Prop where
  L1 : ∀ a, good (A.caa a) = true
  L2 : ∀ a, A.authorize a = foldDown (A.caa a)
  /-- L3*: agreement with the reference semantics (implies the plan's L3, L5 and soundness) -/
  L3 : ∀ a d, W.Consistent a d → full a d = sem (W.truth d) (A.caa a)
  /-- L4*: only conditional refinements, refinement relative to the TRUE oracle -/
  L4 : ∀ a d, W.Consistent a d → ∀ x, isUn x = false →
         Refines (W.truth d) x (A.caa a) → A.eval x d = full a d

structure Guarded {W : World} (A : Authorizer W) : Prop where
  G1c : ∀ x d, isUn x = false → good x = true → (pd x).has (A.eval x d) = true
  G1u : ∀ x d, isUn x = true → A.eval x d = FD x
  G2  : ∀ x d, A.eval x d = .allow → (pd x).has .allow = true

def guard {W : World} (A : Authorizer W) : Authorizer W :=
  { A with eval := fun x d =>
      if isUn x then FD x else
      let r := A.eval x d
      if (pd x).has r then r else FD x }

theorem good_FD {x : CAD} (h : good x = true) (hu : isUn x = false) : (pd x).has (FD x) = true := by
  simp [good, hu] at h; exact h.2

theorem FD_ne_allow (x : CAD) : FD x ≠ .allow := by
  unfold FD; split <;> simp

/-- **A-2 (closed)**: `guard A` is `Guarded` for every `A`; G1 needs `good x` (see Finding 4). -/
theorem guard_guarded {W : World} (A : Authorizer W) : Guarded (guard A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x d hu hg
    simp only [guard, hu, Bool.false_eq_true, ite_false]
    split
    · assumption
    · exact good_FD hg hu
  · intro x d hu; simp [guard, hu]
  · intro x d h
    simp only [guard] at h
    split at h
    · exact absurd h (FD_ne_allow x)
    · split at h
      · rename_i hp; rw [h] at hp; exact hp
      · exact absurd h (FD_ne_allow x)

/-- **FINDING 4**: G1 as written ("for all x") is false for every possible clamp: a union with an
unconditional Allow leaf has PD = {Allow}, but its FailureDecision is NoOpinion. -/
theorem G1_needs_good : ∃ x : CAD, wf x = true ∧ isUn x = false ∧ (pd x).has (FD x) = false :=
  ⟨.ucons "p" (.un .allow) .unil, by decide, by decide, by decide⟩

/-- **A-2 (inert)**. Needs L3* (not the plan's L3) to know `full ∈ PD x` for the refinement `x`. -/
theorem guard_inert {W : World} {full : W.Attrs → W.Data → Dec} (A : Authorizer W) (hL : Lawful full A) (a : W.Attrs) (d : W.Data)
    (hc : W.Consistent a d) (x : CAD) (hx : isUn x = false)
    (hr : Refines (W.truth d) x (A.caa a)) : (guard A).eval x d = A.eval x d := by
  have hwf : wf (A.caa a) = true := by have := hL.L1 a; simp [good] at this; exact this.1
  obtain ⟨hwx, hsx⟩ := refines_sem hr hwf
  have h4 := hL.L4 a d hc x hx hr
  have hmem := sem_mem (W.truth d) x hwx
  rw [hsx, ← hL.L3 a d hc] at hmem
  simp only [guard, hx, Bool.false_eq_true, ite_false]
  rw [h4]; simp [hmem]

theorem guard_lawful {W : World} {full : W.Attrs → W.Data → Dec} (A : Authorizer W) (hL : Lawful full A) : Lawful full (guard A) :=
  ⟨hL.L1, hL.L2, hL.L3, fun a d hc x hx hr => by
    rw [guard_inert A hL a d hc x hx hr]; exact hL.L4 a d hc x hx hr⟩

/-- A-3b: if `eval` is the natural evaluator, L4* follows from L1-L3* (this is P-27 for the toy). -/
theorem natural_L4 {W : World} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hn : ∀ x d, isUn x = false → A.eval x d = sem (W.truth d) x)
    (h1 : ∀ a, good (A.caa a) = true)
    (h3 : ∀ a d, W.Consistent a d → full a d = sem (W.truth d) (A.caa a)) :
    ∀ a d, W.Consistent a d → ∀ x, isUn x = false → Refines (W.truth d) x (A.caa a) →
      A.eval x d = full a d := by
  intro a d hc x hx hr
  have hwf : wf (A.caa a) = true := by have := h1 a; simp [good] at this; exact this.1
  obtain ⟨_, hsx⟩ := refines_sem hr hwf
  rw [hn x d hx, hsx, h3 a d hc]

/-! ## A-8: non-vacuity of the corrected contract -/

def W2 : World where
  Attrs := Option Bool
  Data := Bool
  Consistent a d := a = none ∨ a = some d
  truth := fun (d : Bool) _ => if d then .allow else .noOp

def full2 : W2.Attrs → W2.Data → Dec := fun _ (d : Bool) => if d then .allow else .noOp

def A2 : Authorizer W2 where
  name := "toy"
  authorize a := match a with | some true => .allow | _ => .noOp
  caa a := match a with
    | some true => .un .allow
    | some false => .un .noOp
    | none => .cond false true 7
  eval x d := if isUn x then foldDown x else sem (W2.truth d) x

theorem A2_lawful : Lawful full2 A2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a; cases a with
    | none => decide
    | some b => cases b <;> decide
  · intro a; cases a with
    | none => decide
    | some b => cases b <;> decide
  · intro a d hc
    rcases hc with h | h
    · subst h; cases d <;> decide
    · subst h; cases d <;> decide
  · intro a d hc x hx hr
    exact natural_L4 A2 (fun x d hx => by simp [A2, hx])
      (by intro a; cases a with | none => decide | some b => cases b <;> decide)
      (by intro a d hc; rcases hc with h | h <;> subst h <;> (try cases d) <;> (try (rename_i b; cases b)) <;> decide) a d hc x hx hr

theorem A2_guarded : Guarded (guard A2) := guard_guarded A2

/-- `Consistent` is neither empty nor total, and `Attrs` knows less than `Data`. -/
theorem W2_consistent_nontrivial :
    W2.Consistent none true ∧ W2.Consistent (some true) true ∧ ¬ W2.Consistent (some true) false := by
  refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
  intro h; rcases h with h | h <;> simp at h

/-- always-NoOpinion: Lawful* and (corrected) Guarded, but not (plan Lawful ∧ plan Guarded) -/
def A3 : Authorizer W0 := A0
theorem steps_un {o : Nat → Dec} {d : Dec} {x y : CAD} (h : Steps o x y) : x = .un d → y = .un d := by
  induction h with
  | refl => exact id
  | cons s _ ih =>
    intro hz; subst hz
    cases s with
    | norm hu _ => simp [isUn] at hu

theorem A0_lawful : Lawful full0 A0 := by
  refine ⟨fun _ => rfl, fun _ => rfl, by intro a d _; rfl, ?_⟩
  intro a d _ x hx hr
  have := steps_un hr rfl
  subst this; simp [isUn] at hx


/-! ## A-1: the two-member union authorizer -/

def build (ok : Bool) (u : CAD) : CAD :=
  if !ok then .un (FD u) else
  match (pd u).theOnly with
  | some d => .un d
  | none => u

def namesOk {W : World} (A B : Authorizer W) : Bool :=
  A.name != "" && B.name != "" && A.name != B.name

/-- evaluation walk (`union.go:144-185`): leaves are returned as is; conditional children are routed
by name and clamped into their own PossibleDecisions. -/
def leaf (route : String → CAD → Dec) (n : String) : CAD → Dec
  | .un d => d
  | c => let q := route n c; if (pd c).has q then q else FD c

def evalL (route : String → CAD → Dec) : CAD → Dec
  | .ucons n c r =>
    let v := leaf route n c
    if v = .noOp then evalL route r else v
  | _ => .noOp

def route {W : World} (A B : Authorizer W) (d : W.Data) (n : String) (c : CAD) : Dec :=
  if n == A.name then A.eval c d else if n == B.name then B.eval c d else FD c

def chain2 {W : World} (A B : Authorizer W) : Authorizer W where
  name := "chain"
  authorize a := if A.authorize a = .noOp then B.authorize a else A.authorize a
  caa a :=
    let xa := A.caa a
    if cua xa then build (namesOk A B) (.ucons A.name xa .unil)
    else build (namesOk A B) (.ucons A.name xa (.ucons B.name (B.caa a) .unil))
  eval x d := match x with
    | .ucons _ _ _ => evalL (route A B d) x
    | _ => FD x                      -- non-union input: fail closed (`union.go:134-136`)

def chainFull {W : World} (fA fB : W.Attrs → W.Data → Dec) : W.Attrs → W.Data → Dec :=
  fun a d => if fA a d = .noOp then fB a d else fA a d

/-! ### facts about good decisions -/

theorem fold_allow {x : CAD} (h : foldDown x = .allow) : x = .un .allow := by
  cases x with
  | un d => simpa [foldDown] using h
  | cond hd ha id => exact absurd h (FD_ne_allow _)
  | unil => exact absurd h (FD_ne_allow _)
  | ucons n c r => exact absurd h (FD_ne_allow _)

theorem fold_deny {x : CAD} (h : foldDown x = .deny) : (pd x).d = true := by
  cases x with
  | un d => cases d <;> simp_all [foldDown, pd, info, DS.one]
  | cond hd ha id => simp only [foldDown, FD] at h; split at h <;> simp_all
  | unil => simp only [foldDown, FD] at h; split at h <;> simp_all
  | ucons n c r => simp only [foldDown, FD] at h; split at h <;> simp_all

theorem n_not_cua {x : CAD} (h : (pd x).n = true) (hu : isUn x = false) : cua x = false := by
  cases x with
  | un d => simp [isUn] at hu
  | cond hd ha id => rfl
  | unil => rfl
  | ucons n c r => simp [pd, info, cua] at h ⊢; exact h

theorem fold_noOp {x : CAD} (hg : good x = true) (h : foldDown x = .noOp) :
    (pd x).d = false ∧ cua x = false := by
  cases hu : isUn x with
  | true =>
    cases x with
    | un d => cases d <;> simp_all [foldDown, pd, info, cua, DS.one]
    | cond _ _ _ => simp [isUn] at hu
    | unil => simp [isUn] at hu
    | ucons _ _ _ => simp [isUn] at hu
  | false =>
    have h1 : foldDown x = FD x := by cases x <;> simp_all [isUn, foldDown]
    rw [h1] at h
    have hd : (pd x).d = false := by
      unfold FD at h; split at h <;> simp_all
    have hh := good_FD hg hu
    rw [h] at hh
    exact ⟨hd, n_not_cua hh hu⟩

theorem un_facts {d : Dec} : pd (.un d) = DS.one d ∧ cua (.un d) = (d != .noOp) := ⟨rfl, rfl⟩


theorem build_fold (u : CAD) (hu : isUn u = false) :
    foldDown (build true u) =
      (if (pd u).d = true then .deny else if (pd u).a = true ∧ (pd u).n = false then .allow else .noOp) := by
  have hfd : foldDown u = if (pd u).d = true then Dec.deny else Dec.noOp := by
    cases u <;> simp_all [isUn, foldDown, FD]
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  revert hfd
  generalize pd u = s
  rcases s with ⟨a, d, n⟩
  cases a <;> cases d <;> cases n <;> simp [DS.theOnly, foldDown]

theorem ucons_isUn (n c r) : isUn (CAD.ucons n c r) = false := rfl

/-- **A-1, clause L2** for a two-member chain (decision part). Needs: members `good`, names ok. -/
theorem chain_L2 {W : World} (A B : Authorizer W) (hn : namesOk A B = true) (a : W.Attrs)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true)
    (h2A : A.authorize a = foldDown (A.caa a)) (h2B : B.authorize a = foldDown (B.caa a)) :
    (chain2 A B).authorize a = foldDown ((chain2 A B).caa a) := by
  simp only [chain2, hn]
  rw [h2A, h2B]
  generalize A.caa a = xa at *
  generalize B.caa a = xb at *
  have fa := fold_allow (x := xa)
  have da := fold_deny (x := xa)
  have na := fold_noOp hA (x := xa)
  have fb := fold_allow (x := xb)
  have db := fold_deny (x := xb)
  have nb := fold_noOp hB (x := xb)
  simp only [pd, cua] at da na db nb
  by_cases cA : cua xa = true
  · simp only [cA, ite_true]
    rw [build_fold _ (ucons_isUn _ _ _)]
    cases hxa : foldDown xa with
    | allow =>
      have := fa hxa; subst this; simp [pd, info, DS.union, DS.one, DS.empty]
    | deny =>
      have := da hxa
      simp [hxa, pd, info, DS.union, DS.empty, this]
    | noOp => have := (na hxa).2; exact absurd cA (by simp [cua, this])
  · have cA' : (info xa).cua = false := by simpa [cua] using cA
    simp only [cA, Bool.false_eq_true, ite_false]
    rw [build_fold _ (ucons_isUn _ _ _)]
    cases hxa : foldDown xa with
    | allow => have := fa hxa; subst this; simp [cua, info] at cA'
    | deny =>
      have := da hxa
      simp [hxa, pd, info, DS.union, DS.empty, this]
    | noOp =>
      have h1 := na hxa
      cases hxb : foldDown xb with
      | allow =>
        have := fb hxb; subst this
        simp [hxa, pd, info, DS.union, DS.one, DS.empty, h1.1, cA']
      | deny =>
        have := db hxb
        simp [hxa, hxb, pd, info, DS.union, DS.empty, this]
      | noOp =>
        have h3 := nb hxb
        simp [hxa, hxb, pd, info, DS.union, DS.empty, h1.1, h3.1, h1.2, h3.2]


theorem cua_ab : ∀ x : CAD, wf x = true → cua x = true → ((pd x).a || (pd x).d) = true := by
  intro x
  induction x with
  | un d => intro _ h; cases d <;> simp_all [cua, info, pd, DS.one]
  | cond hd ha id => intro _ h; simp [cua, info] at h
  | unil => intro _ h; simp [cua, info] at h
  | ucons n c r ihc ihr =>
    intro hw h
    simp only [wf, Bool.and_eq_true] at hw
    have e := pd_list r hw.1.2
    simp only [cua, info, Bool.or_eq_true] at h
    simp only [pd, info, DS.union]
    rcases h with h | h
    · have := ihc hw.1.1 h
      simp only [pd, Bool.or_eq_true] at this
      rcases this with h1 | h1 <;> simp [h1]
    · have := ihr hw.2 h
      rw [e] at this
      simp only [Bool.or_eq_true] at this
      rcases this with h1 | h1 <;> simp [h1]

theorem pd_n (x : CAD) (hu : isUn x = false) : (pd x).n = !(cua x) := by
  cases x with
  | un d => simp [isUn] at hu
  | cond hd ha id => rfl
  | unil => rfl
  | ucons n c r => simp [pd, cua, info]

theorem FD_mem_of_none (u : CAD) (hw : wf u = true) (hu : isUn u = false)
    (hs : (pd u).theOnly = none) : (pd u).has (FD u) = true := by
  have hne : ¬ (cua u = true ∧ (pd u).a = false ∧ (pd u).d = false) := by
    rintro ⟨h1, h2, h3⟩
    have := cua_ab u hw h1; simp [h2, h3] at this
  have hn := pd_n u hu
  unfold FD
  revert hs hne hn
  generalize pd u = s
  generalize cua u = c
  rcases s with ⟨a, d, n⟩
  cases a <;> cases d <;> cases n <;> cases c <;> simp [DS.theOnly, DS.has]

theorem wf_build (ok : Bool) (u : CAD) (hw : wf u = true) : wf (build ok u) = true := by
  unfold build
  split
  · rfl
  · split <;> first | rfl | exact hw

theorem good_build (u : CAD) (hw : wf u = true) (hu : isUn u = false) : good (build true u) = true := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases hs : (pd u).theOnly with
  | some d => simp [good, wf, isUn]
  | none => simp only [good, hw, Bool.true_and]; simp [hu, FD_mem_of_none u hw hu hs]

theorem chain_L1 {W : World} (A B : Authorizer W) (hn : namesOk A B = true) (a : W.Attrs)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true) :
    good ((chain2 A B).caa a) = true := by
  have wA : wf (A.caa a) = true := by simp [good] at hA; exact hA.1
  have wB : wf (B.caa a) = true := by simp [good] at hB; exact hB.1
  simp only [chain2, hn]
  split
  · exact good_build (.ucons A.name (A.caa a) .unil) (by simp [wf, isList, wA]) rfl
  · exact good_build (.ucons A.name (A.caa a) (.ucons B.name (B.caa a) .unil))
      (by simp [wf, isList, wA, wB]) rfl


/-! ### A-1, L3* and L4* -/

theorem sem_build (t : Nat → Dec) (u : CAD) (hw : wf u = true) : sem t (build true u) = sem t u := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases hs : (pd u).theOnly with
  | none => rfl
  | some d =>
    have := theOnly_has hs (sem_mem t u hw)
    simp [sem, this]

theorem chain_L3 {W : World} (A B : Authorizer W) (fA fB : W.Attrs → W.Data → Dec)
    (hn : namesOk A B = true) (a : W.Attrs) (d : W.Data)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true)
    (h3A : fA a d = sem (W.truth d) (A.caa a)) (h3B : fB a d = sem (W.truth d) (B.caa a)) :
    chainFull fA fB a d = sem (W.truth d) ((chain2 A B).caa a) := by
  have wA : wf (A.caa a) = true := by simp [good] at hA; exact hA.1
  have wB : wf (B.caa a) = true := by simp [good] at hB; exact hB.1
  have hcc : (chain2 A B).caa a =
      (if cua (A.caa a) = true then build true (CAD.ucons A.name (A.caa a) CAD.unil)
       else build true (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) CAD.unil))) := by
    simp [chain2, hn]
  rw [hcc]
  by_cases hcu : cua (A.caa a) = true
  · rw [if_pos hcu, sem_build _ _ (by simp [wf, isList, wA])]
    have := cua_sem (W.truth d) _ wA hcu
    have h' : fA a d ≠ .noOp := by rw [h3A]; exact this
    simp only [chainFull, h', ite_false, h3A, sem]
    simp [this]
  · rw [if_neg hcu, sem_build _ _ (by simp [wf, isList, wA, wB])]
    simp only [chainFull, h3A, h3B]
    by_cases h : sem (W.truth d) (A.caa a) = .noOp <;> by_cases h' : sem (W.truth d) (B.caa a) = .noOp <;>
      simp [sem, h, h']

theorem steps_ucons {o : Nat → Dec} {x z : CAD} (h : Steps o x z) :
    ∀ n c r, x = .ucons n c r → isList r = true →
    (∃ c' r', z = .ucons n c' r' ∧ Steps o c c' ∧ Steps o r r' ∧ isList r' = true) ∨ (∃ d, z = .un d) := by
  induction h with
  | refl x =>
    intro n c r hx hl; subst hx
    exact Or.inl ⟨c, r, rfl, Steps.refl _, Steps.refl _, hl⟩
  | cons s rest ih =>
    intro n c r hx hl; subst hx
    cases s with
    | head hs =>
      rcases ih n _ r rfl hl with ⟨c', r', hz, h1, h2, h3⟩ | h
      · exact Or.inl ⟨c', r', hz, Steps.cons hs h1, h2, h3⟩
      · exact Or.inr h
    | tail hs hl' =>
      rcases ih n c _ rfl hl' with ⟨c', r', hz, h1, h2, h3⟩ | h
      · exact Or.inl ⟨c', r', hz, h1, Steps.cons hs h2, h3⟩
      · exact Or.inr h
    | norm hu ho =>
      exact Or.inr ⟨_, steps_un rest rfl⟩

theorem steps_unil {o : Nat → Dec} {y : CAD} (h : Steps o .unil y) (hl : isList y = true) : y = .unil := by
  cases h with
  | refl => rfl
  | cons s rest =>
    cases s with
    | norm hu ho =>
      have := steps_un rest rfl
      subst this; simp [isList] at hl

theorem leaf_eq {W : World} (fM : W.Attrs → W.Data → Dec) (M : Authorizer W) (hL : Lawful fM M)
    (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) (rt : String → CAD → Dec) (n : String)
    (hrt : ∀ c, rt n c = M.eval c d) (c : CAD) (hr : Steps (W.truth d) (M.caa a) c) :
    leaf rt n c = fM a d := by
  have hwf : wf (M.caa a) = true := by have := hL.L1 a; simp [good] at this; exact this.1
  obtain ⟨hwc, hsc⟩ := refines_sem hr hwf
  have h3 := hL.L3 a d hc
  cases c with
  | un dd => simp [leaf, sem] at hsc ⊢; rw [h3]; exact hsc
  | cond hd ha id | unil | ucons _ _ _ =>
    all_goals
      first
      | (have h4 := hL.L4 a d hc _ rfl hr
         have hm := sem_mem (W.truth d) _ hwc
         rw [hsc, ← h3] at hm
         simp only [leaf, hrt, h4, hm, ite_true])


theorem build_cases (u : CAD) : build true u = u ∨ ∃ d, build true u = .un d := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases (pd u).theOnly with
  | none => exact Or.inl rfl
  | some d => exact Or.inr ⟨d, rfl⟩

theorem chain_L4 {W : World} (A B : Authorizer W) (fA fB : W.Attrs → W.Data → Dec)
    (hLA : Lawful fA A) (hLB : Lawful fB B)
    (hn : namesOk A B = true) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d)
    (x : CAD) (hx : isUn x = false)
    (hr : Refines (W.truth d) x ((chain2 A B).caa a)) :
    (chain2 A B).eval x d = chainFull fA fB a d := by
  have hA := hLA.L1 a
  have hB := hLB.L1 a
  have wA : wf (A.caa a) = true := by simp [good] at hA; exact hA.1
  have hn' := hn
  simp only [namesOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn'
  have hAB : (B.name == A.name) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hn'.2 h.symm
  have hrtA : ∀ c, route A B d A.name c = A.eval c d := by intro c; simp [route]
  have hrtB : ∀ c, route A B d B.name c = B.eval c d := by intro c; simp [route, hAB]
  have hcc : (chain2 A B).caa a =
      (if cua (A.caa a) = true then build true (CAD.ucons A.name (A.caa a) CAD.unil)
       else build true (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) CAD.unil))) := by
    simp [chain2, hn]
  unfold Refines at hr
  rw [hcc] at hr
  have hev : ∀ n c r, (chain2 A B).eval (.ucons n c r) d = evalL (route A B d) (.ucons n c r) :=
    fun _ _ _ => rfl
  by_cases hcu : cua (A.caa a) = true
  · rw [if_pos hcu] at hr
    rcases build_cases (.ucons A.name (A.caa a) .unil) with hb | ⟨dd, hb⟩
    · rw [hb] at hr
      rcases steps_ucons hr A.name _ _ rfl rfl with ⟨c1, r', hz, h1, h2, h3⟩ | ⟨dd, hz⟩
      · have := steps_unil h2 h3; subst this; subst hz
        rw [hev]
        have e1 := leaf_eq fA A hLA a d hc (route A B d) A.name hrtA c1 h1
        have hne : fA a d ≠ .noOp := by rw [hLA.L3 a d hc]; exact cua_sem _ _ wA hcu
        simp [evalL, e1, hne, chainFull]
      · subst hz; simp [isUn] at hx
    · rw [hb] at hr; have := steps_un hr rfl; subst this; simp [isUn] at hx
  · rw [if_neg hcu] at hr
    rcases build_cases (.ucons A.name (A.caa a) (.ucons B.name (B.caa a) .unil)) with hb | ⟨dd, hb⟩
    · rw [hb] at hr
      rcases steps_ucons hr A.name _ _ rfl (by simp [isList]) with ⟨c1, r', hz, h1, h2, h3⟩ | ⟨dd, hz⟩
      · rcases steps_ucons h2 B.name _ _ rfl (by simp [isList]) with ⟨c2, r'', hz2, h4, h5, h6⟩ | ⟨dd, hz2⟩
        · have := steps_unil h5 h6; subst this; subst hz2; subst hz
          rw [hev]
          have e1 := leaf_eq fA A hLA a d hc (route A B d) A.name hrtA c1 h1
          have e2 := leaf_eq fB B hLB a d hc (route A B d) B.name hrtB c2 h4
          by_cases hfa : fA a d = .noOp <;> simp [evalL, e1, e2, hfa, chainFull] <;> intro h <;> exact h.symm
        · rw [hz2] at h3; simp [isList] at h3
      · subst hz; simp [isUn] at hx
    · rw [hb] at hr; have := steps_un hr rfl; subst this; simp [isUn] at hx

/-- **A-1 (two-member chain)**: `Lawful` is preserved, with `full = firstNonNoOpinion`. -/
theorem chain_lawful {W : World} (A B : Authorizer W) (fA fB : W.Attrs → W.Data → Dec)
    (hLA : Lawful fA A) (hLB : Lawful fB B) (hn : namesOk A B = true) :
    Lawful (chainFull fA fB) (chain2 A B) :=
  ⟨fun a => chain_L1 A B hn a (hLA.L1 a) (hLB.L1 a),
   fun a => chain_L2 A B hn a (hLA.L1 a) (hLB.L1 a) (hLA.L2 a) (hLB.L2 a),
   fun a d hc => chain_L3 A B fA fB hn a d (hLA.L1 a) (hLB.L1 a) (hLA.L3 a d hc) (hLB.L3 a d hc),
   fun a d hc x hx hr => chain_L4 A B fA fB hLA hLB hn a d hc x hx hr⟩


/-! ## Counterexamples to the plan's A-1 as written -/

section cex
def Wu : World where
  Attrs := Unit
  Data := Unit
  Consistent _ _ := True
  truth _ _ := .noOp

def mk (nm : String) (au : Dec) (x : CAD) : Authorizer Wu :=
  { name := nm, authorize := fun _ => au, caa := fun _ => x, eval := fun x _ => foldDown x }

/-- names: an empty (or non-DNS-1123) member name makes the builder fail closed, so `Authorize`
(which does not look at names) and `FoldDown (ConditionsAwareAuthorize)` disagree. -/
theorem chain_needs_valid_names :
    namesOk (mk "" .allow (.un .allow)) (mk "b" .noOp (.un .noOp)) = false ∧
    (chain2 (mk "" .allow (.un .allow)) (mk "b" .noOp (.un .noOp))).authorize () ≠
      foldDown ((chain2 (mk "" .allow (.un .allow)) (mk "b" .noOp (.un .noOp))).caa ()) := by
  decide

/-- members must be `good`: a union with an unconditional Allow leaf has PD = {Allow} but
FailureDecision NoOpinion (P_44_needs_child_WF). Then the chain's `Authorize` (consults B) and
its `ConditionsAwareAuthorize` (stops at A, because A contains an unconditional Allow) disagree. -/
theorem chain_needs_good_members :
    let A := mk "a" .noOp (.ucons "p" (.un .allow) .unil)     -- wf, not good; its own L2 holds
    let B := mk "b" .deny (.un .deny)
    namesOk A B = true ∧ (chain2 A B).authorize () ≠ foldDown ((chain2 A B).caa ()) := by
  decide

/-- the shipped union / webhook `EvaluateConditions` return `FailureDecision` for unconditional
input, so the plan's L4 (which includes the reflexive case `x = caa a` when it is unconditional)
fails for the real union: `evaluateConditions (Allow) = NoOpinion`. -/
theorem union_eval_unconditional_is_FD :
    (chain2 (mk "a" .allow (.un .allow)) (mk "b" .noOp (.un .noOp))).eval (.un .allow) () = .noOp := by
  decide
end cex

/-! ## Vacuity guard: `Consistent` carries all the weight -/

theorem lawful_of_empty_consistent {W : World} (full : W.Attrs → W.Data → Dec) (A : Authorizer W)
    (hE : ∀ a d, ¬ W.Consistent a d) (h1 : ∀ a, good (A.caa a) = true)
    (h2 : ∀ a, A.authorize a = foldDown (A.caa a)) : Lawful full A :=
  ⟨h1, h2, fun a d hc => absurd hc (hE a d), fun a d hc => absurd hc (hE a d)⟩

/-! ## A-4, both directions, for a single lawful authorizer (the chain is a lawful authorizer) -/

/-- filter then enforcer for a classified write: the filter lets the request through iff
`Allow ∈ PD`; an unconditional Allow is admitted by the enforcer; a conditional decision is
evaluated through the guard (`conditionsenforcer.go:90-141`). -/
def served {W : World} (A : Authorizer W) (a : W.Attrs) (d : W.Data) : Bool :=
  let x := A.caa a
  if (pd x).has .allow = false then false
  else if isUn x then foldDown x == .allow
  else (guard A).eval x d == .allow

/-- **A-4 (both directions)**, for `Lawful` `A`, `Consistent a d`, evaluator = issuing authorizer
(`P_72`), enforcer present (`P_68`), one admission invocation per `(a,d)`. -/
theorem enforcement_exact {W : World} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hL : Lawful full A) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) :
    served A a d = decide (full a d = .allow) := by
  have hg := hL.L1 a
  have hwf : wf (A.caa a) = true := by simp [good] at hg; exact hg.1
  have hmem : (pd (A.caa a)).has (full a d) = true := by
    rw [hL.L3 a d hc]; exact sem_mem _ _ hwf
  unfold served
  simp only []
  by_cases hp : (pd (A.caa a)).has .allow = false
  · simp only [hp, ite_true]
    have : full a d ≠ .allow := fun h => by rw [h] at hmem; rw [hmem] at hp; exact absurd hp (by decide)
    simp [this]
  · simp only [hp, ite_false]
    cases hu : isUn (A.caa a) with
    | true =>
      cases hx : A.caa a with
      | un d0 =>
        have h3 := hL.L3 a d hc
        rw [hx] at h3; simp [sem] at h3
        simp [foldDown, h3]; cases d0 <;> rfl
      | cond _ _ _ => simp_all [isUn]
      | unil => simp_all [isUn]
      | ucons _ _ _ => simp_all [isUn]
    | false =>
      have hr : Refines (W.truth d) (A.caa a) (A.caa a) := Steps.refl _
      rw [guard_inert A hL a d hc _ hu hr, hL.L4 a d hc _ hu hr]
      generalize full a d = z; cases z <;> rfl


/-! ## Chain-level safety outside the domain: "never Allow" is not enough, Deny must be preserved -/

def firstNo (x y : Dec) : Dec := if x = .noOp then y else x

/-- A member that fails closed to NoOpinion where `full = Deny` (and never returns Allow wrongly)
makes the chain serve a request the reference denies. -/
theorem fail_closed_to_noOp_is_fail_open :
    ∃ rA rB fA fB : Dec,
      (rA = .allow → fA = .allow) ∧ (rB = .allow → fB = .allow) ∧   -- plan's G2-style safety
      firstNo rA rB = .allow ∧ firstNo fA fB ≠ .allow :=
  ⟨.noOp, .allow, .deny, .allow, by decide, by decide, by decide, by decide⟩

/-- With, in addition, `full = Deny → returned = Deny` ("Deny-faithful"), chain soundness holds. -/
theorem chain_sound_of_deny_faithful (rA rB fA fB : Dec)
    (sA : rA = .allow → fA = .allow) (sB : rB = .allow → fB = .allow)
    (dA : fA = .deny → rA = .deny) (dB : fB = .deny → rB = .deny)
    (h : firstNo rA rB = .allow) : firstNo fA fB = .allow := by
  revert sA sB dA dB h
  cases rA <;> cases rB <;> cases fA <;> cases fB <;> decide










end K
