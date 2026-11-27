import K8sAuthz.Spec.Negative

/-!
# `K8sAuthz.Spec.Examples`: non-vacuity (A-8)

Compiled instances of `Lawful`, `Guarded`, chains and enforcement. `A0` (always `NoOpinion`,
from `Negative.lean`) is `Lawful` and `Guarded` although it is not (plan `Lawful` and plan
`Guarded`) (`A0_not_both`). `A2` is a conditional toy over `Data = Bool` whose `Consistent` is
neither empty nor total.
-/

namespace K8sAuthz

/-- An authorizer whose decision is always the unconditional `f a` is `Lawful` for any domain,
whatever its `eval` does (conditional refinements of an unconditional decision do not exist). -/
theorem lawful_of_unconditional {M : Type} {W : World M} (A : Authorizer W) (f : W.Attrs → Dec)
    (hc : ∀ a, A.caa a = .un (f a)) (ha : ∀ a, A.authorize a = f a)
    (Dom : W.Attrs → W.Data → Prop) (full : W.Attrs → W.Data → Dec)
    (hf : ∀ a d, W.Consistent a d → full a d = f a) : Lawful Dom full A := by
  have hr : ∀ a d x, Refines (W.truth d) x (A.caa a) → isUn x = false → False := by
    intro a d x hr hx
    have := steps_un (d := f a) (by simpa [Refines, hc a] using hr)
    subst this; simp [isUn] at hx
  refine ⟨⟨fun a => by simp [hc a, good, wf, isUn], fun a => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [hc a, ha a, foldDown]
    exact ⟨Nat.le_refl _, id⟩
  · intro a d c h; rw [hf a d c]; simpa [hc a, sem] using h
  · intro a d c x hx h; exact (hr a d x h hx).elim
  · intro a d c h; simp [hf a d c, hc a, sem] at h ⊢; exact h
  · intro a d c x hx h; exact (hr a d x h hx).elim
  · intro a d c _; simp [ha a, hc a, foldDown]
  · intro a d c _; simp [hf a d c, hc a, sem]
  · intro a d c _ x hx h; exact (hr a d x h hx).elim

theorem A0_lawful : Lawful (fun _ _ => True) full0 A0 :=
  lawful_of_unconditional A0 (fun _ => .noOp) (fun _ => rfl) (fun _ => rfl) _ _ (fun _ _ _ => rfl)

theorem A0_guarded : Guarded (guard A0) := guard_guarded A0

/-- the toy conditional authorizer: attributes `none` (unknown) or `some b`, data `b : Bool`. -/
def W2 : World Nat where
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

theorem A2_lawful : Lawful (fun _ _ => True) full2 A2 := by
  refine lawful_of_natural _ full2 A2 ?_ ?_ ?_ ?_
  · intro a; cases a with
    | none => decide
    | some b => cases b <;> decide
  · intro a; cases a with
    | none => decide
    | some b => cases b <;> decide
  · intro x d hx; simp [A2, hx]
  · intro a d hc
    rcases hc with h | h <;> subst h <;> (try cases d) <;> (try (rename_i b; cases b)) <;> decide

theorem A2_guarded : Guarded (guard A2) := guard_guarded A2

theorem A2_guard_lawful : Lawful (fun _ _ => True) full2 (guard A2) := guard_lawful A2 A2_lawful

/-- `Consistent` is neither empty nor total, and `Attrs` knows less than `Data`. -/
theorem W2_consistent_nontrivial :
    W2.Consistent none true ∧ W2.Consistent (some true) true ∧ ¬ W2.Consistent (some true) false := by
  refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
  intro h; rcases h with h | h <;> simp at h

/-- A2 has a genuinely conditional decision and the exact enforcement theorem says it admits
iff the data is `true`. -/
example : served A2 none true = true := by decide
example : served A2 none false = false := by decide

theorem A2_enforcement (a : Option Bool) (d : Bool) (hc : W2.Consistent a d) :
    served A2 a d = decide (full2 a d = .allow) :=
  enforcement_exact A2 A2_lawful a d hc trivial

/-- a second member with a different name -/
def A2b : Authorizer W2 := { A2 with name := "toy2" }

theorem A2b_lawful : Lawful (fun _ _ => True) full2 A2b := A2_lawful.rename "toy2"

theorem names_A2_A2b : namesOk A2 A2b = true := by decide

/-- A-1 and A-4 on a concrete chain: the chain of two lawful members is lawful, and the
enforcer admits it exactly when `full` allows. -/
theorem chain_A2_lawful : Lawful (fun a d => True ∧ True) (chainFull full2 full2) (chain2 A2 A2b) :=
  chain_lawful A2 A2b A2_lawful A2b_lawful names_A2_A2b

theorem chain_A2_enforcement (a : Option Bool) (d : Bool) (hc : W2.Consistent a d) :
    served (chain2 A2 A2b) a d = decide (chainFull full2 full2 a d = .allow) :=
  chain_enforcement_exact A2 A2b A2_lawful A2b_lawful names_A2_A2b a d hc trivial trivial

/-- a chain of `A0` and `A2` (members of different shape) -/
def A0' : Authorizer W2 where
  name := "never"
  authorize _ := .noOp
  caa _ := .un .noOp
  eval x _ := foldDown x

theorem A0'_lawful : Lawful (fun _ _ => True) (fun _ _ => Dec.noOp) A0' :=
  lawful_of_unconditional A0' (fun _ => .noOp) (fun _ => rfl) (fun _ => rfl) _ _ (fun _ _ _ => rfl)

theorem chain_A0'_A2_lawful :
    Lawful (fun _ _ => True ∧ True) (chainFull (fun _ _ => Dec.noOp) full2) (chain2 A0' A2) :=
  chain_lawful A0' A2 A0'_lawful A2_lawful (by decide)

/-- the n-member chain on the same instances -/
def ms2 : List (Member W2) :=
  [⟨A2, _, full2, A2_lawful⟩, ⟨A0', _, _, A0'_lawful⟩]

example : Lawful (domN ms2) (fullN ms2) (chainN ms2) :=
  chainN_lawful ms2 (by intro m hm; simp [ms2] at hm; rcases hm with rfl | rfl <;> decide)

end K8sAuthz
