import K8sAuthz.Spec.Enforcement

/-!
# `K8sAuthz.Spec.Negative`: the plan's old definitions and the negative theorems

The first draft of PLAN 3.1 (`LawfulPlan`, `GuardedPlan`) is kept here, verbatim, so the
review-A findings stay machine-checked:

* `plan_lawful_guarded_clash`, `A0_not_both`: the plan's `Lawful` and `Guarded` contradict
  each other (A-8 (i) was false as written).
* `L4_literal_false`: L4 read as "any oracle agreeing with `full` at the root" is false.
* `G1_needs_good`: G1 "for all x" is false for every clamp.
* `chain_needs_valid_names`, `chain_needs_good_members`: A-1 needs `NamesOk` and `good`.
* `union_eval_unconditional_is_FD`: L4 at unconditional input is false for the real union.
* (`fail_closed_to_noOp_is_fail_open` is in `Chain.lean`.)
-/

namespace K8sAuthz

open K8sAuthz

/-- PLAN section 3.1, L1-L5 as written. `Refines` is quantified over "an oracle that agrees with
`full`", read literally as `sem o (caa a) = full a d`. -/
structure LawfulPlan {W : World Nat} (full : W.Attrs → W.Data → Dec) (A : Authorizer W) : Prop where
  L1 : ∀ a, wf (A.caa a) = true
  L2 : ∀ a, A.authorize a = foldDown (A.caa a)
  L3 : ∀ a d, W.Consistent a d → (pd (A.caa a)).has (full a d) = true
  L4 : ∀ a d, W.Consistent a d → ∀ o, sem o (A.caa a) = full a d →
         ∀ x, Refines o x (A.caa a) → A.eval x d = full a d
  L5 : ∀ a d, W.Consistent a d → isUn (A.caa a) = true → foldDown (A.caa a) = full a d

/-- PLAN G1, G2 as written (unconditional input -> Deny). -/
structure GuardedPlan {W : World Nat} (A : Authorizer W) : Prop where
  G1c : ∀ x d, isUn x = false → (pd x).has (A.eval x d) = true
  G1u : ∀ x d, isUn x = true → A.eval x d = .deny
  G2  : ∀ x d, A.eval x d = .allow → (pd x).has .allow = true

/-- **FINDING 1.** `LawfulPlan` (via L4 at the reflexive refinement `x = caa a`) and `GuardedPlan`
(G1 unconditional clause) contradict each other as soon as some consistent `(a,d)` has an
unconditional non-Deny `full`. In particular A-8 (i) "always-NoOpinion is Lawful and Guarded"
is false. -/
theorem plan_lawful_guarded_clash {W : World Nat} (full : W.Attrs → W.Data → Dec) (A : Authorizer W)
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
def W0 : World Nat where
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
def W1 : World Nat where
  Attrs := Unit
  Data := Unit
  Consistent _ _ := True
  truth _ id := if id = 1 then .allow else .noOp

def full1 : W1.Attrs → W1.Data → Dec := fun _ _ => .allow

def dec2 : CAD Nat := .ucons "a" (.cond false true 1) (.ucons "b" (.cond false true 2) .unil)

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
  let x : CAD Nat := .ucons "a" (.un .noOp) (.ucons "b" (.cond false true 2) .unil)
  have hr : Refines o x dec2 :=
    Steps.cons (Step.head (Step.resolve false true 1)) (Steps.refl _)
  have := h o hs x hr
  revert this; decide

/-- **FINDING 4**: G1 as written ("for all x") is false for every possible clamp: a union with an
unconditional Allow leaf has PD = {Allow}, but its FailureDecision is NoOpinion. -/
theorem G1_needs_good : ∃ x : CAD Nat, wf x = true ∧ isUn x = false ∧ (pd x).has (FD x) = false :=
  ⟨.ucons "p" (.un .allow) .unil, by decide, by decide, by decide⟩

/-! ## Counterexamples to the plan's A-1 as written -/

section cex
def Wu : World Nat where
  Attrs := Unit
  Data := Unit
  Consistent _ _ := True
  truth _ _ := .noOp

def mk (nm : String) (au : Dec) (x : CAD Nat) : Authorizer Wu :=
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


end K8sAuthz
