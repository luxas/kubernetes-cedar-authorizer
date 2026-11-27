import K8sAuthz.Spec.ChainN

/-!
# `K8sAuthz.Spec.Enforcement`: A-4 (enforcement per admission invocation), A-6, A-9

PLAN 3.1. `served` models the filter followed by the enforcer for a classified write: the
filter lets the request through iff `Allow ∈ PD`; an unconditional Allow is admitted; a
conditional decision is evaluated through the guard (`conditionsenforcer.go:90-141`).
-/

namespace K8sAuthz

variable {M : Type}

def served {W : World M} (A : Authorizer W) (a : W.Attrs) (d : W.Data) : Bool :=
  let x := A.caa a
  if (pd x).has .allow = false then false
  else if isUn x then foldDown x == .allow
  else (guard A).eval x d == .allow

/-- **A-4, forward direction, from `Sound` alone**: whatever is admitted is allowed by the
reference semantics `full`. -/
theorem enforcement_forward {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hS : Sound full A) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d)
    (h : served A a d = true) : full a d = .allow := by
  unfold served at h
  simp only [] at h
  by_cases hp : (pd (A.caa a)).has .allow = false
  · simp [hp] at h
  · rw [if_neg hp] at h
    cases hu : isUn (A.caa a) with
    | true =>
      rw [if_pos hu] at h
      have h' : foldDown (A.caa a) = .allow := by simpa using h
      have hx := fold_allow h'
      apply hS.S3 a d hc
      rw [hx]; rfl
    | false =>
      rw [if_neg (by simp [hu])] at h
      have h' : (guard A).eval (A.caa a) d = .allow := by simpa using h
      exact (guard_sound A hS).S3e a d hc _ hu (Steps.refl _) h'

/-- **A-4 (both directions)**, per admission invocation, for a `Lawful` authorizer (a chain of
`Lawful` members is one, `chain_lawful`): the enforcer admits iff `full a d = Allow`.
Hypotheses beyond `Lawful`: `Consistent a d` and `Dom a d`; the evaluating authorizer is the
issuing one (mirror `P_72` reload hypothesis, here: the same `A`); the enforcer is present
(mirror `P_68`); one admission invocation `(a, d)` (the committed object is the validated
one, `deletecollection` is per object, update-to-create adds the unconditional secondary
check, and later plugins can still reject: `Hypotheses.lean`). -/
theorem enforcement_exact {W : World M} {Dom : W.Attrs → W.Data → Prop}
    {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hL : Lawful Dom full A) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) (hD : Dom a d) :
    served A a d = decide (full a d = .allow) := by
  have hg := hL.sound.S1 a
  have hwf : wf (A.caa a) = true := good_wf hg
  have hmem : (pd (A.caa a)).has (full a d) = true := by
    rw [hL.L3 a d hc hD]; exact sem_mem _ _ hwf
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
        have h3 := hL.L3 a d hc hD
        rw [hx] at h3; simp [sem] at h3
        simp [foldDown, h3]; cases d0 <;> rfl
      | cond _ _ _ => simp_all [isUn]
      | unil => simp_all [isUn]
      | ucons _ _ _ => simp_all [isUn]
    | false =>
      have hr : Refines (W.truth d) (A.caa a) (A.caa a) := Steps.refl _
      rw [guard_inert A hL a d hc hD _ hu hr, hL.L4 a d hc hD _ hu hr]
      generalize full a d = z; cases z <;> rfl

/-- A-4 for a two-member chain of `Lawful` members. -/
theorem chain_enforcement_exact {W : World M} {DA DB : W.Attrs → W.Data → Prop}
    {fA fB : W.Attrs → W.Data → Dec} (A B : Authorizer W)
    (hLA : Lawful DA fA A) (hLB : Lawful DB fB B) (hn : namesOk A B = true)
    (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) (hDA : DA a d) (hDB : DB a d) :
    served (chain2 A B) a d = decide (chainFull fA fB a d = .allow) :=
  enforcement_exact _ (chain_lawful A B hLA hLB hn) a d hc ⟨hDA, hDB⟩

/-- A-4 forward direction for a chain, from `Sound` members only. -/
theorem chain_enforcement_forward {W : World M} {fA fB : W.Attrs → W.Data → Dec}
    (A B : Authorizer W) (hSA : Sound fA A) (hSB : Sound fB B) (hn : namesOk A B = true)
    (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d)
    (h : served (chain2 A B) a d = true) : chainFull fA fB a d = .allow :=
  enforcement_forward _ (chain_sound A B hSA hSB hn) a d hc h

/-- **A-6 `unaware_fail_closed`** (mirror P-49 via S2): a consumer that did not ask for
conditions and gets `Allow` from `authorize` was given an unconditional Allow decision, so a
conditional decision never turns into an Allow. With `Consistent`, `full = Allow`. -/
theorem unaware_fail_closed {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hS : Sound full A) (a : W.Attrs) (h : A.authorize a = .allow) : A.caa a = .un .allow := by
  have h2 := (hS.S2 a).1
  rw [h] at h2
  have : foldDown (A.caa a) = .allow := by
    revert h2; cases foldDown (A.caa a) <;> decide
  exact fold_allow this

theorem unaware_allow_is_full {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hS : Sound full A) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d)
    (h : A.authorize a = .allow) : full a d = .allow := by
  apply hS.S3 a d hc
  rw [unaware_fail_closed A hS a h]; rfl

end K8sAuthz
