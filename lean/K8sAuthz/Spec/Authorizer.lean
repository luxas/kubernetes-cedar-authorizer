import K8sAuthz.Spec.Core

/-!
# `K8sAuthz.Spec.Authorizer`: `World`, `Authorizer`, `Sound`, `Lawful`, `Guarded`, `guard`

PLAN 3.1 and `docs/reviews/plan-review-A.md`. An authorizer is a record of functions with no
embedded laws; predicates say what it must satisfy relative to a reference `full`.

Decision type: the plan's `Decision × String × Option Err` is projected to the decision (A-7,
the error nil-ness, is a mirror-level statement, see `Hypotheses.lean`). `M` is the type of
condition maps (the leaves of a conditional decision); `Bridge.lean` instantiates it with the
mirror's `authorizer.ConditionsMap`.
-/

namespace K8sAuthz

variable {M : Type}

structure World (M : Type) where
  Attrs : Type
  Data : Type
  /-- `Data` describes the same request `Attrs` was derived from (`Attrs` may know less). -/
  Consistent : Attrs → Data → Prop
  /-- the instance's own meaning of each condition map on concrete data. -/
  truth : Data → M → Dec

structure Authorizer (W : World M) where
  name : String
  authorize : W.Attrs → Dec
  caa : W.Attrs → CAD M
  eval : CAD M → W.Data → Dec

/-- **`Sound full A`** (PLAN 3.1 S1-S4): holds even when a remote fails. -/
structure Sound {W : World M} (full : W.Attrs → W.Data → Dec) (A : Authorizer W) : Prop where
  /-- S1 -/
  S1 : ∀ a, good (A.caa a) = true
  /-- S2: one-sided fold-down, a Deny is preserved. -/
  S2 : ∀ a, (A.authorize a).rank ≤ (foldDown (A.caa a)).rank ∧
        (foldDown (A.caa a) = .deny → A.authorize a = .deny)
  /-- S3 (reference): an Allow of the decision's reference fold is an Allow of `full`. -/
  S3 : ∀ a d, W.Consistent a d → sem (W.truth d) (A.caa a) = .allow → full a d = .allow
  /-- S3 (evaluation): evaluating a conditional refinement to Allow implies `full = Allow`. -/
  S3e : ∀ a d, W.Consistent a d → ∀ x, isUn x = false → Refines (W.truth d) x (A.caa a) →
        A.eval x d = .allow → full a d = .allow
  /-- S4 (Deny-faithful, reference): `full = Deny` is visible in the decision. -/
  S4 : ∀ a d, W.Consistent a d → full a d = .deny → sem (W.truth d) (A.caa a) = .deny
  /-- S4 (Deny-faithful, evaluation). -/
  S4e : ∀ a d, W.Consistent a d → ∀ x, isUn x = false → Refines (W.truth d) x (A.caa a) →
        full a d = .deny → A.eval x d = .deny

/-- **`Lawful Dom full A`** (PLAN 3.1 L2-L4 on `Dom ∧ Consistent`), on top of `Sound`. -/
structure Lawful {W : World M} (Dom : W.Attrs → W.Data → Prop)
    (full : W.Attrs → W.Data → Dec) (A : Authorizer W) : Prop where
  sound : Sound full A
  /-- L2 -/
  L2 : ∀ a d, W.Consistent a d → Dom a d → A.authorize a = foldDown (A.caa a)
  /-- L3: agreement `full = ⟦caa⟧_truth`. -/
  L3 : ∀ a d, W.Consistent a d → Dom a d → full a d = sem (W.truth d) (A.caa a)
  /-- L4: refinement, conditional input only. -/
  L4 : ∀ a d, W.Consistent a d → Dom a d → ∀ x, isUn x = false →
         Refines (W.truth d) x (A.caa a) → A.eval x d = full a d

/-- **`Guarded A`** (PLAN 3.1 G1, G2). -/
structure Guarded {W : World M} (A : Authorizer W) : Prop where
  G1c : ∀ x d, isUn x = false → good x = true → (pd x).has (A.eval x d) = true
  G1u : ∀ x d, isUn x = true → A.eval x d = FD x
  G2  : ∀ x d, A.eval x d = .allow → (pd x).has .allow = true

/-- The union / webhook clamp (`FailureDecision` on violation). -/
def guard {W : World M} (A : Authorizer W) : Authorizer W :=
  { A with eval := fun x d =>
      if isUn x then FD x else
      let r := A.eval x d
      if (pd x).has r then r else FD x }

/-- **A-2 (closed)**: `guard A` is `Guarded` for every `A`. -/
theorem guard_guarded {W : World M} (A : Authorizer W) : Guarded (guard A) := by
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

/-- **A-2 (inert)**: on a consistent in-domain refinement the guard changes nothing. Needs L3
(`full ∈ PD x` for the refinement `x`). -/
theorem guard_inert {W : World M} {Dom : W.Attrs → W.Data → Prop}
    {full : W.Attrs → W.Data → Dec} (A : Authorizer W) (hL : Lawful Dom full A)
    (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) (hD : Dom a d) (x : CAD M)
    (hx : isUn x = false) (hr : Refines (W.truth d) x (A.caa a)) :
    (guard A).eval x d = A.eval x d := by
  have hwf : wf (A.caa a) = true := good_wf (hL.sound.S1 a)
  obtain ⟨hwx, hsx⟩ := refines_sem hr hwf
  have h4 := hL.L4 a d hc hD x hx hr
  have hmem := sem_mem (W.truth d) x hwx
  rw [hsx, ← hL.L3 a d hc hD] at hmem
  simp only [guard, hx, Bool.false_eq_true, ite_false]
  rw [h4]; simp [hmem]

/-- `guard` preserves `Sound`. -/
theorem guard_sound {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hS : Sound full A) : Sound full (guard A) := by
  refine ⟨hS.S1, hS.S2, hS.S3, ?_, hS.S4, ?_⟩
  · intro a d hc x hx hr h
    have : A.eval x d = .allow := by
      simp only [guard, hx, Bool.false_eq_true, ite_false] at h
      by_cases hp : (pd x).has (A.eval x d) = true
      · simpa [hp] using h
      · exact absurd (by simpa [hp] using h) (FD_ne_allow x)
    exact hS.S3e a d hc x hx hr this
  · intro a d hc x hx hr hf
    have hr' : Refines (W.truth d) x (A.caa a) := hr
    have hwx := (refines_sem hr' (good_wf (hS.S1 a))).1
    have hs := (refines_sem hr' (good_wf (hS.S1 a))).2
    have h1 := hS.S4e a d hc x hx hr' hf
    have hm := sem_mem (W.truth d) x hwx
    rw [hs, hS.S4 a d hc hf] at hm
    simp only [guard, hx, Bool.false_eq_true, ite_false, h1, hm, ite_true]

theorem guard_lawful {W : World M} {Dom : W.Attrs → W.Data → Prop}
    {full : W.Attrs → W.Data → Dec} (A : Authorizer W) (hL : Lawful Dom full A) :
    Lawful Dom full (guard A) :=
  ⟨guard_sound A hL.sound, hL.L2, hL.L3, fun a d hc hD x hx hr => by
    rw [guard_inert A hL a d hc hD x hx hr]; exact hL.L4 a d hc hD x hx hr⟩

/-- If `eval` is the natural evaluator, L4 follows from S1 and L3 (P-27 for the toy). -/
theorem natural_L4 {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W)
    (hn : ∀ x d, isUn x = false → A.eval x d = sem (W.truth d) x)
    (h1 : ∀ a, good (A.caa a) = true) (a : W.Attrs) (d : W.Data)
    (h3 : full a d = sem (W.truth d) (A.caa a)) :
    ∀ x, isUn x = false → Refines (W.truth d) x (A.caa a) → A.eval x d = full a d := by
  intro x hx hr
  obtain ⟨_, hsx⟩ := refines_sem hr (good_wf (h1 a))
  rw [hn x d hx, hsx, h3]

/-- Vacuity guard: with `Consistent` empty everything holds, so non-emptiness of the real
`Consistent` is what gives the contract content (A-5, `Hypotheses.lean`). -/
theorem lawful_of_empty_consistent {W : World M} (Dom : W.Attrs → W.Data → Prop)
    (full : W.Attrs → W.Data → Dec) (A : Authorizer W)
    (hE : ∀ a d, ¬ W.Consistent a d) (h1 : ∀ a, good (A.caa a) = true)
    (h2 : ∀ a, (A.authorize a).rank ≤ (foldDown (A.caa a)).rank ∧
        (foldDown (A.caa a) = .deny → A.authorize a = .deny)) : Lawful Dom full A :=
  ⟨⟨h1, h2, fun a d hc => absurd hc (hE a d), fun a d hc => absurd hc (hE a d),
    fun a d hc => absurd hc (hE a d), fun a d hc => absurd hc (hE a d)⟩,
   fun a d hc => absurd hc (hE a d), fun a d hc => absurd hc (hE a d),
   fun a d hc => absurd hc (hE a d)⟩

/-- Recipe for instances: an authorizer whose `authorize` is exactly the fold-down, whose
decisions are `good`, whose `eval` is the natural evaluator on conditional input and whose
`full` agrees with the reference fold (L3) on consistent pairs is `Lawful` (and `Sound`) on the
domain where this holds. This is the shape the Cedar instantiation (stage 3) will take. -/
theorem lawful_of_natural {W : World M} (Dom : W.Attrs → W.Data → Prop)
    (full : W.Attrs → W.Data → Dec) (A : Authorizer W)
    (h1 : ∀ a, good (A.caa a) = true)
    (h2 : ∀ a, A.authorize a = foldDown (A.caa a))
    (hn : ∀ x d, isUn x = false → A.eval x d = sem (W.truth d) x)
    (h3 : ∀ a d, W.Consistent a d → full a d = sem (W.truth d) (A.caa a)) :
    Lawful Dom full A := by
  have h4 : ∀ a d, W.Consistent a d → ∀ x, isUn x = false →
      Refines (W.truth d) x (A.caa a) → A.eval x d = full a d :=
    fun a d hc x hx hr => natural_L4 A hn h1 a d (h3 a d hc) x hx hr
  refine ⟨⟨h1, fun a => ⟨by rw [h2 a]; exact Nat.le_refl _, fun h => by rw [h2 a]; exact h⟩,
    fun a d hc h => by rw [h3 a d hc]; exact h,
    fun a d hc x hx hr h => by rw [← h4 a d hc x hx hr]; exact h,
    fun a d hc h => by rw [← h3 a d hc]; exact h,
    fun a d hc x hx hr h => by rw [h4 a d hc x hx hr]; exact h⟩,
    fun a _ _ _ => h2 a, fun a d hc _ => h3 a d hc, fun a d hc _ x hx hr => h4 a d hc x hx hr⟩

/-- The name plays no role in `Lawful` (it matters only for `NamesOk` in a chain). -/
theorem Lawful.rename {W : World M} {Dom : W.Attrs → W.Data → Prop}
    {full : W.Attrs → W.Data → Dec} {A : Authorizer W} (h : Lawful Dom full A) (n : String) :
    Lawful Dom full { A with name := n } :=
  ⟨⟨h.sound.S1, h.sound.S2, h.sound.S3, h.sound.S3e, h.sound.S4, h.sound.S4e⟩, h.L2, h.L3, h.L4⟩

end K8sAuthz
