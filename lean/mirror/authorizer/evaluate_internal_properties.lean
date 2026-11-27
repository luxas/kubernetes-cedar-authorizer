import authorizer.conditionsunion_properties
import authorizer.evaluate

/-!
# `authorizer/evaluate_internal_properties.lean`  ↔  `pkg/authorization/authorizer/evaluate_internal_test.go`

Map-level evaluation properties of `review/properties.md` Part 2 §C (and the map forms of
§D): P-18, P-19, P-20, P-21, P-22, P-23, P-25 (map), P-27 (map), P-28 (map), P-31 (map),
about `partiallyEvaluateConditionsMapInternal` (`evaluate.go:121-224`), abbreviated `pmap`.

Method: `phase_spec` characterises `conditionsToAppliedErroredUnevaluated` (`evaluate.go:197-224`)
by three Boolean summaries of a phase (`anyT`: some condition true, `anyE`: some condition
errored, `unevOf`: the unevaluatable conditions, in order); `pmap_cases` lists the ten
outcomes of `pmap`; `pmap_total` computes the decision of a full evaluation as the Boolean
formula `decSpec`. Everything else is a corollary.

Summary of what needs well-formedness:
* hold for ALL maps and ANY oracle: P-20, P-21 (error dropping), P-22, P-25 (map), P-31 (map).
* hold for ALL maps, total oracle: P-18, P-19, P-21 (characterisation), P-23, P-28 (map).
* need `ConditionsMap.WF`: P-27 (map) — the refined sub-maps must be re-accepted unchanged by
  the smart constructor (`mkMap_sub`).
-/

namespace authorizer
open DecisionSet ConditionsAwareDecision ConditionEvaluationResult

/-! ## Phase summaries -/

/-- Some condition of `L` evaluates to `true` under `p`. -/
def anyT (L : List Condition) (p : MaybeEvaluateConditionFunc) : Bool := L.any (fun c => (p c).IsTrue)
/-- Some condition of `L` evaluates to an error under `p`. -/
def anyE (L : List Condition) (p : MaybeEvaluateConditionFunc) : Bool := L.any (fun c => (p c).IsError)
/-- The conditions of `L` that `p` cannot evaluate, in order (the `unevaluated` result of
`conditionsToAppliedErroredUnevaluated`, `evaluate.go:211-213`). -/
def unevOf (L : List Condition) (p : MaybeEvaluateConditionFunc) : List Condition :=
  L.filter (fun c => (p c).IsUnevaluatable)

/-- `conditionsToAppliedErroredUnevaluated.go` (`evaluate.go:197-224`): a hit is the first
`true`; a miss carries the unevaluatable conditions and is error-free iff no condition errored. -/
theorem go_spec (p : MaybeEvaluateConditionFunc) (eff : String) : ∀ (L : List Condition) errs unev,
    (∃ c, conditionsToAppliedErroredUnevaluated.go p eff L errs unev = .hit c ∧ c ∈ L ∧ p c = .true_
        ∧ anyT L p = true)
    ∨ (∃ es, conditionsToAppliedErroredUnevaluated.go p eff L errs unev = .miss es (unev ++ unevOf L p)
        ∧ anyT L p = false ∧ (es = [] ↔ errs = [] ∧ anyE L p = false))
  | [], errs, unev => by
    right; exact ⟨errs, by simp [conditionsToAppliedErroredUnevaluated.go, unevOf], by simp [anyT], by simp [anyE]⟩
  | c :: rest, errs, unev => by
    cases hc : p c with
    | true_ =>
      left; exact ⟨c, by simp [conditionsToAppliedErroredUnevaluated.go, hc], by simp, hc, by simp [anyT, hc, IsTrue]⟩
    | false_ =>
      rcases go_spec p eff rest errs unev with ⟨c', h1, h2, h3, h4⟩ | ⟨es, h1, h2, h3⟩
      · left; exact ⟨c', by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1], by simp [h2], h3,
          by simp_all [anyT]⟩
      · right; refine ⟨es, by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1, unevOf, IsUnevaluatable], ?_, ?_⟩
        · simp_all [anyT, IsTrue]
        · simp_all [anyE, IsError]
    | unevaluatable =>
      rcases go_spec p eff rest errs (unev ++ [c]) with ⟨c', h1, h2, h3, h4⟩ | ⟨es, h1, h2, h3⟩
      · left; exact ⟨c', by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1], by simp [h2], h3,
          by simp_all [anyT]⟩
      · right; refine ⟨es, by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1, unevOf, IsUnevaluatable], ?_, ?_⟩
        · simp_all [anyT, IsTrue]
        · simp_all [anyE, IsError]
    | error e =>
      rcases go_spec p eff rest (errs ++ [s!"condition {c.ID} with effect={eff} evaluated to an error: {e}"]) unev
        with ⟨c', h1, h2, h3, h4⟩ | ⟨es, h1, h2, h3⟩
      · left; exact ⟨c', by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1], by simp [h2], h3,
          by simp_all [anyT]⟩
      · right; refine ⟨es, by simp [conditionsToAppliedErroredUnevaluated.go, hc, h1, unevOf, IsUnevaluatable], ?_, ?_⟩
        · simp_all [anyT, IsTrue]
        · simp only [anyE, List.any_cons, hc, IsError, Bool.true_or, List.append_eq_nil_iff,
            List.cons_ne_nil, and_false, false_and, iff_false] at h3 ⊢
          simp_all

theorem phase_spec (L : List Condition) (p : MaybeEvaluateConditionFunc) (eff : String) :
    (∃ c, conditionsToAppliedErroredUnevaluated L p eff = .hit c ∧ c ∈ L ∧ p c = .true_
        ∧ anyT L p = true)
    ∨ (∃ es, conditionsToAppliedErroredUnevaluated L p eff = .miss es (unevOf L p)
        ∧ anyT L p = false ∧ (es = [] ↔ anyE L p = false)) := by
  rcases go_spec p eff L [] [] with ⟨c, h1, h2⟩ | ⟨es, h1, h2, h3⟩
  · exact Or.inl ⟨c, h1, h2⟩
  · exact Or.inr ⟨es, by simpa [conditionsToAppliedErroredUnevaluated] using h1, h2, by simpa using h3⟩

/-- every condition of `L` evaluates to `false` under `p` -/
def allF (L : List Condition) (p : MaybeEvaluateConditionFunc) : Prop :=
  anyT L p = false ∧ anyE L p = false ∧ unevOf L p = []

theorem allF_nil (p : MaybeEvaluateConditionFunc) : allF [] p := ⟨rfl, rfl, rfl⟩

/-- Short name for `partiallyEvaluateConditionsMapInternal` (`evaluate.go:121`). -/
abbrev pmap := partiallyEvaluateConditionsMapInternal


theorem len_ne_zero {α} {L : List α} (h : L ≠ []) : (L.length != 0) = true := by
  cases L <;> simp_all

theorem phase_allF {L : List Condition} {p : MaybeEvaluateConditionFunc} (eff : String) (h : allF L p) :
    conditionsToAppliedErroredUnevaluated L p eff = .miss [] [] := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases phase_spec L p eff with ⟨c, -, -, -, h⟩ | ⟨es, he, -, hes⟩
  · simp_all
  · rw [he, h3, hes.2 h2]


/-- simp set for unfolding `pmap` -/
theorem pmap_def (m : ConditionsMap) (p : MaybeEvaluateConditionFunc) :
    pmap m p = partiallyEvaluateConditionsMapInternal m p := rfl

theorem pmap_skipD {D N A : List Condition} {p : MaybeEvaluateConditionFunc} (h : allF D p) :
    pmap ⟨D, N, A⟩ p = pmap ⟨[], N, A⟩ p := by
  by_cases hD : D = []
  · subst hD; rfl
  · simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, phase_allF _ h, len_ne_zero hD]
    simp

theorem pmap_skipN {N A : List Condition} {p : MaybeEvaluateConditionFunc} (h : allF N p) :
    pmap ⟨[], N, A⟩ p = pmap ⟨[], [], A⟩ p := by
  by_cases hN : N = []
  · subst hN; rfl
  · simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, phase_allF _ h, len_ne_zero hN]
    simp

theorem pmap_skipA {A : List Condition} {p : MaybeEvaluateConditionFunc} (h : allF A p) :
    pmap ⟨[], [], A⟩ p = .noOpinion "no conditions matched" none := by
  by_cases hA : A = []
  · subst hA; rfl
  · simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, phase_allF _ h, len_ne_zero hA]
    simp

theorem ne_nil_of_anyT {L : List Condition} {p : MaybeEvaluateConditionFunc} (h : anyT L p = true) : L ≠ [] := by
  rintro rfl; simp [anyT] at h
theorem ne_nil_of_anyE {L : List Condition} {p : MaybeEvaluateConditionFunc} (h : anyE L p = true) : L ≠ [] := by
  rintro rfl; simp [anyE] at h
theorem ne_nil_of_unev {L : List Condition} {p : MaybeEvaluateConditionFunc} (h : unevOf L p ≠ []) : L ≠ [] := by
  rintro rfl; simp [unevOf] at h

theorem aggregate_some {es : List Err} (h : es ≠ []) : ∃ e, aggregate es = some e := by
  cases es <;> simp_all [aggregate]

/-- Phase trichotomy: hit / errors / unevaluatable / all-false. -/
theorem phase_tri (L : List Condition) (p : MaybeEvaluateConditionFunc) :
    anyT L p = true ∨ (anyT L p = false ∧ anyE L p = true)
    ∨ (anyT L p = false ∧ anyE L p = false ∧ unevOf L p ≠ []) ∨ allF L p := by
  cases h1 : anyT L p <;> cases h2 : anyE L p <;> simp [allF, h1, h2] <;> exact Classical.em _ |>.symm

theorem pmap_D_T {D N A : List Condition} {p : MaybeEvaluateConditionFunc} (h : anyT D p = true) :
    ∃ r, pmap ⟨D, N, A⟩ p = .deny r none := by
  rcases phase_spec D p "Deny" with ⟨c, hc, -⟩ | ⟨es, -, h', -⟩
  · refine ⟨reasonOf c "denied the request", ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions, hc,
      len_ne_zero (ne_nil_of_anyT h)]
    rfl
  · simp_all

theorem pmap_D_E {D N A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT D p = false)
    (h2 : anyE D p = true) : ∃ e, pmap ⟨D, N, A⟩ p = .deny evaluationErrorsReason (some e) := by
  rcases phase_spec D p "Deny" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have hne : es ≠ [] := fun h => by simp_all
    obtain ⟨e, he⟩ := aggregate_some hne
    refine ⟨e, ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions, hc,
      len_ne_zero (ne_nil_of_anyE h2), len_ne_zero hne, he]
    rfl

theorem pmap_D_U {D N A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT D p = false)
    (h2 : anyE D p = false) (h3 : unevOf D p ≠ []) :
    pmap ⟨D, N, A⟩ p = ConditionsAwareDecisionConditionsMap (unevOf D p) N A := by
  rcases phase_spec D p "Deny" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have : es = [] := hes.2 h2
    subst this
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, hc,
      len_ne_zero (ne_nil_of_unev h3), len_ne_zero h3]
    simp

theorem pmap_N_T {N A : List Condition} {p : MaybeEvaluateConditionFunc} (h : anyT N p = true) :
    ∃ r, pmap ⟨[], N, A⟩ p = .noOpinion r none := by
  rcases phase_spec N p "NoOpinion" with ⟨c, hc, -⟩ | ⟨es, -, h', -⟩
  · refine ⟨reasonOf c "evaluated to NoOpinion", ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.NoOpinionConditions, hc,
      len_ne_zero (ne_nil_of_anyT h)]
    rfl
  · simp_all

theorem pmap_N_E {N A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT N p = false)
    (h2 : anyE N p = true) : ∃ e, pmap ⟨[], N, A⟩ p = .noOpinion evaluationErrorsReason (some e) := by
  rcases phase_spec N p "NoOpinion" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have hne : es ≠ [] := fun h => by simp_all
    obtain ⟨e, he⟩ := aggregate_some hne
    refine ⟨e, ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.NoOpinionConditions, hc,
      len_ne_zero (ne_nil_of_anyE h2), len_ne_zero hne, he]
    rfl

theorem pmap_N_U {N A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT N p = false)
    (h2 : anyE N p = false) (h3 : unevOf N p ≠ []) :
    pmap ⟨[], N, A⟩ p = ConditionsAwareDecisionConditionsMap [] (unevOf N p) A := by
  rcases phase_spec N p "NoOpinion" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have : es = [] := hes.2 h2
    subst this
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, hc,
      len_ne_zero (ne_nil_of_unev h3), len_ne_zero h3]
    simp

theorem pmap_A_T {A : List Condition} {p : MaybeEvaluateConditionFunc} (h : anyT A p = true) :
    ∃ r, pmap ⟨[], [], A⟩ p = .allow r none := by
  rcases phase_spec A p "Allow" with ⟨c, hc, -⟩ | ⟨es, -, h', -⟩
  · refine ⟨reasonOf c "allowed the request", ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.AllowConditions, hc,
      len_ne_zero (ne_nil_of_anyT h)]
    rfl
  · simp_all

theorem pmap_A_E {A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT A p = false)
    (h2 : anyE A p = true) : ∃ e, pmap ⟨[], [], A⟩ p = .noOpinion evaluationErrorsReason (some e) := by
  rcases phase_spec A p "Allow" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have hne : es ≠ [] := fun h => by simp_all
    obtain ⟨e, he⟩ := aggregate_some hne
    refine ⟨e, ?_⟩
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.AllowConditions, hc,
      len_ne_zero (ne_nil_of_anyE h2), len_ne_zero hne, he]
    rfl

theorem pmap_A_U {A : List Condition} {p : MaybeEvaluateConditionFunc} (h1 : anyT A p = false)
    (h2 : anyE A p = false) (h3 : unevOf A p ≠ []) :
    pmap ⟨[], [], A⟩ p = ConditionsAwareDecisionConditionsMap [] [] (unevOf A p) := by
  rcases phase_spec A p "Allow" with ⟨c, -, -, -, h'⟩ | ⟨es, hc, -, hes⟩
  · simp_all
  · have : es = [] := hes.2 h2
    subst this
    simp only [pmap, partiallyEvaluateConditionsMapInternal, ConditionsMap.DenyConditions,
      ConditionsMap.NoOpinionConditions, ConditionsMap.AllowConditions, hc,
      len_ne_zero (ne_nil_of_unev h3), len_ne_zero h3]
    simp


theorem unevOf_total {o : MaybeEvaluateConditionFunc} (ho : o.Total) (L : List Condition) :
    unevOf L o = [] := by
  simp only [unevOf, List.filter_eq_nil_iff]
  intro c _ h
  have := ho c
  revert h this; cases o c <;> simp [IsUnevaluatable]

/-- The decision of the full evaluation of a map, as a Boolean formula
(`evaluate.go:134-191` with a total oracle). -/
def decSpec (m : ConditionsMap) (o : MaybeEvaluateConditionFunc) : Decision :=
  if anyT m.denyConditions o || anyE m.denyConditions o then .Deny
  else if anyT m.noOpinionConditions o || anyE m.noOpinionConditions o then .NoOpinion
  else if anyT m.allowConditions o then .Allow else .NoOpinion

theorem pmap_total (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).dec? = some (decSpec m o) := by
  obtain ⟨D, N, A⟩ := m
  have hu := unevOf_total ho
  rcases phase_tri D o with h | ⟨h1, h2⟩ | ⟨-, -, h3⟩ | hD
  · obtain ⟨r, e⟩ := pmap_D_T (N := N) (A := A) h; simp [e, decSpec, h, dec?]
  · obtain ⟨r, e⟩ := pmap_D_E (N := N) (A := A) h1 h2; simp [e, decSpec, h2, dec?]
  · exact absurd (hu D) h3
  rw [pmap_skipD hD]
  have hD' : (anyT D o || anyE D o) = false := by simp [hD.1, hD.2.1]
  rcases phase_tri N o with h | ⟨h1, h2⟩ | ⟨-, -, h3⟩ | hN
  · obtain ⟨r, e⟩ := pmap_N_T (A := A) h; simp [e, decSpec, hD', h, dec?]
  · obtain ⟨r, e⟩ := pmap_N_E (A := A) h1 h2; simp [e, decSpec, hD', h2, dec?]
  · exact absurd (hu N) h3
  rw [pmap_skipN hN]
  have hN' : (anyT N o || anyE N o) = false := by simp [hN.1, hN.2.1]
  rcases phase_tri A o with h | ⟨h1, h2⟩ | ⟨-, -, h3⟩ | hA
  · obtain ⟨r, e⟩ := pmap_A_T h; simp [e, decSpec, hD', hN', h, dec?]
  · obtain ⟨r, e⟩ := pmap_A_E h1 h2; simp [e, decSpec, hD', hN', h1, dec?]
  · exact absurd (hu A) h3
  rw [pmap_skipA hA]; simp [decSpec, hD', hN', hA.1, dec?]


/-! ### List lemmas for `anyT` / `anyE` / `unevOf` / `allF` -/

theorem anyT_eq_true_iff {L : List Condition} {p : MaybeEvaluateConditionFunc} :
    anyT L p = true ↔ ∃ c ∈ L, p c = .true_ := by
  simp only [anyT, List.any_eq_true]
  constructor <;> rintro ⟨c, hc, h⟩ <;> refine ⟨c, hc, ?_⟩ <;> revert h <;> cases p c <;> simp [IsTrue]

theorem anyE_eq_true_iff {L : List Condition} {p : MaybeEvaluateConditionFunc} :
    anyE L p = true ↔ ∃ c ∈ L, (p c).IsError = true := by
  simp [anyE, List.any_eq_true]

theorem allF_iff {L : List Condition} {p : MaybeEvaluateConditionFunc} :
    allF L p ↔ ∀ c ∈ L, p c = .false_ := by
  simp only [allF, anyT, anyE, unevOf, List.any_eq_false, List.filter_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ c hc
    have := h1 c hc; have := h2 c hc; have := h3 c hc
    revert this; revert this; revert this; cases p c <;> simp [IsTrue, IsError, IsUnevaluatable]
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩ <;> simp [h c hc, IsTrue, IsError, IsUnevaluatable]

theorem anyE_eq_false_of_noErr {L : List Condition} {p : MaybeEvaluateConditionFunc}
    (hp : ∀ c, (p c).IsError = false) : anyE L p = false := by
  simp [anyE, hp]

theorem anyT_unevOf (L : List Condition) (p : MaybeEvaluateConditionFunc) : anyT (unevOf L p) p = false := by
  simp only [anyT, unevOf, List.any_eq_false, List.mem_filter]
  rintro c ⟨-, h⟩; revert h; cases p c <;> simp [IsTrue, IsUnevaluatable]

theorem anyE_unevOf (L : List Condition) (p : MaybeEvaluateConditionFunc) : anyE (unevOf L p) p = false := by
  simp only [anyE, unevOf, List.any_eq_false, List.mem_filter]
  rintro c ⟨-, h⟩; revert h; cases p c <;> simp [IsError, IsUnevaluatable]

theorem unevOf_unevOf (L : List Condition) (p : MaybeEvaluateConditionFunc) :
    unevOf (unevOf L p) p = unevOf L p := by
  simp [unevOf, List.filter_filter]

theorem unevOf_sublist (L : List Condition) (p : MaybeEvaluateConditionFunc) : (unevOf L p).Sublist L :=
  List.filter_sublist

theorem any_filter_eq {L : List Condition} {f g : Condition → Bool}
    (h : ∀ c ∈ L, g c = false → f c = false) : (L.filter g).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    by_cases hg : g c = true
    · simp [hg, ih']
    · have hf := h c (by simp) (by simpa using hg)
      simp [hg, ih', hf]

/-! ### Consistency of a partial oracle with a total one (`properties.md` §D) -/

/-- `p ⊑ o`: `p` agrees with `o` wherever `p` is not `unevaluatable`. -/
def Consistent (p o : MaybeEvaluateConditionFunc) : Prop :=
  ∀ c, p c = .unevaluatable ∨ p c = o c

@[inherit_doc] infix:50 " ⊑ " => Consistent

theorem allF_of_consistent {L : List Condition} {p o : MaybeEvaluateConditionFunc} (hpo : p ⊑ o)
    (h : allF L p) : allF L o := by
  rw [allF_iff] at h ⊢
  intro c hc
  rcases hpo c with h' | h' <;> have := h c hc <;> simp_all

theorem anyT_of_consistent {L : List Condition} {p o : MaybeEvaluateConditionFunc} (hpo : p ⊑ o)
    (h : anyT L p = true) : anyT L o = true := by
  rw [anyT_eq_true_iff] at h ⊢
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  rcases hpo c with h' | h' <;> simp_all

/-- Under `p ⊑ o`, if the phase under `p` has no `true` and no error, `o` agrees on the
whole list and on its unevaluatable sub-list. -/
theorem any_unevOf_consistent {L : List Condition} {p o : MaybeEvaluateConditionFunc} (hpo : p ⊑ o)
    (h1 : anyT L p = false) (h2 : anyE L p = false) :
    anyT (unevOf L p) o = anyT L o ∧ anyE (unevOf L p) o = anyE L o := by
  have key : ∀ c ∈ L, (p c).IsUnevaluatable = false → o c = .false_ := by
    intro c hc hu
    have t := List.any_eq_false.1 h1 c hc
    have e := List.any_eq_false.1 h2 c hc
    rcases hpo c with h' | h'
    · simp [h', IsUnevaluatable] at hu
    · rw [← h']; revert t e hu; cases p c <;> simp [IsTrue, IsError, IsUnevaluatable]
  constructor
  · exact any_filter_eq (fun c hc hu => by simp [key c hc hu, IsTrue])
  · exact any_filter_eq (fun c hc hu => by simp [key c hc hu, IsError])


/-! ### Sub-maps of a well-formed map are constructed unchanged -/

/-- Converse of `validateConditions_ok`: valid, pairwise-distinct conditions whose IDs are not
yet seen pass `validateConditions` (`conditionsmap.go:187-220`). -/
theorem validateConditions_of : ∀ (seen : List String) (l : List Condition),
    (∀ x ∈ l, x.valid = true) → (l.map Condition.ID).Nodup → (∀ x ∈ l, x.ID ∉ seen) →
      validateConditions seen l = .ok ((l.map Condition.ID).reverse ++ seen)
  | seen, [], _, _, _ => rfl
  | seen, c :: rest, hv, hn, hs => by
    have hc := hv c (by simp)
    simp only [Condition.valid, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have ih := validateConditions_of (c.ID :: seen) rest (fun x hx => hv x (by simp [hx])) hn.2
      (fun x hx => by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hn.1 ⟨x, hx, h⟩, hs x (by simp [hx])⟩)
    have hcs : seen.contains c.ID = false := by simpa using hs c (by simp)
    unfold validateConditions
    simp only [hcs, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by omega), if_neg (by rcases h3 with h3 | h3 <;> simp [h3]), if_neg (by omega), ih]
    simp

/-- A well-formed map is returned unchanged by the smart constructor. -/
theorem mkMap_of_WF {m : ConditionsMap} (hm : m.WF) :
    ConditionsAwareDecisionConditionsMap m.denyConditions m.noOpinionConditions m.allowConditions
      = .conditionsMap m := by
  obtain ⟨D, N, A⟩ := m
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  simp only [ConditionsMap.Length] at h1 h2
  simp only [ConditionsMap.all, List.map_append, List.nodup_append, List.mem_append] at h4 h5
  obtain ⟨⟨nD, nN, dDN⟩, nA, dA⟩ := h4
  have vD : validateConditions [] D = .ok ((D.map Condition.ID).reverse) := by
    simpa using validateConditions_of [] D (fun x hx => h5 x (by simp [hx])) nD (by simp)
  have vN : validateConditions ((D.map Condition.ID).reverse) N
      = .ok ((N.map Condition.ID).reverse ++ (D.map Condition.ID).reverse) :=
    validateConditions_of _ N (fun x hx => h5 x (by simp [hx])) nN (by
      intro x hx hm
      simp only [List.mem_reverse] at hm
      exact dDN _ hm _ (List.mem_map_of_mem hx) rfl)
  have vA := validateConditions_of ((N.map Condition.ID).reverse ++ (D.map Condition.ID).reverse) A
    (fun x hx => h5 x (by simp [hx])) nA (by
      intro x hx hm
      simp only [List.mem_append, List.mem_reverse] at hm
      rcases hm with hm | hm
      · exact dA _ (Or.inr hm) _ (List.mem_map_of_mem hx) rfl
      · exact dA _ (Or.inl hm) _ (List.mem_map_of_mem hx) rfl)
  unfold ConditionsAwareDecisionConditionsMap
  simp only
  rw [if_neg (show ¬((D.length + N.length + A.length == 0) = true) by simp only [beq_iff_eq]; omega), if_neg (Nat.not_lt.2 h2),
    if_neg (by rcases h3 with h | h <;> cases D <;> cases A <;> simp_all), vD]
  simp only []
  rw [vN]; simp only []; rw [vA]

/-- Taking sub-lists of a well-formed map (keeping a Deny or Allow condition) is well-formed. -/
theorem WF_sub {m : ConditionsMap} (hm : m.WF) {D N A : List Condition}
    (hD : D.Sublist m.denyConditions) (hN : N.Sublist m.noOpinionConditions)
    (hA : A.Sublist m.allowConditions) (hne : D ≠ [] ∨ A ≠ []) : (⟨D, N, A⟩ : ConditionsMap).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  have hall : (ConditionsMap.all ⟨D, N, A⟩).Sublist m.all :=
    (hD.append hN).append hA
  refine ⟨?_, ?_, hne, ?_, ?_⟩
  · simp only [ConditionsMap.Length]
    rcases hne with h | h <;> cases D <;> cases A <;> simp_all <;> omega
  · have := hD.length_le; have := hN.length_le; have := hA.length_le
    simp only [ConditionsMap.Length] at h2 ⊢; omega
  · exact h4.sublist (hall.map _)
  · exact fun x hx => h5 x (hall.subset hx)

theorem mkMap_sub {m : ConditionsMap} (hm : m.WF) {D N A : List Condition}
    (hD : D.Sublist m.denyConditions) (hN : N.Sublist m.noOpinionConditions)
    (hA : A.Sublist m.allowConditions) (hne : D ≠ [] ∨ A ≠ []) :
    ConditionsAwareDecisionConditionsMap D N A = .conditionsMap ⟨D, N, A⟩ :=
  mkMap_of_WF (m := ⟨D, N, A⟩) (WF_sub hm hD hN hA hne)


/-! ### The ten outcomes of `partiallyEvaluateConditionsMapInternal` -/

/-- Exhaustive case split of `pmap ⟨D, N, A⟩ p` (`evaluate.go:134-191`), for ANY oracle. -/
theorem pmap_cases (D N A : List Condition) (p : MaybeEvaluateConditionFunc) :
    (anyT D p = true ∧ ∃ r, pmap ⟨D, N, A⟩ p = .deny r none)
    ∨ (anyT D p = false ∧ anyE D p = true ∧ ∃ e, pmap ⟨D, N, A⟩ p = .deny evaluationErrorsReason (some e))
    ∨ (anyT D p = false ∧ anyE D p = false ∧ unevOf D p ≠ []
        ∧ pmap ⟨D, N, A⟩ p = ConditionsAwareDecisionConditionsMap (unevOf D p) N A)
    ∨ (allF D p ∧ anyT N p = true ∧ ∃ r, pmap ⟨D, N, A⟩ p = .noOpinion r none)
    ∨ (allF D p ∧ anyT N p = false ∧ anyE N p = true
        ∧ ∃ e, pmap ⟨D, N, A⟩ p = .noOpinion evaluationErrorsReason (some e))
    ∨ (allF D p ∧ anyT N p = false ∧ anyE N p = false ∧ unevOf N p ≠ []
        ∧ pmap ⟨D, N, A⟩ p = ConditionsAwareDecisionConditionsMap [] (unevOf N p) A)
    ∨ (allF D p ∧ allF N p ∧ anyT A p = true ∧ ∃ r, pmap ⟨D, N, A⟩ p = .allow r none)
    ∨ (allF D p ∧ allF N p ∧ anyT A p = false ∧ anyE A p = true
        ∧ ∃ e, pmap ⟨D, N, A⟩ p = .noOpinion evaluationErrorsReason (some e))
    ∨ (allF D p ∧ allF N p ∧ anyT A p = false ∧ anyE A p = false ∧ unevOf A p ≠ []
        ∧ pmap ⟨D, N, A⟩ p = ConditionsAwareDecisionConditionsMap [] [] (unevOf A p))
    ∨ (allF D p ∧ allF N p ∧ allF A p ∧ pmap ⟨D, N, A⟩ p = .noOpinion "no conditions matched" none) := by
  rcases phase_tri D p with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | hD
  · exact Or.inl ⟨h, pmap_D_T h⟩
  · exact Or.inr (Or.inl ⟨h1, h2, pmap_D_E h1 h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, pmap_D_U h1 h2 h3⟩))
  rw [pmap_skipD hD]
  rcases phase_tri N p with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | hN
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, h, pmap_N_T h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, h1, h2, pmap_N_E h1 h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, h1, h2, h3, pmap_N_U h1 h2 h3⟩)))))
  rw [pmap_skipN hN]
  rcases phase_tri A p with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | hA
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, hN, h, pmap_A_T h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, hN, h1, h2, pmap_A_E h1 h2⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hD, hN, h1, h2, h3, pmap_A_U h1 h2 h3⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hD, hN, hA, pmap_skipA hA⟩))))))))

theorem refSem_map {o : MaybeEvaluateConditionFunc} (ho : o.Total) (m : ConditionsMap) :
    refSem o (.conditionsMap m) = decSpec m o := by
  simp [refSem, ← pmap_def, pmap_total m ho]


theorem IsUnconditional_of_dec? {d : ConditionsAwareDecision} {x : Decision} (h : d.dec? = some x) :
    d.IsUnconditional = true := by
  cases d <;> simp_all [dec?, IsUnconditional, IsAllow, IsDeny, IsNoOpinion]

/-! ## P-19 -/

/-- **P-19 Totality: a total oracle yields an unconditional result.** `∀ total o. uncond(pmap(m,o))`:
no condition is ever `unevaluatable`, so the three `mkMap` branches (`evaluate.go:147,166,186`)
are dead. All maps (no well-formedness needed). -/
theorem P_19_total_unconditional (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).IsUnconditional = true :=
  IsUnconditional_of_dec? (pmap_total m ho)

/-- **P-19** (the dead branches, explicitly): with a total oracle no phase collects an
unevaluatable condition, hence the result is never a map (nor a union). -/
theorem P_19_mkMap_branches_dead (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    unevOf m.denyConditions o = [] ∧ unevOf m.noOpinionConditions o = [] ∧ unevOf m.allowConditions o = []
    ∧ (pmap m o).IsConditionsMap = false ∧ (pmap m o).IsUnion = false := by
  have h := P_19_total_unconditional m ho
  refine ⟨unevOf_total ho _, unevOf_total ho _, unevOf_total ho _, ?_, ?_⟩ <;>
    cases hp : pmap m o <;> simp_all [IsUnconditional, IsAllow, IsDeny, IsNoOpinion, IsConditionsMap, IsUnion]

/-! ## P-18 -/

/-- **P-18 Soundness of PD for maps.** `∀ total o. evalMap(m,o) ∈ uncond ∧ dec(evalMap(m,o)) ∈ PD(map m)`.
`D` only from the Deny phase (needs `D ≠ []`), `A` only from the Allow phase (needs `A ≠ []`),
`N` always possible. Holds for ALL maps (WF not needed); `P_18_WF` is the catalogue form. -/
theorem P_18_dec_mem_PD (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).IsUnconditional = true
    ∧ ∃ x, (pmap m o).dec? = some x ∧ (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Has x = true := by
  refine ⟨P_19_total_unconditional m ho, decSpec m o, pmap_total m ho, ?_⟩
  obtain ⟨D, N, A⟩ := m
  simp only [decSpec, PossibleDecisions]
  split
  · rename_i h
    have : D ≠ [] := by
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact ne_nil_of_anyT h
      · exact ne_nil_of_anyE h
    simp [this]
  split; · simp
  split
  · rename_i h; simp [ne_nil_of_anyT h]
  · simp

theorem P_18_WF (m : ConditionsMap) (_hm : m.WF) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).IsUnconditional = true
    ∧ ∃ x, (pmap m o).dec? = some x ∧ (ConditionsAwareDecision.conditionsMap m).PossibleDecisions.Has x = true :=
  P_18_dec_mem_PD m ho

/-! ## P-20 -/

/-- **P-20 (map form) A true Deny dominates.** `(∃c ∈ D. o(c) = T) ⇒ pmap(m,o) = deny(_, nil)`,
regardless of N, A and of the other Deny results (including earlier errors, `evaluate.go:204-210`).
Holds for ANY oracle (partial or total) and every map. -/
theorem P_20_true_deny_dominates (m : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (h : ∃ c ∈ m.denyConditions, p c = .true_) : ∃ r, pmap m p = .deny r none := by
  obtain ⟨D, N, A⟩ := m
  exact pmap_D_T (anyT_eq_true_iff.2 h)

/-! ## P-21 -/

theorem not_TE_iff_allF_total {L : List Condition} {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (anyT L o || anyE L o) = false ↔ ∀ c ∈ L, o c = .false_ := by
  rw [← allF_iff]
  simp only [allF, Bool.or_eq_false_iff, unevOf_total ho, and_true]

/-- **P-21 Allow characterisation.**
`dec(evalMap(m,o)) = A ⟺ (∀c∈D. o c = F) ∧ (∀c∈N. o c = F) ∧ (∃c∈A. o c = T)`. All maps. -/
theorem P_21_allow_iff (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).dec? = some .Allow ↔
      (∀ c ∈ m.denyConditions, o c = .false_) ∧ (∀ c ∈ m.noOpinionConditions, o c = .false_)
      ∧ ∃ c ∈ m.allowConditions, o c = .true_ := by
  rw [pmap_total m ho, ← not_TE_iff_allF_total ho, ← not_TE_iff_allF_total ho, ← anyT_eq_true_iff]
  simp only [decSpec]
  split <;> rename_i h1
  · simp only [Bool.or_eq_true] at h1; rcases h1 with h | h <;> simp_all
  split <;> rename_i h2
  · simp only [Bool.or_eq_true] at h2; rcases h2 with h | h <;> simp_all
  split <;> rename_i h3 <;> simp_all

/-- **P-21 corollary**: an `allow` result never carries an error — errors of other Allow
conditions are dropped (`evaluate.go:177-181,207-210`). ANY oracle, every map. -/
theorem P_21_allow_drops_errors (m : ConditionsMap) (p : MaybeEvaluateConditionFunc) (r : String)
    (e : Option Err) (h : pmap m p = .allow r e) : e = none := by
  obtain ⟨D, N, A⟩ := m
  rcases pmap_cases D N A p with ⟨-, _, h'⟩ | ⟨-, -, _, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, _, h'⟩ | ⟨-, -, -, _, h'⟩
    | ⟨-, -, -, -, h'⟩ | ⟨-, -, -, _, h'⟩ | ⟨-, -, -, -, _, h'⟩ | ⟨-, -, -, -, -, h'⟩ | ⟨-, -, -, h'⟩ <;>
    rw [h'] at h <;> (try simp at h) <;> (try exact (P_14_mkMap_ne_allow _ _ _ _ _ h).elim)
  exact h.2.symm

/-- **P-21 corollary**: with no Allow condition true, the result is never Allow — an errored
Allow condition contributes nothing to Allow on its own. -/
theorem P_21_errored_allow_never_allows (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total)
    (h : ∀ c ∈ m.allowConditions, o c ≠ .true_) : (pmap m o).dec? ≠ some .Allow := by
  intro hx
  obtain ⟨-, -, c, hc, hc'⟩ := (P_21_allow_iff m ho).1 hx
  exact h c hc hc'

/-- **P-21 corollary**: if the Deny and NoOpinion conditions are all false and some Allow
condition is true, the result is `allow(_, nil)`, whatever the other Allow results (errors
included). -/
theorem P_21_true_allow_wins (m : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (hD : ∀ c ∈ m.denyConditions, p c = .false_) (hN : ∀ c ∈ m.noOpinionConditions, p c = .false_)
    (hA : ∃ c ∈ m.allowConditions, p c = .true_) : ∃ r, pmap m p = .allow r none := by
  obtain ⟨D, N, A⟩ := m
  rw [pmap_skipD (allF_iff.2 hD), pmap_skipN (allF_iff.2 hN)]
  exact pmap_A_T (anyT_eq_true_iff.2 hA)

/-! ## P-22 -/

/-- **P-22 row 1 (Deny phase errs).** No Deny condition true, some Deny condition errored ⇒
`deny("…errors…", agg)` with a non-nil error, which is `FD(m)`. ANY oracle, every map
(Deny-phase errors mask every NoOpinion/Allow result). -/
theorem P_22_deny_phase_error (m : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (h1 : ∀ c ∈ m.denyConditions, p c ≠ .true_) (h2 : ∃ c ∈ m.denyConditions, (p c).IsError = true) :
    (∃ e, pmap m p = .deny evaluationErrorsReason (some e))
    ∧ (ConditionsAwareDecision.conditionsMap m).FailureDecision = .Deny := by
  obtain ⟨D, N, A⟩ := m
  have hT : anyT D p = false := by
    cases h : anyT D p
    · rfl
    · obtain ⟨c, hc, hc'⟩ := anyT_eq_true_iff.1 h; exact absurd hc' (h1 c hc)
  have hE := anyE_eq_true_iff.2 h2
  refine ⟨pmap_D_E hT hE, ?_⟩
  simp [FailureDecision, PossibleDecisions, ne_nil_of_anyE hE]

/-- **P-22 row 2 (NoOpinion phase errs).** All Deny false, no NoOpinion true, some NoOpinion
errored ⇒ `noOp("…errors…", agg)` with a non-nil error; this equals `FD(m)` only if `D = []`. -/
theorem P_22_noOpinion_phase_error (m : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (h0 : ∀ c ∈ m.denyConditions, p c = .false_)
    (h1 : ∀ c ∈ m.noOpinionConditions, p c ≠ .true_)
    (h2 : ∃ c ∈ m.noOpinionConditions, (p c).IsError = true) :
    (∃ e, pmap m p = .noOpinion evaluationErrorsReason (some e))
    ∧ ((ConditionsAwareDecision.conditionsMap m).FailureDecision = .NoOpinion ↔ m.denyConditions = []) := by
  obtain ⟨D, N, A⟩ := m
  have hT : anyT N p = false := by
    cases h : anyT N p
    · rfl
    · obtain ⟨c, hc, hc'⟩ := anyT_eq_true_iff.1 h; exact absurd hc' (h1 c hc)
  refine ⟨by rw [pmap_skipD (allF_iff.2 h0)]; exact pmap_N_E hT (anyE_eq_true_iff.2 h2), ?_⟩
  by_cases hD : D = [] <;> simp [FailureDecision, PossibleDecisions, hD]

/-- **P-22 row 3 (Allow phase errs).** All Deny and NoOpinion false, no Allow true, some Allow
errored ⇒ `noOp("…errors…", agg)` with a non-nil error (errors win over unevaluatable,
`evaluate.go:182`); `FD(m)` only if `D = []`. -/
theorem P_22_allow_phase_error (m : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (h0 : ∀ c ∈ m.denyConditions, p c = .false_) (h0' : ∀ c ∈ m.noOpinionConditions, p c = .false_)
    (h1 : ∀ c ∈ m.allowConditions, p c ≠ .true_)
    (h2 : ∃ c ∈ m.allowConditions, (p c).IsError = true) :
    (∃ e, pmap m p = .noOpinion evaluationErrorsReason (some e))
    ∧ ((ConditionsAwareDecision.conditionsMap m).FailureDecision = .NoOpinion ↔ m.denyConditions = []) := by
  obtain ⟨D, N, A⟩ := m
  have hT : anyT A p = false := by
    cases h : anyT A p
    · rfl
    · obtain ⟨c, hc, hc'⟩ := anyT_eq_true_iff.1 h; exact absurd hc' (h1 c hc)
  refine ⟨by rw [pmap_skipD (allF_iff.2 h0), pmap_skipN (allF_iff.2 h0')]; exact pmap_A_E hT (anyE_eq_true_iff.2 h2), ?_⟩
  by_cases hD : D = [] <;> simp [FailureDecision, PossibleDecisions, hD]

/-! ## P-23 -/

theorem anyT_perm {L L' : List Condition} (h : L.Perm L') (p : MaybeEvaluateConditionFunc) :
    anyT L p = anyT L' p := by
  apply Bool.eq_iff_iff.2; simp [anyT, List.any_eq_true, h.mem_iff]

theorem anyE_perm {L L' : List Condition} (h : L.Perm L') (p : MaybeEvaluateConditionFunc) :
    anyE L p = anyE L' p := by
  apply Bool.eq_iff_iff.2; simp [anyE, List.any_eq_true, h.mem_iff]

/-- **P-23 Decision is invariant under permutation within an effect.**
`∀π. dec(evalMap((πD, πN, πA), o)) = dec(evalMap((D,N,A), o))` for a total `o`
(reasons and error lists follow list order and may differ). All maps. -/
theorem P_23_perm_invariant {D N A D' N' A' : List Condition} (hD : D.Perm D') (hN : N.Perm N')
    (hA : A.Perm A') {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap ⟨D', N', A'⟩ o).dec? = (pmap ⟨D, N, A⟩ o).dec? := by
  rw [pmap_total _ ho, pmap_total _ ho]
  simp only [decSpec, anyT_perm hD, anyE_perm hD, anyT_perm hN, anyE_perm hN, anyT_perm hA]

/-! ## P-28 (map form) -/

/-- **P-28 (map form) Partial evaluation with a total oracle is full evaluation.**
`∀ total o. uncond(pmap(m,o)) ∧ dec(pmap(m,o)) = ⟦map m⟧ₒ`. All maps. -/
theorem P_28_map (m : ConditionsMap) {o : MaybeEvaluateConditionFunc} (ho : o.Total) :
    (pmap m o).IsUnconditional = true ∧ (pmap m o).dec? = some (refSem o (.conditionsMap m)) := by
  refine ⟨P_19_total_unconditional m ho, ?_⟩
  rw [refSem_map ho, pmap_total m ho]


/-! ## P-25 (map form) -/

theorem PD_mkMap_subset (D' N' A' : List Condition) (m : ConditionsMap)
    (hD : D' ≠ [] → m.denyConditions ≠ []) (hA : A' ≠ [] → m.allowConditions ≠ []) :
    (ConditionsAwareDecisionConditionsMap D' N' A').PossibleDecisions.Subset
      (ConditionsAwareDecision.conditionsMap m).PossibleDecisions := by
  rcases mkMap_cases D' N' A' with h | ⟨r, e, h⟩ <;> rw [h] <;> intro x hx
  · cases x <;> simp_all [PossibleDecisions]
  · by_cases h0 : D' = []
    · simp only [h0, ↓reduceIte, PossibleDecisions, Has_singleton, decide_eq_true_eq] at hx
      subst hx; simp [PossibleDecisions]
    · simp only [h0, ↓reduceIte, PossibleDecisions, Has_singleton, decide_eq_true_eq] at hx
      subst hx; simp [PossibleDecisions, hD h0]

/-- **P-25 (map form) Monotone refinement.** `PD(pmap(m,p)) ⊆ PD(map m)` for ANY oracle and
EVERY map: Deny only from the Deny branch, Allow only from the Allow branch, refined maps are
sub-lists, NoOpinion always possible (`evaluate.go:134-191`). -/
theorem P_25_map (m : ConditionsMap) (p : MaybeEvaluateConditionFunc) :
    (pmap m p).PossibleDecisions.Subset (ConditionsAwareDecision.conditionsMap m).PossibleDecisions := by
  obtain ⟨D, N, A⟩ := m
  have hN : ∀ r e, (ConditionsAwareDecision.noOpinion r e).PossibleDecisions.Subset
      (ConditionsAwareDecision.conditionsMap ⟨D, N, A⟩).PossibleDecisions := by
    intro r e x hx; simp [PossibleDecisions] at hx; subst hx; simp [PossibleDecisions]
  have hDn : D ≠ [] → ∀ r e, (ConditionsAwareDecision.deny r e).PossibleDecisions.Subset
      (ConditionsAwareDecision.conditionsMap ⟨D, N, A⟩).PossibleDecisions := by
    intro h r e x hx; simp [PossibleDecisions] at hx; subst hx; simp [PossibleDecisions, h]
  rcases pmap_cases D N A p with ⟨h, r, h'⟩ | ⟨-, h, e, h'⟩ | ⟨-, -, h, h'⟩ | ⟨-, -, r, h'⟩ | ⟨-, -, -, e, h'⟩
    | ⟨-, -, -, -, h'⟩ | ⟨-, -, h, r, h'⟩ | ⟨-, -, -, -, e, h'⟩ | ⟨-, -, -, -, h, h'⟩ | ⟨-, -, -, h'⟩ <;> rw [h']
  · exact hDn (ne_nil_of_anyT h) _ _
  · exact hDn (ne_nil_of_anyE h) _ _
  · exact PD_mkMap_subset _ _ _ _ (fun _ => ne_nil_of_unev h) id
  · exact hN _ _
  · exact hN _ _
  · exact PD_mkMap_subset _ _ _ _ (fun h => absurd rfl h) id
  · intro x hx; simp [PossibleDecisions] at hx; subst hx; simp [PossibleDecisions, ne_nil_of_anyT h]
  · exact hN _ _
  · exact PD_mkMap_subset _ _ _ _ (fun h => absurd rfl h) (fun _ => ne_nil_of_unev h)
  · exact hN _ _

/-! ## P-27 (map form) -/

theorem anyT_nil (p : MaybeEvaluateConditionFunc) : anyT [] p = false := rfl
theorem anyE_nil (p : MaybeEvaluateConditionFunc) : anyE [] p = false := rfl

/-- **P-27 (map form) Confluence.** For a WF map, `p ⊑ o`, `o` total and `p` error-free:
`⟦pmap(m,p)⟧ₒ = ⟦map m⟧ₒ`. WF is used to know that the refined sub-maps are re-constructed
unchanged by `ConditionsAwareDecisionConditionsMap` (`evaluate.go:148,167,186`). -/
theorem P_27_map {m : ConditionsMap} (hm : m.WF) {p o : MaybeEvaluateConditionFunc} (hpo : p ⊑ o)
    (ho : o.Total) (hp : ∀ c, (p c).IsError = false) :
    refSem o (pmap m p) = refSem o (.conditionsMap m) := by
  obtain ⟨D, N, A⟩ := m
  rw [refSem_map ho]
  have noE := fun L => @anyE_eq_false_of_noErr L p hp
  have hlen : N.length ≤ MaxConditionsPerMap := by
    have := hm.2.1; simp [ConditionsMap.Length] at this; omega
  rcases pmap_cases D N A p with ⟨h, r, h'⟩ | ⟨-, h, e, h'⟩ | ⟨h1, h2, h3, h'⟩ | ⟨hD, h, r, h'⟩ | ⟨-, -, h, e, h'⟩
    | ⟨hD, h1, h2, h3, h'⟩ | ⟨hD, hN, h, r, h'⟩ | ⟨-, -, -, h, e, h'⟩ | ⟨hD, hN, h1, h2, h3, h'⟩ | ⟨hD, hN, hA, h'⟩ <;>
    rw [h']
  · simp [refSem, decSpec, anyT_of_consistent hpo h]
  · simp [noE] at h
  · rw [mkMap_sub hm (unevOf_sublist D p) (List.Sublist.refl _) (List.Sublist.refl _) (Or.inl h3),
      refSem_map ho]
    obtain ⟨e1, e2⟩ := any_unevOf_consistent hpo h1 h2
    simp only [decSpec, e1, e2]
  · have hD' := allF_of_consistent hpo hD
    simp [refSem, decSpec, hD'.1, hD'.2.1, anyT_of_consistent hpo h]
  · simp [noE] at h
  · have hD' := allF_of_consistent hpo hD
    obtain ⟨e1, e2⟩ := any_unevOf_consistent hpo h1 h2
    by_cases hA : A = []
    · subst hA
      rw [P_14_mkMap_noOpinion_only_skips_validation _ h3 (Nat.le_trans (unevOf_sublist N p).length_le hlen)]
      simp [refSem, decSpec, hD'.1, hD'.2.1, anyT_nil]
    · rw [mkMap_sub hm (List.nil_sublist _) (unevOf_sublist N p) (List.Sublist.refl _) (Or.inr hA),
        refSem_map ho]
      simp only [decSpec, e1, e2, hD'.1, hD'.2.1, anyT_nil, anyE_nil]
  · have hD' := allF_of_consistent hpo hD
    have hN' := allF_of_consistent hpo hN
    simp [refSem, decSpec, hD'.1, hD'.2.1, hN'.1, hN'.2.1, anyT_of_consistent hpo h]
  · simp [noE] at h
  · have hD' := allF_of_consistent hpo hD
    have hN' := allF_of_consistent hpo hN
    obtain ⟨e1, -⟩ := any_unevOf_consistent hpo h1 h2
    rw [mkMap_sub hm (List.nil_sublist _) (List.nil_sublist _) (unevOf_sublist A p) (Or.inr h3),
      refSem_map ho]
    simp only [decSpec, e1, hD'.1, hD'.2.1, hN'.1, hN'.2.1, anyT_nil, anyE_nil]
  · have hD' := allF_of_consistent hpo hD
    have hN' := allF_of_consistent hpo hN
    have hA' := allF_of_consistent hpo hA
    simp [refSem, decSpec, hD'.1, hD'.2.1, hN'.1, hN'.2.1, hA'.1]

/-! ## P-31 (map form) -/

/-- **P-31 (map form) Idempotence.** If partial evaluation of a map yields a (refined) map
`m'`, partially evaluating `m'` again with the same oracle returns `m'` unchanged: its first
non-empty phase contains only unevaluatable conditions. ANY oracle, every map. -/
theorem P_31_map (m m' : ConditionsMap) (p : MaybeEvaluateConditionFunc)
    (h : pmap m p = .conditionsMap m') : pmap m' p = .conditionsMap m' := by
  obtain ⟨D, N, A⟩ := m
  rcases pmap_cases D N A p with ⟨-, r, h'⟩ | ⟨-, -, e, h'⟩ | ⟨-, -, h3, h'⟩ | ⟨-, -, r, h'⟩ | ⟨-, -, -, e, h'⟩
    | ⟨-, -, -, h3, h'⟩ | ⟨-, -, -, r, h'⟩ | ⟨-, -, -, -, e, h'⟩ | ⟨-, -, -, -, h3, h'⟩ | ⟨-, -, -, h'⟩ <;>
    rw [h'] at h <;> (try simp at h)
  · obtain ⟨rfl, -⟩ := mkMap_eq_conditionsMap h
    rw [pmap_D_U (anyT_unevOf D p) (anyE_unevOf D p) (by rwa [unevOf_unevOf]), unevOf_unevOf, h]
  · obtain ⟨rfl, -⟩ := mkMap_eq_conditionsMap h
    rw [pmap_N_U (anyT_unevOf N p) (anyE_unevOf N p) (by rwa [unevOf_unevOf]), unevOf_unevOf, h]
  · obtain ⟨rfl, -⟩ := mkMap_eq_conditionsMap h
    rw [pmap_A_U (anyT_unevOf A p) (anyE_unevOf A p) (by rwa [unevOf_unevOf]), unevOf_unevOf, h]

end authorizer