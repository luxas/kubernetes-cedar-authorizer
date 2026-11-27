import cel.authorization_conditions

/-!
# `cel/authorization_conditions_properties.lean`  ↔  `authorization_conditions_test.go`

Properties P-74 … P-79 of `review/properties.md` §J for the in-process CEL evaluator
(PR #143024, unmerged). CEL itself is the opaque oracle `Evaluator.celEval`; every theorem
quantifies over it.
-/

namespace cel

open authorizer

/-! ## P-74 Result mapping -/

/-- P-74 (a). "`p_cel(c) = U` for … non-CEL type". -/
theorem P_74_non_cel_type_unevaluatable (e : Evaluator) (c : Condition)
    (h : c.CondType ≠ ConditionTypeAuthorizationCEL) : e.EvaluateCondition c = .unevaluatable := by
  simp [Evaluator.EvaluateCondition, Condition.GetType, h, ConditionEvaluationResult.Unevaluatable]

/-- P-74 (b). "`p_cel(c) = U` for … empty expression". -/
theorem P_74_empty_expression_unevaluatable (e : Evaluator) (c : Condition)
    (h : c.Condition.length = 0) : e.EvaluateCondition c = .unevaluatable := by
  unfold Evaluator.EvaluateCondition
  by_cases ht : c.CondType = ConditionTypeAuthorizationCEL <;>
    simp [Condition.GetType, Condition.GetCondition, ht, h, ConditionEvaluationResult.Unevaluatable]

/-- P-74 (c). "`E` for compile … error". -/
theorem P_74_compile_error (e : Evaluator) (c : Condition)
    (ht : c.CondType = ConditionTypeAuthorizationCEL) (hne : c.Condition.length ≠ 0)
    (h : e.celEval c.Condition = .compileError) : (e.EvaluateCondition c).IsError = true := by
  simp [Evaluator.EvaluateCondition, Condition.GetType, Condition.GetCondition, ht, hne, h,
    ConditionEvaluationResult.IsError]

/-- P-74 (d). "`E` for … runtime error". -/
theorem P_74_runtime_error (e : Evaluator) (c : Condition)
    (ht : c.CondType = ConditionTypeAuthorizationCEL) (hne : c.Condition.length ≠ 0)
    (h : e.celEval c.Condition = .runtimeError) : (e.EvaluateCondition c).IsError = true := by
  have hs : c.Condition ≠ "" := by intro h'; simp [h'] at hne
  simp only [Evaluator.EvaluateCondition, Condition.GetType, Condition.GetCondition, ht, h,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have : (c.Condition.length == 0) = false := by simp [hne]
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : e.celCost c.Condition > e.builder.runtimeCELCostBudget <;>
    simp [hc, ConditionEvaluationResult.IsError]

/-- P-74 (e). "`E` for … runtime error (incl. cost exceeded)": exhausting the per-condition
budget is an error even when CEL produced a value. -/
theorem P_74_cost_exceeded (e : Evaluator) (c : Condition) (b : Bool)
    (ht : c.CondType = ConditionTypeAuthorizationCEL) (hne : c.Condition.length ≠ 0)
    (h : e.celEval c.Condition = .value b)
    (hc : e.celCost c.Condition > e.builder.runtimeCELCostBudget) :
    (e.EvaluateCondition c).IsError = true := by
  simp [Evaluator.EvaluateCondition, Condition.GetType, Condition.GetCondition, ht, hne, h, hc,
    ConditionEvaluationResult.IsError]

/-- P-74 (f). "else `T ⟺ result == true`" (and `F` otherwise). -/
theorem P_74_value (e : Evaluator) (c : Condition) (b : Bool)
    (ht : c.CondType = ConditionTypeAuthorizationCEL) (hne : c.Condition.length ≠ 0)
    (h : e.celEval c.Condition = .value b)
    (hc : e.celCost c.Condition ≤ e.builder.runtimeCELCostBudget) :
    e.EvaluateCondition c = ConditionEvaluationResult.Boolean b := by
  have : ¬ e.celCost c.Condition > e.builder.runtimeCELCostBudget := by omega
  simp [Evaluator.EvaluateCondition, Condition.GetType, Condition.GetCondition, ht, hne, h, this]

/-- P-74, full characterisation of `true_`: "`T ⟺ result == true`". -/
theorem P_74_true_iff (e : Evaluator) (c : Condition) :
    e.EvaluateCondition c = .true_ ↔
      (c.CondType = ConditionTypeAuthorizationCEL ∧ c.Condition.length ≠ 0
        ∧ e.celEval c.Condition = .value true
        ∧ e.celCost c.Condition ≤ e.builder.runtimeCELCostBudget) := by
  unfold Evaluator.EvaluateCondition
  by_cases ht : c.CondType = ConditionTypeAuthorizationCEL
  · by_cases hne : c.Condition.length = 0
    · simp [Condition.GetType, Condition.GetCondition, ht, hne, ConditionEvaluationResult.Unevaluatable]
    · simp only [Condition.GetType, Condition.GetCondition, ht, hne, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, beq_iff_eq, ne_eq, not_false_eq_true, true_and]
      cases hv : e.celEval c.Condition with
      | compileError => simp
      | runtimeError =>
        by_cases hc : e.celCost c.Condition > e.builder.runtimeCELCostBudget <;> simp [hc]
      | value b =>
        by_cases hc : e.celCost c.Condition > e.builder.runtimeCELCostBudget
        · simp [hc]
        · have hc' : e.celCost c.Condition ≤ e.builder.runtimeCELCostBudget := by omega
          cases b <;> simp [hc, hc', ConditionEvaluationResult.Boolean]
  · simp [Condition.GetType, ht, ConditionEvaluationResult.Unevaluatable]

/-! ## P-75 The boolean test is total -/

/-- P-75. "A successful evaluation returns a CEL bool": in the model the success case of the
oracle carries a `Bool` (compilation's `IsExactType(bool)` check, `compile.go:189-205`), so
`result == true` is a total test and a value outcome is always `T` or `F`. -/
theorem P_75_value_is_bool (e : Evaluator) (c : Condition) (b : Bool)
    (ht : c.CondType = ConditionTypeAuthorizationCEL) (hne : c.Condition.length ≠ 0)
    (h : e.celEval c.Condition = .value b)
    (hc : e.celCost c.Condition ≤ e.builder.runtimeCELCostBudget) :
    e.EvaluateCondition c = .true_ ∨ e.EvaluateCondition c = .false_ := by
  rw [P_74_value e c b ht hne h hc]
  cases b <;> simp [ConditionEvaluationResult.Boolean]

/-! ## P-76 Axiom O3 -/

/-- The authoring authorizer's verdict on condition `c` for the request data the evaluator
`e` was built for (the webhook's ConditionsReview answer). Unknowable from the API server. -/
axiom oAuthor : Evaluator → Condition → ConditionEvaluationResult

/-- P-76, Axiom O3. "`∀c. p_cel(c) ∈ {T,F} ⇒ p_cel(c) = o_author(c)`".
Status: **unknown / not established** — this is an ASSUMPTION, not a fact about the code.
Version skew between the API server's CEL environment (compatibility version,
`authorization_conditions.go:44-47`), CEL library semantics, or the namespace snapshot from the
informer vs. what the webhook sees can change a boolean undetectably; only skew that yields an
error is neutralised (`webhook.go:968-970`). Confluence (P-27) and the FD-drop safety (P-26)
rest on it. Consistent: `oAuthor := Evaluator.EvaluateCondition` is a model. -/
axiom P_76_O3_builtin_agrees_with_author :
  ∀ (e : Evaluator) (c : Condition),
    (e.EvaluateCondition c = .true_ ∨ e.EvaluateCondition c = .false_) →
      e.EvaluateCondition c = oAuthor e c

/-! ## P-77 Compound authorization is unconditional -/

/-- P-77 (shape). "CEL `authorizer` checks … never yield a conditional decision": the
`authorizer` variable is an `UnconditionalAuthorizer`, whose answer is a three-valued
`Decision`; there is no conditional answer to return. -/
theorem P_77_authorizer_answer_unconditional (u : UnconditionalAuthorizer) (a : Attributes) :
    (u.Authorize a).1 = .Allow ∨ (u.Authorize a).1 = .Deny ∨ (u.Authorize a).1 = .NoOpinion := by
  cases (u.Authorize a).1 <;> simp

/-- P-77 (wiring). The `authorizer` variable is the caching wrapper around `Authorize` of the
API server's authorizer (`:101-104`), and it is declared iff that authorizer is non-nil (`:114`). -/
theorem P_77_authorizer_variable (b : Builder) (d : Option EvalData) (z : Option Authorizer)
    (e : Evaluator) (h : EvaluatorForData b d z = .ok e) :
    e.activation.authorizer = z.map (fun a => NewCachingAuthorizer a.toUnconditional)
      ∧ e.optionalVarsDecls.HasAuthorizer = z.isSome
      ∧ e.activation.authorizer.isSome = z.isSome := by
  unfold EvaluatorForData at h
  split at h
  · simp at h
  · rename_i x
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst h
          simp

/-- P-77 (no conditional path). `ConditionsAwareAuthorize` of the API server's authorizer is
never consulted: two authorizers with the same `Authorize` yield the same evaluator, hence
the same answer for every condition. -/
theorem P_77_conditions_aware_authorize_unused (b : Builder) (d : Option EvalData)
    (z z' : Authorizer) (h : z.Authorize = z'.Authorize) :
    EvaluatorForData b d (some z) = EvaluatorForData b d (some z') := by
  have : z.toUnconditional = z'.toUnconditional := by simp [Authorizer.toUnconditional, h]
  simp [EvaluatorForData, this]

/-! ## P-78 Cost is per condition, not per request -/

/-- A witness evaluator: every expression compiles to `false` and costs exactly `budget`. -/
def costlyEvaluator (budget : Nat) : Evaluator where
  builder := { celEval := fun _ _ _ => .value false, celCost := fun _ _ => budget,
               runtimeCELCostBudget := budget }
  optionalVarsDecls := { HasParams := false, HasAuthorizer := false }
  activation := { data := { isVersionedAttributes := true }, namespaceObject := none, authorizer := none }

/-- A witness map: 128 (= `MaxConditionsPerMap`) Allow conditions of CEL type. ID validity
(`IsDomainPrefixedKey`, opaque) and uniqueness are irrelevant to cost and not established. -/
def costlyMap : ConditionsMap where
  allowConditions := (List.range 128).map fun i =>
    { ID := s!"example.com/c{i}", CondType := ConditionTypeAuthorizationCEL, Condition := "false" }

private theorem sum_map_const {α : Type} (l : List α) (k : Nat) :
    (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ t ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- P-78. "Cost is bounded per condition, not per request" — the per-request bound does NOT
hold: a map of 128 conditions, each individually within the budget (each evaluates to `F`,
none errors), costs `128 × budget` in total. -/
theorem P_78_cost_per_condition_witness (budget : Nat) :
    costlyMap.Length = 128
    ∧ (∀ c ∈ costlyMap.all, (costlyEvaluator budget).EvaluateCondition c = .false_)
    ∧ mapCost (costlyEvaluator budget) costlyMap = 128 * budget := by
  refine ⟨by simp [costlyMap, ConditionsMap.Length], ?_, ?_⟩
  · intro c hc
    simp only [costlyMap, ConditionsMap.all, List.nil_append, List.mem_map] at hc
    obtain ⟨i, _, rfl⟩ := hc
    have hne : ("false" : String).length ≠ 0 := by decide
    have := P_74_value (costlyEvaluator budget)
      { ID := s!"example.com/c{i}", CondType := ConditionTypeAuthorizationCEL, Condition := "false" }
      false rfl hne rfl (Nat.le_refl _)
    rw [this]; rfl
  · have hne : ("false" : String).length ≠ 0 := by decide
    simp only [mapCost, costlyMap, ConditionsMap.all, List.nil_append, List.map_map]
    have : ((Evaluator.conditionCost (costlyEvaluator budget)) ∘ fun (i : Nat) =>
        ({ ID := s!"example.com/c{i}", CondType := ConditionTypeAuthorizationCEL,
           Condition := "false" } : Condition)) = fun _ => budget := by
      funext i
      simp [Function.comp, Evaluator.conditionCost, Condition.GetType, Condition.GetCondition,
        Evaluator.celEval, Evaluator.celCost, costlyEvaluator, hne]
    rw [this, sum_map_const]
    simp

/-- P-78, negative form. -- status: does NOT hold.
"Total cost of one map ≤ the per-condition budget" fails: counterexample `budget = 1`,
`costlyMap` (128 conditions, total cost 128). -/
theorem P_78_not_per_request_bound :
    ¬ ∀ (e : Evaluator) (m : ConditionsMap), m.Length ≤ MaxConditionsPerMap →
        mapCost e m ≤ e.builder.runtimeCELCostBudget := by
  intro h
  have h1 := h (costlyEvaluator 1) costlyMap
    (by rw [(P_78_cost_per_condition_witness 1).1]; decide)
  rw [(P_78_cost_per_condition_witness 1).2.2] at h1
  simp [costlyEvaluator] at h1

/-! ## P-79 Builder failure falls back to the webhook -/

/-- P-79 (builder). Nil informer factory or nil client ⇒ no builder (`:54-59`,
`reload.go:209-211`). -/
theorem P_79_builder_requires_informer_and_client (inf cl : Bool)
    (ce : Activation → OptionalVariableDeclarations → String → CELOutcome)
    (cc : Activation → String → Nat) (budget : Nat) :
    reloadBuiltinBuilder inf cl ce cc budget = none ↔ (inf = false ∨ cl = false) := by
  cases inf <;> cases cl <;>
    simp [reloadBuiltinBuilder, NewAuthorizationConditionsEvaluatorBuilder]

/-- P-79 (evaluator). "`EvaluatorForData` error (nil data, data not `*VersionedAttributes`,
namespace lookup, activation)": exactly these four make the `Option` view `none`. -/
theorem P_79_evaluator_none_iff (b : Builder) (d : Option EvalData) (z : Option Authorizer) :
    evaluatorFor? (some b) d z = none ↔
      (d = none ∨ ∃ x, d = some x ∧
        (x.isVersionedAttributes = false ∨ (getNamespace x).toOption = none ∨ x.activationOk = false)) := by
  cases d with
  | none => simp [evaluatorFor?, EvaluatorForData]
  | some x =>
    simp only [evaluatorFor?, EvaluatorForData]
    cases hv : x.isVersionedAttributes
    · simp [hv]
    · cases hn : getNamespace x
      · simp [Except.toOption, hv, hn]
      · cases ha : x.activationOk <;> simp [Except.toOption, hv, hn, ha]

/-- P-79. "`EvaluatorForData` error … ⇒ `peval` skipped, full decision sent to ACR": no
evaluator ⇒ `tryEvaluateUsingBuiltins` returns the decision unchanged. -/
theorem P_79_no_evaluator_skips_partial_evaluation (builder : Option Builder)
    (d : ConditionsAwareDecision) (data : Option EvalData) (z : Option Authorizer)
    (h : evaluatorFor? builder data z = none) :
    tryEvaluateUsingBuiltins builder d data z = d := by
  cases builder with
  | none => rfl
  | some b =>
    simp only [evaluatorFor?] at h
    simp only [tryEvaluateUsingBuiltins]
    cases hev : EvaluatorForData b data z with
    | error _ => rfl
    | ok ev => simp [hev] at h

/-- P-79, composed with the builder: missing informer factory or client ⇒ the webhook path
sees the decision unchanged. -/
theorem P_79_builder_failure_skips_partial_evaluation (inf cl : Bool)
    (ce : Activation → OptionalVariableDeclarations → String → CELOutcome)
    (cc : Activation → String → Nat) (budget : Nat) (hf : inf = false ∨ cl = false)
    (d : ConditionsAwareDecision) (data : Option EvalData) (z : Option Authorizer) :
    tryEvaluateUsingBuiltins (reloadBuiltinBuilder inf cl ce cc budget) d data z = d := by
  rw [(P_79_builder_requires_informer_and_client inf cl ce cc budget).2 hf]
  rfl

end cel
