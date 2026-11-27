import authorizer.evaluate

/-!
# `cel/authorization_conditions.lean`  ↔  `pkg/admission/plugin/cel/authorization_conditions.go`

The in-process CEL evaluator for `authorizer.kubernetes.io/cel` conditions
(PR #143024, **unmerged**; `properties.md` §1.12 and §J). Line references are to
`staging/src/k8s.io/apiserver/pkg/admission/plugin/cel/authorization_conditions.go`.

Abstractions (in addition to `lean/README.md` §Abstractions):
* **CEL is an opaque oracle.** Compilation plus evaluation of one expression string in one
  activation is `celEval : String → CELOutcome`; its runtime cost is `celCost : String → Nat`.
  Both are fields of the `Builder` (applied to the activation and the declared optional
  variables), so every theorem quantifies over them. The CEL library's own per-call
  abort (`cel.CostLimit(celconfig.PerCallLimit)`, `pkg/cel/environment/base.go:91`) is
  inside the oracle: it surfaces as `CELOutcome.runtimeError`.
* **Cost budget.** `activation.Evaluate` (`activation.go:141-212`) checks the actual cost
  against `runtimeCELCostBudget` *after* evaluation (`activation.go:193`); exceeding it is a
  Go `err`, mapped to `.error` (`:169-171`). Cost exactly equal to the budget is accepted.
  Both limits are reachable in production: cel-go charges a call's cost only after the call
  returns (`cel-go/.../tracker.go` `recordCallCost` → `checkLimit`), so one expensive call
  (e.g. `sets.intersects` over two ~3,500-element lists, cost ≈ 12M) overshoots the 1M
  `PerCallLimit` and the 10M budget in a single step, and neither limit bounds the CPU spent
  inside that call (verified by the `cel` equivalence review with an in-package probe).
* **`ConditionsData`** for this evaluator is `EvalData` (below): only the facts
  `EvaluatorForData` branches on. `nil` data is `Option.none`.
* **Go nil pointers** for `informerFactory`/`client` are Bools; a nil `Condition` cannot be
  expressed (Lean `Condition` is a value), so the `:150-152` branch is not modelled.
* **`NewCachingAuthorizer`** (`admission/plugin/authorizer/caching_authorizer.go:48`) is the
  identity on the answer function: by Axiom O1 (purity) caching is semantically transparent
  within one `EvaluatorForData` call. The cache's lifetime is not modelled.
* Contexts, `CompositionContext`, the admission request object, logging are omitted.
-/

namespace cel

open authorizer

/-- Request attributes passed to an authorizer (`authorizer.Attributes`,
`pkg/authorization/authorizer/interfaces.go`). Opaque. -/
opaque Attributes : Type

/-- `authorizer.UnconditionalAuthorizer` (`interfaces.go:86-88`): only `Authorize`. The answer
type is the three-valued `Decision`, which has no conditional variant. -/
structure UnconditionalAuthorizer where
  Authorize : Attributes → Decision × String × Option Err

/-- `authorizer.Authorizer` (`interfaces.go:84-125`): `Authorize` plus the conditions-aware
entry point. -/
structure Authorizer where
  Authorize : Attributes → Decision × String × Option Err
  ConditionsAwareAuthorize : Attributes → ConditionsAwareDecision

/-- Go's implicit interface narrowing `Authorizer → UnconditionalAuthorizer`: keeps `Authorize`
only. -/
def Authorizer.toUnconditional (a : Authorizer) : UnconditionalAuthorizer :=
  { Authorize := a.Authorize }

/-- `admissionauthorizer.NewCachingAuthorizer` (`caching_authorizer.go:48-53`). Transparent
under Axiom O1 (see module doc). Its argument type is `UnconditionalAuthorizer`. -/
def NewCachingAuthorizer (in_ : UnconditionalAuthorizer) : UnconditionalAuthorizer := in_

/-- `*v1.Namespace` as fetched by the namespace matcher. Only identity matters here. -/
structure Namespace where
  name : String
  deriving DecidableEq, Repr

/-- The facts about `ConditionsData` that `EvaluatorForData` (`:79-116`) branches on. -/
structure EvalData where
  /-- `data.(*admission.VersionedAttributes)` succeeds (`:84-87`). -/
  isVersionedAttributes : Bool
  /-- `attrs.GetNamespace()` (`:122`). -/
  GetNamespace : String := ""
  /-- `gvk == {Group:"", Version:"v1", Kind:"Namespace"}` (`:126`). -/
  kindIsCoreV1Namespace : Bool := false
  /-- Result of `nsmatcher.GetNamespace(ctx, namespaceName)` (`:133`); `none` = error. -/
  namespaceLookup : Option Namespace := none
  /-- `newActivation(...)` succeeds (`:106-109`). -/
  activationOk : Bool := true

/-- `OptionalVariableDeclarations` (`:114`). -/
structure OptionalVariableDeclarations where
  HasParams : Bool
  HasAuthorizer : Bool

/-- `evaluationActivation` built by `newActivation` (`:106`): what CEL can read. The
`authorizer` CEL variable is `authorizer`; its only operation is `Authorize`. -/
structure Activation where
  data : EvalData
  /-- `CreateNamespaceObject(ns)` (`:139`); `none` = nil namespace (cluster-scoped). -/
  namespaceObject : Option Namespace
  /-- `OptionalVariableBindings.Authorizer` (`:101-106`). -/
  authorizer : Option UnconditionalAuthorizer

/-- Outcome of compiling and evaluating one CEL expression (opaque oracle). `value b` is a
CEL bool: compilation enforces `ReturnTypes = [bool]` with `IsExactType` (`:186-188`,
`compile.go:189-205`), so `dyn`-typed expressions fail compilation. -/
inductive CELOutcome where
  | compileError
  | runtimeError
  | value (b : Bool)
  deriving DecidableEq, Repr

/-- `celAuthorizationConditionsEvaluatorBuilder` (`:73-77`) with the CEL oracle. -/
structure Builder where
  /-- `compiler.CompileCELExpression` + `activation.Evaluate` (`:163-168`), opaque. -/
  celEval : Activation → OptionalVariableDeclarations → String → CELOutcome
  /-- Actual runtime cost of the expression in the activation (`activation.go:185`). -/
  celCost : Activation → String → Nat
  /-- `runtimeCELCostBudget` (`:76`), per condition. -/
  runtimeCELCostBudget : Nat

/-- `NewAuthorizationConditionsEvaluatorBuilder` (`:53-71`): errors on nil informer factory
(`:54-56`) or nil client (`:57-59`), in that order. -/
def NewAuthorizationConditionsEvaluatorBuilder (informerFactoryPresent clientPresent : Bool)
    (celEval : Activation → OptionalVariableDeclarations → String → CELOutcome)
    (celCost : Activation → String → Nat) (runtimeCELCostBudget : Nat) : Except Err Builder :=
  if !informerFactoryPresent then
    .error "NewAuthorizationConditionsEvaluator: informerFactory is required"
  else if !clientPresent then
    .error "NewAuthorizationConditionsEvaluator: client is required"
  else .ok { celEval, celCost, runtimeCELCostBudget }

/-- The caller, `pkg/kubeapiserver/authorizer/reload.go:204-211`: on error a warning is logged
and the builder stays nil, so conditions go to the webhook. -/
def reloadBuiltinBuilder (informerFactoryPresent clientPresent : Bool)
    (celEval : Activation → OptionalVariableDeclarations → String → CELOutcome)
    (celCost : Activation → String → Nat) (runtimeCELCostBudget : Nat) : Option Builder :=
  match NewAuthorizationConditionsEvaluatorBuilder informerFactoryPresent clientPresent celEval celCost
      runtimeCELCostBudget with
  | .ok b => some b
  | .error _ => none

/-- `getNamespace` (`:119-140`): the `Namespace` kind's own namespace is cleared (`:126-128`);
an empty name means cluster-scoped (nil namespace); otherwise the lookup must succeed. -/
def getNamespace (attrs : EvalData) : Except Err (Option Namespace) :=
  let namespaceName := if attrs.kindIsCoreV1Namespace then "" else attrs.GetNamespace
  if namespaceName != "" then
    match attrs.namespaceLookup with
    | some ns => .ok (some ns)
    | none => .error "namespace lookup failed"
  else .ok none

/-- `celAuthorizationConditionsEvaluator` (`:142-146`). -/
structure Evaluator where
  builder : Builder
  optionalVarsDecls : OptionalVariableDeclarations
  activation : Activation

/-- `EvaluatorForData` (`:79-116`). Errors, in order: nil data (`:80-82`), not
`*VersionedAttributes` (`:84-87`), namespace lookup (`:91-94`), activation (`:106-109`). The
`authorizer` variable is the caching wrapper around `apiServerAuthorizer` narrowed to
`UnconditionalAuthorizer` (`:101-104`) and is declared iff `apiServerAuthorizer ≠ nil` (`:114`). -/
def EvaluatorForData (b : Builder) (data : Option EvalData) (apiServerAuthorizer : Option Authorizer) :
    Except Err Evaluator :=
  match data with
  | none => .error "programmer error: data is required"
  | some versionedAttrs =>
    if !versionedAttrs.isVersionedAttributes then
      .error "in-process conditions evaluation only supported when data is of type *admission.VersionedAttributes"
    else
      match getNamespace versionedAttrs with
      | .error e => .error e
      | .ok ns =>
        let authz : Option UnconditionalAuthorizer :=
          apiServerAuthorizer.map (fun a => NewCachingAuthorizer a.toUnconditional)
        if !versionedAttrs.activationOk then .error "newActivation failed"
        else .ok {
          builder := b
          activation := { data := versionedAttrs, namespaceObject := ns, authorizer := authz }
          optionalVarsDecls := { HasParams := false, HasAuthorizer := apiServerAuthorizer.isSome } }

namespace Evaluator

/-- The oracle as seen by one evaluator: `celEval : String → CELOutcome`. -/
def celEval (e : Evaluator) : String → CELOutcome :=
  e.builder.celEval e.activation e.optionalVarsDecls

/-- Actual cost of one expression in this evaluator's activation. -/
def celCost (e : Evaluator) : String → Nat := e.builder.celCost e.activation

/-- `EvaluateCondition` (`:148-178`). Unevaluatable for a non-CEL type (`:153-155`) or an
empty expression (`:158-161`; Go `len` is bytes, zero iff zero characters). A compile error
is an `EvalResult.Error` (`activation.go:148-155`, `:173-175`); cost above the budget is a Go
`err` (`activation.go:193-199`, `:169-171`); a runtime error is an `EvalResult.Error`
(`activation.go:203-207`). Otherwise `Boolean(result == true)` (`:177`). -/
def EvaluateCondition (e : Evaluator) (condition : Condition) : ConditionEvaluationResult :=
  if condition.GetType != ConditionTypeAuthorizationCEL then
    ConditionEvaluationResult.Unevaluatable
  else
    let condStr := condition.GetCondition
    if condStr.length == 0 then ConditionEvaluationResult.Unevaluatable
    else
      match e.celEval condStr with
      | .compileError => .error "compilation error"
      | .runtimeError =>
        if e.celCost condStr > e.builder.runtimeCELCostBudget then .error "out of cost budget"
        else .error "runtime error"
      | .value b =>
        if e.celCost condStr > e.builder.runtimeCELCostBudget then .error "out of cost budget"
        else ConditionEvaluationResult.Boolean (b == true)

/-- Cost charged for one condition: zero when it is never compiled or does not compile
(no evaluation, `activation.go:148-155`), else the actual cost. -/
def conditionCost (e : Evaluator) (c : Condition) : Nat :=
  if c.GetType != ConditionTypeAuthorizationCEL then 0
  else if c.GetCondition.length == 0 then 0
  else match e.celEval c.GetCondition with
    | .compileError => 0
    | _ => e.celCost c.GetCondition

end Evaluator

/-- Total cost of evaluating every condition of a map once (an upper bound on what one
`PartiallyEvaluateConditionsAwareDecision` over the map can spend). -/
def mapCost (e : Evaluator) (m : ConditionsMap) : Nat :=
  (m.all.map e.conditionCost).sum

/-- The builtin-evaluator path of the webhook authorizer, `tryEvaluateUsingBuiltins`
(`plugin/pkg/authorizer/webhook/webhook.go:951-973`), copied here so P-79 can be stated
without importing `webhook/webhook.lean`. Errors from the builtin evaluator become
unevaluatable (`webhook.go:968-970`). `authz` is the context's API-server authorizer (`:956`). -/
def tryEvaluateUsingBuiltins (builder : Option Builder) (unevaluatedDecision : ConditionsAwareDecision)
    (data : Option EvalData) (authz : Option Authorizer) : ConditionsAwareDecision :=
  match builder with
  | none => unevaluatedDecision
  | some b =>
    match EvaluatorForData b data authz with
    | .error _ => unevaluatedDecision
    | .ok ev =>
      PartiallyEvaluateConditionsAwareDecision unevaluatedDecision (fun cond =>
        let res := ev.EvaluateCondition cond
        if res.IsError then ConditionEvaluationResult.Unevaluatable else res)

/-- The `Option` view of builder + `EvaluatorForData` (`webhook.go:952-961`). -/
def evaluatorFor? (builder : Option Builder) (data : Option EvalData) (authz : Option Authorizer) :
    Option Evaluator :=
  match builder with
  | none => none
  | some b =>
    match EvaluatorForData b data authz with
    | .ok ev => some ev
    | .error _ => none

end cel
