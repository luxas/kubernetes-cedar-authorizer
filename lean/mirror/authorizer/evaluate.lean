import authorizer.conditionsunion

/-!
# `authorizer/evaluate.lean`  ↔  `pkg/authorization/authorizer/evaluate.go`

`ConditionEvaluationResult`, `partiallyEvaluateConditionsMapInternal`,
`ConditionsMap.Evaluate` and `PartiallyEvaluateConditionsAwareDecision`.

Oracle modelling (see `interfaces.lean`): Go computes, per condition,
`r(c) = cond.Evaluate(data)` and falls back to `evaluateConditionFn(c, data)` when that is
unevaluatable (`evaluate.go:122-131`). Both are pure functions of `(c, data)` by contract
(`interfaces.go:298-310`), so the model takes the combined result as one function
`p : Condition → ConditionEvaluationResult` (the `data` argument is already applied).
A *total* oracle never returns `unevaluatable`.

Reason strings and error-wrapping formats are abstracted: `reasonOf c` and the
constant error texts below stand for the Go `fmt.Sprintf` output.
-/

namespace authorizer

/-- `evaluate.go:29-98`. The zero value is `unevaluatable`. -/
inductive ConditionEvaluationResult where
  | true_
  | false_
  | error (err : Err)
  | unevaluatable
  deriving DecidableEq, Repr

/-- The Go zero value is `unevaluatable` (`evaluate.go:42-46`). -/
instance : Inhabited ConditionEvaluationResult := ⟨.unevaluatable⟩

namespace ConditionEvaluationResult

/-- `ConditionEvaluationResultBoolean`, `evaluate.go:48-54`. -/
def Boolean (b : Bool) : ConditionEvaluationResult := if b then .true_ else .false_
/-- `ConditionEvaluationResultError`, `evaluate.go:56-67`; a nil error is normalised. -/
def Error' (e : Option Err) : ConditionEvaluationResult :=
  .error (e.getD "unspecified evaluation error")
/-- `ConditionsEvaluationResultUnevaluatable` (sic, plural in Go), `evaluate.go:70-75`. -/
def Unevaluatable : ConditionEvaluationResult := .unevaluatable

def IsTrue : ConditionEvaluationResult → Bool | .true_ => true | _ => false
def IsFalse : ConditionEvaluationResult → Bool | .false_ => true | _ => false
def IsError : ConditionEvaluationResult → Bool | .error _ => true | _ => false
def IsUnevaluatable : ConditionEvaluationResult → Bool | .unevaluatable => true | _ => false

end ConditionEvaluationResult

/-- `MaybeEvaluateConditionFunc` (`interfaces.go:302`) with `data` already applied. -/
abbrev MaybeEvaluateConditionFunc := Condition → ConditionEvaluationResult
/-- `EvaluateConditionFunc` (`interfaces.go:299`) with `data` already applied: total. -/
abbrev EvaluateConditionFunc := Condition → Bool × Option Err

/-- A total oracle never answers `unevaluatable` (`properties.md` §1.1: `R3 = R4 \ {U}`). -/
def MaybeEvaluateConditionFunc.Total (p : MaybeEvaluateConditionFunc) : Prop :=
  ∀ c, p c ≠ .unevaluatable

/-- The reason text Go builds for the first applied condition (`evaluate.go:204-208`). -/
def reasonOf (c : Condition) (appliedDescription : String) : String :=
  let r := s!"condition {c.ID} {appliedDescription}"
  if c.Description.length != 0 then r ++ s!" with description {c.Description}" else r

/-- Result of scanning one effect list (`conditionsToAppliedErroredUnevaluated`). -/
inductive phaseResult where
  /-- the first condition that evaluated to `true` -/
  | hit (c : Condition)
  /-- no hit: the errors and the unevaluatable conditions, in list order -/
  | miss (errored : List Err) (unevaluated : List Condition)

/-- `conditionsToAppliedErroredUnevaluated`, `evaluate.go:197-224`: scan in order, return at
the first `true`; otherwise collect errors and unevaluatable conditions. -/
def conditionsToAppliedErroredUnevaluated (conditions : List Condition) (p : MaybeEvaluateConditionFunc)
    (effect : String) : phaseResult :=
  go conditions [] []
where
  go : List Condition → List Err → List Condition → phaseResult
    | [], errs, unev => .miss errs unev
    | c :: rest, errs, unev =>
      match p c with
      | .true_ => .hit c
      | .false_ => go rest errs unev
      | .unevaluatable => go rest errs (unev ++ [c])
      | .error e => go rest (errs ++ [s!"condition {c.ID} with effect={effect} evaluated to an error: {e}"]) unev

def evaluationErrorsReason : String := "one or more conditional evaluation errors occurred"

/-- `partiallyEvaluateConditionsMapInternal`, `evaluate.go:121-192`. Precedence
`Deny > NoOpinion > Allow`; within one effect `true > error > unevaluatable > false`. -/
def partiallyEvaluateConditionsMapInternal (c : ConditionsMap) (p : MaybeEvaluateConditionFunc) :
    ConditionsAwareDecision :=
  let denyPhase : Option ConditionsAwareDecision :=
    if c.denyConditions.length != 0 then
      match conditionsToAppliedErroredUnevaluated c.DenyConditions p "Deny" with
      | .hit cond => some (.deny (reasonOf cond "denied the request") none)
      | .miss errored unevaluated =>
        if errored.length != 0 then some (.deny evaluationErrorsReason (aggregate errored))
        else if unevaluated.length != 0 then
          some (ConditionsAwareDecisionConditionsMap unevaluated c.noOpinionConditions c.allowConditions)
        else none
    else none
  match denyPhase with
  | some d => d
  | none =>
  let noOpinionPhase : Option ConditionsAwareDecision :=
    if c.noOpinionConditions.length != 0 then
      match conditionsToAppliedErroredUnevaluated c.NoOpinionConditions p "NoOpinion" with
      | .hit cond => some (.noOpinion (reasonOf cond "evaluated to NoOpinion") none)
      | .miss errored unevaluated =>
        if errored.length != 0 then some (.noOpinion evaluationErrorsReason (aggregate errored))
        else if unevaluated.length != 0 then
          some (ConditionsAwareDecisionConditionsMap [] unevaluated c.allowConditions)
        else none
    else none
  match noOpinionPhase with
  | some d => d
  | none =>
  let allowPhase : Option ConditionsAwareDecision :=
    if c.allowConditions.length != 0 then
      match conditionsToAppliedErroredUnevaluated c.AllowConditions p "Allow" with
      | .hit cond => some (.allow (reasonOf cond "allowed the request") none)
      | .miss errored unevaluated =>
        if errored.length != 0 then some (.noOpinion evaluationErrorsReason (aggregate errored))
        else if unevaluated.length != 0 then
          some (ConditionsAwareDecisionConditionsMap [] [] unevaluated)
        else none
    else none
  match allowPhase with
  | some d => d
  | none => .noOpinion "no conditions matched" none

/-- `ConditionsMap.Evaluate`, `evaluate.go:102-112`: full evaluation with a total oracle,
then `UnconditionalPartsOrError`. `evaluateConditionFn` here is the EFFECTIVE oracle
`c ↦ if ev₀ c ≠ U then ev₀ c else fn c` (README §Abstractions 2): Go consults
`cond.Evaluate` first (`:125`) and calls its parameter only on `unevaluatable`. (Go panics if `evaluateConditionFn` is nil and some
`cond.Evaluate` is unevaluatable; the Lean oracle is total by type.) -/
def ConditionsMap.Evaluate (c : ConditionsMap) (evaluateConditionFn : EvaluateConditionFunc) :
    Decision × String × Option Err :=
  (partiallyEvaluateConditionsMapInternal c (fun cond =>
      match evaluateConditionFn cond with
      | (_, some err) => .error err
      | (applied, none) => .Boolean applied)).UnconditionalPartsOrError

/-- `PartiallyEvaluateConditionsAwareDecision`, `evaluate.go:235-282`. Maps are evaluated
in place; a union is rebuilt child by child with the builder, stopping early after a
child that contains an unconditional Allow/Deny and copying the tail verbatim after the
first child that stays conditional; unconditional inputs are returned unchanged. -/
def PartiallyEvaluateConditionsAwareDecision (unevaluatedDecision : ConditionsAwareDecision)
    (p : MaybeEvaluateConditionFunc) : ConditionsAwareDecision :=
  match unevaluatedDecision with
  | .conditionsMap m => partiallyEvaluateConditionsMapInternal m p
  | .union l => loop l {} false
  | d => d
where
  loop : List (String × ConditionsAwareDecision) → ConditionsAwareDecisionUnion → Bool → ConditionsAwareDecision
    | [], chain, _ => chain.ToDecision
    | (name, sub) :: rest, chain, collectTail =>
      if collectTail then loop rest (chain.Add name sub) true
      else
        let evaluated := PartiallyEvaluateConditionsAwareDecision sub p
        let chain := chain.Add name evaluated
        if evaluated.ContainsUnconditionalAllowOrDeny then chain.ToDecision
        else loop rest chain (!evaluated.IsUnconditional)

/-! ### Reference semantics (`properties.md` §1.7)

The meaning every evaluator must agree with: maps by full evaluation, unions by
"first non-NoOpinion wins" (`kep.md:861-869`). -/

/-- `⟦d⟧ₒ` for a total oracle `o`. Defined for every tree; on an unconditional result of a
map it projects the decision (`dec?` is `some` there by `evalMap_total`). -/
def refSem (o : MaybeEvaluateConditionFunc) : ConditionsAwareDecision → Decision
  | .deny _ _ => .Deny
  | .allow _ _ => .Allow
  | .noOpinion _ _ => .NoOpinion
  | .conditionsMap m => ((partiallyEvaluateConditionsMapInternal m o).dec?).getD
      (partiallyEvaluateConditionsMapInternal m o).FailureDecision
  | .union l => seq l
where
  seq : List (String × ConditionsAwareDecision) → Decision
    | [] => .NoOpinion
    | (_, c) :: rest =>
      match refSem o c with
      | .NoOpinion => seq rest
      | r => r

end authorizer
