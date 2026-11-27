import authorizer.conditionsunion

/-!
# `encoding/encoding.lean`  ↔  `pkg/apis/authorization/v1/encoding.go`

The v1 wire types (`staging/src/k8s.io/api/authorization/v1/types.go:434-625`, only the
decision-related ones) and the encoder/decoder between them and the in-memory
`authorizer.ConditionsAwareDecision`.

Modelling decisions:
* Go pointers `*UnconditionalDecision`, `*ConditionsMap` are `Option`.
* Go slices are `List`; nil and empty slices are NOT distinguished (both `[]`). The Go
  encoder always emits non-nil (empty) slices (`encoding.go:96-107`), so this loses
  nothing the encoder could observe; the decoder treats nil and empty the same.
* `ConditionsAwareDecisionType` is a Go `string`. The five known values are constructors;
  every other string is `unknown s`. The model does not forbid `unknown "Deny"` (which is
  not a distinct Go value); theorems about `unknown` hold for every `s`.
* `Type` is a Lean keyword: the decision's discriminator field is `«Type»`
  (Go `ConditionsAwareDecision.Type`) and the condition's type field is `CondType`
  (Go `Condition.Type`), as in `authorizer.Condition`.
* `Condition.Evaluate` / `GenericCondition.EvaluateFunc` are not modelled (see
  `lean/README.md` §Abstractions 2): a decoded condition is `GenericCondition` with
  `EvaluateFunc = nil` (`encoding.go:154-163`), which the model cannot tell apart.
-/

namespace v1

open authorizer (Err)

/-- `types.go:510-537`. `ConditionsAwareDecisionType` (a Go string enum). -/
inductive ConditionsAwareDecisionType where
  /-- `ConditionsAwareDecisionTypeDeny = "Deny"`, `types.go:518`. -/
  | Deny
  /-- `ConditionsAwareDecisionTypeAllow = "Allow"`, `types.go:521`. -/
  | Allow
  /-- `ConditionsAwareDecisionTypeNoOpinion = "NoOpinion"`, `types.go:526`. -/
  | NoOpinion
  /-- `ConditionsAwareDecisionTypeConditionsMap = "ConditionsMap"`, `types.go:530`. -/
  | ConditionsMap
  /-- `ConditionsAwareDecisionTypeUnion = "Union"`, `types.go:536`. -/
  | Union
  /-- Any other string (the Go type is an open `string`). -/
  | unknown (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- Go constant names, for correlation. -/
abbrev ConditionsAwareDecisionTypeDeny : ConditionsAwareDecisionType := .Deny
abbrev ConditionsAwareDecisionTypeAllow : ConditionsAwareDecisionType := .Allow
abbrev ConditionsAwareDecisionTypeNoOpinion : ConditionsAwareDecisionType := .NoOpinion
abbrev ConditionsAwareDecisionTypeConditionsMap : ConditionsAwareDecisionType := .ConditionsMap
abbrev ConditionsAwareDecisionTypeUnion : ConditionsAwareDecisionType := .Union

/-- The Go string value (`%q` in error messages). -/
def ConditionsAwareDecisionType.String : ConditionsAwareDecisionType → String
  | .Deny => "Deny"
  | .Allow => "Allow"
  | .NoOpinion => "NoOpinion"
  | .ConditionsMap => "ConditionsMap"
  | .Union => "Union"
  | .unknown s => s

/-- `UnconditionalDecision`, `types.go:612-625`. -/
structure UnconditionalDecision where
  Reason : String := ""
  EvaluationError : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- `Condition`, `types.go:432-468`. (`Type` is a keyword, hence `CondType`.) -/
structure Condition where
  ID : String
  Condition : String := ""
  CondType : String := ""
  Description : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- `ConditionsMap`, `types.go:470-509`. -/
structure ConditionsMap where
  DenyConditions : List Condition := []
  NoOpinionConditions : List Condition := []
  AllowConditions : List Condition := []
  deriving DecidableEq, Repr, Inhabited

mutual
/-- `ConditionsAwareDecision`, `types.go:539-594`. Mutually (and nested) recursive with
`NamedConditionsAwareDecision` through the `Union` slice. -/
inductive ConditionsAwareDecision where
  | mk («Type» : ConditionsAwareDecisionType)
       (Deny : Option UnconditionalDecision)
       (NoOpinion : Option UnconditionalDecision)
       (Allow : Option UnconditionalDecision)
       (ConditionsMap : Option ConditionsMap)
       (Union : List NamedConditionsAwareDecision)
/-- `NamedConditionsAwareDecision`, `types.go:596-610`. -/
inductive NamedConditionsAwareDecision where
  | mk (AuthorizerName : String) (Decision : ConditionsAwareDecision)
end

namespace ConditionsAwareDecision
/-- Field `type`, `types.go:546`. -/
def «Type» : ConditionsAwareDecision → ConditionsAwareDecisionType | mk t _ _ _ _ _ => t
/-- Field `deny`, `types.go:553`. -/
def Deny : ConditionsAwareDecision → Option UnconditionalDecision | mk _ d _ _ _ _ => d
/-- Field `noOpinion`, `types.go:560`. -/
def NoOpinion : ConditionsAwareDecision → Option UnconditionalDecision | mk _ _ n _ _ _ => n
/-- Field `allow`, `types.go:567`. -/
def Allow : ConditionsAwareDecision → Option UnconditionalDecision | mk _ _ _ a _ _ => a
/-- Field `conditionsMap`, `types.go:574`. -/
def ConditionsMap : ConditionsAwareDecision → Option v1.ConditionsMap | mk _ _ _ _ m _ => m
/-- Field `union`, `types.go:593`. -/
def Union : ConditionsAwareDecision → List NamedConditionsAwareDecision | mk _ _ _ _ _ u => u
end ConditionsAwareDecision

namespace NamedConditionsAwareDecision
/-- Field `authorizerName`, `types.go:605`. -/
def AuthorizerName : NamedConditionsAwareDecision → String | mk n _ => n
/-- Field `decision`, `types.go:609`. -/
def Decision : NamedConditionsAwareDecision → ConditionsAwareDecision | mk _ d => d
end NamedConditionsAwareDecision

/-- A v1 decision with only the discriminator and the given members set (Go composite
literal with omitted fields). -/
def ConditionsAwareDecision.lit («Type» : ConditionsAwareDecisionType)
    (Deny NoOpinion Allow : Option UnconditionalDecision := none)
    (ConditionsMap : Option v1.ConditionsMap := none)
    (Union : List NamedConditionsAwareDecision := []) : ConditionsAwareDecision :=
  .mk «Type» Deny NoOpinion Allow ConditionsMap Union

/-! ### Encoder, `encoding.go:30-107` -/

/-- `fromAuthorizerConditions`, `encoding.go:96-107`: always a non-nil slice. -/
def fromAuthorizerConditions (conds : List authorizer.Condition) : List Condition :=
  conds.map fun c =>
    { ID := c.GetID, Condition := c.GetCondition, CondType := c.GetType,
      Description := c.GetDescription }

/-- `errString` in `encoding.go:32-35`: `err.Error()` or `""` for nil. -/
def errString (e : Option Err) : String := e.getD ""

/-- `FromAuthorizerConditionsAwareDecision`, `encoding.go:31-94`. The Go `default`
branch (`:82-92`, unrecognized internal variant) is unreachable in the Lean model, whose
`authorizer.ConditionsAwareDecision` has exactly the five variants. -/
def FromAuthorizerConditionsAwareDecision :
    authorizer.ConditionsAwareDecision → ConditionsAwareDecision
  | .deny r e => .lit .Deny (Deny := some { Reason := r, EvaluationError := errString e })
  | .noOpinion r e => .lit .NoOpinion (NoOpinion := some { Reason := r, EvaluationError := errString e })
  | .allow r e => .lit .Allow (Allow := some { Reason := r, EvaluationError := errString e })
  | .conditionsMap m =>
    .lit .ConditionsMap (ConditionsMap := some
      { DenyConditions := fromAuthorizerConditions m.DenyConditions
        NoOpinionConditions := fromAuthorizerConditions m.NoOpinionConditions
        AllowConditions := fromAuthorizerConditions m.AllowConditions })
  | .union l => .lit .Union (Union := go l)
where
  /-- the loop `encoding.go:70-76` over `UnionedDecisions()` (order preserved). -/
  go : List (String × authorizer.ConditionsAwareDecision) → List NamedConditionsAwareDecision
    | [] => []
    | (n, c) :: rest => .mk n (FromAuthorizerConditionsAwareDecision c) :: go rest

/-! ### Decoder, `encoding.go:109-163` -/

/-- `UnconditionalEvaluationError`, `encoding.go:110-115`: `nil` for a nil pointer or an
empty string, else `errors.New(EvaluationError)`. -/
def UnconditionalEvaluationError : Option UnconditionalDecision → Option Err
  | none => none
  | some ud => if ud.EvaluationError.length == 0 then none else some ud.EvaluationError

/-- `UnconditionalReason`, `encoding.go:118-123`. -/
def UnconditionalReason : Option UnconditionalDecision → String
  | none => ""
  | some ud => ud.Reason

/-- `toAuthorizerConditions`, `encoding.go:154-163`: each becomes a `GenericCondition`
(with `EvaluateFunc = nil`, not modelled). -/
def toAuthorizerConditions (serializedConditions : List Condition) : List authorizer.Condition :=
  serializedConditions.map fun s =>
    { ID := s.ID, Condition := s.Condition, CondType := s.CondType, Description := s.Description }

/-- `ToAuthorizerConditionsAwareDecision`, `encoding.go:126-152`. Total: the only
recursion is into union children. -/
def ToAuthorizerConditionsAwareDecision (serializedDecision : ConditionsAwareDecision)
    (failClosed : Err → authorizer.ConditionsAwareDecision) : authorizer.ConditionsAwareDecision :=
  match serializedDecision with
  | .mk ty deny noOpinion allow cm union =>
    match ty with
    | .Allow => authorizer.ConditionsAwareDecisionAllow (UnconditionalReason allow) (UnconditionalEvaluationError allow)
    | .Deny => authorizer.ConditionsAwareDecisionDeny (UnconditionalReason deny) (UnconditionalEvaluationError deny)
    | .NoOpinion => authorizer.ConditionsAwareDecisionNoOpinion (UnconditionalReason noOpinion) (UnconditionalEvaluationError noOpinion)
    | .ConditionsMap =>
      match cm with
      | some m =>
        authorizer.ConditionsAwareDecisionConditionsMap
          (toAuthorizerConditions m.DenyConditions)
          (toAuthorizerConditions m.NoOpinionConditions)
          (toAuthorizerConditions m.AllowConditions)
      | none => authorizer.ConditionsAwareDecisionConditionsMap [] [] []
    | .Union => (go failClosed union {}).ToDecision
    | .unknown s => failClosed s!"unrecognized ConditionsAwareDecision.type=\"{s}\""
where
  /-- the loop `encoding.go:144-147`: `chain.Add(name, decode(child))` in order. -/
  go (failClosed : Err → authorizer.ConditionsAwareDecision) :
      List NamedConditionsAwareDecision → authorizer.ConditionsAwareDecisionUnion →
      authorizer.ConditionsAwareDecisionUnion
    | [], chain => chain
    | .mk n d :: rest, chain =>
      go failClosed rest (chain.Add n (ToAuthorizerConditionsAwareDecision d failClosed))

end v1
