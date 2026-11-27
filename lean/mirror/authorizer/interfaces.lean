/-!
# `authorizer/interfaces.lean`  ↔  `pkg/authorization/authorizer/interfaces.go`

Base types shared by the whole model. Line references are to the Go file on the
reviewed HEAD (`review/shipped.md`).

Modelling decisions (see `lean/README.md` §Abstractions):
* Go `error` values are modelled as `Option Err` with `Err := String` (the message).
  Aggregation (`utilerrors.NewAggregate`) is `aggregate : List Err → Option Err`.
* `Condition.Evaluate` (the condition's own pre-compiled evaluator, `interfaces.go:295`)
  and the fallback `MaybeEvaluateConditionFunc` are folded into ONE oracle
  (`properties.md` §1.1): the evaluation functions in `evaluate.lean` take the
  effective per-condition result as an argument.
* `ConditionsData` is opaque: conditions are only ever evaluated through an oracle.
-/

namespace authorizer

/-- `interfaces.go:231-242`. The zero value is `DecisionDeny` (= 0). -/
inductive Decision where
  | Deny
  | Allow
  | NoOpinion
  deriving DecidableEq, Repr, Inhabited

/-- Go constant names, for correlation. -/
abbrev DecisionDeny      : Decision := .Deny
abbrev DecisionAllow     : Decision := .Allow
abbrev DecisionNoOpinion : Decision := .NoOpinion

/-- `interfaces.go:244-257`. -/
def Decision.String : Decision → String
  | .Deny => "Deny"
  | .Allow => "Allow"
  | .NoOpinion => "NoOpinion"

/-- A finite subset of `{Deny, Allow, NoOpinion}`; models `sets.Set[Decision]`. -/
structure DecisionSet where
  deny      : Bool := false
  allow     : Bool := false
  noOpinion : Bool := false
  deriving DecidableEq, Repr

namespace DecisionSet

def empty : DecisionSet := {}

def singleton : Decision → DecisionSet
  | .Deny => { deny := true }
  | .Allow => { allow := true }
  | .NoOpinion => { noOpinion := true }

/-- `sets.Set.Has`. -/
def Has (s : DecisionSet) : Decision → Bool
  | .Deny => s.deny
  | .Allow => s.allow
  | .NoOpinion => s.noOpinion

/-- `sets.Set.Insert`. -/
def Insert (s : DecisionSet) : Decision → DecisionSet
  | .Deny => { s with deny := true }
  | .Allow => { s with allow := true }
  | .NoOpinion => { s with noOpinion := true }

/-- `sets.Set.Delete`. -/
def Delete (s : DecisionSet) : Decision → DecisionSet
  | .Deny => { s with deny := false }
  | .Allow => { s with allow := false }
  | .NoOpinion => { s with noOpinion := false }

/-- `sets.Set.Union` (Go: `Insert(other.UnsortedList()...)`). -/
def union (s t : DecisionSet) : DecisionSet :=
  { deny := s.deny || t.deny, allow := s.allow || t.allow, noOpinion := s.noOpinion || t.noOpinion }

/-- `sets.Set.Len`. -/
def Len (s : DecisionSet) : Nat :=
  (if s.deny then 1 else 0) + (if s.allow then 1 else 0) + (if s.noOpinion then 1 else 0)

def Subset (s t : DecisionSet) : Prop :=
  ∀ d, s.Has d = true → t.Has d = true

instance : DecidableRel Subset := fun s t =>
  decidable_of_iff
    ((s.deny → t.deny) ∧ (s.allow → t.allow) ∧ (s.noOpinion → t.noOpinion))
    (by
      constructor
      · rintro ⟨h1, h2, h3⟩ d hd
        cases d <;> simp_all [Has]
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · exact fun hd => h .Deny hd
        · exact fun hd => h .Allow hd
        · exact fun hd => h .NoOpinion hd)

/-- `UnsortedList()[0]` when `Len = 1`: the single member. -/
def theOnly (s : DecisionSet) : Option Decision :=
  if s.Len = 1 then
    if s.deny then some .Deny else if s.allow then some .Allow else some .NoOpinion
  else none

end DecisionSet

/-- Go `error`: modelled by its message. -/
abbrev Err := String

/-- `utilerrors.NewAggregate`: `nil` for an empty list. The message format is abstracted. -/
def aggregate (errs : List Err) : Option Err :=
  match errs with
  | [] => none
  | _ => some (String.intercalate ", " errs)

/-- `ConditionsData` (`interfaces.go:313-348`): what conditions are evaluated against.
Kept opaque; the model never inspects it. -/
opaque ConditionsData : Type

/-- `Condition` (`interfaces.go:262-296`). The `Evaluate` method is NOT a field here:
it is folded into the oracle passed to the evaluation functions (see module doc). -/
structure Condition where
  /-- `GetID()`: required, unique within a map, domain-prefixed label key. -/
  ID : String
  /-- `GetType()`: optional, domain-prefixed label key when non-empty.
  (`Type` is a Lean keyword, hence `CondType`.) -/
  CondType : String := ""
  /-- `GetCondition()`: the opaque string encoding of the condition. -/
  Condition : String := ""
  /-- `GetDescription()`: optional, ≤ 1024 bytes. -/
  Description : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- Go getter names, for correlation. -/
def Condition.GetID (c : authorizer.Condition) : String := c.ID
def Condition.GetType (c : authorizer.Condition) : String := c.CondType
def Condition.GetCondition (c : authorizer.Condition) : String := c.Condition
def Condition.GetDescription (c : authorizer.Condition) : String := c.Description

/-- `interfaces.go:350`: the well-known in-process CEL condition type (PR #143024). -/
def ConditionTypeAuthorizationCEL : String := "authorizer.kubernetes.io/cel"

/-- `interfaces.go:128`: returned by authorizers that cannot evaluate conditions. -/
def ErrorConditionEvaluationNotSupported : Err := "condition evaluation not supported"

/-! ### Validation predicates (opaque)

`utilvalidation.IsDomainPrefixedKey` and `IsDNS1123Subdomain`
(`apimachinery/pkg/util/validation/validation.go`) are treated as opaque
decidable predicates: the model never needs their definitions, only that they are
functions of the string. -/

opaque IsDomainPrefixedKey : String → Bool
opaque IsDNS1123Subdomain : String → Bool

end authorizer
