import authorizer.interfaces

/-!
# `authorizer/conditionsmap.lean`  ↔  `pkg/authorization/authorizer/conditionsmap.go`

The `ConditionsMap` value type, its limits, `validateConditions`, `PossibleDecisions`
and `FailureDecision`.

The smart constructor `ConditionsAwareDecisionConditionsMap` (`conditionsmap.go:138-185`)
returns a `ConditionsAwareDecision`, so in Lean it lives in `conditions.lean` right after
the inductive type (Lean modules cannot be mutually recursive). The `GenericCondition`
struct (`conditionsmap.go:224-254`) is subsumed by `Condition` in `interfaces.lean`.
-/

namespace authorizer

/-- `conditionsmap.go:34-47`. Invariant (established only by the smart constructor):
`denyConditions ≠ [] ∨ allowConditions ≠ []`, see `ConditionsMap.WF`. -/
structure ConditionsMap where
  denyConditions      : List Condition := []
  noOpinionConditions : List Condition := []
  allowConditions     : List Condition := []
  deriving DecidableEq, Repr, Inhabited

/-- `conditionsmap.go:116`. Total across the three lists. -/
def MaxConditionsPerMap : Nat := 128
/-- `conditionsmap.go:119`. -/
def MaxConditionBytes : Nat := 10240
/-- `conditionsmap.go:122`. -/
def MaxConditionDescriptionBytes : Nat := 1024

namespace ConditionsMap

/-- `conditionsmap.go:59-61`. -/
def Length (c : ConditionsMap) : Nat :=
  c.denyConditions.length + c.noOpinionConditions.length + c.allowConditions.length

/-- `conditionsmap.go:65-99`: the iterators, in construction order. -/
def DenyConditions (c : ConditionsMap) : List Condition := c.denyConditions
def NoOpinionConditions (c : ConditionsMap) : List Condition := c.noOpinionConditions
def AllowConditions (c : ConditionsMap) : List Condition := c.allowConditions

/-- `conditionsmap.go:103-112`. -/
def PossibleDecisions (c : ConditionsMap) : DecisionSet :=
  let s := DecisionSet.singleton .NoOpinion
  let s := if c.allowConditions.length > 0 then s.Insert .Allow else s
  if c.denyConditions.length > 0 then s.Insert .Deny else s

/-- `conditionsmap.go:50-56`. -/
def FailureDecision (c : ConditionsMap) : Decision :=
  if c.PossibleDecisions.Has .Deny then .Deny else .NoOpinion

/-- All conditions in evaluation order `D ++ N ++ A`. -/
def all (c : ConditionsMap) : List Condition :=
  c.denyConditions ++ c.noOpinionConditions ++ c.allowConditions

end ConditionsMap

/-- Per-condition validity, `conditionsmap.go:197-217` (everything except the duplicate-ID
check, which is stateful across lists). -/
def Condition.valid (c : authorizer.Condition) : Bool :=
  IsDomainPrefixedKey c.ID
    && c.Condition.utf8ByteSize ≤ MaxConditionBytes
    && (c.CondType.length == 0 || IsDomainPrefixedKey c.CondType)
    && c.Description.utf8ByteSize ≤ MaxConditionDescriptionBytes

/-- `validateConditions(seenIDs, conditions)`, `conditionsmap.go:187-220`.
Returns the updated `seenIDs` on success, or the first error. Order of checks per
condition: duplicate ID, ID format, condition size, type format, description size.
Error texts are abstracted to a tag. -/
def validateConditions (seenIDs : List String) : List Condition → Except Err (List String)
  | [] => .ok seenIDs
  | c :: rest =>
    if seenIDs.contains c.ID then .error s!"duplicate condition ID {c.ID}"
    else if !IsDomainPrefixedKey c.ID then .error "invalid condition: id"
    else if c.Condition.utf8ByteSize > MaxConditionBytes then .error "condition too large"
    else if c.CondType.length != 0 && !IsDomainPrefixedKey c.CondType then .error "invalid condition: type"
    else if c.Description.utf8ByteSize > MaxConditionDescriptionBytes then .error "description too large"
    else validateConditions (c.ID :: seenIDs) rest

/-- `WFMap` (`properties.md` §1.2): exactly what the smart constructor guarantees about
an emitted map. `1 ≤ total ≤ 128`, not NoOpinion-only, IDs unique across all three
lists, every condition valid. -/
def ConditionsMap.WF (c : ConditionsMap) : Prop :=
  1 ≤ c.Length ∧ c.Length ≤ MaxConditionsPerMap
  ∧ (c.denyConditions ≠ [] ∨ c.allowConditions ≠ [])
  ∧ (c.all.map Condition.ID).Nodup
  ∧ ∀ x ∈ c.all, x.valid = true

end authorizer
