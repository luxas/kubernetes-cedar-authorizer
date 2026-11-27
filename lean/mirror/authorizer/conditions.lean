import authorizer.conditionsmap

/-!
# `authorizer/conditions.lean`  ↔  `pkg/authorization/authorizer/conditions.go`

`ConditionsAwareDecision` and everything defined on it. Also hosts the map smart
constructor `ConditionsAwareDecisionConditionsMap` from `conditionsmap.go:138-185`
(see the note in `conditionsmap.lean`).

Go represents the five variants with an unexported tag plus payload fields; the zero
value is `Deny("", nil)`. Here the variants are constructors. Only the Go struct's
observable behaviour (the exported methods) is modelled.

The `union` payload in Go is a `ConditionsAwareDecisionUnion` carrying `inner`, a cached
`containsUnconditionalAllowOrDeny` flag and a cached `subDecisionsPossibleDecisions`
set. Both caches are derivable from `inner`, so the Lean payload is just the list; the
builder in `conditionsunion.lean` keeps its own state.
-/

namespace authorizer

/-- `conditions.go:60-68`. -/
inductive ConditionsAwareDecision where
  /-- unconditional Deny (`conditions.go:71-80`); the zero value is `deny "" none`. -/
  | deny (reason : String) (err : Option Err)
  /-- unconditional Allow (`conditions.go:82-89`). -/
  | allow (reason : String) (err : Option Err)
  /-- unconditional NoOpinion (`conditions.go:91-99`). -/
  | noOpinion (reason : String) (err : Option Err)
  /-- conditional, a map of conditions (`conditionsmap.go:176-184`). -/
  | conditionsMap (m : ConditionsMap)
  /-- conditional, an ordered tree of named sub-decisions (`conditionsunion.go:176-184`). -/
  | union (inner : List (String × ConditionsAwareDecision))
  deriving Inhabited, Repr

namespace ConditionsAwareDecision

/-! ### Constructors with Go names -/

/-- `ConditionsAwareDecisionDeny`, `conditions.go:71`. -/
abbrev _root_.authorizer.ConditionsAwareDecisionDeny (reason : String) (err : Option Err) :
    ConditionsAwareDecision := .deny reason err
/-- `ConditionsAwareDecisionAllow`, `conditions.go:82`. -/
abbrev _root_.authorizer.ConditionsAwareDecisionAllow (reason : String) (err : Option Err) :
    ConditionsAwareDecision := .allow reason err
/-- `ConditionsAwareDecisionNoOpinion`, `conditions.go:91`. -/
abbrev _root_.authorizer.ConditionsAwareDecisionNoOpinion (reason : String) (err : Option Err) :
    ConditionsAwareDecision := .noOpinion reason err

/-- `ConditionsAwareDecisionFromParts`, `conditions.go:102-118`. `Decision` has exactly three
values in Lean, so the Go `default` branch (unknown integer ⇒ Deny + aggregated error) is
unreachable and not modelled. -/
def _root_.authorizer.ConditionsAwareDecisionFromParts (unconditional : Decision) (reason : String)
    (err : Option Err) : ConditionsAwareDecision :=
  match unconditional with
  | .Allow => .allow reason err
  | .NoOpinion => .noOpinion reason err
  | .Deny => .deny reason err

/-- The Go zero value `ConditionsAwareDecision{}` (`conditions.go:57`). -/
def zero : ConditionsAwareDecision := .deny "" none

/-! ### Variant predicates, `conditions.go:121-157` -/

def IsAllow : ConditionsAwareDecision → Bool
  | .allow _ _ => true | _ => false
def IsNoOpinion : ConditionsAwareDecision → Bool
  | .noOpinion _ _ => true | _ => false
def IsDeny : ConditionsAwareDecision → Bool
  | .deny _ _ => true | _ => false
def IsConditionsMap : ConditionsAwareDecision → Bool
  | .conditionsMap _ => true | _ => false
def IsUnion : ConditionsAwareDecision → Bool
  | .union _ => true | _ => false
/-- `conditions.go:154-157`. -/
def IsUnconditional (d : ConditionsAwareDecision) : Bool :=
  d.IsAllow || d.IsDeny || d.IsNoOpinion

/-- `conditions.go:143-146`: the map, or the zero map for other variants. -/
def ConditionsMap : ConditionsAwareDecision → authorizer.ConditionsMap
  | .conditionsMap m => m | _ => {}

/-- `conditions.go:246-254`: the sub-decisions, empty unless `IsUnion`. -/
def UnionedDecisions : ConditionsAwareDecision → List (String × ConditionsAwareDecision)
  | .union l => l | _ => []

/-- `conditions.go:259-261`: empty for conditional variants. -/
def Reason : ConditionsAwareDecision → String
  | .deny r _ | .allow r _ | .noOpinion r _ => r
  | _ => ""

/-- `conditions.go:266-268`: `nil` for conditional variants. -/
def Error : ConditionsAwareDecision → Option Err
  | .deny _ e | .allow _ e | .noOpinion _ e => e
  | _ => none

/-- `ContainsUnconditionalAllowOrDeny`, `conditions.go:233-241`, with the union case
`conditionsunion.go:75-77,108-110` (the cached flag is `∃ child, cua child`). -/
def ContainsUnconditionalAllowOrDeny : ConditionsAwareDecision → Bool
  | .allow _ _ | .deny _ _ => true
  | .noOpinion _ _ | .conditionsMap _ => false
  | .union l => go l
where
  go : List (String × ConditionsAwareDecision) → Bool
    | [] => false
    | (_, c) :: rest => c.ContainsUnconditionalAllowOrDeny || go rest

/-- `PossibleDecisions`, `conditions.go:204-217`; union case `conditionsunion.go:116-129`:
`{N} ∪ ⋃ PD(cᵢ)`, minus `N` when some child contains an unconditional Allow/Deny. -/
def PossibleDecisions : ConditionsAwareDecision → DecisionSet
  | .allow _ _ => .singleton .Allow
  | .noOpinion _ _ => .singleton .NoOpinion
  | .deny _ _ => .singleton .Deny
  | .conditionsMap m => m.PossibleDecisions
  | .union l =>
    let s := (DecisionSet.singleton .NoOpinion).union (subPD l)
    if ContainsUnconditionalAllowOrDeny.go l then s.Delete .NoOpinion else s
where
  /-- the cached `subDecisionsPossibleDecisions`: union of the children's sets. -/
  subPD : List (String × ConditionsAwareDecision) → DecisionSet
    | [] => .empty
    | (_, c) :: rest => c.PossibleDecisions.union (subPD rest)

/-- `FailureDecision`, `conditions.go:224-229`. -/
def FailureDecision (d : ConditionsAwareDecision) : Decision :=
  if d.PossibleDecisions.Has .Deny then .Deny else .NoOpinion

/-! ### Splitters, `conditions.go:162-198` -/

/-- `UnconditionalPartsOrError`, `conditions.go:162-176`: a conditional input yields
`(FailureDecision, "failed closed", some err)`. -/
def UnconditionalPartsOrError (d : ConditionsAwareDecision) : Decision × String × Option Err :=
  match d with
  | .deny r e => (.Deny, r, e)
  | .allow r e => (.Allow, r, e)
  | .noOpinion r e => (.NoOpinion, r, e)
  | _ => (d.FailureDecision, "failed closed",
          some "conditional decision cannot be split into unconditional parts")

/-- `UnconditionalPartsOrFailClosed`, `conditions.go:181-198`: a conditional input yields
`(FailureDecision, descriptive reason, none)` so that the caller answers 403, not 500. -/
def UnconditionalPartsOrFailClosed (d : ConditionsAwareDecision) : Decision × String × Option Err :=
  match d with
  | .deny r e => (.Deny, r, e)
  | .allow r e => (.Allow, r, e)
  | .noOpinion r e => (.NoOpinion, r, e)
  | _ => (d.FailureDecision,
          s!"failed closed from conditional decision to {d.FailureDecision.String} during unconditional authorization",
          none)

/-- Projection to the unconditional decision when `IsUnconditional`. -/
def dec? : ConditionsAwareDecision → Option Decision
  | .deny _ _ => some .Deny
  | .allow _ _ => some .Allow
  | .noOpinion _ _ => some .NoOpinion
  | _ => none

end ConditionsAwareDecision

/-! ### Map smart constructor, `conditionsmap.go:138-185` -/

/-- `ConditionsAwareDecisionConditionsMap(deny, noOpinion, allow)`. Checks in Go order:
no conditions; too many (total > 128); NoOpinion-only (returns `noOpinion` WITHOUT
validating); then validation of `deny`, `noOpinion`, `allow` with one shared `seenIDs`.
Fail-closed is `deny` iff `deny ≠ []`, else `noOpinion` (`:140-146`). -/
def ConditionsAwareDecisionConditionsMap (denyConditions noOpinionConditions allowConditions : List Condition) :
    ConditionsAwareDecision :=
  let hasDenyEffect := denyConditions.length > 0
  let makeFailClosedError : Err → ConditionsAwareDecision := fun err =>
    if hasDenyEffect then .deny "failed closed" (some err) else .noOpinion "failed closed" (some err)
  let conditionsAmount := denyConditions.length + noOpinionConditions.length + allowConditions.length
  if conditionsAmount == 0 then
    .noOpinion "no conditions" (some "at least one condition must be passed to ConditionsAwareDecisionConditionsMap(), got none")
  else if conditionsAmount > MaxConditionsPerMap then
    makeFailClosedError "too many conditions"
  else if denyConditions.length == 0 && allowConditions.length == 0 then
    .noOpinion "only NoOpinion conditions always evaluate to NoOpinion" none
  else
    match validateConditions [] denyConditions with
    | .error e => makeFailClosedError e
    | .ok seen =>
      match validateConditions seen noOpinionConditions with
      | .error e => makeFailClosedError e
      | .ok seen =>
        match validateConditions seen allowConditions with
        | .error e => makeFailClosedError e
        | .ok _ => .conditionsMap { denyConditions, noOpinionConditions, allowConditions }

end authorizer
