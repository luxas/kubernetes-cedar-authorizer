import authorizer.conditions

/-!
# `authorizer/conditionsunion.lean`  ↔  `pkg/authorization/authorizer/conditionsunion.go`

The builder for Union decisions. Go mutates a `*ConditionsAwareDecisionUnion`; here
`Add` is a pure function returning the new builder state.
-/

namespace authorizer

/-- `conditionsunion.go:30-34`. -/
structure namedConditionsAwareDecision where
  conditionalAuthorizerName : String
  d : ConditionsAwareDecision

/-- `conditionsunion.go:37-56`. `subDecisionsPossibleDecisions` is kept as a field, as in Go
(it is the union of the children's `PossibleDecisions`, see `subPD_eq` in the properties). -/
structure ConditionsAwareDecisionUnion where
  inner : List (String × ConditionsAwareDecision) := []
  errs : List Err := []
  containsUnconditionalAllowOrDeny : Bool := false
  subDecisionsPossibleDecisions : DecisionSet := .empty

namespace ConditionsAwareDecisionUnion

/-- `conditionsunion.go:86-90`. -/
def hasConditionalAuthorizerName (u : ConditionsAwareDecisionUnion) (name : String) : Bool :=
  u.inner.any (fun nd => nd.1 == name)

/-- `conditionsunion.go:108-110`. -/
def ContainsUnconditionalAllowOrDeny (u : ConditionsAwareDecisionUnion) : Bool :=
  u.containsUnconditionalAllowOrDeny

/-- `conditionsunion.go:116-129`. -/
def PossibleDecisions (u : ConditionsAwareDecisionUnion) : DecisionSet :=
  let s := (DecisionSet.singleton .NoOpinion).union u.subDecisionsPossibleDecisions
  if u.ContainsUnconditionalAllowOrDeny then s.Delete .NoOpinion else s

/-- `conditionsunion.go:98-103`. -/
def FailureDecision (u : ConditionsAwareDecisionUnion) : Decision :=
  if u.PossibleDecisions.Has .Deny then .Deny else .NoOpinion

/-- `Add`, `conditionsunion.go:58-84`. A no-op once an unconditional Allow/Deny child is
present (no name validation happens either). Otherwise records name errors (empty,
duplicate, non-DNS-1123) and appends the child. -/
def Add (u : ConditionsAwareDecisionUnion) (authorizerName : String) (d : ConditionsAwareDecision) :
    ConditionsAwareDecisionUnion :=
  if u.ContainsUnconditionalAllowOrDeny then u
  else
    let errs := u.errs
    let errs := if authorizerName.length == 0 then errs ++ ["authorizerName must be non-empty"] else errs
    let errs := if u.hasConditionalAuthorizerName authorizerName then errs ++ [s!"duplicate authorizerName {authorizerName}"] else errs
    let errs := if !IsDNS1123Subdomain authorizerName then errs ++ ["invalid authorizerName"] else errs
    { inner := u.inner ++ [(authorizerName, d)]
      errs := errs
      containsUnconditionalAllowOrDeny := u.containsUnconditionalAllowOrDeny || d.ContainsUnconditionalAllowOrDeny
      subDecisionsPossibleDecisions := u.subDecisionsPossibleDecisions.union d.PossibleDecisions }

end ConditionsAwareDecisionUnion

/-- `collectReasonsAndErrors`, `conditionsunion.go:187-208`: depth-first collection of the
reasons/errors of leaves of kind `toCollect`, prefixed by the authorizer-name path. -/
def collectReasonsAndErrors (prefix_ : List String) (d : ConditionsAwareDecision) (toCollect : Decision) :
    List String × List Err :=
  match d with
  | .allow r e => leaf (toCollect == .Allow) r e
  | .noOpinion r e => leaf (toCollect == .NoOpinion) r e
  | .deny r e => leaf (toCollect == .Deny) r e
  | .conditionsMap _ => ([], [])
  | .union l => go l
where
  leaf (isMatch : Bool) (r : String) (e : Option Err) : List String × List Err :=
    if isMatch then
      ((if r.length != 0 then [s!"{String.intercalate ": " prefix_}: \{{r}}"] else []),
       (match e with | some err => [s!"{String.intercalate ": " prefix_}: {err}"] | none => []))
    else ([], [])
  go : List (String × ConditionsAwareDecision) → List String × List Err
    | [] => ([], [])
    | (n, c) :: rest =>
      let (rs, es) := collectReasonsAndErrors (prefix_ ++ [n]) c toCollect
      let (rs', es') := go rest
      (rs ++ rs', es ++ es')

namespace ConditionsAwareDecisionUnion

/-- `ToDecision`, `conditionsunion.go:135-185`. Errors ⇒ fail closed with `FailureDecision`;
a singleton `PossibleDecisions` ⇒ fold to that unconditional decision with aggregated
reasons/errors; otherwise emit the Union. -/
def ToDecision (u : ConditionsAwareDecisionUnion) : ConditionsAwareDecision :=
  if u.errs.length != 0 then
    ConditionsAwareDecisionFromParts u.FailureDecision "failed closed" (aggregate u.errs)
  else
    match u.PossibleDecisions.theOnly with
    | some only =>
      let collected := u.inner.map (fun nd => collectReasonsAndErrors [nd.1] nd.2 only)
      let reasons := collected.flatMap (·.1)
      let errs := collected.flatMap (·.2)
      ConditionsAwareDecisionFromParts only (String.intercalate ", " reasons) (aggregate errs)
    | none => .union u.inner

end ConditionsAwareDecisionUnion

end authorizer
