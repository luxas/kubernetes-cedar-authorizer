import authorizer.conditionsunion

/-!
# `union/union.lean`  ↔  `pkg/authorization/union/union.go`

The union authorizer: `unionAuthzHandler` with its `chain` and `nameToAuthorizer`
routing table, `New`, `Authorize`, `ConditionsAwareAuthorize`, `EvaluateConditions` and
`evaluateConditions`.

Modelling decisions:
* `context.Context` is dropped; authorizers are pure functions of their inputs.
* `authorizer.Attributes` and `authorizer.Authorizer` (`interfaces.go:86-124`) are declared
  here, in namespace `union`; `filters/authorization.lean` declares the same shape
  independently (accepted duplication, the two are never imported together).
* The Go map `nameToAuthorizer` is an association list in insertion order; `lookup` is
  `find?` on the key. `New` rejects duplicates, so the first hit is the only one.
* `New` returns the concrete `unionAuthzHandler` (Go returns it as an `authorizer.Authorizer`
  interface value); `unionAuthzHandler.toAuthorizer` is the interface conversion
  (`union.go:38`).
* The Go `for … range` loops are written as structurally recursive top-level helpers
  (`authorizeLoop`, `caaLoop`, `evaluateLoop`) taking the loop accumulators explicitly.
* `NewRuleResolvers` / `RulesFor` (`union.go:197-231`) are out of scope (no property uses them).
* Error and reason texts are approximations of the Go `fmt.Sprintf` output; no theorem
  relies on them.
-/

namespace union

open authorizer

/-- `authorizer.Attributes` (`interfaces.go`): the request attributes. Opaque. -/
opaque Attributes : Type

/-- `authorizer.Authorizer` (`interfaces.go:86-124`), without `context.Context`. -/
structure Authorizer where
  /-- `Authorize(ctx, a) (Decision, string, error)`, `interfaces.go:94`. -/
  Authorize : Attributes → Decision × String × Option Err
  /-- `ConditionsAwareAuthorize(ctx, a) ConditionsAwareDecision`, `interfaces.go:114`. -/
  ConditionsAwareAuthorize : Attributes → ConditionsAwareDecision
  /-- `EvaluateConditions(ctx, decision, data) (Decision, string, error)`, `interfaces.go:123`. -/
  EvaluateConditions : ConditionsAwareDecision → ConditionsData → Decision × String × Option Err

/-- `NamedAuthorizer`, `union.go:46-53`. The name must be unique within one union. -/
structure NamedAuthorizer where
  AuthorizerName : String
  Authorizer : Authorizer

/-- `unionAuthzHandler`, `union.go:40-44`. -/
structure unionAuthzHandler where
  chain : List NamedAuthorizer
  /-- `map[string]authorizer.Authorizer`, as an association list. -/
  nameToAuthorizer : List (String × Authorizer)

/-- Go map read `m[name]` with the `ok` flag (`union.go:62,189`). -/
def lookup (m : List (String × Authorizer)) (name : String) : Option Authorizer :=
  (m.find? (fun p => p.1 == name)).map (·.2)

/-- The loop of `New`, `union.go:57-69`: per handler, reject an empty name, reject a
duplicate name, then insert. NOTE: no DNS-1123 check (contrast `conditionsunion.go:70`). -/
def buildNameToAuthorizer : List NamedAuthorizer → List (String × Authorizer) →
    Except Err (List (String × Authorizer))
  | [], m => .ok m
  | handler :: rest, m =>
    if handler.AuthorizerName.length == 0 then
      .error "empty AuthorizerName in union.New is invalid"
    else if (lookup m handler.AuthorizerName).isSome then
      .error s!"duplicate AuthorizerName {handler.AuthorizerName} in union.New"
    else buildNameToAuthorizer rest (m ++ [(handler.AuthorizerName, handler.Authorizer)])

/-- `New(authorizationHandlers ...NamedAuthorizer)`, `union.go:56-74`. -/
def New (authorizationHandlers : List NamedAuthorizer) : Except Err unionAuthzHandler :=
  match buildNameToAuthorizer authorizationHandlers [] with
  | .error e => .error e
  | .ok m => .ok { chain := authorizationHandlers, nameToAuthorizer := m }

/-- `if err != nil { errlist = append(errlist, err) }` (`union.go:86-88,176-178`). -/
def appendErr (errlist : List Err) : Option Err → List Err
  | some e => errlist ++ [e]
  | none => errlist

/-- `if len(reason) != 0 { reasonlist = append(reasonlist, fmt.Sprintf("%s: %s", name, reason)) }`
(`union.go:89-91,179-181`). -/
def appendReason (reasonlist : List String) (name reason : String) : List String :=
  if reason.length != 0 then reasonlist ++ [s!"{name}: {reason}"] else reasonlist

/-- The loop of `Authorize`, `union.go:83-99`: the first Allow/Deny is returned verbatim;
otherwise errors and `name: reason` strings are accumulated and NoOpinion is returned. -/
def authorizeLoop (a : Attributes) : List NamedAuthorizer → List Err → List String →
    Decision × String × Option Err
  | [], errlist, reasonlist =>
    (.NoOpinion, String.intercalate "\n" reasonlist, aggregate errlist)
  | currAuthzHandler :: rest, errlist, reasonlist =>
    let (decision, reason, err) := currAuthzHandler.Authorizer.Authorize a
    let errlist := appendErr errlist err
    let reasonlist := appendReason reasonlist currAuthzHandler.AuthorizerName reason
    match decision with
    | .Allow | .Deny => (decision, reason, err)
    | .NoOpinion => authorizeLoop a rest errlist reasonlist

/-- `unionAuthzHandler.Authorize`, `union.go:77-100`. -/
def unionAuthzHandler.Authorize (authzHandler : unionAuthzHandler) (a : Attributes) :
    Decision × String × Option Err :=
  authorizeLoop a authzHandler.chain [] []

/-- The loop of `ConditionsAwareAuthorize`, `union.go:107-122`: `Add` every child, and stop
(with `ToDecision`) right after a child that contains an unconditional Allow/Deny. -/
def caaLoop (a : Attributes) : List NamedAuthorizer → ConditionsAwareDecisionUnion →
    ConditionsAwareDecision
  | [], decisions => decisions.ToDecision
  | currAuthzHandler :: rest, decisions =>
    let decision := currAuthzHandler.Authorizer.ConditionsAwareAuthorize a
    let decisions := decisions.Add currAuthzHandler.AuthorizerName decision
    if decision.ContainsUnconditionalAllowOrDeny then decisions.ToDecision
    else caaLoop a rest decisions

/-- `unionAuthzHandler.ConditionsAwareAuthorize`, `union.go:104-127`. -/
def unionAuthzHandler.ConditionsAwareAuthorize (authzHandler : unionAuthzHandler)
    (a : Attributes) : ConditionsAwareDecision :=
  caaLoop a authzHandler.chain {}

/-- `unionAuthzHandler.evaluateConditions`, `union.go:188-194`: route by name through
`nameToAuthorizer`; a missing name fails closed with the sub-decision's `FailureDecision`. -/
def unionAuthzHandler.evaluateConditions (authzHandler : unionAuthzHandler)
    (authorizerName : String) (unevaluatedSubDecision : ConditionsAwareDecision)
    (data : ConditionsData) : Decision × String × Option Err :=
  match lookup authzHandler.nameToAuthorizer authorizerName with
  | none => (unevaluatedSubDecision.FailureDecision, "failed closed",
             some s!"couldn't find authorizer with name: {authorizerName}")
  | some z => z.EvaluateConditions unevaluatedSubDecision data

/-- The ConditionsMap/Union branch of the `EvaluateConditions` loop, `union.go:160-165`:
delegate, then clamp an impossible result to `FailureDecision` with an error. -/
def unionAuthzHandler.evaluateAndClamp (authzHandler : unionAuthzHandler)
    (name : String) (sub : ConditionsAwareDecision) (data : ConditionsData) :
    Decision × String × Option Err :=
  let r := authzHandler.evaluateConditions name sub data
  if sub.PossibleDecisions.Has r.1 then r
  else (sub.FailureDecision, "failed closed",
        some s!"evaluated to decision {r.1.String}, but only the possible decisions were possible")

/-- Per-child result of the `EvaluateConditions` loop, `union.go:147-168`. In Go the Deny
and Allow leaf cases `return` directly (`:152-155`); here they yield the same triple and the
caller's `switch decision` (`:170-172`) returns it, which is the same observable result.
The `default` branch (`:166-167`) is unreachable: the Lean variants are exhaustive. -/
def unionAuthzHandler.evalChild (authzHandler : unionAuthzHandler)
    (name : String) (sub : ConditionsAwareDecision) (data : ConditionsData) :
    Decision × String × Option Err :=
  match sub with
  | .deny r e => (.Deny, r, e)
  | .allow r e => (.Allow, r, e)
  | .noOpinion r e => (.NoOpinion, r, e)
  | .conditionsMap m => authzHandler.evaluateAndClamp name (.conditionsMap m) data
  | .union l => authzHandler.evaluateAndClamp name (.union l) data

/-- The loop of `EvaluateConditions`, `union.go:144-185`. -/
def evaluateLoop (authzHandler : unionAuthzHandler) (data : ConditionsData) :
    List (String × ConditionsAwareDecision) → List Err → List String →
    Decision × String × Option Err
  | [], errlist, reasonlist =>
    (.NoOpinion, String.intercalate "\n" reasonlist, aggregate errlist)
  | (currentAuthorizerName, unevaluatedSubDecision) :: rest, errlist, reasonlist =>
    let (decision, reason, err) :=
      authzHandler.evalChild currentAuthorizerName unevaluatedSubDecision data
    match decision with
    | .Allow | .Deny => (decision, reason, err)
    | .NoOpinion =>
      let errlist := appendErr errlist err
      let reasonlist := appendReason reasonlist currentAuthorizerName reason
      evaluateLoop authzHandler data rest errlist reasonlist

/-- `unionAuthzHandler.EvaluateConditions`, `union.go:131-186`. A non-union input fails
closed with its `FailureDecision` and an error (`:134-136`). -/
def unionAuthzHandler.EvaluateConditions (authzHandler : unionAuthzHandler)
    (unevaluatedDecision : ConditionsAwareDecision) (data : ConditionsData) :
    Decision × String × Option Err :=
  if !unevaluatedDecision.IsUnion then
    (unevaluatedDecision.FailureDecision, "failed closed",
     some "the union authorizer can only evaluate union ConditionsAwareDecisions")
  else evaluateLoop authzHandler data unevaluatedDecision.UnionedDecisions [] []

/-- `var _ = authorizer.Authorizer(unionAuthzHandler{})`, `union.go:38`: a union is itself an
`Authorizer` (so unions nest). -/
def unionAuthzHandler.toAuthorizer (authzHandler : unionAuthzHandler) : Authorizer where
  Authorize := authzHandler.Authorize
  ConditionsAwareAuthorize := authzHandler.ConditionsAwareAuthorize
  EvaluateConditions := authzHandler.EvaluateConditions

end union
