import authorizer.conditions

/-!
# `filters/authorization.lean`  ↔  `pkg/endpoints/filters/authorization.go`

The two authorization filters (`WithAuthorization`, `WithConditionsAwareAuthorization`),
together with the request-context slot from `pkg/endpoints/request/context.go:86-110`
that carries the `(authorizer, decision)` tuple to the conditions enforcer.

Abstractions (in addition to `lean/README.md` §Abstractions):
* HTTP is abstracted: a filter returns a `FilterOutcome` (call the next handler with a
  context, or write 403 / 500). Audit annotations, metrics, latency tracking and logging
  are omitted.
* `GetAuthorizerAttributes` (`authorization.go:225`) is assumed to succeed: its failure
  only produces a 500 before any authorizer call, which no property depends on. The
  filter therefore takes the `Attributes` directly.
* The request context is reduced to the one slot the conditional-authorization feature
  uses: `Option (Authorizer × ConditionsAwareDecision)`.
* `ctx context.Context` arguments of the authorizer methods are dropped (authorizers are
  modelled as pure functions of their inputs; the reload wrapper is treated in P-72 by
  letting the enforcer use a different `Authorizer`).
* The `a == nil` "authorization disabled" short-circuit (`authorization.go:67-70,
  :155-158`) is not modelled: an `Authorizer` is always configured.
* `Authorizer` is defined here; `union/union.lean` defines the same shape independently
  (accepted duplication).
-/

namespace filters

open authorizer

/-- `authorizer.Attributes` (`interfaces.go`): the request attributes. Opaque. -/
opaque Attributes : Type

/-- `authorizer.Authorizer` (`interfaces.go:86-124`), without `context.Context`.
`UnconditionalAuthorizer` (`:86-95`) is the `Authorize` field alone. -/
structure Authorizer where
  /-- `Authorize(ctx, a) (Decision, string, error)`, `interfaces.go:94`. -/
  Authorize : Attributes → Decision × String × Option Err
  /-- `ConditionsAwareAuthorize(ctx, a) ConditionsAwareDecision`, `interfaces.go:114`. -/
  ConditionsAwareAuthorize : Attributes → ConditionsAwareDecision
  /-- `EvaluateConditions(ctx, decision, data) (Decision, string, error)`, `interfaces.go:123`. -/
  EvaluateConditions : ConditionsAwareDecision → ConditionsData → Decision × String × Option Err

/-- `ConditionsAwareDecisionFromParts` applied to an `Authorize` triple. -/
def fromParts (t : Decision × String × Option Err) : ConditionsAwareDecision :=
  ConditionsAwareDecisionFromParts t.1 t.2.1 t.2.2

/-- `authorizer.AuthorizerFunc` lifted to an `Authorizer` (`interfaces.go:133-145`):
`ConditionsAwareAuthorize` is `FromParts ∘ Authorize`; `EvaluateConditions` always returns
`(Deny, "", ErrorConditionEvaluationNotSupported)`. -/
def AuthorizerFunc (f : Attributes → Decision × String × Option Err) : Authorizer where
  Authorize := f
  ConditionsAwareAuthorize := fun a => fromParts (f a)
  EvaluateConditions := fun _ _ => (.Deny, "", some ErrorConditionEvaluationNotSupported)

/-- `ConditionalAuthorizationRequestClassifier`, `authorization.go:55`. -/
abbrev ConditionalAuthorizationRequestClassifier := Attributes → Bool

/-- The request-context slot keyed by `conditionallyAuthorizedDecisionKey`
(`request/context.go:86-89`, `authorizerDecisionTuple`). `none` = not set. -/
abbrev Context := Option (Authorizer × ConditionsAwareDecision)

/-- `request.ConditionallyAuthorizedDecisionFrom`, `request/context.go:105-108`. -/
def ConditionallyAuthorizedDecisionFrom (ctx : Context) : Option (Authorizer × ConditionsAwareDecision) :=
  ctx

/-- `request.WithConditionallyAuthorizedDecision`, `request/context.go:92-101`: errors if a
decision is already set, otherwise stores the tuple. -/
def WithConditionallyAuthorizedDecision (parent : Context) (z : Authorizer)
    (decision : ConditionsAwareDecision) : Except Err Context :=
  match ConditionallyAuthorizedDecisionFrom parent with
  | some _ => .error "a conditionally authorized decision is already set in the request context"
  | none => .ok (some (z, decision))

/-- What an authorization filter does with a request: `handler.ServeHTTP` with the
(possibly extended) context, `responsewriters.Forbidden` (403) or
`responsewriters.InternalError` (500). -/
inductive FilterOutcome where
  | next (ctx : Context)
  | forbidden403
  | internal500

/-- The decision computed by the conditions-aware filter, `authorization.go:161-167`. -/
def conditionsAwareDecisionFor (z : Authorizer) (classifier : ConditionalAuthorizationRequestClassifier)
    (a : Attributes) : ConditionsAwareDecision :=
  if classifier a then z.ConditionsAwareAuthorize a else fromParts (z.Authorize a)

/-- `withConditionsAwareAuthorization`, `authorization.go:153-221` (the handler body).
Order: compute `d` (`:161-167`); attach, 500 on error (`:170-174`); `allow d` → next
(`:190-199`); `Allow ∈ PD(d)` → next (`:202-208`); `err(d) ≠ nil` → 500 (`:210-214`);
else 403 (`:216-220`). -/
def withConditionsAwareAuthorization (z : Authorizer)
    (classifier : ConditionalAuthorizationRequestClassifier) (ctx : Context) (a : Attributes) :
    FilterOutcome :=
  let d := conditionsAwareDecisionFor z classifier a
  match WithConditionallyAuthorizedDecision ctx z d with
  | .error _ => .internal500
  | .ok ctx' =>
    if d.IsAllow then .next ctx'
    else if d.PossibleDecisions.Has .Allow then .next ctx'
    else if d.Error.isSome then .internal500
    else .forbidden403

/-- `WithConditionsAwareAuthorization`, `authorization.go:143-151`: refuses to build the
filter unless the gate is on and the classifier is non-nil. -/
def WithConditionsAwareAuthorization (gateOn : Bool) (z : Authorizer)
    (classifier : Option ConditionalAuthorizationRequestClassifier) :
    Except Err (Context → Attributes → FilterOutcome) :=
  match gateOn, classifier with
  | true, some cl => .ok (withConditionsAwareAuthorization z cl)
  | _, _ => .error "WithConditionsAwareAuthorization requires the ConditionalAuthorization feature to be set, and the conditionalAuthzClassifier to be non-nil"

/-- `withAuthorization`, `authorization.go:66-125` (the handler body). Only `z.Authorize`
is used (the parameter type is `UnconditionalAuthorizer`); the authorizer attached to the
context is the lift `AuthorizerFunc(a.Authorize)` (`:71`), and only on Allow with the gate
on (`:101-110`). Allow is checked before the error (`:93`). -/
def withAuthorization (gateOn : Bool) (z : Authorizer) (ctx : Context) (a : Attributes) :
    FilterOutcome :=
  let (authorized, reason, err) := z.Authorize a
  if authorized = .Allow then
    if gateOn then
      match WithConditionallyAuthorizedDecision ctx (AuthorizerFunc z.Authorize)
          (ConditionsAwareDecisionAllow reason err) with
      | .error _ => .internal500
      | .ok ctx' => .next ctx'
    else .next ctx
  else if err.isSome then .internal500
  else .forbidden403

/-- `WithAuthorization`, `authorization.go:61-64`. The feature-gate read inside the handler
(`:101`) is the `gateOn` argument. -/
def WithAuthorization (gateOn : Bool) (z : Authorizer) : Context → Attributes → FilterOutcome :=
  withAuthorization gateOn z

end filters
