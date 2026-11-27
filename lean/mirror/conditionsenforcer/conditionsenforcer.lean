import filters.authorization

/-!
# `conditionsenforcer/conditionsenforcer.lean`  ↔
# `pkg/admission/plugin/authorizer/conditionsenforcer/conditionsenforcer.go`

The `AuthorizationConditionsEnforcer` validating admission plugin, and the end-to-end
composition filter → enforcer with the server wiring of `pkg/server/config.go:1073-1091`.

Abstractions:
* Admission errors are abstracted to `AdmissionOutcome`. A plain Go `error` (not an
  `apierrors.StatusError`), e.g. the missing-tuple error at `:87` or the conversion error at
  `:108`, is rendered by the generic handlers via `ErrorToAPIStatus` as 500, so it maps to
  `internal500`. `apierrors.NewInternalError` is 500; `ForbiddenStatusError` is 403.
* `admission.NewVersionedAttributes` (`:106`) is an input `x : Except Err ConditionsData`
  (its error branch is modelled; its content is opaque).
* `filters.GetAuthorizerAttributes` on the 403 path (`:131-134`) is assumed to succeed (its
  failure is another non-admitting error).
* Audit annotations and logging are omitted.
-/

namespace conditionsenforcer

open authorizer filters

/-- `PluginName`, `conditionsenforcer.go:40`. -/
def PluginName : String := "AuthorizationConditionsEnforcer"

/-- `conditionsEnforcer`, `conditionsenforcer.go:59-61`. `featureEnabled = none` before
`InspectFeatureGates` ran. -/
structure conditionsEnforcer where
  featureEnabled : Option Bool := none

/-- `InspectFeatureGates`, `conditionsenforcer.go:63-65`. -/
def conditionsEnforcer.InspectFeatureGates (_c : conditionsEnforcer) (gateOn : Bool) :
    conditionsEnforcer :=
  { featureEnabled := some gateOn }

/-- `ValidateInitialization`, `conditionsenforcer.go:67-72`. -/
def conditionsEnforcer.ValidateInitialization (c : conditionsEnforcer) : Option Err :=
  match c.featureEnabled with
  | none => some "InspectFeatureGates must be called during admission initialization time"
  | some _ => none

/-- `Handles`, `conditionsenforcer.go:74-76`: independent of the operation. -/
def conditionsEnforcer.Handles (c : conditionsEnforcer) (_operation : String) : Bool :=
  c.featureEnabled == some true

/-- Result of the admission plugin's `Validate`: `nil`, a 403 status error, or a 500. -/
inductive AdmissionOutcome where
  | admitted
  | forbidden403
  | internal500
  deriving DecidableEq, Repr, Inhabited

/-- `evaluateWithReturnGuard`, `conditionsenforcer.go:145-153`: a result outside
`PD(decisionToEvaluate)` is replaced by `(Deny, "failed closed", err)`. -/
def evaluateWithReturnGuard (z : Authorizer) (decisionToEvaluate : ConditionsAwareDecision)
    (versionedAttributes : ConditionsData) : Decision × String × Option Err :=
  let (decision, reason, err) := z.EvaluateConditions decisionToEvaluate versionedAttributes
  if !decisionToEvaluate.PossibleDecisions.Has decision then
    (.Deny, "failed closed",
      some s!"authorizer tried to return {decision.String} from EvaluateConditions, but the possible outcomes were …")
  else (decision, reason, err)

/-- `Validate`, `conditionsenforcer.go:78-142`, with the evaluating authorizer taken from
the context tuple (`:84`). The `switch` at `:90-104`: Deny / NoOpinion / `Allow ∉ PD` → 500;
Allow → nil; map / union → evaluate. (The Go `default` branch at `:101-103` is unreachable:
the five variants are exhaustive.) -/
def conditionsEnforcer.ValidateWith (c : conditionsEnforcer)
    (evaluator : Authorizer → Authorizer)
    (ctx : Context) (x : Except Err ConditionsData) : AdmissionOutcome :=
  if c.featureEnabled != some true then .admitted
  else
    match ConditionallyAuthorizedDecisionFrom ctx with
    | none => .internal500
    | some (authz, d) =>
      if d.IsDeny || d.IsNoOpinion || !d.PossibleDecisions.Has .Allow then .internal500
      else if d.IsAllow then .admitted
      else
        match x with
        | .error _ => .internal500
        | .ok versionedAttributes =>
          let (decision, _reason, err) :=
            evaluateWithReturnGuard (evaluator authz) d versionedAttributes
          if decision = .Allow then .admitted
          else if err.isSome then .internal500
          else .forbidden403

/-- `Validate`, `conditionsenforcer.go:78-142`: the authorizer that evaluates is the one
stored in the context. -/
def conditionsEnforcer.Validate (c : conditionsEnforcer) (ctx : Context)
    (x : Except Err ConditionsData) : AdmissionOutcome :=
  c.ValidateWith id ctx x

/-! ## Server wiring and end-to-end composition -/

/-- The three switches of `DefaultBuildHandlerChain` (`pkg/server/config.go:1077`) plus the
configured authorizer. `enforcerEnabled` is `ConditionsEnforcerPluginEnabled`, i.e. the
plugin is in the validating admission chain. -/
structure Config where
  gateOn : Bool
  classifier : Option ConditionalAuthorizationRequestClassifier
  enforcerEnabled : Bool
  authorizer : Authorizer

/-- `config.go:1077`: `gate ∧ classifier ≠ nil ∧ ConditionsEnforcerPluginEnabled`. -/
def Config.usesConditionsAwareFilter (cfg : Config) : Bool :=
  cfg.gateOn && cfg.classifier.isSome && cfg.enforcerEnabled

/-- The installed authorization filter, `config.go:1077-1087`. The `klog.Fatalf` branch at
`:1080-1084` is unreachable (`WithConditionsAwareAuthorization` succeeds under the guard),
so the classifier is pattern-matched directly. -/
def Filter (cfg : Config) (ctx : Context) (a : Attributes) : FilterOutcome :=
  match cfg.usesConditionsAwareFilter, cfg.classifier with
  | true, some cl => withConditionsAwareAuthorization cfg.authorizer cl ctx a
  | _, _ => WithAuthorization cfg.gateOn cfg.authorizer ctx a

/-- The decision the installed filter acts on (`authorization.go:79` or `:161-167`). -/
def filterDecision (cfg : Config) (a : Attributes) : ConditionsAwareDecision :=
  match cfg.usesConditionsAwareFilter, cfg.classifier with
  | true, some cl => conditionsAwareDecisionFor cfg.authorizer cl a
  | _, _ => fromParts (cfg.authorizer.Authorize a)

/-- The enforcer instance after admission initialization (`InspectFeatureGates`). -/
def Config.enforcer (cfg : Config) : conditionsEnforcer :=
  ({} : conditionsEnforcer).InspectFeatureGates cfg.gateOn

/-- End-to-end outcome: filter, then (if the plugin is in the chain) the enforcer's
`Validate` on the context the filter passed on. `ctx` is the incoming request context
(normally `none`). This models the path on which validating admission is reached; see
`P_68_enforcer_runs` for the paths on HEAD where it is not. -/
def Outcome (cfg : Config) (ctx : Context) (a : Attributes) (x : Except Err ConditionsData) :
    AdmissionOutcome :=
  match Filter cfg ctx a with
  | .next ctx' => if cfg.enforcerEnabled then cfg.enforcer.Validate ctx' x else .admitted
  | .forbidden403 => .forbidden403
  | .internal500 => .internal500

/-- `Outcome` with a possibly different evaluating authorizer (P-72: the reloadable wrapper
stored in the context may resolve to a different chain at admission time). -/
def OutcomeReloaded (cfg : Config) (evaluator : Authorizer → Authorizer) (ctx : Context)
    (a : Attributes) (x : Except Err ConditionsData) : AdmissionOutcome :=
  match Filter cfg ctx a with
  | .next ctx' => if cfg.enforcerEnabled then cfg.enforcer.ValidateWith evaluator ctx' x else .admitted
  | .forbidden403 => .forbidden403
  | .internal500 => .internal500

end conditionsenforcer
