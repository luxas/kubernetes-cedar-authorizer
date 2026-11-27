import authorizer.evaluate

/-!
# `webhook/webhook.lean`  ↔  `plugin/pkg/authorizer/webhook/webhook.go`

Decision logic of the webhook authorizer: the legacy `Authorize`, `ConditionsAwareAuthorize`,
`conditionsAwareFailureDecision`, `EvaluateConditions`, `webhookEvaluateConditions` and
`tryEvaluateUsingBuiltins`.

Abstractions (in addition to `lean/README.md` §Abstractions):
* **HTTP transport, retries, caching, metrics and logging are omitted.** The SAR call is an
  input (`Except Err SubjectAccessReviewStatus`, `.error` = transport/marshal failure), and
  for the conditions-aware path a function of the advertised flag `handlesConditional`
  (the webhook may answer differently depending on what was advertised).
* **Match conditions** (`w.match`, `webhook.go:250,307`) are an input `Except Err Bool`.
* **Decoding** (`encoding.go:126-152`) is not modelled here: `ConditionalDecision` carries the
  already decoded `ConditionsAwareDecision`, i.e. the output of
  `ToAuthorizerConditionsAwareDecision(*cd, w.conditionsAwareFailureDecision)`. A decode
  that fails closed is represented by its result (a `conditionsAwareFailureDecision`, possibly
  nested in a union), so no separate marker is needed.
* **SAR validation** (`CombinedValidateSubjectAccessReviewCreate`, `webhook.go:327`) is an
  opaque Bool predicate `valid` on the status (the spec, hence `handlesConditional`, is fixed
  per call). The single fact the theorems use is `ValidRejectsUnrequested`
  (`validation.go:98-103`).
* **The ACR round trip** (`webhook.go:461-544`: encode, object apiVersion/kind check, UID
  generation, transport, `response ≠ nil`, validation, UID match) is an oracle `acr` that
  returns `none` for every one of those failures and `some (decision, reason, evalErr)` for
  a validated, UID-matched response. The `default` branch of the type switch (`:560-561`) is
  unreachable after validation (`P-59`) and folded into `none`.
* **Builtin evaluator** (`webhook.go:951-973`, PR #143024): `builtin` is the per-request
  in-process evaluator with `data` (and the context authorizer) already applied; `none`
  covers both a nil `builtinConditionsEvaluatorBuilder` and an `EvaluatorForData` error
  (`:956-963`), which both return the decision unchanged.
* `data == nil` (`webhook.go:437`) is `Option ConditionsData`.
-/

namespace webhook

open authorizer

/-- `authorizationv1.SubjectAccessReviewStatus` with `ConditionalDecision` already decoded
(see module doc). Go: `staging/src/k8s.io/api/authorization/v1/types.go`. -/
structure SubjectAccessReviewStatus where
  Allowed : Bool := false
  Denied : Bool := false
  Reason : String := ""
  EvaluationError : String := ""
  ConditionalDecision : Option ConditionsAwareDecision := none
  deriving Inhabited

/-- `WebhookAuthorizer`, `webhook.go:90-102`, reduced to the fields the decision logic reads.
`hasReviewer` is `authorizationConditionsReviewer != nil`, which `newWithBackoff`
(`webhook.go:150-157`) sets only when the `ConditionalAuthorization` gate is on and an ACR
client was configured. -/
structure WebhookAuthorizer where
  /-- `decisionOnError` (failurePolicy): `NoOpinion` or `Deny` (`webhook.go:97`). -/
  decisionOnError : Decision
  /-- `authorizationConditionsReviewer != nil` (`webhook.go:92,152-157`). -/
  hasReviewer : Bool
  /-- the in-process evaluator for this request, `webhook.go:951-963` (see module doc). -/
  builtin : Option (Condition → ConditionEvaluationResult)
  /-- the remote ACR round trip, `webhook.go:461-544`; `none` = any transport, validation,
  apiVersion/kind or UID failure. -/
  acr : ConditionsAwareDecision → ConditionsData → Option (Decision × String × Option Err)

/-- Well-formedness of a constructed webhook: `failurePolicy` is `NoOpinion` or `Deny`
(`staging/src/k8s.io/apiserver/pkg/apis/apiserver/validation`). Only used where noted. -/
def WebhookAuthorizer.WF (w : WebhookAuthorizer) : Prop :=
  w.decisionOnError ≠ .Allow

/-- The single fact about SAR validation that the model uses (`validation.go:98-103`): if
conditions were not advertised (no reviewer), a status with a `conditionalDecision` fails
validation. -/
def ValidRejectsUnrequested (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool) : Prop :=
  ∀ s : SubjectAccessReviewStatus, w.hasReviewer = false → s.ConditionalDecision ≠ none → valid s = false

/-- Error texts (abstracted). -/
def errBothAllowDeny : Err := "webhook subject access review returned both allow and deny response"
def errUnrequestedConditional : Err := "webhook subject access review returned unrequested conditional decision"
def errValidation : Err := "invalid SubjectAccessReview status"
def errUnconditionalInput : Err := "got unconditional decisionToEvaluate in EvaluateConditions"
def errNilData : Err := "data must be non-nil in EvaluateConditions"
def errNoReviewer : Err := "no authorization conditions review client configured for the webhook authorizer, cannot evaluate conditions"
def errACR : Err := "authorization conditions review failed"
def errNotPossible (d : Decision) : Err :=
  s!"webhook authorizer tried to return {d.String} from EvaluateConditions, but it was not a possible outcome"

namespace WebhookAuthorizer

/-- Legacy `Authorize` after the SAR response is known: the switch at `webhook.go:258-272`.
Order: both ⇒ Deny+err; denied ⇒ Deny; conditional ⇒ its FailureDecision + err;
allowed ⇒ Allow; else NoOpinion. -/
def authorizeStatus (s : SubjectAccessReviewStatus) : Decision × String × Option Err :=
  if s.Denied && s.Allowed then (.Deny, s.Reason, some errBothAllowDeny)
  else if s.Denied then (.Deny, s.Reason, none)
  else match s.ConditionalDecision with
    | some d => (d.FailureDecision, s.Reason, some errUnrequestedConditional)
    | none => if s.Allowed then (.Allow, s.Reason, none) else (.NoOpinion, s.Reason, none)

/-- `Authorize`, `webhook.go:220-273`. Match-condition error and SAR transport error both
return `decisionOnError` (`:250-256`, `:257-260`); a FALSE match condition skips the
webhook (`:253-255`). The SAR is sent with `handlesConditional = false` (`:257`). -/
def Authorize (w : WebhookAuthorizer) (matchResult : Except Err Bool)
    (sarResponse : Except Err SubjectAccessReviewStatus) : Decision × String × Option Err :=
  match matchResult with
  | .error e => (w.decisionOnError, "", some e)
  | .ok false => (.NoOpinion, "", none)
  | .ok true =>
    match sarResponse with
    | .error e => (w.decisionOnError, "", some e)
    | .ok s => authorizeStatus s

/-- `conditionsAwareFailureDecision`, `webhook.go:349-354`. Go always passes a non-nil
error; the model keeps `Option Err` for uniformity. -/
def conditionsAwareFailureDecision (w : WebhookAuthorizer) (err : Option Err) : ConditionsAwareDecision :=
  if w.decisionOnError = .NoOpinion then .noOpinion "failed closed" err
  else .deny "failed closed" err

/-- `handlesConditional`, `webhook.go:287`: conditions are advertised iff a reviewer exists. -/
def handlesConditional (w : WebhookAuthorizer) : Bool := w.hasReviewer

/-- `evaluationErr`, `webhook.go:331-334`. -/
def evaluationErrOf (s : SubjectAccessReviewStatus) : Option Err :=
  if s.EvaluationError.length != 0 then some s.EvaluationError else none

/-- `ConditionsAwareAuthorize` after the SAR response is known: `webhook.go:322-346`. -/
def conditionsAwareStatus (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (s : SubjectAccessReviewStatus) : ConditionsAwareDecision :=
  if s.Denied && s.Allowed then .deny s.Reason (some errBothAllowDeny)
  else if !valid s then w.conditionsAwareFailureDecision (some errValidation)
  else if s.Denied then .deny s.Reason (evaluationErrOf s)
  else match s.ConditionalDecision with
    | some d => d
    | none => if s.Allowed then .allow s.Reason (evaluationErrOf s) else .noOpinion s.Reason (evaluationErrOf s)

/-- `ConditionsAwareAuthorize`, `webhook.go:275-347`. `sarResponse handlesConditional` is the
webhook's answer to a SAR that advertises conditions iff `handlesConditional`. -/
def ConditionsAwareAuthorize (w : WebhookAuthorizer) (valid : SubjectAccessReviewStatus → Bool)
    (matchResult : Except Err Bool) (sarResponse : Bool → Except Err SubjectAccessReviewStatus) :
    ConditionsAwareDecision :=
  match matchResult with
  | .error e => w.conditionsAwareFailureDecision (some e)
  | .ok false => .noOpinion "" none
  | .ok true =>
    match sarResponse w.handlesConditional with
    | .error e => w.conditionsAwareFailureDecision (some e)
    | .ok s => w.conditionsAwareStatus valid s

/-- The oracle handed to partial evaluation by `tryEvaluateUsingBuiltins`
(`webhook.go:965-972`): builtin errors become `unevaluatable`. -/
def builtinOracle (b : Condition → ConditionEvaluationResult) : MaybeEvaluateConditionFunc :=
  fun c => match b c with
    | .error _ => .unevaluatable
    | r => r

/-- Effective oracle of `partiallyEvaluateConditionsMapInternal` (`evaluate.go:122-129`): the
condition's own evaluator first, the fallback only on `unevaluatable`. -/
def composeOracle (ev₀ fallback : MaybeEvaluateConditionFunc) : MaybeEvaluateConditionFunc :=
  fun c => match ev₀ c with
    | .unevaluatable => fallback c
    | r => r

/-- Conditions decoded from the wire carry no evaluator (`encoding.go:154-163`), so for the
webhook's own decisions the effective oracle IS the builtin oracle. This is the precondition
under which `tryEvaluateUsingBuiltins` below (which omits `ev₀`) models Go exactly. -/
theorem compose_decoded (b : Condition → ConditionEvaluationResult) :
    composeOracle (fun _ => .unevaluatable) (builtinOracle b) = builtinOracle b := rfl

/-- `tryEvaluateUsingBuiltins`, `webhook.go:951-973`. Precondition: every condition of
`unevaluatedDecision` has `ev₀ ≡ unevaluatable` (true for decisions this webhook decoded,
see `compose_decoded`); a precompiled condition evaluator would take precedence in Go. -/
def tryEvaluateUsingBuiltins (w : WebhookAuthorizer) (unevaluatedDecision : ConditionsAwareDecision) :
    ConditionsAwareDecision :=
  match w.builtin with
  | none => unevaluatedDecision
  | some b => PartiallyEvaluateConditionsAwareDecision unevaluatedDecision (builtinOracle b)

/-- `webhookEvaluateConditions`, `webhook.go:453-563`, with the ACR round trip abstracted
(module doc). Every failure answers `FailureDecision` of the (refined) input, never
`decisionOnError`; a webhook answer outside `PossibleDecisions` is clamped the same way
(`:546-559`). -/
def webhookEvaluateConditions (w : WebhookAuthorizer) (decisionToEvaluate : ConditionsAwareDecision)
    (data : ConditionsData) : Decision × String × Option Err :=
  if !w.hasReviewer then (decisionToEvaluate.FailureDecision, "failed closed", some errNoReviewer)
  else match w.acr decisionToEvaluate data with
    | none => (decisionToEvaluate.FailureDecision, "failed closed", some errACR)
    | some r =>
      if decisionToEvaluate.PossibleDecisions.Has r.1 then r
      else (decisionToEvaluate.FailureDecision, "failed closed", some (errNotPossible r.1))

/-- `EvaluateConditions`, `webhook.go:429-449`. -/
def EvaluateConditions (w : WebhookAuthorizer) (decisionToEvaluate : ConditionsAwareDecision)
    (data : Option ConditionsData) : Decision × String × Option Err :=
  if decisionToEvaluate.IsUnconditional then
    (decisionToEvaluate.FailureDecision, "failed closed", some errUnconditionalInput)
  else match data with
    | none => (decisionToEvaluate.FailureDecision, "failed closed", some errNilData)
    | some x =>
      let possiblyEvaluatedDecision := w.tryEvaluateUsingBuiltins decisionToEvaluate
      if possiblyEvaluatedDecision.IsUnconditional then possiblyEvaluatedDecision.UnconditionalPartsOrError
      else w.webhookEvaluateConditions possiblyEvaluatedDecision x

end WebhookAuthorizer

end webhook
