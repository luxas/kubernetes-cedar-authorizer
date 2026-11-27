# Proposed Go doc and API changes for the authorizer interface (PLAN 3.1)

Status: proposal produced by stage 2. Nothing here is implemented in Go. Each item names the
Lean statement it documents (`lean/K8sAuthz/Spec/*`). Go source reference: the review branch
`impl-conditional-authz-review` at `2ee49d340c9` (`pkg/authorization/authorizer`,
`pkg/authorization/union`, `plugin/pkg/authorizer/webhook`, `pkg/admission/plugin/.../conditionsenforcer`).

Vocabulary. `full(a, d)` is the decision the authorizer would return if it had the attributes
`a` and the admission data `d` at once. `Consistent(a, d)` says `d` describes the request `a`
was derived from. `Refines` is the closure of agreeing partial-evaluation steps.
`good(x)` is "well formed, and for a conditional `x`, `FailureDecision(x) ∈ PossibleDecisions(x)`".

## Change 1: document the contract on `Authorizer`

Add to the doc comment of `authorizer.Authorizer` (today only "MUST implement as FromParts"):

```go
// An Authorizer that supports conditions must satisfy, for every Attributes a:
//
//  1. (Sound) ConditionsAwareAuthorize(a) is well formed, and if it is conditional its
//     FailureDecision is one of its PossibleDecisions.
//  2. (Fold-down) Authorize(a) is never more permissive than the failure-closed fold of
//     ConditionsAwareAuthorize(a) (Deny < NoOpinion < Allow), and preserves a Deny.
//     Equality is expected, but not required when two remote calls back the two methods.
//  3. (Agreement) for every ConditionsData d consistent with a, evaluating the conditional
//     decision with full data yields what the authorizer would have returned with a and d
//     together ("as if it had the resource data").
//  4. (Refinement) EvaluateConditions applied to any conditional decision obtained from
//     ConditionsAwareAuthorize(a) by partial evaluation (by this or another party) and
//     to d returns that same decision.
//  5. (Deny-faithful) when the full-data decision is Deny, a failure of the authorizer
//     (encoding limits, evaluation errors, unreachable backend) must return Deny, never
//     NoOpinion. An authorizer that fails closed to NoOpinion lets a later authorizer
//     in the chain Allow what this one would have denied.
```

Lean: `Sound` (S1-S4), `Lawful` (L2-L4), `chain_sound_of_deny_faithful`,
`fail_closed_to_noOp_is_fail_open` (negative).

## Change 2: `EvaluateConditions` receives a refinement, only for conditional input

State on `EvaluateConditions`: the decision passed in is either the decision returned by this
authorizer's `ConditionsAwareAuthorize` or a refinement of it (a webhook may send back a decision
with some conditions already evaluated, per the ACR "Request" section of the KEP); the
authorizer must not expect to get back exactly what it issued. For an unconditional input the
authorizer returns `FailureDecision(x)` (or `Deny` with `ErrorConditionEvaluationNotSupported`
for an authorizer without condition support), as the shipped union and webhook already do.

Why: the first draft required `EvaluateConditions(x) = full` for unconditional `x` as well. That
contradicts the guard clause and is false for the shipped union
(`union_eval_unconditional_is_FD`, `plan_lawful_guarded_clash`).

Lean: `Lawful.L4` (conditional refinements only), `Guarded.G1u`, `peval_is_refinement`
(the mirror's partial evaluator produces refinements).

## Change 3: define `Consistent(Attributes, ConditionsData)` and require the enforcer to honour it

Document that `ConditionsData` (user, kind, name, namespace, operation, object, oldObject)
describes the same request as the `Attributes` the decision was authored from, with
`Attributes` allowed to know less. Table of classified writes (PLAN 1.3):

| verb at authorization | admission operation | name at authorization |
|---|---|---|
| create | CREATE | unknown (`generateName`, or name in body); known for create on a subresource |
| update, patch | UPDATE (or CREATE for update-to-create) | known |
| delete | DELETE | known |
| deletecollection | DELETE, once per matching object | unknown |

The enforcer must supply `ConditionsData` taken from the admission request, and must evaluate on
the post-mutation object. A conformance test decodes each pair and checks `Consistent`
(PLAN A-5, `Hypotheses.ConsistencyEstablished`); an empty `Consistent` on real pairs would make
the contract vacuous (`lawful_of_empty_consistent`).

## Change 4: `EvaluateConditions` reads nothing beyond its arguments

State that an authorizer whose condition IDs are opaque must not read mutable state in
`EvaluateConditions` beyond `(decision, data)`, or must be stable over the snapshot it used in
`ConditionsAwareAuthorize`. A policy reload between the two phases must not change the result
(mirror `P_72`). The Cedar instantiation meets this by embedding the residual policies in the
conditions. This is an implementation obligation, not a Lean theorem (every Lean function is
pure): `Hypotheses.EvalSnapshotIndependent`.

## Change 5: one exported guard for union, webhook and enforcer

Provide `authorizer.GuardEvaluation(decision, result)` used by all three call sites:
conditional `x` with `good(x)`: result must be in `PossibleDecisions(x)`, otherwise
`FailureDecision(x)`; unconditional `x`: `FailureDecision(x)`.

The three shipped clamps differ today: the union (`evaluateAndClamp`) and the webhook answer
`FailureDecision`; the enforcer's `evaluateWithReturnGuard` answers `Deny` with a fixed error.
Unifying is a behaviour change at the enforcer only (allow-versus-not-allow is unchanged; the
reason and status can differ), and must be called out as such.

Lean: `guard`, `guard_guarded`, `guard_inert` (inert on consistent in-domain refinements,
needs L3), `guard_sound`, `guard_lawful`.

## Change 6: validate DNS-1123 names in `union.New`

`union.New` rejects only empty and duplicate names, while
`ConditionsAwareDecisionUnion.Add` also requires DNS-1123 and fails the whole union closed. Then
`Authorize` (ignores names) may return `Allow` while `FoldDown(ConditionsAwareAuthorize)` is
`NoOpinion`. Check `IsDNS1123Subdomain` in `New` so a misconfiguration fails at startup.

Lean: `chain_needs_valid_names` (negative), `NamesOk` is a hypothesis of `chain_lawful`
(`namesOk`, `NamesOkN`).

## KEP delta (kep.md, "Authorizer requirements" and the union section)

1. Replace "the authorizer scopes down its policy as if it had the resource data" by the four
   numbered clauses of Change 1, so the property is checkable (Lean: `Lawful`).
2. Union section: "the two-phase result equals what a single-phase chain would have returned"
   becomes a theorem with explicit hypotheses: every member satisfies Change 1, member names are
   non-empty, DNS-1123 and distinct, and every member decision is `good`. Then the union is itself
   such an authorizer with `full_chain = first non-NoOpinion of the members' full` (Lean:
   `chain_lawful`, `chainN_lawful`).
3. ACR section: add that the webhook may send a refined decision and that the evaluation of an
   unconditional decision is not required to equal the full-data decision.
4. Failure section: a failing remote member must not fail open. For a webhook this means
   `failurePolicy: Deny` for an authorizer that can issue Deny conditions, or the stated hypothesis
   that it is not fail-open (`fail_closed_to_noOp_is_fail_open`, `FailClosedIsDeny`).
5. Enforcement section: "admit iff the authorizer allows with full data" holds per admission
   invocation under: `Consistent`, the enforcer present (`P_68`), the evaluating authorizer
   equals the issuing one (`P_72`), the committed object is the validated one,
   `deletecollection` evaluated per object, update-to-create adds the unconditional secondary
   `create` check, later plugins can still reject (`enforcement_exact`; forward direction only
   needs `Sound`: `enforcement_forward`).
