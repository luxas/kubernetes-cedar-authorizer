# Lean model of Kubernetes Conditional Authorization (KEP-5681)

A hand-written Lean 4 model of the Go implementation reviewed in `../review/`, with the
properties catalogued in `../review/properties.md` stated (and where feasible proved) as
theorems. Lean toolchain: `lean-toolchain` (v4.35.0), no Mathlib dependency.

Build: `lake build` (from this directory, with `~/.elan/bin` on PATH).

## Go ↔ Lean mapping

Each top-level directory is one Go package, flattened. Inside a directory, `foo.lean`
mirrors `foo.go`; `foo_properties.lean` holds theorems and mirrors `foo_test.go`.

| Lean | Go (under `staging/src/k8s.io/apiserver/`) |
|---|---|
| `authorizer/interfaces.lean` | `pkg/authorization/authorizer/interfaces.go` (Decision, Condition, ConditionsData, oracles) |
| `authorizer/conditionsmap.lean` | `pkg/authorization/authorizer/conditionsmap.go` (type, limits, `validateConditions`, PD/FD) |
| `authorizer/conditions.lean` | `pkg/authorization/authorizer/conditions.go` (**plus** `ConditionsAwareDecisionConditionsMap` from `conditionsmap.go:138`, because Lean modules cannot be mutually recursive) |
| `authorizer/conditionsunion.lean` | `pkg/authorization/authorizer/conditionsunion.go` |
| `authorizer/evaluate.lean` | `pkg/authorization/authorizer/evaluate.go` (plus the reference semantics `refSem`) |
| `authorizer/*_properties.lean` | `pkg/authorization/authorizer/*_test.go` |
| `union/union.lean` | `pkg/authorization/union/union.go` |
| `webhook/webhook.lean` | `plugin/pkg/authorizer/webhook/webhook.go` |
| `encoding/encoding.lean` | `pkg/apis/authorization/v1/encoding.go` |
| `filters/authorization.lean` | `pkg/endpoints/filters/authorization.go` |
| `conditionsenforcer/conditionsenforcer.lean` | `pkg/admission/plugin/authorizer/conditionsenforcer/conditionsenforcer.go` |
| `cel/authorization_conditions.lean` | `pkg/admission/plugin/cel/authorization_conditions.go` (PR #143024, unmerged) |

Names of types, constructors, methods and constants are the Go names wherever Lean allows
(`Type` is a keyword, so `Condition.Type` is `Condition.CondType` with a `GetType` getter).
Every definition carries the Go `file:line` it models in its doc comment.

## Abstractions (deliberate differences from Go)

1. **Errors.** `error` is `Option Err`, `Err := String`. `utilerrors.NewAggregate` is
   `aggregate`. Message formats are approximated, never relied on by theorems.
2. **One oracle.** `Condition.Evaluate` (pre-compiled evaluator) and the fallback
   `MaybeEvaluateConditionFunc` are folded into a single `p : Condition →
   ConditionEvaluationResult` with the request data already applied (both are pure by
   contract, `interfaces.go:298-310`). Theorems quantify over `p`.
3. **`ConditionsData` is opaque.** Only oracles look at it.
4. **Validation predicates are opaque.** `IsDomainPrefixedKey`, `IsDNS1123Subdomain` are
   `opaque` Bool functions. Theorems hold for any choice.
5. **Variant tag.** Go's unexported tag + payload struct is a Lean inductive; the Go zero
   value is `ConditionsAwareDecision.zero = .deny "" none`.
6. **Union payload.** Go caches `containsUnconditionalAllowOrDeny` and
   `subDecisionsPossibleDecisions` inside the emitted union; both are functions of the
   child list, so the Lean `union` constructor carries only `List (String × CAD)`. The
   builder (`ConditionsAwareDecisionUnion`) keeps the caches as fields, as in Go.
7. **Mutation.** Go's `*ConditionsAwareDecisionUnion.Add` mutates; Lean's `Add` returns
   the new state.
8. **Unreachable branches** (unknown `Decision` integer, unknown evaluation result) are
   not modelled: the Lean types are exact.
9. **Contexts, metrics, audit, logging** are omitted unless a property mentions them.

## Properties

`../review/properties.md` Part 2 numbers the properties P-1 … P-85. Each theorem in a
`*_properties.lean` file is named `P_<n>_<slug>` and its doc comment quotes the property.
Properties that do NOT hold on HEAD are stated as negative theorems (`¬ ∀ …` with an
explicit counterexample) and marked `-- status: does NOT hold` so the text matches the
catalogue. Properties that are axioms about the environment (webhook agreement, oracle
purity, out-of-tree authorizers) are `axiom`s in the file of the component that relies on
them, each with a doc comment saying why it cannot be proved.

Any `sorry` is a known gap and is listed in `STATUS.md`.

## Future work

Differential testing against the Go implementation (as Cedar does) or a Go-to-Lean
bridge; until then this model is hand-written and reviewed for equivalence with the Go
source by independent reviewers (see `../review/lean-equivalence.md` and `STATUS.md`).
