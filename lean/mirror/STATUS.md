# Status of the Lean model

Snapshot: `lake build` green, 23 modules, 347 theorems, **0 `sorry`**, 2 axioms (both in `cel/`,
see below). Toolchain Lean 4.35.0, no Mathlib.

## Coverage of `../review/properties.md`

54 of the 85 catalogued properties have at least one theorem (`P_<n>_*`). Every component the
catalogue marks "Lean: yes" is covered; most "Lean: later" items (P-23, P-30, P-31, P-56 full
round trip, P-72 as a model-level negation) are covered too.

| Property | Theorems (file) |
|---|---|
| P-1, P-3, P-4, P-5, P-6, P-9, P-13, P-14, P-15, P-35 | `authorizer/conditions_properties.lean` (48 thms; also the `WF` predicate, `WF_mkMap`, DecisionSet lemmas) |
| P-4, P-5, P-33, P-34, P-35, P-36 (builder forms) | `authorizer/conditionsunion_properties.lean` (`Reachable` builder invariants, `WF_ToDecision`) |
| P-18, P-19, P-20, P-21, P-22, P-23, map forms of P-25/27/28/31 | `authorizer/evaluate_internal_properties.lean` (`pmap_cases`: all ten outcomes; `decSpec`) |
| P-19, P-20 (chain), P-25, P-26, P-27 (+ both counterexamples), P-28, P-30, P-31, P-37, P-38 | `authorizer/evaluate_properties.lean` (`CAD_induct`, `loopB` lemmas, `peval_WF`) |
| P-41, P-42, P-44, P-45, P-46, P-47 | `union/union_properties.lean` |
| P-32, P-49, P-50, P-51, P-52, P-69 (legacy fold-down), P-26 hypothesis form | `webhook/webhook_properties.lean` |
| P-56 (unconditional exact; map under WF; union under P-36 hypotheses; all `RoundTripWF`), P-57 (7 classes), P-58 | `encoding/encoding_properties.lean` |
| P-64, P-65, P-66, P-69, P-70, P-72, P-80(a,b), P-82, `end_to_end_safety`, `served_safety_classified` | `conditionsenforcer/conditionsenforcer_properties.lean` |
| P-74, P-75, P-77, P-78, P-79 | `cel/authorization_conditions_properties.lean` |
| P-80 (eight gate-off switches) | `filters/featuregate.lean` |

### Negative theorems (`-- status: does NOT hold`)

`P_4_not_all_trees`, `P_6_not_all_trees`, `P_15_map_Len_not_all_maps`, `P_25_needs_WF`,
`P_28_needs_WF`, `P_27_counterexample`, `P_27_error_component_counterexample`,
`P_27_needs_no_error_premise`(`'`), `P_20_chain_earlier_allow_wins`,
`P_42_New_accepts_non_DNS1123`, `P_44_needs_child_WF`, `P_51_unrestricted_does_not_hold`,
`P_57_*` (7), `P_56_roundtrip_empty_error_lost`, `P_72_evaluator_may_differ`,
`P_78_not_per_request_bound`.

### Axioms and named hypotheses

- `cel/authorization_conditions_properties.lean`: `oAuthor` (the authoring authorizer's oracle,
  unobservable) and `P_76_O3_builtin_agrees_with_author` (Axiom O3 of the catalogue: unknown
  on HEAD). Consistent; nothing proved depends on them. Should become a named hypothesis of
  any future theorem that uses it.
- `conditionsenforcer/conditionsenforcer_properties.lean`: `P_68_enforcer_runs` is a **`Prop`
  taken as an explicit hypothesis** by `served_safety_classified`, not an axiom, because it is
  false on HEAD (aggregated APIs, unsafe corrupt-object delete). `end_to_end_safety` does not
  need it: it is about the modelled filter → enforcer pipeline.
- `webhook/webhook_properties.lean`: `P_25_hyp` is a per-instance hypothesis of the webhook's
  P-26 statement; the general P-25 is proved under `WF` in `authorizer/evaluate_properties.lean`.

### Properties without a theorem, and why

| Property | Reason |
|---|---|
| P-2, P-7, P-8, P-12 | free from the inductive type / value semantics (catalogue: "Lean: no") |
| P-10, P-11, P-83, P-84 | axioms about leaf authorizers and out-of-tree code; stated in the catalogue, not modelled |
| P-16, P-17, P-40 | declarative validation, reserved-prefix enforcement and tree bounds are not modelled (negative in the catalogue) |
| P-24, P-29, P-43, P-45 (operational part) | operational (which calls happen); P-45 has a shape theorem only |
| P-39 | reason/error text formatting, abstracted |
| P-48, P-53, P-54, P-55, P-59, P-60, P-61, P-62, P-63 | transport, UID, caching, validation and SAR-registry details outside the model |
| P-67, P-68, P-71, P-73, P-81, P-85 | request-pipeline multiplicity, served-outcome, audit, metrics: P-68 is the named hypothesis above; P-81 is documented in `filters/featuregate.lean` |
| P-76 | axiom (see above) |

## Corrections to `properties.md` found by proving

1. **P-25 and P-28 need `WF`** (union names valid). Counterexample `union [("", allow)]`: PD = {A},
   but partial evaluation re-adds the child under the invalid name and `ToDecision` fails closed
   to `noOpinion` (PD = {N}). The catalogue says "no premise needed" for P-25 and states P-28 for
   every `d`. The map forms need no WF.
2. **P-44's argument is incomplete.** A nested union child with PD = {Allow} has FD = NoOpinion,
   outside its PD; the clamp theorem needs child well-formedness (`|PD| ≥ 2`), which the catalogue's
   "a conditional child is never `allow`" does not give. `P_44_needs_child_WF` is the counterexample.
3. **P-27 needs `o` total** as an explicit hypothesis (the catalogue's §D convention, omitted in
   the statement).
4. **Stronger than catalogued:** P-37 (soundness) holds for every tree, not only WF; P-38 (fold
   correctness) needs only a reachable builder with no name errors, not WF children; P-31 is exact
   equality for every tree and oracle; P-18, P-20 (map), P-22 hold for any oracle, partial or total.
5. **P-41 needs non-empty names** as a separate hypothesis because `IsDNS1123Subdomain` is opaque.
6. **P-36**: the clause "the tree contains at least one map leaf" is not stated or proved.
7. **CEL cost (P-78, §J):** both the 1M `PerCallLimit` and the 10M `runtimeCELCostBudget` are
   reachable in production, because cel-go charges a call's cost after it returns; one call can
   overshoot both, and neither bounds the CPU spent inside that call. (A wave-1 claim that the
   budget check was inert was wrong; corrected by the `cel` equivalence review with a probe.)

## Go ↔ Lean equivalence review

Seven independent reviewers compared every Lean definition with its Go source branch by
branch (`../review/lean-equivalence/*.md`): **no divergence** in decision, possible-decision
set, failure decision, error nil-ness or structure in any component. Their hardening proposals
applied in this snapshot: `ConditionEvaluationResult` zero value is `unevaluatable`;
`composeOracle` + `compose_decoded` make the `ev₀ ≡ U` precondition of
`tryEvaluateUsingBuiltins` explicit; `P_68_enforcer_runs` is a hypothesis, not an axiom; the CEL
cost note above. Open proposals (coverage, not correctness): `ConditionsAwareDecisionType.ofString`
canonicalisation in `encoding/`, the missing P-14 `err ≠ nil`, P-36 map-leaf and P-44 "every error
path returns FD" clauses, the remaining P-57 classes, and the line-number nits listed in the
reviews.
