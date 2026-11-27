# Plan: restructure kubernetes-cedar-authorizer around KEP-5681 as shipped in v1.38 (writes first, Lean first)

Status: revision 7 (stages 0-2 implemented, spike findings folded in; both blind reviews folded in; decisions D-1..D-13, section 8; follow-ups section 9). Not started; nothing in this
plan has been executed.
Inputs read: `kubernetes` review branch `impl-conditional-authz-review` (HEAD `2ee49d340c9`;
`review/kep.md`, `summary.md`, `decisions.md`, `properties.md`, `shipped.md`; `lean/`),
earlier attempts `origin/lean-test` and `origin/lean-test-2` of `luxas/kubernetes` (section 1.5),
this repo at `main` (`c1ce0f6`), cedar-spec PR #1015 (base) and #1021 (partial-attribute
testing), cedar PR #2547 (base) and #2581 (partial-attribute public API + JSON).
The TPE partial-attribute changes were audited by an explore agent (experiments in Lean and
Rust against the PR heads); the full report is `docs/tpe-risk-report.md` (kept verbatim, with
[V]erified/[I]nferred markers) and is folded into sections 1.3, 1.4, 3.2, 5 and 7.
Headline: R-1, R-2, R-3 are **go**. T-4 (`error` nodes do not round trip) is a documented
current limitation of Cedar (D-10). T-5 (no public reauthorize for decoded residuals) is not a
blocker: `evaluateConditions` works on concrete data and uses a normal `PolicySet`.

Standing rules for this plan:
- **Lean version of cedar-spec, always.** The Lean toolchain is whatever the pinned cedar-spec
  commit declares (`cedar-lean/lean-toolchain`). Nothing else may choose it. Code vendored
  from `kubernetes/lean` (4.35.0) is adapted to compile there, not the other way round.
- **One branch per stage**, named `<N>-<slug>` with `N` equal to the stage number, each a
  draft PR stacked on the previous branch (see section 5, conventions).

---

## 1. Findings that drive the plan

### 1.1 This repo targets a design that did not ship

- 8.2k lines of Rust built for the earlier `conditional_authz_2` fork: conditions are
  **CEL strings** translated from Cedar residuals (`cedar_authorizer/cel.rs`), and the apiserver
  evaluates them. v1.38 ships a different wire model: `ConditionsMap` / `Union` decisions in
  `SubjectAccessReview.status.conditionalDecision`, evaluated either by an in-process evaluator
  or by the webhook through the new `AuthorizationConditionsReview` (ACR) call.
- `kube_invariants/` (about 1.3k lines) exists only because the old Cedar TPE could express
  "unknown" only as an entity reference. It rewrites `resource.name`, `resource.namespace` etc.
  into entity refs. Partial attributes (`AttrState = value | partialRecord | present | absent |
  unknown`) remove the need for that rewrite.
- `symcc.rs`/`fork.rs` (analysis), `selectors.rs` (reads), `impersonate.rs`/`connect.rs`
  (other verbs) are outside the first scope.
- Still valuable: `schema/` (OpenAPI + discovery -> Cedar schema, ~2.5k lines),
  `entitybuilder.rs` (object JSON -> Cedar entity), `attributes.rs` (SAR -> attributes),
  `kubestore.rs` (policy loading), the localdev kind setup.

### 1.2 The existing Lean model is a model of Go, not an authorizer interface

`kubernetes/lean/` (23 modules, 347 theorems, 0 `sorry`, Lean 4.35.0, no Mathlib) mirrors the Go
packages one-to-one. It proves a lot about the decision *algebra* (`ConditionsAwareDecision`,
`ConditionsMap`, union builder, partial evaluation, webhook folding, enforcer clamps). But:

1. **There is no `Authorizer` in the Lean model.** `ConditionsAwareAuthorize` and
   `EvaluateConditions` appear only as ad-hoc function arguments (`union.lean`,
   `webhook.lean`). Nothing states what a *correct* authorizer is.
2. **The only semantic contract is `PossibleDecisions` soundness** (P-18, P-37, P-44, P-52): the
   answer lies in a set. The KEP's real claim is stronger: "the authorizer scopes down its
   policy *as if* it had the resource data" (Abstract), and "the two-phase result equals what a
   single-phase chain would have returned" (union section). That is a *refinement* statement
   against a reference semantics, and it is not stated anywhere. The clamps (union, webhook,
   enforcer) enforce the weak contract defensively; nothing says the unclamped path is right.
3. **The consumer side of consistency is implicit.** `EvaluateConditions` is called with
   admission-time data (`AdmissionRequest`: user, kind, name, namespace, operation, object,
   oldObject) for a decision authored from authorization-time attributes (URL-derived). Nothing
   states that these describe the same request, nor what "consistent" means when the name is
   unknown at authorization time (`create` with `generateName`, `deletecollection`).
4. **Webhook may send a refined decision** (`kep.md`, ACR "Request"): the authorizer "must not
   expect to receive back exactly the decision it issued". The contract therefore has to
   quantify over *refinements* of what `ConditionsAwareAuthorize` returned, not just the
   returned decision. The Lean model has partial evaluation (`evaluate.lean`, P-25..P-31) and
   confluence (P-27/P-28, with counterexamples), but not as a property of an authorizer.

Cedar's formalization already has exactly the missing vocabulary:
`PartialRequest`/`PartialEntities`, `RequestAndEntitiesRefine`, `isValidAndConsistent`,
`Response.reauthorize`, and the theorems `residuals_decision_agrees`,
`batched_authorize_loop_decision_agrees`, `partial_authorize_*_is_sound`. The plan is to
state the K8s contract in those terms and instantiate it with Cedar.

### 1.3 Partial attributes map onto K8s write requests directly

| Cedar entity / attr | create | update / patch | delete | deletecollection |
|---|---|---|---|---|
| `principal` (user, groups, uid, extra) | value | value | value | value |
| `resource.apiGroup / resource / subresource / namespace` | value | value | value | value (namespace may be unset for cluster-wide) |
| `resource.name` | **unknown** for create without subresource (`generateName`, name in body); **value** for create with a subresource (`create serviceaccounts/token`, `pods/binding`, `pods/eviction`: the name is in the URL) | value | value | **unknown**, always modelled so (a `metadata.name` field selector would just have been a `delete`) |
| `resource.request` (new object) | `present`/`unknown` | `present`/`unknown` | `absent` | `absent` |
| `resource.stored` (old object) | **`absent`** | `unknown` (update-to-create exists) | `unknown` | `unknown` |

**Action mapping (review B, C2).** The authorization-time action is the request verb. `patch` is
a member of the action group `update`, and `deletecollection` of the group `delete`, so
`action in k8s::Action::"delete"` matches both and one policy covers per-object admission (the KEP
says delete conditions apply to `deletecollection`, `kep.md:3451-3460`); stage 1 confirms how the
existing schema groups actions. Phase 2 never reconstructs the verb: `AdmissionRequest` carries
`operation`, not the verb. Cedar residuals are scope-less `when` clauses and TPE substitutes the
concrete action, so a residual never mentions `action`; phase 2 uses a fixed placeholder action
and a load-time check rejects residuals containing `Var::Action`. The Lean `Consistent` is
therefore defined modulo the action (lemma `residual_independent_of_action`). **Verified in
stage 1:** `TpeResponse::reauthorize` with the placeholder action fails for all 17 conditional
shapes with `InconsistentRequests(InconsistentAction)`; the plain `Authorizer` over the decoded
JSON conditions is correct, which is the design (3.2). Action entities are **not** put in the
entity JSON in either phase (both parsers reject them); the schema supplies them, and
`action in k8s::Action::"update"` / `"delete"` matches `patch` / `deletecollection`.

| verb at authorization | admission `operation`(s) in phase 2 | `object` | `oldObject` |
|---|---|---|---|
| create | CREATE | new object | none |
| create `pods/exec` etc. (POST connect) | CONNECT | `PodExecOptions` etc. | none |
| create on a subresource (`serviceaccounts/token`, `pods/eviction`) | CREATE | body of the subresource kind (`TokenRequest`, `Eviction`), not the parent | none (the target object is invisible to policies, `security.md` S-10) |
| update, patch | UPDATE, or CREATE (update-to-create; the secondary check is unconditional `Authorize` in v1.38, so conditional-only create policies deny it, to be documented and tested) | new | stored |
| delete | DELETE | none | stored |
| deletecollection | DELETE, once per matching object | none | stored |

**Deterministic entity ids (review B, C3; decision D-12).** Residuals keep entity literals, so
every entity that can appear as a literal has an id that is a pure function of request data:
principal id is the user `uid` when set, else a hash of the username; principal `extra`,
`groups` and the label and annotation maps are **records or sets, not entities** (schema
generator change); `resource.namespace` is the namespace name as a string (F-5 revisits). The old
`new_uuid()` entity ids are removed, not ported. A load-time check rejects schemas with
entity-typed attributes reachable from the principal or resource other than the principal and the
synthetic resource.

Schema and encoding constraints found by the TPE audit (verified, `docs/tpe-risk-report.md` Q1/Q2/T-7/T-8):
- `request` and `stored` must be declared **optional** record attributes: `absent` on a required
  attribute is rejected by both implementations, and `unknown` on a required attribute is
  silently upgraded to `present`.
- The resource entity gets a **synthetic uid** with `name` stated `unknown`. A
  `PartialEntityUid` whose `id` is `None` loses all attribute-level knowledge, so "name
  unknown" must not be modelled as an unknown id. The uid is an implementation artefact:
  **policies never mention it** (a load-time lint rejects entity literals of the synthetic id
  and `resource == ...` comparisons; the policy scope uses `resource is <type>`). The same uid
  must be used in both phases because the residual embeds it; the plan uses one fixed reserved
  uid per resource type (for example `core::Secret::"@conditional-request"`, not a valid
  Kubernetes name), so `evaluateConditions` needs no discovery step. A random uid would have to
  be carried in the condition and gains nothing, since it cannot be referenced by policies.
- A record without markers is **closed**: an omitted optional attribute is `absent` and prunes
  policies. Request/stored objects must therefore be stated `present` (or as a partial record
  containing a marker), never as a concrete record unless fully known (risk T-7).
- Every optional access in a policy needs a `has` guard, otherwise TPE rejects the whole policy
  set (T-6); policies are validated individually at load time.
- Kubernetes `map[string]string` (labels) typing was measured in stage 1 (R-9): a record with
  declared keys type-checks `labels["owner"]` behind a `has` guard but rejects objects with any
  other key (the converter must drop undeclared keys); open records are unsupported at the pin;
  `Set<{key, value}>` always conforms and stays decidable but loses the `labels["owner"]` syntax.
  Open decision D-14. Subresource action types declare no `stored`; `namespace` is stated only
  when non-empty. The Lean policy ASTs must be left-nested like Cedar's parser (TPE folds
  `A && (false && error)` but not `(A && false) && error`).

`absent` for `stored` on create lets `resource has stored` prune at authorization time, which the old
entity-ref rewrite could not do. Open question to retire in a spike (Stage 1): whether TPE keeps
deep paths such as `resource.request.metadata.labels["owner"]` as residuals when `request` is
only `present`, and what size the residual policies have.

### 1.4 Environment facts that affect sequencing

- **Pins (verified by the audit).** Lean: cedar-spec #1015 head `7d6298b054e70b2152c379d0b89e045b80d5a37b`
  (`tpe-lean-model`), toolchain **Lean v4.36.0** with batteries `v4.36.0`; a downstream
  Lake project with `subDir = "cedar-lean"` builds and `#print axioms` on the headline
  theorems shows only `propext`, `Classical.choice`, `Quot.sound`. Rust: cedar #2581 head
  `99a88d53fd587299d41e2d0c8b9da88632490711` (includes #2547 `782a4f28...`), `cedar-policy`
  with feature `tpe`, MSRV 1.89. **#1021 is not used**: it is stale (`DIRTY`, toolchain
  v4.33.1, older Lean commit), so partial-attribute differential testing is built here
  (stage 4). Local toolchains seen: cedar-spec main v4.34.1, K8s mirror v4.35.0, so the vendored mirror must be moved to v4.36.0.
- All four PRs are open and `REVIEW_REQUIRED`; `tpe` is experimental with no semver promise.
  Open upstream questions that could change semantics: `unknown` on a required attribute,
  meaning of explicit `absent`, a possible `Residual::PartialError`. Pin by SHA, mirror each
  SHA to a branch in a fork you control (PR heads can vanish), and keep all Cedar-facing code
  in one adapter module per language.
- K8s limits that the Cedar instantiation must respect: 128 conditions per map (total over the
  three lists), 10240 bytes per condition, IDs and types domain-prefixed, a map must not be
  NoOpinion-only (folds to an unconditional NoOpinion without error, `kep.md:1404-1410`; description at most 1024 bytes; `conditionsmap.go`, mirrored in `lean/authorizer/conditionsmap.lean`).
- Cedar skips policies that error (both permit and forbid). K8s' algebra fails closed on
  Deny-effect errors. See decision D-2.

### 1.5 Prior art: `lean-test` and `lean-test-2` (what to keep, what to fix)

Both branches carry a Mathlib-based Lean model (`ConditionalAuthorization/{Authorizer,Spec,Union,
Go,ConditionsMapReal}.lean`) and planning notes (`plan/plans/*.md`, `plan-updated-impl.md`).
`lean-test-2` is the simplified one (Spec 112 lines, Union 296, Go 457).

Worth keeping:
- An `Authorizer` **structure** with `name`, `authorize`, `conditionsAwareAuthorize`,
  `evaluateConditions`, plus a per-authorizer contract; the union authorizer built as an
  `Authorizer` instance with a proved contract (`unification-plan.md`); the proof that
  walking the union in parallel with its sub-decisions equals the ideal chain
  (`evaluate_eq_ideal`); a Go-style `Do`-notation transliteration compared to a proof-friendly form
  (`compositional-eq.md`); the Lean-FFI differential-fuzzing idea (`lean-ffi.md`).
- The user's notes (`plan/plans/notes.md`): prove the *exact* decision, not just "is Allow";
  `authorize` must fold down soundly (conditional Deny-effect -> `Deny`) and `Authorize == Allow`
  must imply `ConditionsAwareAuthorize == Allow`; unconditional `ConditionsAwareAuthorize`
  must equal `Authorize`; guard misbehaving authorizers in the framework instead of assuming
  them away; 403-vs-500 handling in the filter must equal the enforcer's; name-based
  matching in union evaluation.

Problems to fix (each is addressed in 3.1):
1. **`Ideal` is circular.** `ConditionsMap.Ideal c d := c.evaluate d`, and the contract says
   `evaluateConditions = Ideal`. For maps that is a tautology: the "reference semantics" is the
   map's own evaluator. Nothing relates it to what the authorizer would answer with full data.
2. **The contract is baked into the structure** (`ax_authorizer` is a field), so a faulty
   authorizer cannot be expressed, and clamps/guards cannot be stated as theorems about
   arbitrary authorizers.
3. **`ConditionsData` and `Attributes` are unrelated string records.** No notion of consistency.
4. **Contract for unconditional decisions says `evaluateConditions _ = Deny`**, an artefact of
   calling it on a non-conditional input; the real rule (fail closed with
   `ErrorConditionEvaluationNotSupported`, mirror `interfaces.lean`) is not the same statement.
5. **Refinement is absent**: the webhook may send a refined decision.
6. **Mathlib dependency and drift from Go.** The review-branch mirror drops Mathlib and tracks
   Go line by line; the new work builds on the mirror.

---

## 2. Scope

In scope (first milestone):
- Write requests as classified by the KEP: resource requests with verb `create`, `update`,
  `patch`, `delete`, `deletecollection` (subresources included, e.g. `create pods/exec`,
  `create serviceaccounts/token`), excluded groups as the classifier excludes them.
- Authorizer role only: the webhook answers `SubjectAccessReview` with `Allow`, `Deny`,
  `NoOpinion` or a `ConditionsMap`, and answers `AuthorizationConditionsReview`.
- Lean first, with theorems; then Rust backport; then kind e2e.

Out-of-scope request shapes still reach the webhook (it is the cluster's authorizer). They
receive an unconditional `NoOpinion`, never an error; a test covers every such shape. A SAR for a
write that does not advertise `ConditionsMap` and `Union` in `handledDecisionTypes` runs the same
TPE and is folded with `FailureDecision` (`Deny` if a Deny condition exists, else `NoOpinion`).

Out of scope (recorded so they are not lost):
reads/selectors, `GET` connect, impersonation and constrained impersonation, update-to-create
compound authorization, Node authorizer, namespace-object conditions (D-5), Cedar -> CEL
translation and the in-process evaluator path (D-4), SymCC analysis, aggregated API servers,
a served ACR endpoint inside kube-apiserver.

---

## 3. Target architecture

Three layers, each in Lean and mirrored in Rust with the same names.

```
L0  Cedar (dependency, not ours)      Cedar.TPE.*, Cedar.Thm.TPE.*    cedar-policy (tpe-inf)
L1  K8sAuthz  (Kubernetes contract)   Go-mirror (existing) + Spec     crates/core: algebra + wire types
L2  CedarK8s  (instantiation)         K8s write request -> Cedar      crates/core: cedar module
                                      TPE; residuals <-> conditions
```

### 3.1 L1 `K8sAuthz.Spec`: the strengthened authorizer interface (Lean, no Cedar)

Revised after blind review A (`docs/reviews/plan-review-A.md`). The reviewer's compiling Lean core
sketch (`docs/reviews/sketch/ReviewASketch.lean`, 917 lines, no `sorry`) is the starting point
of stage 2; it showed that the first draft of this section was **unsatisfiable** (`Lawful` and
`Guarded` contradicted each other, and `Refines` was not definable from `World`).

**Principle.** An authorizer is a record of functions with *no* embedded laws. A separate
predicate says what it must satisfy, relative to an **independent reference semantics**
`full`. Faulty authorizers stay expressible, and the framework (union, filter, enforcer, guard)
is proved correct for lawful ones and safe for guarded ones.

```lean
structure World where
  Attrs      : Type                          -- authorization-time attributes (URL-derived metadata)
  Data       : Type                          -- ConditionsData (admission-time request, object, oldObject)
  Consistent : Attrs → Data → Prop           -- Data describes the same request Attrs was derived from;
                                             -- Attrs may know LESS (name unknown on create)
  truth      : Data → Condition → CondResult -- the instance's own meaning of each condition
                                             -- (Cedar: evaluate the decoded residual on concrete data)

structure Authorizer (W : World) where
  name                     : String          -- non-empty, distinct, DNS-1123 within a union
  authorize                : W.Attrs → Decision × String × Option Err
  conditionsAwareAuthorize : W.Attrs → ConditionsAwareDecision
  evaluateConditions       : ConditionsAwareDecision → W.Data → Decision × String × Option Err
```

`full : W.Attrs → W.Data → Decision` is a **parameter of the predicates**, not a field of `World`
(each authorizer family supplies its own; a chain's `full` differs from its members').
`⟦x⟧_o` is the reference fold of a decision under an oracle `o`: D > N > A within a map, first
non-`NoOpinion` within a union. `Refines o x y` (x refines y) is the reflexive-transitive
closure of agreeing partial-evaluation steps (a condition replaced by its result under `o`; a
union collapsed when one outcome remains). `good x` is `WF x` together with `FailureDecision x ∈
PossibleDecisions x` for conditional `x`: the review showed that a union child with
`PD = {Allow}` is WF yet has `FD = NoOpinion ∉ PD` (mirror `P_44_needs_child_WF`).

**`Sound full A` (holds even when a remote fails; what A-4's forward direction needs).** For all
`a`, and `d` with `Consistent a d`:

| # | Clause |
|---|---|
| S1 | `good (A.conditionsAwareAuthorize a)` |
| S2 | one-sided fold-down: `authorize a` is never more permissive than `FoldDown (conditionsAwareAuthorize a)` in the order `Deny < NoOpinion < Allow`, and a Deny is preserved (`FoldDown x = x` if unconditional, else `FailureDecision x`). Equality is not provable for the shipped webhook (two separate remote calls; the legacy path and the conditions-aware path can disagree while both fail closed) |
| S3 | for every conditional `x` with `Refines (truth d) x (conditionsAwareAuthorize a)`: `evaluateConditions x d = Allow → full a d = Allow` |
| S4 | **Deny-faithful**: `full a d = Deny → evaluateConditions x d = Deny` for such `x` with `Deny ∈ PD x`, and any forbid the authorizer could not encode or evaluate is counted as a Deny effect when building the fail-closed result (review C4: a member that fails closed to `NoOpinion` where `full = Deny` lets a later chain member allow) |

**`Lawful Dom full A` (exactness; extends `Sound`; needs availability).** Adds, for `Dom a d ∧
Consistent a d` (a domain of inputs where the authorizer can succeed: the limits, builder and
error-node conditions `H` of 3.2 live here, not in a prose caveat):

| # | Clause | Notes |
|---|---|---|
| L2 | `authorize a = FoldDown (conditionsAwareAuthorize a)` (decision part) | exact; error nil-ness is added only if A-7 is proved at this level |
| L3 | **agreement:** `full a d = ⟦conditionsAwareAuthorize a⟧_{truth d}` | implies the old possible-set soundness (P-37), exactness of unconditional decisions, and ties every unconditional result of partial evaluation to `full` (the "P-28 gap"); the former L5 and L7 are derived and removed |
| L4 | **refinement, conditional input only:** for every conditional `x` with `Refines (truth d) x (conditionsAwareAuthorize a)`: `evaluateConditions x d = full a d` | unconditional input is *not* constrained here (the first draft was false: the shipped union and webhook return `FailureDecision` for unconditional input, as the KEP requires of authorizers without condition support) |

**`Guarded A` (closure that today lives only in external clamps).** For all `x d` (consistent or
not):

| # | Clause |
|---|---|
| G1 | if `x` is conditional and `good x`: `evaluateConditions x d ∈ PossibleDecisions x`; if `x` is unconditional: the result is `FailureDecision x` (or `Deny` with `ErrorConditionEvaluationNotSupported` for an authorizer without condition support) |
| G2 | `evaluateConditions x d = Allow → Allow ∈ PossibleDecisions x` |

L6 (purity) is **not** a Lean clause (every Lean function is pure, so it would be vacuous). It is an
implementation obligation, reviewed in Rust: `evaluateConditions` reads nothing but `(x, d)`.
Lean statements are made per store snapshot `S` (`full_S`, `A_S`); that conditions embed the
residual policies is what lets Cedar meet the obligation (C-8).

`guard : Authorizer W → Authorizer W` implements the union and webhook clamp (`FailureDecision`
on violation). Proved: `Guarded (guard A)` for every `A`; for `Lawful`, `guard_inert` and
`Lawful Dom full (guard A)` (this needs L3: `full ∈ PD x` for the refined `x`, since only
`PD x ⊆ PD (caa a)` is known). The three Go clamps are different functions: the enforcer's
return guard answers `Deny` with a fixed error where the union and webhook answer
`FailureDecision`. Unifying them (Go change 5) is a behaviour change at the enforcer only, and
is stated as such.

**Theorems on top** (all abstract; proved once, with the sketch's proofs as the base):

| ID | Statement |
|---|---|
| A-1 | `chain_lawful`: if every member is `Lawful` (hence `good`) and names are non-empty, pairwise distinct and DNS-1123 (`NamesOk`), the union authorizer is `Lawful` with `full_chain = firstNonNoOpinion (members.map full)`. `NamesOk` is a hypothesis because `union.New` checks only empty and duplicate names and the builder checks DNS-1123 later, failing the whole union closed (then `Authorize` ignores names and can return `Allow` while `FoldDown` gives `NoOpinion`: a real inconsistency, proposed Go change 6). Routing is by name; `Add` is a no-op after the first member containing an unconditional Allow or Deny. Proved for two members in the sketch; the `n`-member version is an induction |
| A-2 | `guard_guarded`, `guard_inert`, `guard_lawful` as above |
| A-3 | `refines_sem`: `Refines o x y` and `wf y` imply `wf x` and `⟦x⟧_o = ⟦y⟧_o` (confluence); `peval_is_refinement`: for `WF d`, a total oracle `o`, a partial evaluator `p ⊑ o` that returns no errors, `Refines o (peval d p) d` (mirror P-25/P-27/P-28; the error premise and well-formed names are the hypotheses, the counterexamples stay as negative theorems). The bare closure property is only transitivity of `Refines` and is not an interesting theorem |
| A-4 | `enforcement_exact`, **per admission invocation**: for a classified write, one `(a, d)` with `Consistent a d`, `Dom a d`, a `Lawful` chain, the evaluating authorizer equal to the issuing one (mirror `P_72` reload hypothesis), and the enforcer present (mirror `P_68`): the enforcer admits iff `full a d = Allow`. The forward direction (admit implies `Allow`) needs only `Sound`. Request-level statements add hypotheses: the committed object is the validated one (storage retries re-run validation), `deletecollection` is evaluated per object, update-to-create adds the unconditional secondary `create` check, and later admission plugins can still reject. Evaluation by the enforcer is on the post-mutation object, so `full` is defined on that object |
| A-5 | `consistency_established`: a **Go-side conformance property**, not a Lean theorem: decoding the `AdmissionRequest` and recomputing the attributes must give `Consistent a d`. The corpus shows which `(verb, operation)` pairs are consistent: create/CREATE, update/UPDATE, patch/UPDATE, update/CREATE, delete/DELETE, deletecollection/DELETE with n objects. A `Consistent` that is empty on real pairs would make A-4 silently vacuous (`lawful_of_empty_consistent`), so non-emptiness on the real relation is a stage 3 exit criterion |
| A-6 | `unaware_fail_closed`: a consumer that did not ask for conditions never gets `Allow` from a conditional decision (mirror P-49 via S2) |
| A-7 | `status_agreement`: filter and enforcer map `(decision, hasError)` to HTTP status with one function (mirror-level, not at authorizer level) |
| A-8 | `lawful_nonvacuous`: `Lawful ∧ Guarded` hold for the always-`NoOpinion` authorizer (`A0_lawful`, `guard_guarded`) and for a toy conditional authorizer over `Data = Bool` with a `Consistent` that is neither empty nor total (`A2_lawful`, `W2_consistent_nontrivial`) |
| A-9 | `chain_sound_of_deny_faithful`: chain soundness holds if every member is `Allow`-sound and Deny-faithful; and `fail_closed_to_noOp_is_fail_open` as the negative theorem. For the webhook deployment this means `failurePolicy: Deny` for the Cedar webhook, or the stated hypothesis that it is not fail-open |

**Proposed Go-side changes** (written to `docs/interface.md`, not implemented here):
1. Doc comment on `Authorizer`: state agreement (L3), refinement (L4) and fold-down (S2/L2) in prose; today only "MUST implement as FromParts" exists.
2. State that `EvaluateConditions` receives a refinement of what the authorizer issued, only for conditional input.
3. Define the relation between `ConditionsData` and `Attributes` (`Consistent`) and require the enforcer to supply data satisfying it; document that `name` is unknown at authorization time for `create` without subresource and for `deletecollection`.
4. State that an authorizer with opaque IDs must read no state in `EvaluateConditions` beyond its arguments, or be stable over a snapshot.
5. Provide one exported guard used by union, webhook and enforcer (with the Deny-versus-`FailureDecision` difference made explicit).
6. Validate DNS-1123 names in `union.New` so a misconfiguration fails at startup instead of failing every decision closed (mirror review K11).

### 3.2 L2 `CedarK8s`: Cedar as a lawful authorizer for writes

- `attrsToPartial : Attrs → PartialRequest × PartialEntities` per table in 1.3.
- `dataToConcrete : Data → Request × Entities` (principal, placeholder action, resource entity
  with `request`/`stored` attributes from `object`/`oldObject`). Normative derivation from the ACR
  `AdmissionRequest` (review B, I4): `userInfo` {username, uid, groups, extra} -> principal, with
  the principal type derived from the username prefix exactly as in phase 1; `requestKind` (not
  `kind`) selects the schema version of `object`/`oldObject`, and both must be asserted equal or
  the evaluation fails closed (multi-version CRDs); `name` for a create comes from
  `object.metadata.name`, not from `AdmissionRequest.name`, which is empty on create (mutation
  test in stage 1; **not yet pinned against the Go admission order**: if only `generateName` is
  present when validating admission runs, the name is absent and name policies do not apply,
  a stage 3 item to confirm in Go);
  the phase-2 resource type comes from `requestResource` and `requestSubResource`, not from
  `kind` (for `serviceaccounts/token` the kind group is `authentication.k8s.io`, the resource
  group is empty), and the object's `apiVersion` must equal `requestKind` or evaluation fails
  closed; `namespace`, `resource`, `subresource` -> resource
  coordinates; `dryRun` and `options` are not exposed (Cedar context is `{}`); an object without
  `apiVersion`/`kind` never reaches the webhook.
- `Consistent a d :≡ RequestAndEntitiesRefine (dataToConcrete d) (attrsToPartial a)`. This is
  *defined* via Cedar's relation, so Cedar's soundness theorems apply without a bridge lemma.
- `conditionsAwareAuthorize a`: run `Cedar.TPE.isAuthorized`, but **do not use its `decision`
  directly** (review B, C1): Cedar's TPE answers `Deny` when no permit can fire even if undecided
  residual forbids remain, and for Kubernetes that is "Deny if the forbid is true, else
  NoOpinion", so returning NoOpinion would let a later authorizer allow a request the forbid
  denies. Let `F` be the residual forbids that are neither `false` nor `error`, `P` the residual
  permits that are neither `false` nor `error`, `TF` the forbids that are exactly `true` and `TP`
  the permits that are exactly `true`. Then: `TF ≠ {}` -> `Deny`; else `F = {}` and `TP ≠ {}` ->
  `Allow`; else `F = {}` and `P = {}` and `TP = {}` -> `NoOpinion`; otherwise a `ConditionsMap`
  with one Deny condition per member of `F` and one Allow condition per member of `P ∪ TP` (a
  `true` permit becomes an Allow condition whose body is `true`; a map with only Deny conditions
  is intended, since a conditional Deny must survive, `kep.md` "Authorizer requirements"). Cedar
  has no NoOpinion-effect policies, so `noOpinionConditions = []`. The map constructor is never
  called with zero Deny and zero Allow conditions.
  **Condition encoding (D-3, resolved).** No CEL translation: the condition *is* the Cedar
  residual. `id = kubernetes.cedarpolicy.com/p-<first 24 hex of sha256(policy-id)>` (an injective map of
  arbitrary policy ids into at most 63 label characters does not exist, so collisions are
  detected at policy load and the policy set is rejected: injectivity is a load-time invariant,
  not a theorem; the original policy id goes into `description`, at most 1024 bytes),
  `type = kubernetes.cedarpolicy.com/residual-policy`, `condition` = the residual policy in
  Cedar's JSON policy format (Rust: `Policy::to_json` on `TpeResponse::residual_policies()`;
  measured 242-849 bytes per policy, about 3.7x the text form, so the 10240-byte limit is
  far away but the 128-condition count is the likelier limit).
  **Residuals that never apply are dropped.** A residual that is exactly `false` or exactly
  `error` takes no part in the decision (`reauthorize_is_sound`: erroring policies are skipped),
  so `conditionsAwareAuthorize` emits no condition for it. Errors from the first phase are not
  carried to the second phase (follow-up F-1).
  **`error` nodes inside a remaining residual (T-4, current limitation, D-10).** Such a residual
  does not round trip through Cedar JSON (`to_json` emits `{"error":[]}`, `from_json` rejects
  it). For now the authorizer fails closed for that request (the map constructor's fail-closed
  result, with a counter). This is a limitation of today's Cedar and is expected to be fixed
  upstream (F-2); it is stated as a hypothesis `NoErrorNodes` of the completeness theorem
  (soundness is unconditional, since failing closed never returns `Allow`).
- `evaluateConditions x d`: `evaluateConditions` is concrete, so it needs no partial-evaluation
  machinery. It (1) builds a Cedar `PolicySet` from the Cedar JSON policies in `x`'s conditions,
  (2) builds the concrete request and entities from `d` (the entity builder is schema-conformant
  by construction; a build failure fails closed to `FailureDecision x`), (3) runs the ordinary
  Cedar authorizer, (4) maps the response to Deny / NoOpinion / Allow as above (satisfied forbid ->
  `Deny`; otherwise no satisfied permit -> `NoOpinion`; satisfied permit and no forbid -> `Allow`).
  Lean states the same thing with `Response.reauthorize` on the residual list; the Lean proof
  carries `isValidAndConsistent` as the hypothesis `Consistent a d` (clause L4's domain), and
  the `Guarded` wrapper covers inconsistent input, so no runtime consistency check is added.
  The audit showed a plain `Authorizer` over the residual policy set agrees with
  `TpeResponse::reauthorize` (3/3 cases, `response.rs:344-362`); this stays a differential
  test (C-9), not a design constraint.
- Conditions are *self-contained* residual policies, so `evaluateConditions` takes no policy
  store: purity (L6) holds by construction, and the atomicity goal is met for free.
- Size limits: if the residual set exceeds 128 conditions or any residual exceeds 10240 bytes,
  fall back to the map constructor's fail-closed result. The theorem states completeness only
  "up to limits" (hypothesis `Fits`) and states soundness unconditionally.

Theorems:

| ID | Statement | Proof source |
|---|---|---|
| C-1 | `cedarAuthorizer_lawful`: `Lawful Dom` with `Dom = Fits ∧ NoErrorNodes ∧ BuilderOk` (limits, D-10, entity builder), and unconditionally `Sound`, `Guarded` and Deny-faithful: every fail-closed branch counts each forbid that could not be encoded as a Deny effect (review A, C4; review B, I1), `full a d = ofCedar (isAuthorized req es policies)` | `residuals_decision_agrees`, `partial_authorize_*_is_sound`, `reauthorize_*_equiv` |
| C-2 | `unconditional_exact`: whenever `conditionsAwareAuthorize` returns an unconditional decision by the case split above it equals `full a d` for every consistent `d` (the KEP's positive and negative pruning); and a conditional result keeps every undecided forbid (no conditional Deny is pruned) | `no_satisfied_effect_if_empty_...`, `satisfied_effect_if_non_empty_...` |
| C-3 | `map_agrees_with_fold` (invariant: Cedar conditions are never evaluated by the generic K8s evaluator; they carry no in-process evaluator, so the oracle `error -> false` is the only one in use, review A M4): Cedar's `reauthorize` on a map's residuals equals the K8s D > N > A fold (`pmap`) under the oracle `o c = ⟦decode c⟧ req es` with Cedar's error -> not-applicable (D-2) | mirror `evaluate.lean` + C-1 |
| C-4 | `invalid_data_fails_closed`: if the entity builder rejects the data, the result is `FailureDecision`, never `Allow`; inconsistent data is covered by `Guarded` (G1/G2) | by construction + guard |
| C-5 | `encode_decode`: structured round trip `decode (encode r) = r` at the Lean `Residual` level (the byte-level print/parse is a Rust obligation, covered by differential tests, see 5.5) | Lean |
| C-6 | `limits_fail_closed`: if limits are exceeded the result is `FailureDecision`-shaped and never `Allow` | mirror `conditionsmap.lean` |
| C-8 | `store_independent`: `evaluateConditions` depends on nothing but the decision and the data, so a policy reload between the phases cannot change the result (KEP P-72; a selling point of self-contained residuals) | by type |
| C-9 | `plain_authorizer_eq_reauthorize`: a plain `Authorizer` over the policies decoded from conditions equals `Response.reauthorize` on the residuals | differential, stage 5 |
| C-7 | `request_name_unknown_on_create`: partial name is respected, i.e. a policy mentioning `resource.name` residualizes on create and is decided on update/delete | tests + theorem instance of C-1 |

### 3.3 Trusted gap, stated openly

(Consequence, review B M10: Lean cannot generate expected results for object JSON because the
converter is a hypothesis there, so `Vectors` only covers pre-converted entities. The converter,
the riskiest Rust code, gets a Rust-only golden corpus in stage 5 and the R-13 data.)

`object JSON -> Cedar record` (schema-directed conversion in `entitybuilder.rs`) is the largest
piece that cannot be proved cheaply. Plan: the Lean model fully covers metadata
(principal, action, resource coordinates, `absent`/`unknown` markers) and takes
`objToRecord : Json → Option (Map Attr Value)` as an *explicit hypothesis* with one stated
property: its output is an instance of the declared record type. It is differential-tested
against Rust (5.3). Every theorem that depends on it lists it by name in `STATUS.md`.

---

## 4. Repository layout (target)

```
PLAN.md                         this file, replaced by docs/ after stage 0
README.md                       rewritten, short
docs/
  design.md  interface.md  decisions.md  properties.md  status.md (generated)
  legacy/                       old impersonation.md, GETTING_STARTED.md until rewritten
lean/                           one Lake package `k8s-cedar-authz`
  lakefile.lean  lean-toolchain  lake-manifest.json   (pins cedar-spec commit)
  mirror/                       VENDORED copy of kubernetes/lean (D-1), verbatim modules
    UPSTREAM                    source commit (`kubernetes@2ee49d340c9` + path), never edited by hand
    {authorizer,union,webhook,encoding,filters,conditionsenforcer,cel}/   unchanged names
  K8sAuthz/Spec/                World, Authorizer, Lawful, Guarded, Chain, Enforcement, Refinement
  CedarK8s/Adapter.lean         the ONLY file naming Cedar.TPE internals
  CedarK8s/{Request,Entities,Conditions,Authorizer}.lean
  CedarK8s/Thm/                 C-1 .. C-7
  Vectors/                      executable: JSON in -> decision out, for conformance
crates/                         Cargo workspace
  core/                         pure, no I/O; mirrors lean/K8sAuthz + lean/CedarK8s name for name
  schema/                       OpenAPI + discovery -> Cedar schema (ported from src/schema)
  webhook/                      axum server, config, policy store, metrics
conformance/                    JSON vectors, produced by Lean, consumed by Rust tests
localdev/                       kind setup for the v1.38 build with gate on
```

Rules carried over from the Lean/Go mirror: every Rust item has a doc comment
`Lean: <Module>.<decl>`; every Lean decl has a doc comment `Rust: <path>::<item>` once the
backport lands.

Disposition of current files:

| Current | Action |
|---|---|
| `src/schema/*` | move to `crates/schema` with `git mv` (history kept); regenerate against the cedar pin; drop `impersonate`, `connect`, `customverbs` from the first build (recoverable from the legacy tag) |
| `src/cedar_authorizer/kube_invariants/*` | delete (superseded by partial attributes); keep the `ActionCapability` idea as a 4-row table in `core` |
| `src/cedar_authorizer/{cel,symcc,fork}.rs` | delete from the main tree (legacy tag) |
| `src/cedar_authorizer/entitybuilder.rs` | port into `crates/core`, rewritten for `request`/`stored` partial states |
| `src/cedar_authorizer/{authorizer,kubestore}.rs` | rewrite; keep policy-loading ideas |
| `src/k8s_authorizer/{attributes,err}.rs` | port; `selectors.rs` deleted (reads) |
| `src/main.rs` | rewrite in `crates/webhook` for the v1.38 wire types |
| `localdev/*`, `Makefile`, `Dockerfile` | rewrite for a v1.38 node image and `ConditionalAuthorization=true` + `conditionsReview` |

Preserve before touching anything: tag `legacy-pre-1.38` on current `main`.

---

## 5. Stages

Branches (one per stage, linear stack, each a draft PR whose base is the previous branch; the
first is based on `main`):
`0-skeleton` -> `1-tpe-spike` -> `2-lean-interface` -> `3-lean-cedar` -> `4-conformance` ->
`5-rust-backport` -> `6-kind-e2e`. Stages 1 and 2 are independent, but sit in this order so
the stack stays linear; if stage 1 stalls, `2-lean-interface` is rebased onto `0-skeleton`
with `git rebase --onto`.

Conventions for every stage (from standing preferences): a fresh plan sub-agent reviews all
evidence and commits the stage's `PLAN.md` before coding; branch number equals stage number;
every higher branch is rebased (`--force-with-lease`) when a lower one moves; commits carry the Claude co-author
trailer and are written with `git commit -F`; tests are reported with counts, never bare
exit codes, and each new behaviour has a test shown to fail when the implementation is
reverted; blind reviewers get a sharp central question and a full environment preamble.

### Stage 0: pin, freeze, skeleton (no semantics)
- Tag `legacy-pre-1.38`. Create the layout in section 4 with empty modules that compile.
- Pin cedar-spec #1015 (`7d6298b`, Lean v4.36.0) and cedar #2581 (`99a88d5`, includes #2547)
  by commit, and push each SHA to a branch in a fork you control (T-15). Add the verified
  Lake `require` (`subDir = "cedar-lean"`) and Cargo git dependency snippets from
  `docs/tpe-risk-report.md` Q7. Do not pin #1021. Move the vendored mirror from v4.35.0 to v4.36.0.
- Vendor `kubernetes/lean` verbatim into `lean/mirror/` (D-1), record `UPSTREAM`, and make it
  build on the pinned cedar-spec toolchain. Adaptations (4.35.0 -> pinned) are listed in
  `lean/mirror/ADAPTATIONS.md`, one line each; theorem statements are not edited.
  Unification of the mirror with the new `K8sAuthz.Spec` layer is deliberately deferred.
- Go source reference stays the review branch `impl-conditional-authz-review` at `2ee49d340c9`
  (the `file:line` doc comments in the mirror refer to it); `lean-test`/`lean-test-2` are read-only prior art.
- CI script `scripts/check.sh`: `lake build`, `cargo test`, zero-`sorry` check,
  `#print axioms` audit written to `docs/status.md`, a test-count report.
- Exit: both toolchains build the empty skeleton from a clean checkout.

### Stage 1: partial-attribute spike (parallel with stage 2)
- Input: `docs/tpe-risk-report.md`. Its R-1..R-4 answers are re-run, not trusted: copy the
  audit's experiments (`exp/Exp1.lean`, `rexp/src/main.rs`, `rexp/src/bin/exp2.rs`) into
  `spike/` and run them against the pinned SHAs.
- Additional checks: (R-6) frequency of residuals with an `error` node (D-10 limitation); (R-7) plain
  `Authorizer` over decoded residuals equals `reauthorize`; (R-8) closed-record versus
  partial-record behaviour of the object converter; (R-9) K8s `map[string]string` typing
  for `labels["x"]`; (R-10) a Lean type-erased printer compared with Rust `to_json` for the
  five KEP policies (normalise `&&` association); (R-11) which constructs can error inside a
  `forbid` (a D-2 lint list).
- The schema declares `request`/`stored` optional and every optional access is `has`-guarded.
- Hand-write a three-entity K8s-flavoured schema (`User`, `Namespace`, `core::configmaps`)
  and five policies from the KEP example list (owner label, sensitive field unchanged,
  name prefix on create, finalizer, node-bound) in both Lean (#1015 API) and Rust (#2581 API).
- Answer, with written evidence: (R-1) does TPE keep `resource.request.<path>` as a residual
  when `request` is `present`; (R-2) is `stored: absent` on create pruned as expected;
  (R-3) residual size per policy against the 10240-byte limit; (R-4) can the Lean and Rust
  residuals be compared structurally; (R-5) which Cedar names the adapter must wrap.
- **Shape corpus (R-12, review B, Q5; the cheapest test of the riskiest assumption).** Write
  `conformance/shapes.json` with about 14 request shapes: create, create with `generateName`,
  create `serviceaccounts/token`, create `pods/exec` (CONNECT), update, update-to-create, patch,
  delete, deletecollection over two objects, dryRun, a multi-version CRD, a ServiceAccount
  principal, a node principal. Each has the SAR attributes and a hand-built or captured
  `AdmissionRequest` (take them from `test/integration/apiserver/conditionalauthorization` on the
  review branch). For each shape: build the partial request and entities, run TPE with the five
  KEP policies, run phase 2 with a plain `Authorizer` over the decoded JSON policies, and
  compare with the original policies on the concrete data. Pass: identical decision for every
  shape. This fixes the Attrs <-> Data table of section 1.3 before any Lean theorem relies on it.
- **Real-object conformance (R-13).** Push about 200 real objects (pods, deployments, secrets,
  configmaps, a CRD with `x-kubernetes-preserve-unknown-fields`, a newer-version object) through
  schema generation, the converter and entity validation. Pass: at least 99% conform; failures are
  listed by cause (they fail closed in production, so this measures availability).
- **Schema generator for writes** (own deliverable, not a footnote): resource types per
  (resource, subresource), optional `request`/`stored` whose type is the kind of the
  (resource, subresource) in the request's version, labels and annotations as records, no
  entity-typed attributes (D-12), the `has`-guard lint, the reserved-uid lint, and the
  `NameCollisions` on `meta::V1ObjectMeta` that Stage 0 found (the OpenAPI golden test is
  currently `#[ignore]`d).
- Exit (thresholds): `docs/spike.md` records go/no-go per risk. R-3: at most 2 KiB per residual
  policy and at most 16 conditions for at least 95% of the KEP policies; R-12: all shapes pass;
  R-13: at least 99% conform. If R-1 fails, the plan changes (a Cedar change request, or a
  two-level entity encoding) before stage 3 starts.

### Stage 2: strengthened interface in Lean (parallel with stage 1)
- Start from `docs/reviews/sketch/ReviewASketch.lean` (compiles, no `sorry`, toy decision type) and
  rebuild it over the vendored mirror's real types (`ConditionsAwareDecision`, `ConditionsMap`,
  `DecisionSet`, the union builder) in `lean/K8sAuthz/Spec/`: `World` (with `truth`), `Authorizer`,
  `good`, `Refines`, `Sound`, `Lawful Dom full`, `Guarded`, `guard`, then A-1..A-9. Lift useful
  proofs from `lean-test-2` (`evaluate_eq_ideal`) only where they still apply (its contract was
  one-sided on `authorize` and Deny-on-unconditional).
- Re-derive the mirror's end-to-end theorems from `Lawful` where possible; record which mirror
  theorems become corollaries and which stay Go-specific.
- Non-vacuity as compiled `example`s (A-8) and the negative theorems the review found
  (`chain_needs_valid_names`, `chain_needs_good_members`, `G1_needs_good`,
  `fail_closed_to_noOp_is_fail_open`, `L4_literal_false`, `plan_lawful_guarded_clash`).
- Write `docs/interface.md` (proposed Go doc changes 1-6 and the KEP delta).
- Exit: 0 `sorry`; axioms listed; every A-n has a theorem or an explicit hypothesis entry;
  `lake build` and `scripts/check.sh` pass; a blind review asks "is `Lawful` too strong for any
  real authorizer (the webhook with a remote engine) or too weak to imply A-4?".

### Stage 3: Cedar instantiation in Lean (needs stages 1 and 2)
- Implement `CedarK8s` (3.2) behind `Adapter.lean`; prove C-1..C-7 for writes.
- Executable: `Vectors` reads a JSON case (policies, schema, attrs, data) and prints the
  `ConditionsAwareDecision` and the evaluated decision.
- Exit: 0 `sorry`; trusted gap (3.3) is the only hypothesis outside Cedar's own theorems;
  blind review question: "does C-1's `full` equal what Cedar's `isAuthorized` returns for
  the concrete request, including `generateName` and `deletecollection`?"

### Stage 4: conformance corpus and Lean sign-off
- Generate vectors from Lean: every KEP use case, every verb, `absent`/`unknown` edge cases,
  limit cases (129 conditions, 10241 bytes), invalid data, refinement cases (a decision with
  some conditions already removed).
- Review the *statements*, not just the proofs: a fresh agent reads KEP + properties.md and
  lists every KEP property with no Lean counterpart (extends `lean/STATUS.md`'s table).
- Exit: corpus checked in under `conformance/`; the coverage table shows which P-n have
  theorems and which are explicitly out of scope for writes.

### Stage 5: Rust backport
- 5a (can start after stage 0): `crates/core` wire types for SAR (with `authorizationOptions`,
  `conditionalDecision`) and ACR, `ConditionsMap` constructor and validation, `PossibleDecisions`,
  `FailureDecision`. `k8s-openapi 0.25` predates these types, so hand-written serde types
  generated from the v1.38 OpenAPI, with a round-trip test against Go-produced JSON (fixtures
  extracted from `encoding_test.go` and the integration tests of the review branch; they are a
  stage 0/5a deliverable).
- 5b (Cedar-facing code uses the public `cedar-policy` API of #2581, not `cedar_policy_core::tpe`
  internals; the entity-reference rewrite is dropped): `core::cedar` mirrors `CedarK8s` (attrs -> partial, conditions, authorize, evaluate).
- 5c: `crates/webhook`: SAR endpoint (a write without options runs TPE and folds with
  `FailureDecision`; with advertised options returns the conditional decision; every
  out-of-scope shape returns an unconditional `NoOpinion`), ACR endpoint with UID echo, policy
  store (source, hot reload, per-policy validation, T-6), counters for every fail-closed branch
  (D-10, limits, builder failure), TLS with required apiserver client certificate, and **no
  logging of request or object bodies** (the old `#[instrument(ret)]` in `main.rs` would log
  Secrets; the ACR carries full objects). Rust unit tests for gate-off/version-skew behaviour
  (P-61, P-80, P-81) so they do not wait for stage 6.
- 5d: conformance runner: every vector from stage 4 passes in Rust; byte-level residual
  print/parse fidelity tested against the Lean `Residual`; fuzzing with generated schemas,
  policies and objects; deterministic seeds only.
- Mutation checks on `core` (guards: limits, fail-closed branches, `absent`/`unknown`
  states), run in a scratch worktree; survivors are listed.
- Equivalence review: fresh agents compare each Rust module to its Lean module branch by branch
  (same procedure as the Go<->Lean reviews in `review/lean-equivalence/`).
- Exit: all vectors pass with zero unexplained diffs; equivalence reviews report no divergence
  or each divergence is recorded as a decision.

### Stage 6: integration on kind
- Node image from the `kubernetes` branch with `ConditionalAuthorization=true`,
  `authorizers[].webhook.conditionsReview`, enforcer plugin on.
- e2e: create/update/patch/delete/deletecollection with allow, deny, conditional-allow,
  conditional-deny; `SelfSubjectAccessReview` with `handledDecisionTypes`; webhook down;
  invalid object; limits; version skew (gate off).
- Rewrite `README.md` and `docs/GETTING_STARTED.md`.
- Exit: scripted run, output saved, with test counts.

### Later
Reads (selectors), constrained impersonation, update-to-create, namespace-object conditions,
CEL builtin evaluator, SymCC analysis. Each starts with its own stage-1-style spike.

---

## 5.5 Rust <-> Lean parity, now and later

- **Now:** differential testing. The Lean `Vectors` executable and the checked-in
  `conformance/` corpus are the oracle for `crates/core` (stage 4/5); in-process comparison
  through `cedar-lean-ffi`-style bridging is an option, a subprocess with JSON is the default.
- **Later:** close the gap with Aeneas (Rust -> Lean). So that this stays possible,
  `crates/core` is written in an Aeneas-friendly subset from the start: no `unsafe`, no `async`,
  no trait objects, no interior mutability, no I/O, simple ownership, iteration through
  explicit loops or slices. Cedar itself cannot be extracted (it is a dependency), so the
  Cedar calls sit behind one small trait whose Lean counterpart is Cedar's own spec, and that
  trait is the verified boundary. Unverified: Aeneas' Lean backend toolchain and library
  requirements versus the pinned cedar-spec toolchain; checked in a dedicated later spike.

---

## 6. Parallelism and critical path

```
0 ──┬─ 1 (spike) ───────┐
    ├─ 2 (Spec in Lean) ┴─ 3 (CedarK8s) ─ 4 (corpus) ─ 5b/5c/5d ─ 6
    └─ 5a (wire types, validation)  ─────────────────────┘
```
Critical path is 1 -> 3. Stage 2 is independent of Cedar and can absorb Cedar PR churn.

## 7. Risks

| Risk | Mitigation |
|---|---|
| Cedar PRs change under us | pin by commit; one adapter module per language; rebase only deliberately |
| R-1 fails (no deep residuals) | detected in stage 1 before any proof work |
| Residuals exceed 10 KiB or 128 conditions | limits modelled and proved fail-closed; measure in stage 1 |
| Entity builder is unproved | named hypothesis, differential tests, listed in `status.md` |
| KEP/Go still moving (alpha) | mirror pinned to `2ee49d340c9`; `docs/interface.md` is a delta, not a fork |
| `Lawful` too strong | stage-2 review question; webhook-with-remote-engine as the test case |
| `error` nodes do not round trip (T-4) | current limitation (D-10): fail closed; follow-up F-2; frequency measured in spike R-6 |
| No public reauthorize for decoded residuals (T-5) | not needed: `evaluate` uses a normal `PolicySet` over the decoded JSON policies; differential test C-9 |
| One invalid policy fails the whole TPE call (T-6) | validate each policy at load; run TPE per policy; fails closed |
| Closed-record footgun (T-7), `unknown`-on-required (T-8) | state `present` for unknown objects; optional `request`/`stored`; trusted gap 3.3 |
| Cedar skips erroring `forbid` (T-10) | D-2 reference semantics, plus a lint for constructs that can error in a forbid |
| Lean toolchain skew | the cedar-spec pin decides (D-8); the vendored mirror is adapted in stage 0 before any new proof |

## 8. Decisions (resolved)

- **D-1 Mirror.** Vendor/copy `kubernetes/lean` into `lean/mirror/` for now, to keep it distinct
  from the new layer; unify later. The Go source of truth is the review branch
  (`impl-conditional-authz-review`, `2ee49d340c9`).
- **D-2 Error semantics.** Start with Cedar's reference semantics (an erroring policy is not
  applicable). Strengthening (fail closed on a Deny-effect error) is a later option, recorded
  against KEP D-3; the `oracle` in C-3 is where it would change.
- **D-3 Condition encoding.** The Cedar residual itself, no CEL; domain `kubernetes.cedarpolicy.com/`
  for condition ids and type; Cedar JSON policy format now, Cedar text format as a follow-up.
- **D-4 No in-process CEL path** in this milestone.
- **D-5 No namespace object** (or other non-request entity) in conditions now; possible follow-up.
- **D-6 Workspace of three crates** (`core`, `schema`, `webhook`).
- **D-7 `main` history.** Tag `legacy-pre-1.38`, delete old files in the first stacked PR.
- **D-8 Lean version.** Always the one pinned by the cedar-spec commit we depend on.
- **D-9 Name on create / deletecollection.** Always unknown; no special case for a
  `metadata.name` field selector.

- **D-10 Residuals with an `error` node.** Current limitation of Cedar: fail closed for the
  request (counter, no `Allow`), documented; fix expected in a future Cedar (F-2). Residuals that
  are exactly `false` or `error` are dropped as they never apply.
- **D-11 Resource uid.** One fixed reserved synthetic uid per resource type, never usable by policies
  (lint); not random, because it would have to be carried in the condition (see 1.3).

- **D-12 Deterministic entity ids**, maps as records, namespace as a string (see 1.3).
- **D-14 (open) Map typing.** Recommended: generate a declared-keys record for keys that appear in
  loaded policies (the converter drops other keys) and `Set<{key, value}>` for maps no policy
  references by key. Alternative: `Set<{key, value}>` everywhere (100% conformance, different
  policy syntax). Needs your decision before the stage 3 schema generator.
- **D-13 Actions.** `patch` in group `update`, `deletecollection` in group `delete`; phase 2 uses a
  placeholder action and residuals must not mention `action` (see 1.3).

Open, to decide at stage boundaries: Aeneas feasibility (5.5); whether `Lawful` should also
cover reason/error text (currently only decision, with error-ness handled by A-7).

---

## 9. Follow-ups (explicitly not in this plan)

- **F-1** Carry errors from the first phase (`conditionsAwareAuthorize`) into `evaluateConditions`
  so diagnostics and error-sensitive policies survive the two phases.
- **F-2** Handle residuals with `error` nodes once Cedar can round-trip them (upstream fix),
  then drop the `NoErrorNodes` hypothesis; until then fail closed.
- **F-3** Cedar text format for conditions instead of JSON.
- **F-4** Stricter error semantics (fail closed on a Deny-effect error), D-2.
- **F-5** Namespace object and other non-request entities in conditions.
- **F-6** Reads and selectors, constrained impersonation, update-to-create, `GET` connect.
- **F-7** Aeneas extraction of `crates/core`; unification of the vendored mirror and `K8sAuthz.Spec`.
- **F-8** CEL / in-process evaluator path.

---

## 10. Progress log

| Stage | Branch | State | Evidence |
|---|---|---|---|
| plan | `plan` | revision 7 | this file, `docs/reviews/` |
| 0 | `0-skeleton` | done | `scripts/check.sh` PASS; mirror builds unchanged on v4.36.0 (347 theorems, 2 mirror axioms, 0 `sorry`); `docs/status.md` |
| 1 | `1-tpe-spike` | done | `docs/spike.md`: R-1..R-4, R-6..R-8, R-10..R-12 GO; R-13 prototype only (73/73 fixtures conform only because undeclared fields are dropped; 2/73 with nothing dropped); 20 shapes, 21 admission requests, 0 mismatches; 30 spike tests, mutation-checked |
| 2 | `2-lean-interface` | done, with gaps | `docs/properties.md`, `docs/interface.md`; A-1..A-4, A-6, A-8, A-9 and the negative theorems proved; A-5, A-7, L6 are named hypotheses (`Hypotheses.lean`); 128 theorems, 0 `sorry`, no new axioms. Deviations from 3.1: `Sound` has separate reference and evaluation clauses (S3/S3e, S4/S4e); `Refines` gained `shrink` and `trunc` steps; the chain domain is `DA ∧ DB`; decisions are projected to `Dec` (no reason/error text); the n-member chain is a nested right fold, the flat union is not mechanised; the mirror's union handler, webhook and enforcer are not shown equal to the spec, only decisions and the partial evaluator are bridged |

Open items carried into stage 3: D-14; the Go admission order for `generateName`; the
update-to-create secondary check; principal `uid`/`extra`; the Lean re-run of R-1..R-3 (only the
R-10 printer exists in Lean); a blind review of the final `Lawful` ("too strong for the webhook?
too weak for A-4?"); R-13 on real clusters and CRDs; the write schema generator per
(resource, subresource) from discovery. `evaluateConditions` runs no consistency check (the
plain `Authorizer` path), so soundness rests on A-5 and on the entity builder: a recorded trusted gap.
