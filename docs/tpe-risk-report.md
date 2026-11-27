# TPE partial-attributes: risk report for the Kubernetes conditional-authorization authorizer (writes)

Date of analysis: 2026-11-27. All paths are relative to the cloned PR trees unless absolute.
Legend: **[V]** verified by running code or reading the cited line; **[I]** inference; **[?]** not verified.

## 0. Summary and verdict

- **R-1 (deep paths stay residual): GO.** [V] In both Lean (#1015) and Rust (#2547/#2581), `resource.request.metadata.labels.owner == principal.name` stays a residual over `Res::"r1".request.metadata.labels.owner` when `request` is `present`, unknown, or a partial record that does not decide the leaf. It folds to `true`/`false` as soon as the leaf (or an enclosing `absent`) is known.
- **R-2 (`absent` prunes): GO.** [V] `stored: absent` makes `resource has stored` → `false` and a `forbid` that guards on `resource has stored` → `false`, in both implementations. `request: absent` kills every guarded policy.
- **R-3 (size): GO for realistic policies, with a caveat.** [V] Per-policy residual: 83–230 bytes as Cedar text, 242–849 bytes as Cedar JSON (≈3.7× text). The 10 240-byte limit is far away. The caveat is `error()` nodes (R-4).
- **R-4 (Lean vs Rust residual comparable): PARTIAL.** [V] Same residual shape in my Lean and Rust runs, but the Lean `Residual` carries a `CedarType` on every node (raw `repr` 6 463 bytes vs 177 bytes of type-erased printing), the Rust residual is only exposed as `Policy` (text / JSON / PST), and the only existing comparison tool is the PST-based DRT harness in `cedar-lean-ffi`, whose partial-attribute extension lives in the **stale, conflicting PR #1021**.
- **Blocking finding (new, not in PLAN.md):** residual policies that contain an `error` node **cannot be round-tripped**. `Policy::to_json` succeeds and emits `{"error":[]}`, but `Policy::from_json` fails; the text form prints `error()` and `Policy::parse` fails. This directly hits D-3 (condition = the residual) and C-5.
- **Second new finding:** `TpeResponse::reauthorize` cannot be driven from decoded residual policies. It needs the live `TpeResponse` (borrows schema, partial request, partial entities). Its body is "validate + consistency-check + standard `Authorizer` over `policy_set()`" (`cedar-policy-core/src/tpe/response.rs:344-362`). The webhook-side `evaluateConditions` therefore has to re-implement the validation and consistency checks around a plain `Authorizer`.
- **Proof status:** [V] the soundness theorems build with Lean v4.36.0 on #1015, with no `sorry` and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
- **Overall:** Go for stage 1 spike and stage 3 on #1015 + #2547/#2581, conditional on the mitigations in section 4 (pin to mirrored SHAs, handle `error` nodes, own the second-phase evaluator, validate policy sets up front). Do not depend on #1021.

---

## 1. Findings per question

### Q1. The Lean model (cedar-spec #1015, head `7d6298b`, base = upstream `main` `0e8c45c`)

**Data types** (`cedar-lean/Cedar/TPE/`)

| Item | Definition | Evidence |
|---|---|---|
| `AttrState` | `value v` / `partialRecord (Map Attr AttrState)` / `present` (exists, value unknown) / `absent` (known not to exist) / `unknown` (existence unknown) | `Value.lean:34` |
| `PartialRecord` | `Map Attr AttrState`. **An attribute not listed is `unknown`** (`PartialRecord.attr`) | `Value.lean:~50` |
| `AttrState.ofDeclared` | required → `present`; optional → `unknown`; undeclared → `absent` | `Value.lean:70` |
| `PartialRecord.resolveAttr` | if the record states `unknown`, fall back to `ofDeclared`; any other stated state wins. So an explicit `unknown` on a **required** attribute is silently upgraded to `present` | `Value.lean:78` |
| `PartialRecord.isConcreteAt` / `asValues?` | a partial record folds to a concrete record only if every declared attribute is stated, each as `value`, `absent` or a concrete nested `partialRecord` | `Value.lean:89` |
| `PartialEntityUID` | `{ty, id : Option String}` | `Input.lean:~32` |
| `PartialRequest` | `{principal, action (concrete), resource, context : Option PartialRecord}` | `Input.lean:39` |
| `PartialEntityData` | `{attrs : Option PartialRecord, ancestors : Option (Set EntityUID), tags : Option PartialRecord}` | `Input.lean:51` |
| `PartialEntities` | `Map EntityUID PartialEntityData`. **An entity not in the map has no attribute knowledge at all**, so `entityAttr` returns `unknown` even for a required attribute | `Residual.lean:100` |
| `Residual` | `val/var/ite/and/or/unaryApp/binaryApp/getAttr/hasAttr/extHasAttr/set/record/call/error`, every node typed. **No `unknown` node**: unknowns are represented as attribute dereferences on an entity literal | `Residual.lean:31` |

**Validity** (are the partial inputs well formed against the schema)
- `partialRecordIsValid` (`Input.lean:91`): every stated attribute must be declared (new in #1015: stating an undeclared attribute, even `absent`/`unknown`, is rejected); `absent` is only valid for an **optional** attribute; `partialRecord` only at a record type; `value` must be `instanceOfType`.
- `entitiesIsValid` (`Input.lean:154`): entity id valid, ancestor types allowed by the schema, `attrs`/`tags` valid, action entities must agree with the schema.
- `validatePartialRequest`: the (principal type, resource type, action) triple must match a request environment; known pieces must instantiate the types.

**Consistency** (does the concrete world refine the partial one)
- `requestIsConsistent` (`Input.lean:184`), `entitiesIsConsistent` (`Input.lean:195`: **every partial entity must exist in the concrete store**), combined and executable in `isValidAndConsistent : Except ConcretizationError Unit` (`Input.lean:210`; errors `typeError | requestsDoNotMatch | entitiesDoNotMatch | invalidEnvironment`). It also checks `entitiesMatchEnvironment` (the whole concrete store conforms to the schema) and `env.validateWellFormed`.
- Proof-level relation: `RequestAndEntitiesRefine = RequestRefines ∧ EntitiesRefine` (`Thm/TPE/Input.lean:220`), connected by `consistent_checks_ensure_refinement` (`Thm/TPE/Input.lean:272`) and `isValidAndConsistent_env` (`Thm/TPE/Authorizer.lean:49`).

**Top-level theorems** (all in `cedar-lean/Cedar/Thm/`; hypotheses abbreviated, `V&C` = `isValidAndConsistent schema req es preq pes = .ok ()`)

| Theorem | File:line | Statement |
|---|---|---|
| `reauthorize_is_sound` | `TPE.lean:53` | `V&C` ∧ `TPE.isAuthorized … = ok response` ⟹ `response.reauthorize req es = Spec.isAuthorized req es policies` (full response equality, including determining and erroring policies) |
| `partial_authorize_decision_is_sound` | `TPE.lean:81` | `TPE.isAuthorized = ok r` ∧ `V&C` ∧ `r.decision = some d` ⟹ `(Spec.isAuthorized …).decision = d` |
| `partial_re_authorize_decision_eq` | `TPE.lean:104` | composition of the two: `(r.reauthorize req es).decision = d` |
| `partial_authorize_erroring_policies_is_sound` | `TPE.lean:125` | `errorForbids ∪ errorPermits ⊆ (Spec.isAuthorized …).erroringPolicies` (one direction only) |
| `partial_authorize_allow_determining_policies_is_sound` | `TPE.lean:150` | determining policies of a partial `allow` are determining in the concrete result |
| `partial_authorize_satisfied_forbid_is_determining`, `…_no_satisfied_forbids_if_allow`, `…_satisfied_permits_not_determining_if_deny` | `TPE.lean:217/267/180` | finer reason-set facts |
| `partial_evaluate_is_sound` | `TPE/Soundness.lean:64` | expression-level core: `Residual.WellTyped env x` ∧ `InstanceOfWellFormedEnvironment req es env` ∧ `RequestAndEntitiesRefine …` ⟹ `(x.evaluate req es).toOption = ((TPE.evaluate env x preq pes).evaluate req es).toOption` |
| `evaluatePolicies_residuals_equiv` | `TPE/Authorizer.lean:82` | per-policy residual ≡ original under `toOption` |
| `batched_authorize_decision_eq_authorize` | `BatchedEvaluator.lean:126` | `req.context.WellFormed` ∧ `EntityLoader.WellBehaved schema.ets es loader` ∧ `schema.validateWellFormed = ok ()` ∧ `validateEntities schema es = ok ()` ∧ batched result has decision `d` ⟹ same concrete decision |
| `batched_evaluate_eq_evaluate` | `BatchedEvaluator.lean:22` | single expression version |

`EntityLoader.WellBehaved` (`BatchedEvaluator/Common.lean:25`): every loaded slice refines the store. The "loads everything requested" condition is **not** required, because no convergence/completeness proof exists.

**Soundness caveat:** all statements are equalities under `Except.toOption`, i.e. they identify "evaluates to an error" with each other. Error-vs-false distinctions are only recovered by the separate erroring-policies theorem (one-directional).

**`sorry` / axioms** [V]
- `grep -rn "sorry\|^axiom\|native_decide"` over `Cedar/TPE`, `Cedar/Thm/TPE*`, `Cedar/Thm/BatchedEvaluator*`: no hits (one `TODO` comment in `Soundness/Binary.lean:297` about proof tidiness).
- `lake env lean Ax.lean` with `#print axioms` on `reauthorize_is_sound`, `partial_authorize_decision_is_sound`, `partial_re_authorize_decision_eq`, `partial_authorize_erroring_policies_is_sound`, `partial_authorize_allow_determining_policies_is_sound`, `partial_authorize_satisfied_forbid_is_determining`, `partial_evaluate_is_sound`, `batched_authorize_decision_eq_authorize`, `batched_evaluate_eq_evaluate`, `isValidAndConsistent_env`: **all** report `[propext, Classical.choice, Quot.sound]`.
- The same result was reproduced from a **downstream Lake project** that `require`s the commit (section 3, Q7).

### Q2. Residual forms for `unknown` / `present` / nested `partialRecord` / `absent`

Mechanics (Lean `Evaluator.lean`, Rust `tpe/value.rs`, `tpe/evaluator.rs`):
- `getAttr` → `stateToResidual (attrStateAt …)`: `value` → literal; `absent` → `.error`; `partialRecord` → literal only if `asValues?` succeeds, else the `getAttr` residual; `present`/`unknown` → the `getAttr` residual (`Evaluator.lean:49`, `value.rs:125`).
- `hasAttr` → `true` for `value/partialRecord/present`, `false` for `absent` or an attribute not in the type, residual `hasAttr` for `unknown` (`Evaluator.lean:207`).
- `has a.b.c` (`extHasAttr`) is decided step by step and stops at the first `false` or undecided step (`Evaluator.lean:251`).
- `and`/`or` simplify with a literal on the left; with `false` on the right they only collapse if the left side is error-free (`Evaluator.lean:78`), so `A && false` stays when `A` can error.

**Experiment A (Lean, `exp/Exp1.lean`, output `exp/exp1.out`).** Schema: `User{name}`, `Res{request?: {metadata: {name?, labels?: {owner?}}}, stored?: …}`; principal `alice` known (`name = "alice"`). The policy must guard optional attributes: the validator rejects unguarded optional access (`attrNotFound`, see Q5). Policy `owner`: `resource has request && …metadata has labels && …labels has owner && …labels.owner == principal.name`.

| State of `resource.request` | Residual (type annotations erased) |
|---|---|
| (a) unstated / explicit `.unknown`, optional attr | `(Res::"r1" has request) && (…request.metadata has labels) && (…labels has owner) && (…labels.owner == "alice")` |
| (b) `.present` | `(Res::"r1".request.metadata has labels) && (…labels has owner) && (…labels.owner == "alice")` |
| (c) `partialRecord{metadata: partialRecord{name:'x'}}`, `labels` unstated | same as (b): `labels` is optional, so `unknown` |
| (c2) …`labels: .present` | `(…labels has owner) && (…labels.owner == "alice")` |
| (c3) …`labels: partialRecord{owner:'alice'}` | `true` |
| (c4) …`labels: partialRecord{owner: absent}` / (c5) `labels: absent` / (d) `request: absent` | `false` |
| `request` **required** in schema, unstated or explicit `.unknown` | as (b): the `has request` step is gone (`unknown` upgraded to `present`) |
| resource entity missing from partial store | as (a): nothing folds, `Res::"r1"` is only a literal |

`has` and `stored` (Lean): `stored: absent` → `false`; unstated → `Res::"r1" has stored`; `present` → `true`. The `forbid` guarded on `resource has stored`: `absent` → `false`; `present` → `(Res::"r1".stored.metadata has name) && (…name == "protected")`.

**Experiment B (Rust #2581, `rexp/src/main.rs`, output `exp/rust-out.txt`).** Same schema in Cedar syntax and same policies, partial entities in the new JSON format with `{"__extn":{"fn":"partial","arg":"present|absent|unknown"}}`. Selected rows (text form of the residual; `policyN` ids are positional):

```
(a) request unstated        owner:    (Res::"r1" has request) && (Res::"r1".request.metadata has labels) && (Res::"r1".request.metadata.labels has owner) && (Res::"r1".request.metadata.labels.owner == "alice")
(b) request present         owner:    (Res::"r1".request.metadata has labels) && (…labels has owner) && (…labels.owner == "alice")
                            ownerExt: (Res::"r1".request has metadata.labels.owner) && (Res::"r1".request.metadata.labels.owner == "alice")
                            hasDeep:  Res::"r1".request has metadata.labels.owner
(c1) request {metadata: present}         ownerExt: (Res::"r1".request.metadata has labels.owner) && (…labels.owner == "alice")
(c2) request {metadata:{labels: present}} owner:   (Res::"r1".request.metadata.labels has owner) && (…labels.owner == "alice")
(c8) request {metadata:{labels:{owner: present}}}  owner: Res::"r1".request.metadata.labels.owner == "alice"
(c3) labels {owner:'alice'} -> owner,ownerExt,hasDeep all TRUE ; (c3b) owner:'bob' -> owner,ownerExt FALSE, hasDeep TRUE
(c4)/(c5)/(d) owner:absent | labels:absent | request:absent -> owner,ownerExt,hasDeep all FALSE
(e) stored absent:   hasStored FALSE, forbidStored FALSE (decision still None because of the residual permits)
(e3) stored {metadata:{name:'protected'}} -> decision Some(Deny), true_forbids [forbidStored]
```

The Lean and Rust residuals agree on every row that both ran (modulo `&&` association: my hand-built Lean AST is right-nested, the Rust parser is left-nested, and Rust prints `has a.b.c` for the extended form).

**Two behaviours the plan table in 1.3 must respect** [V]
1. A nested JSON record **without** markers is a closed concrete value, so omitted optional attributes are `absent`: row `(c)` `request: {"metadata":{"name":"x"}}` made `owner`, `ownerExt`, `hasDeep` all `false`. With a marker inside the record (`{"name": present}`, row `(c7)`) the record becomes a partial record and unstated attributes are `unknown` (the residual keeps `has labels`). Mapping a K8s object to a closed record is only correct when the object is fully known. For `present`-only objects, emit the marker.
2. `absent` on a **required** attribute is rejected at entity construction (`MissingRequiredEntityAttr`, Rust row "request absent on required attr"; Lean `partialRecordIsValid`, `Input.lean:91`). `Res.request` and `Res.stored` must therefore be **optional** in the schema, otherwise delete/create cannot state `absent`.

**Resource with unknown id** [V, `rexp/src/bin/exp3.rs`]: `PartialEntityUid::new("Res", None)` leaves the residual in terms of the `resource` variable, e.g. `resource has stored`, nothing prunes. Attribute-level knowledge only attaches to an entity with a known uid. Use a synthetic known uid (for example the request coordinates) for the resource entity, and encode "name unknown" as `name: unknown` on that entity (row "synthetic resource id": `has stored` → `false`, `name` and `request` residuals as expected).

### Q3. Residual size and serialization

Rust serialization surface (#2581, `cedar-policy/src/api/tpe.rs`): `TpeResponse::residual_policies()` (non-trivial only, `:756`), `policies()`, `policy_set()` (`:782`), `get_policy`; each is a `Policy` (scope unconstrained, one `when` clause), with `Display` (Cedar text), `Policy::to_json()` (EST), `Policy::to_pst()`. [V]

Sizes measured (`rexp`):

| Policy | residual text (bytes) | EST JSON (bytes) |
|---|---|---|
| `hasStored` (`Res::"r1" has stored`) | 83 | 242 |
| `hasDeep` (`…request has metadata.labels.owner`) | 104 | 293 |
| `ownerExt` | 163 | 512–556 |
| `forbidStored` (present) | 153–179 | 518–623 |
| `owner` (4 conjuncts, deep paths, principal name folded in) | 203–230 | 743–849 |
| Lean `Residual`, `owner`, `repr` (types on every node) | 5 782–6 463 | n/a |
| Lean `Residual`, `owner`, type-erased printer | 148–177 | n/a |

Observations
- [V] JSON ≈ 3.7× text; every deep path repeats the entity literal `{"Value":{"__entity":{"type":…,"id":…}}}` (49 bytes) plus ~25–30 bytes per attribute hop.
- [V] Request-specific literals are folded in (`principal.name` became `"alice"`), so residual sets cannot be cached across requests.
- [V] The `sets` policy in `exp2` produced `(…has spec.replicas) && (!(…replicas <= 3)) && false && error()` (573 bytes JSON): never satisfiable but still non-trivial, because the left side can error (`Evaluator.lean:78`). Such dead residuals still count toward the 128-condition limit.
- [I] The 10 240-byte limit is only a risk for pathological policies (large `in [...]`/set literals, many guards). The 128-condition count is the more likely limit if every non-trivial residual becomes a condition.

**Round trip** [V, `exp/exp2.out`]: for 7 of 8 residual policies, `Policy::from_json(to_json())` and `Policy::parse(to_string())` reproduce the identical policy. The 8th, the one containing `error()`, fails both ways: JSON deserialization error, and text "`error` is not a valid function". `TpeError::ExprToResidualError::ErrorNotSupported` (`tpe/err.rs`, raised at `tpe/residual.rs:293`) also means a residual with an `error` node cannot be fed back into TPE.

**Lean vs Rust comparability (R-4)**
- Different shapes: Lean `Residual` is typed per node; the Rust residual → `Policy`/PST is type-erased. Structural equality therefore needs erasure (done by `cedar-lean-ffi`, `lean_ffi/tpe.rs::assert_tpe_responses_match`, which compares via `pst::Expr`).
- The harness exists (`cedar-lean-ffi`, `tpe-*-drt.rs` fuzz targets, protobuf `PartialInput`) but covering partial attributes needs #1021, which is stale (section 4, T-2).
- [I] Cheapest option for this project: a Lean type-erased printer (like the 20-line `pp` in `exp/Exp1.lean`) emitting the Cedar JSON/EST shape, compared in the Stage 4 corpus against `Policy::to_json`. Normalise `&&`/`||` association first.

### Q4. What the second phase needs

Lean: `Response.reauthorize (response) (req : Request) (es : Entities)` (`Authorizer.lean:156`) is total; the **precondition** is the theorem hypothesis `isValidAndConsistent schema req es preq pes = ok ()`. It evaluates every `ResidualPolicy` with `Residual.evaluate req es`; satisfied = `ok true`; errors are collected, not decisive.

Rust: `TpeResponse::reauthorize(&Request, &Entities)` (`cedar-policy/src/api/tpe.rs:708`, core `response.rs:344`):
1. `schema.validate_request(request)`;
2. `EntitySchemaConformanceChecker::validate_entity` on **every** concrete entity;
3. `self.entities.check_consistency(entities)` (`tpe/entities.rs:787`);
4. `self.request.check_consistency(request)` (`tpe/request.rs:290`);
5. `Authorizer::is_authorized(request, &self.policy_set(), entities)`.

Experiments [V] (`rexp`, section "reauthorize"):
- Concrete resource entity with `request.metadata.labels.owner = "alice"` → `Allow` (reason `owner`, `ownerExt`, `hasDeep`); `"bob"` → `Allow` (reason `hasDeep` only); labels missing → `Deny` with no errors.
- Resource entity missing from `Entities` → `Err(InconsistentEntities(MissingEntity))` ("present in the partial entities but missing from the concrete entities"). This matches Lean `entitiesIsConsistent`.
- Concrete `stored` present although partial said `absent` → `Err(InconsistentEntities(InconsistentEntity(MismatchedAttribute)))`. Same for `request` absent although partial said `present`. Fail closed by `Err`.
- Different concrete resource uid → `Err` (partial uid is known).
- Running the plain `Authorizer` over `resp.policy_set()` gave the same decision, reason set and error count as `reauthorize` and as the original policies in 3 cases (`exp2`). [V for these 3 cases; it follows from the code in `response.rs:361`.]

What entities must the evaluator hold: [V by the above, I for the general rule]
- the resource entity itself, with every attribute the residuals dereference (`request`, `stored`) and conforming to the schema; the principal entity with its ancestors if any residual contains `principal in G` (row "principal ancestors unknown": residual `User::"alice" in Group::"admins"`, so ancestors must be in `Entities`); group entities named in `in` literals as needed.
- Every uid that appears in the partial store must exist in the concrete store (both implementations enforce this).
- Residual literal uids are the loader's work list: `Residual.allLiteralUIDs` (`Residual.lean:~245`), Rust `ResidualPolicy::all_literal_uids`, `EntityLoader` trait (`tpe.rs:812`: must return all ancestors too; may return more; `None` for missing). Missing entities are omitted from the partial store on purpose (`SlicedEntities.asPartial`, `Input.lean:286`), because a `present` claim is only sound for an existing entity.

### Q5. Error semantics and fail-closed design points

- Residual `error` = "evaluates to an error": `absent` attribute dereference, arithmetic overflow, failing extension call. A policy whose residual is exactly `error` goes to `errorPermits/errorForbids` (`Authorizer.lean:ResidualPolicy.hasError`) and **does not take part in the decision**. `Response.reauthorize` ignores erroring policies for the decision and reports them in `erroringPolicies` (matches `Spec.isAuthorized`, theorem `reauthorize_is_sound`).
- **Forbid that errors is skipped** [V]: Rust `errs` experiment: `forbid … when { … && 1 + 9223372036854775807 > 0 }` → TPE residual `… && error()`; reauthorize → `Allow` with error "extension function `error` does not exist". This is PLAN decision D-2, confirmed.
- TPE decision logic (`isAuthorizedFromResiduals`, `Authorizer.lean:97`): a decisive `allow` needs a satisfied permit and **no** residual forbid; decisive `deny` needs a satisfied forbid or no satisfied/residual permit.
- Lean `TPE.Error` (`Evaluator.lean:26`): `evaluation | invalidPolicy (TypeError) | invalidEnvironment | invalidRequestOrEntities`. `isAuthorized.evaluatePolicies` is a `mapM`, so **one invalid policy fails the whole response**.
- Rust `TpeError` (`tpe/err.rs:154`): `IncompleteSchema | NoMatchingReqEnv | Validation(PolicyValidationError) | ExprToResidualError {MissingTypeAnnotation | UnlinkedSlot | UnknownNotSupported | ErrorNotSupported}`. Same all-or-nothing behaviour [V]: an unguarded `resource.request.metadata.labels["owner"]` produced `UnsafeOptionalAttributeAccess` for three attributes and the TPE call returned `Err`, also when it sat in a set with valid policies.
- Rust reauthorize errors (`ReauthorizationError`): `RequestValidation | EntityValidation | EntitiesConsistency | RequestConsistency` [V]. All are `Err`, none yields a decision. Lean has no runtime equivalent; `isValidAndConsistent` is executable and returns the corresponding `ConcretizationError`.

### Q6. API stability and limitations

PR state [V via `gh pr view`]

| PR | Base | State | Opened | Last updated | Notes |
|---|---|---|---|---|---|
| cedar #2547 | `main` | open, `REVIEW_REQUIRED`, `BLOCKED` | 2026-09-01 | 2026-11-24 | 1 commit, 10 files, +3 097/−452; 7 inline review threads from one reviewer (2026-09-30) plus a "lost track of whether to review again" comment |
| cedar #2581 | `tpe-final` (#2547) | open, `REVIEW_REQUIRED`, `BLOCKED` | 2026-09-25 | 2026-11-24 | public API + JSON + CLI, 23 files, +1 813/−374 |
| cedar-spec #1015 | `main` | open, `REVIEW_REQUIRED`, `BLOCKED` | 2026-09-02 | 2026-11-24 | 1 commit, 36 files, rebased onto current `main` |
| cedar-spec #1021 | `tpe-lean-model` (#1015) | open, `REVIEW_REQUIRED`, **`DIRTY`** | 2026-09-10 | head commit dated 2026-09-03 | **not rebased**; contains the older `fe204b8` version of the Lean commit; toolchain `v4.33.1` |

Open review questions that could change semantics (cedar #2547 inline comments, reviewer `victornicolet`):
- `entities.rs:561`: should explicit `AttrState::Unknown` on a **required** attribute be accepted? (Today it is accepted and upgraded to `present`; a stricter rule would reject it.) Affects the K8s adapter if it emits `unknown` for required attrs.
- `evaluator.rs:1860`: "what it means to be explicitly absent" (regression comment about a test).
- `evaluator.rs:546`: is returning `Unknown` too approximate for some case; maybe an extra `AttrState` variant.
- `evaluator.rs:101/323`: extra cloning vs the old TPE (performance).
- `evaluator.rs:592`: error residual with attribute access unreachable?
- Review also asks for a high-level spec of valid partial entities/records (required/optional vs `AttrState`). The Lean `partialRecordIsValid`/`partialTagsAreValid` is that spec today.
- In-code TODO by luxas (`evaluator.rs:131`): "introduce a `Residual::PartialError` variant". If added, it changes the residual vocabulary (and therefore the encoding in Q3).

Surfaces likely to churn [I from the above]
- Rust public API: all `tpe` items carry the experimental warning and sit behind feature `tpe` (`cedar-policy/Cargo.toml:79`, `cedar-policy-core` `tpe = []`). Neither PR touches the CHANGELOG. `PartialContext`, `PartialAttribute`, `PartialRecord`, `PartialEntity::new(uid, attrs, ancestors, tags, schema)`, `PartialRequest::new(principal, action, resource, context, schema)`, `TpeResponse` accessors, `EntityLoader`, JSON marker `{"__extn":{"fn":"partial","arg":…}}`. `PartialRequestCreationError` and `TpeReauthorizationError` became `#[non_exhaustive]` in #2581. The doc comment on `PartialRequest` still says the context "must either be fully known or unknown" (stale).
- Your current code uses `cedar_policy_core::tpe::{entities, request, residual::{Residual, ResidualKind}, response}` directly (14 `ResidualKind` references; `PartialEntity {uid, attrs: None, ancestors, tags}` and 5-arg `PartialRequest::new(.., None, schema)` in `authorizer.rs:423-442`) at fork rev `792e6d2` (2025-08-20), 612 commits before #2547's base. Core-crate internals have no stability promise. #2581's public API removes the need for them.
- Lean: names that recur in the PR diff and were renamed in the 5-commit history of #1021 (`388d786 renames`, `5d25b2c proofs tweaks`). The theorem names listed in Q1 predate the partial-attribute work (they exist in the older TPE) and are the most stable; `AttrState`, `PartialRecord`, `resolveAttr`, `partialRecordIsValid` are new and can still move.

Unsupported / limited forms relevant to Kubernetes policies
- Policies containing `unknown(...)` or an `error` node are rejected by TPE (`ExprToResidualError`).
- Extension-function calls are only folded when all arguments are values; otherwise they stay as `call` residuals (`Evaluator.lean:call`). `like`, `contains`, `containsAny`, `in`, arithmetic: all stay as residuals when an operand is unknown [V, `exp2`: `like`, `contains`, `containsAny`, `+`, `*`, `in`].
- `in`: with principal ancestors known it folds (`User::"alice" in Group::"admins"` → `true`); with ancestors `None` it stays `User::"alice" in Group::"admins"` [V]. Folds only depend on the ancestors set, so group membership for K8s must be given as ancestors.
- Tags: no declared key set, so a tag can never be concluded absent unless stated; `partialTagsAreValid` rejects stating any tag when the schema has none (Lean `Input.lean`).
- Cedar records have no open maps. `labels["owner"]` type-checks only if `labels` is a record type that declares `owner`; K8s `map[string]string` needs a schema encoding decision outside TPE [I; check how `entitybuilder.rs` handles it].
- The cedar CLI sample test `test_tpe_invalid_entities` fails on #2581 in my environment only because the snapshot contains a temp-file path (`[TEMPFILE]` redaction vs a `TMPDIR` in a different location). All other TPE tests passed (section 2).

### Q7. Toolchain and pinning

| Item | Value |
|---|---|
| Lean toolchain #1015 | `leanprover/lean4:v4.36.0` (`cedar-lean/lean-toolchain`); installed here with `elan toolchain install leanprover/lean4:v4.36.0` |
| Lean toolchain #1021 | `v4.33.1` (stale) |
| Local `cedar-spec` main / K8s mirror | `v4.34.1` / `v4.35.0` (from PLAN.md 1.4) so **three-way skew becomes a fourth**: the pin forces `v4.36.0` and batteries `v4.36.0` (`b4b25a3886a1…`) |
| Lean deps | only `batteries` (`require "leanprover-community" / "batteries" @ git "v4.36.0"`); `doc-gen4` is dev-only |
| Rust MSRV | `rust-version = "1.89"` (workspace) |

Downstream Lake project that works [V] (`downstream/lakefile.toml`, built with `lake build Down`, 407 jobs, success; `#print axioms reauthorize_is_sound` printed the three standard axioms):

```toml
name = "down"
defaultTargets = ["Down"]

[[require]]
name = "Cedar"
git = "https://github.com/cedar-policy/cedar-spec"      # I used a file:// clone for the test
rev = "7d6298b054e70b2152c379d0b89e045b80d5a37b"
subDir = "cedar-lean"

[[lean_lib]]
name = "Down"
```
plus `lean-toolchain` = `leanprover/lean4:v4.36.0`. Lake wrote the manifest entry with `"subDir": "cedar-lean"`, `"inputRev"` = the SHA, and pulled `batteries` as an inherited dependency. Import roots: `Cedar.TPE` (definitions), `Cedar.Thm.TPE` (theorems), `Cedar.Thm.BatchedEvaluator`.
- [V] A blobless clone of `https://github.com/cedar-policy/cedar-spec` contains `7d6298b…` (`git cat-file -t` → `commit`): #1015 is a same-repo branch (`tpe-lean-model`). If that branch is rewritten or deleted after a squash-merge, the SHA can disappear from clones, so mirror it to a fork branch you control.

Cargo [V] (`cargodep`, `cargo check` succeeded, 28 s):
```toml
cedar-policy = { git = "https://github.com/cedar-policy/cedar.git", rev = "99a88d53fd587299d41e2d0c8b9da88632490711", features = ["tpe"] }
# if you keep touching core internals (not recommended):
# cedar-policy-core = { git = "https://github.com/cedar-policy/cedar.git", rev = "99a88d53…", features = ["tpe"] }
```
`tpe` in `cedar-policy` enables `cedar-policy-core/tpe`; the CLI feature `tpe` additionally enables `partial-eval`. A git `rev` that is a PR head SHA is fetchable by Cargo from the upstream repo. Pin the same commit for `cedar-policy-symcc` if you keep using it (all crates share the workspace version `4.15.0`).

---

## 2. Experiments run

All sources are under `$KIROCREW_SCRATCH` = `/home/luxask/.kiro/crew/scratch/runtime-bce3c298` (`exp/`, `rexp/`, `downstream/`, `cargodep/`). The repositories in `~/code/` were only used as git object stores; I removed the worktrees, scratch branches and the `upstream` remotes I added (see section 6).

1. **Lean build of #1015.** `cd spec1015/cedar-lean && PATH=$HOME/.elan/bin:$PATH lake build Cedar.Thm.TPE Cedar.Thm.BatchedEvaluator UnitTest.TPE` → `Build completed successfully (415 jobs).` (log `lake1015.log`).
2. **Axioms.** `lake env lean Ax.lean` (file `Ax.lean`):
   ```
   'Cedar.Thm.reauthorize_is_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'Cedar.Thm.partial_authorize_decision_is_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'Cedar.Thm.partial_re_authorize_decision_eq' …                   [propext, Classical.choice, Quot.sound]
   'Cedar.Thm.partial_evaluate_is_sound' …                          [propext, Classical.choice, Quot.sound]
   'Cedar.Thm.batched_authorize_decision_eq_authorize' …            [propext, Classical.choice, Quot.sound]
   'Cedar.Thm.batched_evaluate_eq_evaluate' …                       [propext, Classical.choice, Quot.sound]
   (and the 4 others, identical)
   ```
3. **Lean residual experiment** `lake env lean exp/Exp1.lean` (excerpt of `exp/exp1.out`; `pp bytes` = type-erased, `repr bytes` = raw `Residual`):
   ```
   (a) request unknown (unstated)
   ((Res::"r1" has request) && ((Res::"r1".request.metadata has labels) && ((Res::"r1".request.metadata.labels has owner) && (Res::"r1".request.metadata.labels.owner == "alice"))))   [repr bytes=6463, pp bytes=177]
   (b) request present
   ((Res::"r1".request.metadata has labels) && ((Res::"r1".request.metadata.labels has owner) && (Res::"r1".request.metadata.labels.owner == "alice")))   [repr bytes=5782, pp bytes=148]
   (c3) ... labels partialRecord{owner: 'alice'}      true   [repr bytes=149]
   (c4) ... labels partialRecord{owner: absent}       false
   (d) request absent (delete)                        false
   == owner policy; schema: request REQUIRED   (a) request unstated -> same as (b)
   hasStored: stored absent -> false ; unstated -> (Res::"r1" has stored) ; present -> true
   forbidStored: stored absent -> false ; present -> ((Res::"r1".stored.metadata has name) && (Res::"r1".stored.metadata.name == "protected"))
   resource entity not in store at all -> same as (a)
   ```
   First attempt without `has` guards: `Error.invalidPolicy (TypeError.attrNotFound (entity Res) "request")` for every row.
4. **Rust build and tests of #2581.** `CARGO_TARGET_DIR=$S/target-cedar cargo build -p cedar-policy-cli --features tpe` OK (46 s). `cargo test -p cedar-policy-core --features tpe tpe::` → `177 passed; 0 failed`. `cargo test -p cedar-policy-cli --features tpe --test sample tpe` → `test_tpe_partial_attributes ... ok`, `test_tpe_partial_context ... ok`, `test_tpe`, `test_tpe_link` ok; `test_tpe_invalid_entities` fails only on a temp-path snapshot difference (`[TEMPFILE]` vs `/…/.tmpF08EH3`).
5. **CLI sample.** `cedar tpe --request-json …/tpe_partial_context/request_unstated.json -p …policies.cedar --entities … -s …`:
   ```
   UNKNOWN
   All policy residuals:
   @id("has-mfa")
   permit(principal, action, resource) when { context has mfa };
   ```
6. **Rust residual experiment** `cargo run --bin rexp` (excerpt of `exp/rust-out.txt`):
   ```
   --- (b) request present
   RESIDUAL[policy0] text (203 bytes): @id("owner") permit(principal, action, resource) when { (Res::"r1".request.metadata has labels) && (Res::"r1".request.metadata.labels has owner) && (Res::"r1".request.metadata.labels.owner == "alice") };
      json (743 bytes): {"effect":"permit",…"conditions":[{"kind":"when","body":{"&&":{"left":{"&&":{"left":{"has":{"left":{".":{"left":{".":{"left":{"Value":{"__entity":{"type":"Res","id":"r1"}}},"attr":"request"}},"attr":"metadata"}},"attr":"labels"}}, … ,"annotations":{"id":"owner"}}
   --- (e) stored absent    false_permits ["policy2"] false_forbids ["policy3"] residual_permits ["policy1","policy4","policy0"]
   --- (e3) stored {metadata:{name:'protected'}}   decision: Some(Deny)  true_forbids ["policy3"]
   ##### unguarded optional access
   TPE ERROR: Validation(PolicyValidationError { errors: [UnsafeOptionalAttributeAccess(… resource.request.metadata.labels["owner"] …) ×3
   ##### reauthorize
   [owner label matches] decision Allow reason ["policy0","policy4","policy1"] errors []
   [owner label mismatch] decision Allow reason ["policy4"] errors []
   [labels missing (guarded)] decision Deny reason [] errors []
   [resource entity not in Entities] reauthorize ERR InconsistentEntities(MissingEntity(…)) / entity `Res::"r1"` is present in the partial entities but missing from the concrete entities
   [INCONSISTENT: stored present though TPE said absent, protected] reauthorize ERR InconsistentEntities(InconsistentEntity(MismatchedAttribute(…)))
   [INCONSISTENT: request absent though TPE said present]          reauthorize ERR InconsistentEntities(InconsistentEntity(MismatchedAttribute(…)))
   errs: policy0 => @id("errforbid") forbid(principal, action, resource) when { (…labels has owner) && (…labels.owner like "*") && error() };
         reauth decision Allow errors ["error while evaluating policy `policy0`: extension function `error` does not exist"]
   ```
7. **Round trip and plain-authorizer equivalence** `cargo run --bin exp2` (`exp/exp2.out`): 
   ```
   policy2 => @id("sets") permit(…) when { (Res::"r1".request has spec.replicas) && (!(Res::"r1".request.spec.replicas <= 3)) && false && error() };
       json 573 bytes; json roundtrip: ERR error deserializing a policy/template from JSON; text roundtrip: ERR `error` is not a valid function
       json: {…"right":{"error":[]}…}
   (other 7 policies)  json roundtrip: identical; text roundtrip: identical
   [replicas 1/no fin] reauthorize=Ok((Allow, ["policy7","policy1"], 0)) plain(residual set)=(Allow, [...], 0) plain(original)=(Allow, [...], 0)
   [max replicas]      reauthorize=Ok((Allow, ["policy0","policy1"], 2)) plain(residual set)=(Allow, [...], 2) plain(original)=(Allow, [...], 2)
   ```
8. **Unknown resource id** `cargo run --bin exp3`: with `PartialEntityUid::new("Res", None)` the residuals are `resource has stored`, `(resource has name) && (resource.name like "x-*")`, `(resource has request.metadata.labels.owner) && (resource.request.metadata.labels.owner == "alice")`; with a synthetic known uid and `stored: absent`, `has stored` → `false`.
9. **Downstream Lake** (`downstream/`): `lake build Down` → `Build completed successfully (407 jobs).` with `#print axioms Cedar.Thm.reauthorize_is_sound` → `[propext, Classical.choice, Quot.sound]`.
10. **Cargo git dep** (`cargodep/`): `cargo check` OK against `rev = 99a88d53…`.

Not run [?]: Lean `CedarUnitTests` executable (only compiled `UnitTest.TPE`), Lean FFI/DRT harness (needs the `cedar-drt` build), a build of #1021 (stale, different toolchain), fuzz/DRT agreement of Rust and Lean on partial attributes.

---

## 3. Differences from the current code (contrast)

- Current Rust at `luxas/cedar@792e6d2` models unknown fields by turning them into entity references (`unknown_jsonpaths_to_uid`, `PartialValue::{Unknown, Unset, Known}` in `authorizer.rs` / `entitybuilder.rs`) and calls `policies.tpe(&req, &entities)` with `PartialEntity {attrs: None, …}` for the action. The new model states `present`/`absent`/`unknown` per attribute and per nested record, so the entity-reference rewrite and the JSON-path bookkeeping can go away.
- `PartialRequest::new` now takes a `PartialContext`; `PartialEntity::new` is schema-validating and fallible; JSON markers replace the old encodings.
- The old code reaches into `tpe::residual::{Residual, ResidualKind}` to classify residuals; the new public API offers `residual_policies()`, `true_*`/`false_*`/`error_*` iterators and `to_pst()`.

---

## 4. Risk register

| ID | Risk | Likelihood | Impact | Evidence | Mitigation |
|---|---|---|---|---|---|
| T-1 | The four PRs change or are not merged; names and semantics move (open review questions on required+`unknown`, explicit `absent`, a possible `PartialError` residual) | High (all `REVIEW_REQUIRED`/`BLOCKED`, reviewer asked who should re-review) | Medium (adapter and proofs reworked) | Q6 table; review comments | Pin SHAs (section 5), mirror each to a branch in your fork, one adapter module per language (already planned), re-verify the spike on every bump with `scripts/check.sh` |
| T-2 | #1021 is stale and conflicting; DRT coverage for partial attributes is not in #1015's tree | High | Medium (no differential Rust↔Lean evidence in a buildable state) | `mergeStateStatus=DIRTY`, head commit 2026-09-03, toolchain `v4.33.1`, contains older `fe204b8` | Do not pin to #1021. Own a small Stage 4 corpus comparing Lean `pp`/JSON vs Rust `to_json`; ask upstream for the restack or do it in your fork |
| T-3 | Toolchain skew: #1015 needs Lean `v4.36.0` and batteries `v4.36.0`; mirror is `v4.35.0` | Certain | Low–Medium (mirror needs a bump before stage 3) | `lean-toolchain`, `lake-manifest.json` | Adapt the mirror in Stage 0 (PLAN D-8 already says the cedar-spec pin decides) |
| T-4 | **Residual with an `error` node is not round-trippable**: `from_json` and text parse reject it; TPE rejects it as input (`ErrorNotSupported`); `to_json` emits `{"error":[]}` silently | High (any policy that can fold an absent/overflow/failing call into a conjunct) | High (D-3/C-5 encode/decode breaks; `decode` may fail closed for good policies, or someone adds a lenient decoder) | `exp/exp2.out` policy2; `tpe/err.rs`, `tpe/residual.rs:293` | In `encode`, round-trip check and reject; or substitute a type-correct always-erroring expression (for example an overflowing integer comparison) which preserves "skipped on error" semantics [I]; or send only non-trivially-erroring residuals and treat a residual that `Residual.isError`-folds as `false` for decisions (decision-equivalent, not diagnostics-equivalent) [I]. Prove or test the choice at the Lean `Residual` level (C-5) |
| T-5 | No public API to reauthorize **decoded** residuals with consistency checks; `TpeResponse` is not serializable and borrows its inputs | Certain | High for stage 3/5 design | `response.rs:344-362`; `tpe.rs:554` | Implement `evaluateConditions` as: schema validation of request/entities + consistency check against a re-derived partial world + plain `Authorizer` over decoded policies. In Lean, state it via `isValidAndConsistent` (executable, `Input.lean:210`). Add a differential test against `TpeResponse::reauthorize` (matches in 3/3 cases tried) |
| T-6 | One invalid policy fails the whole TPE call (Lean `mapM`, Rust `TpeError::Validation`) | High in practice (any optional access without a `has` guard) | Medium: availability, not safety (fails closed) | Q5, `exp/rust-out.txt` unguarded rows | Validate each policy against the schema at load time; run TPE per policy (or drop invalid ones with a loud error) instead of failing the request |
| T-7 | Closed-record footgun: a JSON record without markers is a fully known value, so omitted optional attributes become `absent` and prune policies | Medium | High if the object-to-record conversion wrongly claims completeness (incorrect `absent` prunes a permit or a forbid) | Rust row `(c)` vs `(c7)`; Lean `PartialRecord.ofConcrete` | Emit `present`/markers for unknown request objects; only emit concrete records for fully known objects. Reauthorize (or its re-implementation) must re-check consistency (T-5); this is the trusted gap in PLAN 3.3 |
| T-8 | `unknown` on a required attribute is silently upgraded to `present`; `absent` on a required attribute is rejected | Medium | Medium: can cause entity-construction failure for delete/create if `request`/`stored` are required | Lean `Value.lean:78`, `Input.lean:91`; Rust `MissingRequiredEntityAttr`; reviewer question `entities.rs:561` | Declare `request` and `stored` optional in the schema. Do not rely on explicit `unknown` for required attributes |
| T-9 | Entity must exist for `present`/`absent` claims; partial entity not in concrete store fails the consistency check; residual literal uids must be loadable | Medium | Medium | `entitiesIsConsistent` (`Input.lean:195`), Rust `MissingEntity`, `SlicedEntities.asPartial` | Build the resource and principal entities in both phases; use a synthetic known resource uid (unknown id loses all attribute knowledge) |
| T-10 | Cedar skips erroring policies, including forbids (fail-open on errors) | Medium | High for security-relevant forbids | `errs` experiment: forbid errored → `Allow`; `reauthorize_is_sound` | Keep D-2 (reference semantics) for stage 3, document it, and add a lint: reject policies where a `forbid` condition can error (arithmetic, extension calls) [I] |
| T-11 | Residual size/count: JSON ≈ 3.7× text; dead residuals (`… && false && error()`) stay "non-trivial"; 128 conditions max | Low for the five KEP policies, Medium for large policy sets | Medium (falls to fail-closed) | Q3 table | Measure on the real policy set in stage 1; pre-filter residuals that cannot be satisfied (contain a literal `false` conjunct with an error-free remainder is already folded; the remainder here is not) [I]; use text form after T-4 is solved |
| T-12 | Lean vs Rust residual not structurally comparable without erasure and normalisation | High | Low–Medium | Q3 | Type-erased Lean printer + `&&` normalisation + Cedar JSON; keep the PST route as optional |
| T-13 | Using `cedar_policy_core::tpe` internals | High (already in use) | Medium | 14 `ResidualKind` references | Move to the public `cedar-policy` API (#2581) behind the Rust adapter |
| T-14 | `tpe` is experimental; breaking changes allowed without semver | High | Medium | `experimental_warning.md`, no changelog entry in either PR | Pin and vendor; treat any bump as a project event |
| T-15 | PR SHAs vanish from upstream after merge/rewrite | Medium | Medium | #1015 is a same-repo branch | Push the pinned SHAs to branches in your forks and depend on the fork URL |
| T-16 | Soundness statements assume `isValidAndConsistent` / `EntityLoader.WellBehaved` and (batched) `req.context.WellFormed`; the proofs say nothing about how you build the partial world from K8s objects | Certain | Medium | `reauthorize_is_sound` hypotheses; `batched_authorize_decision_eq_authorize` | Keep these hypotheses explicit in `status.md`; the object→record converter stays a named hypothesis (PLAN 3.3) |
| T-17 | Statements equate error and error via `toOption`; the erroring-policies theorem is only `⊆` | Low | Low | `partial_authorize_erroring_policies_is_sound` | Do not promise exact error diagnostics in `Lawful` (already planned: decision only) |

---

## 5. Exact commit SHAs to pin

| Repo | PR | Branch | SHA | Base |
|---|---|---|---|---|
| cedar-policy/cedar-spec | #1015 | `tpe-lean-model` | `7d6298b054e70b2152c379d0b89e045b80d5a37b` | `main` = `0e8c45ca4e920ebe78b6bc705263a0b56467bb66` |
| cedar-policy/cedar-spec | #1021 | `tpe-inf-lean-drt` | `3994ae239ee17b30534cb29526e3b654c421e49b` (**do not pin: stale, conflicting**) | merge-base with #1015: `3a193590016f1966d24ab8cb3f39b83f1bc9673d` |
| cedar-policy/cedar | #2547 | `tpe-final` | `782a4f28d15c11402e2e58c36e2086de1b853078` | parent `6eea3a4ad86aab30b59e67a3d2d16426f4ff212b` (upstream `main` is now `1c9d1c21da7a3af387497aa1d0126100920e8fe7`, 9 commits ahead) |
| cedar-policy/cedar | #2581 | `stack/tpe-api-json-cli` | `99a88d53fd587299d41e2d0c8b9da88632490711` | #2547 head |

Lean pin: `#1015` `7d6298b…`. Rust pin: `#2581` `99a88d53…` (includes #2547). Cedar-spec #1015's Lean is the counterpart of cedar #2547 (the Lean model and Rust internals are described as the same feature in both PR bodies). I did not verify DRT agreement (T-2).

Superseded in your tree: `luxas/cedar` rev `792e6d246440433f2d2a6a6adeadc910859919fc` (2025-08-20).

---

## 6. Recommended changes to PLAN.md

**Section 1.3 (table) and 1.4**
- Add the schema constraint: `Res.request` and `Res.stored` must be **optional** record-typed attributes; `absent` on a required attribute is rejected by both implementations.
- Replace "resource.name always unknown" with: the resource entity has a **synthetic known uid**; `name` is stated as `unknown` (or left unstated if optional). A `PartialEntityUid` with `id = None` loses all attribute-level knowledge (verified).
- State the nested-record rule: a record **without markers is closed** (omitted optional attributes are `absent`); only records containing a marker keep unstated attributes `unknown`.
- Replace the toolchain line: pin to #1015 `7d6298b` ⇒ Lean `v4.36.0`, batteries `v4.36.0`; #1021 is not usable (stale, `DIRTY`, `v4.33.1`).
- Mark R-1, R-2, R-3 as "answered by this report, re-verify in `docs/spike.md`".

**Section 3.2 (L2 CedarK8s)**
- `conditionsAwareAuthorize`: one condition per residual policy as planned, but drop residual policies for which `isError` or `isFalse` already (they are in the response sets), and add an `encode` precondition: round trip `decode (encode r) = r`; if the policy contains an `error` node, apply the chosen T-4 strategy (reject, or replace by an always-erroring typed expression). Decision needed before stage 3.
- `evaluateConditions`: spell out that it is **not** `TpeResponse::reauthorize` in Rust. It must (1) validate the concrete request and entities against the schema, (2) re-derive the partial world (`attrsToPartial`) and run the consistency check (Lean `isValidAndConsistent`, Rust `PartialEntities::check_consistency` equivalent), (3) run a plain `Authorizer` over the decoded residuals. The Lean statement can use `Response.reauthorize` directly because the residual list is a Lean value.
- Add a theorem or test row **C-8 `consistency_check_equiv`**: the Rust re-implementation rejects exactly when `isValidAndConsistent` does for the corpus (differential), and **C-9 `plain_authorizer_eq_reauthorize`** (the Rust plain `Authorizer` over `policy_set()` equals `TpeResponse::reauthorize`; 3/3 cases verified so far).
- Add to C-4 the exact Rust error cases that must fail closed: `RequestValidation | EntityValidation | EntitiesConsistency | RequestConsistency`.
- Keep D-3 JSON as the encoding, but note the JSON size (≈3.7× text) when checking the 10 240-byte limit; measure with the real policies.

**Stage 1 (spike)**
- Replace "Input: the explore agent's report" with the results above, and make the spike re-run the experiments in `exp/Exp1.lean`, `rexp/src/main.rs`, `rexp/src/bin/exp2.rs` against the pinned SHAs (copy them into `spike/`). Add three checks: (R-6) `error` node round trip, (R-7) plain `Authorizer` vs `reauthorize` equivalence, (R-8) closed-record vs partial-record behaviour for the object converter.
- Add a Lean `pp` (type-erased printer) and compare with Rust `to_json` for the five KEP policies (R-4).
- Write the K8s-flavoured schema with optional `request`/`stored` and guard every optional access with `has` (unguarded access fails the whole TPE call).
- Exit criterion additions: documented T-4 strategy; list of policy constructs that can error inside a `forbid` (D-2 lint).

**Stage 0 / 5**
- Stage 0: fork-mirror the four SHAs; add the Cargo and Lake dependency snippets from Q7; add the `#print axioms` audit to `scripts/check.sh` (the audit command in section 2 works as written).
- Stage 5: switch from `cedar_policy_core::tpe` internals to the public API (#2581) in the adapter; drop the entity-reference rewrite.

---

## 7. Housekeeping note

I used `~/code/cedar-spec` and `~/code/cedar-spec/cedar` only as object stores: I added a temporary `upstream` remote and `scratch-*` branches plus worktrees, and removed them afterwards (`git worktree list` is back to the user's original entries). `git fetch` also downloaded upstream tags (for example `v4.9.1`, `v4.14.0`, `v4.15.0` in cedar-spec, `v4.3.0` and others in cedar) into those repositories; they were not removed. Scratch trees that remain: `spec1015/` (with `.lake` build), `cedar2581/` (plain copies without `.git`), `target-cedar/` (7.6 GB of build artifacts), `rexp/`, `exp/`, `downstream/`, `cargodep/`.
