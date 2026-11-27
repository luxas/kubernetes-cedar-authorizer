# Blind review A: PLAN.md section 3.1 / 3.2 (`Lawful` / `Guarded`)

Reviewed: `/home/luxask/code/kubernetes-cedar-authorizer/PLAN.md`, branch `plan`, HEAD `48219f4` (revision 5).
Checked against: `kep.md` (Core interface changes, Properties, chain computation, enforcer),
`kubernetes/lean/*` (HEAD `2ee49d340c9`), `review/properties.md`, Go `union.go` / `webhook.go`, `origin/lean-test-2`.
Nothing in any repository was modified. Lean 4.36.0 (core only). Sketch: `/home/luxask/.kiro/crew/scratch/runtime-bce3c298/review-A-Sketch.lean`
(917 lines, compiles with **0 errors and no `sorry`**; axioms only `propext`/`Classical.choice`/`Quot.sound`).

## 1. Verdicts

| Q | Verdict as written | Verdict after the edits below |
|---|---|---|
| (a) satisfiable and non-vacuous | **No.** `Lawful` (L4 incl. the reflexive case) and `Guarded` (G1 unconditional clause) are jointly unsatisfiable for every authorizer that ever returns an unconditional non-Deny decision, so A-8(i) is false. L4's `Refines` is not definable from `World`, and read literally ("an oracle that agrees with `full`") is false for any truthful evaluator. | **Yes.** `Lawful*`/`Guarded*` below are satisfied by the always-NoOpinion authorizer (`A0_lawful`) and a conditional toy over `Data = Bool` with a `Consistent` that is neither empty nor total (`A2_lawful`, `W2_consistent_nontrivial`). Non-vacuity of the *real* `Consistent` is only as good as A-5 (see I4). |
| (b) true of the real systems | **Partly.** Union: true only with extra hypotheses (valid unique names; every member decision `good`; L4 restricted to conditional input; truth-agreement). Webhook: L2 is false in a corner case and L4 cannot hold under ACR/SAR failure. Cedar: lawful only up to `H`, and the fail-closed branches must additionally be Deny-preserving or the chain is fail-open. | Union: proved for a two-member chain (`chain_lawful`). Webhook: becomes a hypothesis on the remote, split into safety (holds under failures) and exactness (availability). Cedar: needs the `Dom`/Deny-faithful additions (C4). |
| (c) implies "two-phase = single-phase with all data" and A-4 in both directions | **Not as written** (C1-C4 break the chain). | **Yes** per admission invocation: `enforcement_exact : served A a d = decide (full a d = Allow)` is proved for any `Lawful*` authorizer, and `chain_lawful` gives `full_chain = firstNonNoOpinion` (`chainFull`). Forward direction needs only safety; reverse needs exactness + domain hypotheses. |

## 2. Findings

### Critical

**C1. `Lawful` and `Guarded` contradict each other; A-8(i) is false.**
Evidence (Lean, `plan_lawful_guarded_clash`, `A0_not_both`):
```lean
theorem plan_lawful_guarded_clash ... (hL : LawfulPlan full A) (hG : GuardedPlan A) (a d)
    (hc : W.Consistent a d) (hu : isUn (A.caa a) = true) : full a d = .deny
theorem A0_not_both : ¬ (LawfulPlan full0 A0 ∧ GuardedPlan A0)   -- always-NoOpinion authorizer
```
Why: L4 quantifies over every `x` with `Refines x (caa a)`, and `Refines` is reflexive, so `x = caa a` when `caa a` is unconditional (e.g. `NoOpinion`). L4 then demands `evaluateConditions (NoOpinion) d = full a d = NoOpinion`, while G1 demands `Deny`. The KEP agrees with G1 for unaware authorizers (rule 2, `kep.md:841-843`: always Deny + `ErrorConditionEvaluationNotSupported`), and the shipped union/webhook return `FailureDecision` for unconditional input (`union.lean` `EvaluateConditions` first branch; `webhook.lean` `EvaluateConditions`). That is `NoOpinion` for an input `Allow` (`union_eval_unconditional_is_FD`: `(chain2 ..).eval (.un .allow) () = .noOp`). So plan-L4 is false of the real union as well. A partial evaluation that collapses to an unconditional result is never passed to `EvaluateConditions` (`webhook.go` returns the unconditional parts directly; the enforcer admits/rejects without calling), so nothing real needs L4 on unconditional `x`.
Proposed edit (L4 row): replace the clause text with
> **L4 Refinement (conditional input only):** for every `x` with `IsConditional x` and `Refines (truth d) x (A.conditionsAwareAuthorize a)`: `(A.evaluateConditions x d).1 = full a d`. Unconditional input is not constrained by L4; `Guarded` (G1) covers it.

and G1: "if `x` is unconditional, the result is `FailureDecision x` (union, webhook; `Deny` + `ErrorConditionEvaluationNotSupported` for authorizers that do not support conditions)". Fix A-8(i) accordingly (it holds for `Lawful*`: `A0_lawful`, and `guard_guarded` gives `Guarded*`).

**C2. `Refines` cannot be defined from `World`, and its literal reading is false.**
The plan: "conditions replaced by their result under an oracle that agrees with `full`". `World` has no per-condition semantics, and the only available reading ("any oracle `o` with `⟦caa a⟧_o = full a d`") quantifies over fake oracles that agree only at the root. Counterexample (Lean `L4_literal_false`): two Allow conditions, truth `(1 ↦ Allow, 2 ↦ NoOpinion)`, fake oracle `(1 ↦ NoOpinion, 2 ↦ Allow)`. Both give root `Allow`. Refining condition 1 under the fake oracle and then evaluating with the true semantics yields `NoOpinion ≠ full = Allow`. So no truthful evaluator (Cedar included) satisfies plan-L4. The same ambiguity hides the P-27/P-28 side conditions.
Proposed edit: add to `World` a field `truth : Data → Condition → CondResult` (the instance's own meaning of each condition; for Cedar `⟦decode c⟧ req es`, which is already C-3's oracle), define `Refines (truth d)`, and replace **L3** by
> **L3\* Agreement:** `full a d = ⟦A.conditionsAwareAuthorize a⟧_{truth d}` (the reference fold D > N > A within a map, first-non-NoOpinion within a union). This implies the old L3 (P-37), L5 (unconditional decision equals `full`), and ties every unconditional partial-evaluation result to `full`. Without it the unconditional output of a refinement is unconstrained (the "P-28 gap").

L5 and L7 become derived and can be deleted from the table (minor M1). Also state `full` as a parameter of `Lawful` only, not a `World` field (M2).

**C3. A-1 `chain_lawful` is false without two hypotheses the plan does not state.**
(i) Valid, unique names. `union.New` rejects only empty and duplicate names (`union.go:58-66`) and does not check DNS-1123, while `ConditionsAwareDecisionUnion.Add` does (`conditionsunion.go:70`) and fails the whole union closed. Then `Authorize` (ignores names) returns `Allow` while `FoldDown(caa)` is `NoOpinion`. Lean: `chain_needs_valid_names` (member name `""`, `Authorize = Allow`, `FoldDown caa ≠ Allow`).
(ii) Members' decisions are `good`: `WF` and `FailureDecision ∈ PossibleDecisions` for conditional ones. Lean `G1_needs_good`: `ucons "p" (un allow) unil` is `wf` but has `PD = {Allow}` and `FD = NoOpinion`. Lean `chain_needs_good_members`: with such a member `A` (`authorize = NoOpinion`, which satisfies L2 for `A` itself) and `B = Deny`, `Authorize = Deny` but the union decision folds to `Allow` (the union stops at `A` because it contains an unconditional Allow). This is `P_44_needs_child_WF`. The plan's L1 says only `WF`; it must include the `FD ∈ PD` conjunct (my `good`).
Proved with these hypotheses, in Lean, for a two-member chain (sketch lines 443-805):
```lean
theorem chain_lawful {W} (A B : Authorizer W) (fA fB) (hLA : Lawful fA A) (hLB : Lawful fB B)
    (hn : namesOk A B = true) : Lawful (chainFull fA fB) (chain2 A B)
-- chainFull fA fB a d = if fA a d = .noOp then fB a d else fA a d
```
including evaluation routed **by name**, per-child clamp (`leaf`, shown inert via `leaf_eq`), and the eager short-circuit (`cua xa` drops `B`; `cua_sem` shows `full A ≠ NoOpinion` there, so `chainFull` is unaffected).
Proposed edit (A-1 row): replace "built from named, unique members" with
> `chain_lawful`: if every member is `Lawful` (hence `good`) and member names are non-empty, pairwise distinct and DNS-1123 (`NamesOk`; `union.New` does not enforce DNS-1123, so `NamesOk` is a hypothesis, or a Go-side fix), then the union authorizer is `Lawful` with `full_chain = firstNonNoOpinion (members.map full)`. Names are routed by name; `Add` is a no-op after the first member containing an unconditional Allow/Deny.

**C4. A-4 soundness and "Lawful up to H" do not compose: fail-closed must preserve Deny.**
C-1 says outside `H = Fits ∧ NoErrorNodes ∧ BuilderOk` the Cedar authorizer "never returns Allow" (deliberately violating L3/L5). That is not enough for chain soundness. If a member fails closed to `NoOpinion` where `full = Deny` (for example the size-limit fallback or the `error`-node fail-closed built from a list that omitted the offending forbid, so `hasDenyEffect = false`), a later member can `Allow`. Lean (`fail_closed_to_noOp_is_fail_open`): `rA = NoOpinion, fA = Deny, rB = Allow` gives chain result `Allow`, reference `Deny`, with both members satisfying "Allow implies full = Allow". Positive result (`chain_sound_of_deny_faithful`): chain soundness holds if each member also satisfies `full = Deny → returned = Deny`. The same applies at deployment level: a webhook with `failurePolicy: NoOpinion` (`webhook.go` `decisionOnError`) is fail-open in the same sense, so A-4's forward direction needs `decisionOnError = Deny` for the Cedar webhook, or a stated hypothesis.
Also `Lawful` is not parameterised by a domain, so "Lawful up to H" is not a statement the chain theorem can consume. `H` depends on `(a, d)` (builder failure depends on `d`; limits on `a`), and the chain domain is `Dom_chain a d := Dom_A a d ∧ (full_A a d = NoOpinion → Dom_B a d)` (B is irrelevant when A decides; I did not prove this refinement).
Proposed edits: (1) change the definition to `Lawful Dom full A` where L3\*/L4\* range over `Dom a d ∧ Consistent a d` and L1/L2 over all `a`; (2) add clause **G3 Deny-faithful** to `Guarded`: `full a d = Deny → (A.evaluateConditions x d).1 = Deny` for conditional refinements `x` with `Deny ∈ PD x`, and for the authorizer outside `Dom`: "if `Deny` is possible for any policy the authorizer could not evaluate, return `Deny`"; (3) C-1 states "unconditionally `Guarded` and Deny-faithful" (the fail-closed constructor must be called with every forbid that could not be encoded counted as a Deny effect); (4) A-4 forward direction hypotheses: members Deny-faithful and `Allow`-sound outside `Dom`.

### Important

**I1. L2 and L4 are not theorems of the shipped webhook.**
`Authorize` and `ConditionsAwareAuthorize` make two separate remote calls (`sendSARWebhook(..., false)` at `webhook.go:257`, `(..., handlesConditional)` in the other), and only the second path runs `CombinedValidateSubjectAccessReviewCreate`. Concrete L2 violation inside the model (`webhook.lean` `authorizeStatus` vs `conditionsAwareStatus`): no reviewer configured, `decisionOnError = NoOpinion`, remote returns a status carrying a conditional decision with a Deny condition. `Authorize` gives its `FailureDecision = Deny` plus `errUnrequestedConditional`; the conditions-aware path fails validation and gives `conditionsAwareFailureDecision = NoOpinion`. Both are fail-closed, not equal. Error nil-ness also differs (`Authorize` drops `EvaluationError`, the conditions-aware path returns it). L4 fails whenever the ACR call fails: `webhookEvaluateConditions` returns `FailureDecision` of the refined decision, not `full`.
Edit: split `Lawful` into `Sound` (holds under failures: L1, L2 weakened to the one-sided "`authorize ≤ FoldDown` in the order Deny < NoOpinion < Allow, and Deny is preserved", L3, "`eval = Allow → full = Allow`", G1-G3) and `Exact` (adds L2 equality and L4 equality; hypothesis `Available`). State the webhook's `Exact` as a hypothesis on the remote, like Axiom O2/O3 (`P-76`). `lean-test-2`'s `AuthorizerContract` was already one-sided here (`authorize = Allow → ideal Allow`, `ideal Deny → authorize Deny`); that is the portion A-4's forward direction needs.

**I2. G1 "for all x" is false for every clamp, and the three Go clamps are different functions.**
Lean `G1_needs_good` (above) shows no function returns `∈ PD x` for the non-`good` `x` shown. The shipped clamps differ: union `evaluateAndClamp` and webhook return `FailureDecision` (`union.lean`, `webhook.lean`), the enforcer's `evaluateWithReturnGuard` returns `Deny` with a fixed error (`conditionsenforcer.lean`). Inside a union FD vs Deny changes whether the chain continues, so one `guard` function changes behaviour of two of the three call sites.
Edit: G1 reads "for all `x` with `good x`"; `guard` is proved for the union form (`FD`); the enforcer guard is `guardTop := fun x d => if (guard A).eval x d = Allow ∨ ... else Deny` or the plan states that unifying them (`authorizer.GuardEvaluation`, Go change 5) is a behaviour change at the enforcer only (Allow-vs-non-Allow is the same; reason/status differ). Proved in Lean: `guard_guarded : Guarded (guard A)` for every `A` (needs `good x` for G1c), and
```lean
theorem guard_inert (A) (hL : Lawful full A) (hc) (x) (hx : isUn x = false)
    (hr : Refines (W.truth d) x (A.caa a)) : (guard A).eval x d = A.eval x d
theorem guard_lawful ... : Lawful full (guard A)
```
`guard_inert` **needs L3\*** (`full ∈ PD x` for the refined `x`, not just for `caa a`; `PD x ⊆ PD (caa a)` only). With the plan's L3 it is not derivable.

**I3. A-4 is stated about "served"; the provable object is the enforcer outcome per admission invocation.**
Lean (`served`, `enforcement_exact`): filter passes iff `Allow ∈ PD`; unconditional Allow admitted; conditional evaluated through the guard:
```lean
theorem enforcement_exact {W} {full} (A : Authorizer W) (hL : Lawful full A)
    (a d) (hc : W.Consistent a d) : served A a d = decide (full a d = .allow)
```
Both directions, for one `(a, d)`. Not covered, and each is a real way "served iff" fails: later plugins (`ValidatingAdmissionWebhook`, quota; enforcer order is D-6); the update-to-create secondary `create` check (`kep.md:741-747`, unconditional `Authorize`); `P_72` reload (the evaluating authorizer may differ from the issuing one; add the mirror's `OutcomeReloaded` hypothesis explicitly, the plan names only `P_68`); mutating admission makes `d` the post-mutation object, so `full a d` must be defined on that object (say so); storage retries re-run validation with a possibly different `d`, so the claim is about the `d` of the last invocation that was committed, which needs a hypothesis "committed object = validated object" (L6 does not give this). A-4 also says "evaluation idempotent (L6)": in Lean every function is pure, so L6 is vacuous (see I6).
Edit (A-4): "For a classified write and one admission invocation with data `d`, `Consistent a d`, a `Lawful` chain, `Dom a d`, evaluating authorizer = issuing authorizer (`P_72`), enforcer present (`P_68`): the enforcer admits iff `full a d = Allow`. The forward direction (admit implies `full a d = Allow`) needs only `Sound`+Deny-faithful members. Request-level statements add: the committed object is the validated one; `deletecollection` is per object; update-to-create adds the secondary check; later plugins can still reject."

**I4. `Consistent` carries all the weight and A-5 is unprovable.**
`lawful_of_empty_consistent` (Lean): with `Consistent := False`, L3\*/L4\* hold for any authorizer meeting L1/L2, so the contract's non-vacuity is exactly the non-emptiness of the real `Consistent`. A-5 is declared a hypothesis. For Cedar the definition `RequestAndEntitiesRefine (dataToConcrete d) (attrsToPartial a)` (modulo action, `residual_independent_of_action`) can be empty on real pipeline pairs: update-to-create (verb `update`, operation CREATE), `deletecollection` (per object, DELETE), generateName creates (admission `name` empty; the plan already reads it from `object.metadata.name`), and entity-builder rejection (the plan puts it in `H`). If `Consistent` is empty or too strict on those pairs, A-4 is silently vacuous there.
Edit: add a "consistency witnesses" list to 3.1 stating which `(verb, operation)` pairs the Lean test corpus must show consistent (create/CREATE, update/UPDATE, patch/UPDATE, update/CREATE, delete/DELETE, deletecollection/DELETE with n objects), and change A-5 to a Go-side conformance property that the corpus checks (decode `AdmissionRequest`, recompute `Attrs`, check `Consistent`). `Attrs knows less than Data` is satisfiable (`W2` in the Lean sketch: `Attrs = Option Bool`, `Consistent a d := a = none ∨ a = some d`); the point is that it must be shown for the real relation, not the toy.

**I5. A-3 as stated is transitivity of a reflexive-transitive closure.**
Lean `refinement_closed : Refines o x y → Refines o y z → Refines o x z` is `Steps.trans` (3 lines). The content the plan attributes to it ("in-process partial evaluation followed by the webhook's evaluation equals direct evaluation") is two other facts: (1) Go's `PartiallyEvaluateConditionsAwareDecision` **is** a `Refines` step under error-free `p ⊑ o` and `WF` names (mirror P-25/P-27 and the counterexamples `P_27_counterexample`, `P_25_needs_WF`); (2) refinement preserves the reference semantics. (2) is `refines_sem` in my toy (`sem o x = sem o y` and `wf` preserved, P-27/P-28), (1) is the mirror's theorem and is not an abstract fact.
Edit (A-3 row): "`refines_sem`: `Refines o x y` and `wf y` imply `wf x` and `⟦x⟧_o = ⟦y⟧_o`. `peval_is_refinement`: for `WF d`, `p ⊑ o` total `o`, and `∀ c, p c ∉ Error`, `Refines o (peval d p) d` (mirror P-27, P-28; the error premise and WF names are the hypotheses; the counterexamples remain as negative theorems)."

**I6. L6 "purity by type" is vacuous in Lean and the atomicity argument is about the store snapshot.**
All Lean functions are pure, so L6 holds of every instance and says nothing about Go/Rust. What actually carries Cedar's atomicity is that conditions embed the residual policies, so phase 2 cannot see a newer store; `full` is then relative to the snapshot `S` used in phase 1 (`full_S`). State `Lawful (full_S) (A_S)` and make "`A_S` captures the snapshot at construction/request time" a Rust review obligation.
Edit: replace L6 by "Obligation on implementations (not provable in Lean): `evaluateConditions` reads no state other than `(x, d)`; Lean instances are stated per store snapshot `S`".

### Minor

* **M1.** L5 and L7 are consequences of L3\* and of equality in L4. Remove them as separate clauses (L5: unconditional `caa` means `PD` is a singleton, so `full` is that decision by L3).
* **M2.** `World` contains `full`, yet the text says each authorizer family supplies it and `Lawful A full` takes it as an argument, and a chain needs `full_chain ≠ full_member`. Make `full` a parameter of `Lawful`, as in the sketch (`Lawful (full) (A)`).
* **M3.** L2 compares `.1` only. A-7 (status agreement) depends on error nil-ness (`500` vs `403`); add `(A.authorize a).err.isSome = (caa a).Error.isSome` if A-7 is to be proved at the authorizer level, or state A-7 on the mirror's model.
* **M4.** Error semantics differ between Cedar and the K8s map fold: a Deny-phase evaluation error is `Deny + error` in `partiallyEvaluateConditionsMapInternal` (`P-K1`) but "skipped" in Cedar. C-3 resolves this by choosing the oracle `error ↦ false`. That is correct only if Cedar conditions are never evaluated by the generic K8s evaluator (they have `ev₀ = unevaluatable`, no builtin); add this as a stated invariant.
* **M5.** `kep.md` property 2 says partial evaluation never adds outcomes "for unions whose names are well-formed"; the plan's A-1 omits it (see C3).
* **M6.** The plan says A-1's walk is "lifted from `lean-test-2`'s `evaluate_eq_ideal`". Not checked beyond `Spec.lean`, whose `AuthorizerContract` is one-sided on `authorize` (see I1) and Deny-on-unconditional (see C1), so the lifted proof will need those clauses adapted.

## 3. Hunt list: answers

* **Agreeing partial evaluation, errors, P-27/P-28.** Error-free premise is not representable in the toy (oracle results are `Option Dec`), which is exactly the plan's "no errors in the partial evaluator" hypothesis; the Lean mirror already proves the counterexamples (`P_27_counterexample`, `P_27_error_component_counterexample`, STATUS.md). Names: `P_25_needs_WF`. In the toy, `Step.tail` carries `isList r'` for the same reason (a tail collapsing to an unconditional leaf would break the union shape).
* **L2 for union legacy path and NoOpinion-with-error.** Holds for the union given `good` members and valid names (`chain_L2`). A NoOpinion carrying an error is skipped identically in `Authorize`, `caa`, and the evaluation walk; the error text is not part of `Decision`-level L2 (M3).
* **L3 vs L4 vs L5.** L5 does follow from L3 (M1). An authorizer whose `caa` is unconditional but whose `authorize` differs violates L2, not L5. The real interplay failure is C1 (L4 at unconditional input) and C2 (L4 oracle).
* **`full_chain = firstNonNoOpinion` vs the builder.** Consistent with eager short-circuit (`cua_sem`), name routing, the clamp (`leaf_eq`), and NoOpinion-with-error, under C3's two hypotheses; `chain_L3` also uses `sem_build` (collapse by singleton `PD`, P-37).
* **`guard` inertness (A-2) when `evaluate` returns the failure decision.** Inert only on `good` conditional `x` whose `full ∈ PD x`, which needs L3\* (I2). On `x` with `FD ∉ PD` the "failure decision" is itself outside `PD`.
* **A-4 vs deletecollection, retries, mutation, aggregated, unsafe delete.** I3, and `P_68_enforcer_runs` for the last two.
* **`Consistent` satisfiable and meaningful.** I4.
* **L6.** I6.

## 4. Lean sketch and proof status

Core (abridged; full file at the path above). `Dec`, `DS` (a PD as three Booleans), `CAD` with union as a cons list so recursion is structural:
```lean
inductive CAD
  | un (d : Dec) | cond (hd ha : Bool) (id : Nat) | unil | ucons (n : String) (c r : CAD)
def pd (x) : DS ; def cua (x) : Bool ; def FD (x) : Dec := if (pd x).d then .deny else .noOp
def foldDown : CAD → Dec | .un d => d | x => FD x
def sem (t : Nat → Dec) : CAD → Dec   -- reference semantics under a total oracle
inductive Step (o) : CAD → CAD → Prop     -- agreeing partial evaluation: resolve | head | tail | norm
inductive Steps (o) ...                   -- reflexive-transitive closure
def Refines (o) (x y : CAD) : Prop := Steps o y x

structure World where
  Attrs : Type; Data : Type; Consistent : Attrs → Data → Prop
  truth : Data → Nat → Dec                -- NOT in the plan: needed to define Refines
structure Authorizer (W : World) where
  name : String; authorize : W.Attrs → Dec; caa : W.Attrs → CAD; eval : CAD → W.Data → Dec
```
Plan's `Lawful`/`Guarded` verbatim (`LawfulPlan`, `GuardedPlan`) and the proposed replacements:
```lean
def good (x : CAD) : Bool := wf x && (isUn x || (pd x).has (FD x))
structure Lawful (full) (A : Authorizer W) : Prop where
  L1 : ∀ a, good (A.caa a) = true
  L2 : ∀ a, A.authorize a = foldDown (A.caa a)
  L3 : ∀ a d, W.Consistent a d → full a d = sem (W.truth d) (A.caa a)          -- L3*
  L4 : ∀ a d, W.Consistent a d → ∀ x, isUn x = false →
         Refines (W.truth d) x (A.caa a) → A.eval x d = full a d                -- conditional only
structure Guarded (A) : Prop where
  G1c : ∀ x d, isUn x = false → good x = true → (pd x).has (A.eval x d) = true
  G1u : ∀ x d, isUn x = true → A.eval x d = FD x
  G2  : ∀ x d, A.eval x d = .allow → (pd x).has .allow = true
def guard (A) : Authorizer W := { A with eval := fun x d =>
  if isUn x then FD x else let r := A.eval x d; if (pd x).has r then r else FD x }
```

| Statement (plan ID) | Status | Lean name | Extra hypothesis needed beyond the plan |
|---|---|---|---|
| Lawful ∧ Guarded satisfiable (A-8 i) | **false as written**; true with fixes | `plan_lawful_guarded_clash`, `A0_not_both`; fixed: `A0_lawful`, `guard_guarded` | L4 restricted to conditional `x` |
| L4 literal oracle reading | **false** | `L4_literal_false` | `truth` in `World`; L3\* |
| A-8 (ii) toy, `Consistent` neither empty nor total | proved (corrected contract) | `A2_lawful`, `A2_guarded`, `W2_consistent_nontrivial` | none |
| Vacuity when `Consistent` empty | proved | `lawful_of_empty_consistent` | n/a |
| A-2 `guard_closed` (G2) | proved, all `A`, all `x` | `guard_guarded` | none |
| A-2 `guard_closed` (G1) | proved only for `good x`; false otherwise | `guard_guarded`, `G1_needs_good` | `good x` (FD ∈ PD) |
| A-2 `guard_inert` | proved | `guard_inert`, `guard_lawful` | L3\* (`full = ⟦caa⟧`), conditional `x`, `Refines` against `truth` |
| A-3 `refinement_closed` | proved (transitivity) | `refinement_closed` | none; trivial |
| A-3 content (P-27/P-28 semantic preservation) | proved in the toy | `step_sem`, `refines_sem` | `wf`; errors excluded by construction |
| A-1 L1, L2, L3\*, L4\*, two-member chain | proved | `chain_L1..L4`, `chain_lawful` | members `Lawful` (incl. `good`), `namesOk` |
| A-1 without valid names | **false** | `chain_needs_valid_names` | `NamesOk` |
| A-1 without `good` members | **false** | `chain_needs_good_members` | `FD ∈ PD` for conditional members |
| A-1 L4 at unconditional `x` for the union | **false** | `union_eval_unconditional_is_FD` | L4 conditional only |
| A-4 both directions, per invocation | proved | `enforcement_exact` | `Lawful*`, `Consistent`, evaluator = issuer (implicit: same `A`), single `d` |
| A-4 forward, chain with fail-closed member | **false** if member fails closed to NoOpinion where `full = Deny` | `fail_closed_to_noOp_is_fail_open` | Deny-faithful members |
| chain soundness with Deny-faithful members | proved (2 members) | `chain_sound_of_deny_faithful` | `Allow`-sound and Deny-faithful |
| Webhook L2 equality, L4 under failure | not provable (remote); model counterexample in `webhook.lean` | argued, not mechanised here | `Exact`/`Available` hypothesis on remote |
| A-5, L6 | cannot be proved in Lean | n/a | named hypotheses |
| Domain-indexed `Lawful Dom` for "up to `H`" and chain `Dom` | **not attempted** | n/a | see C4 |

Not mechanised: `n`-member chains (two members cover the interesting cases: eager stop, collapse, routing, clamp), the `Dom`-indexed chain, nested chains of chains (the `CAD` type allows nesting and `good` children, but `chain_lawful` was proved for arbitrary member `Authorizer`s so nesting follows by instantiation), error carrying decisions, reasons.

## 5. Suggested replacement text (summary of exact edits)

1. `World`: delete `full`; add `truth : Data → Condition → CondResult`.
2. `Lawful full A` (replace L1 to L7): L1 `good (caa a)`; L2 equality (as is, decision part) for `Exact`, one-sided for `Sound`; **L3\*** `full a d = ⟦caa a⟧_{truth d}`; **L4\*** conditional refinements only. Delete L5, L7; L6 becomes an implementation obligation.
3. `Guarded`: G1 (`good x`; unconditional input returns `FailureDecision x`, or `Deny` + `ErrorConditionEvaluationNotSupported` for authorizers without condition support), G2, **G3 Deny-faithful**.
4. A-1: add `NamesOk` (non-empty, distinct, DNS-1123) and "members `good`".
5. A-3: replace by `refines_sem` and `peval_is_refinement` (error-free, `WF` names).
6. A-4: restate per invocation; add hypotheses `P_72` (same evaluator), `Dom`, committed = validated object; forward needs `Sound` + Deny-faithful, reverse needs `Exact`.
7. A-8: (i) holds for `Lawful*`/`Guarded*` only.
8. C-1: "`Lawful` on `Dom = Fits ∧ NoErrorNodes ∧ BuilderOk`, and `Sound`, `Guarded` and Deny-faithful everywhere (every fail-closed branch passes all unencodable forbids as Deny effects)".
9. C-3: add the invariant that Cedar conditions are never evaluated by the generic K8s evaluator (M4).
