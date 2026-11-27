import K8sAuthz.Spec.Enforcement

/-!
# `K8sAuthz.Spec.Hypotheses`: A-5, A-7 and L6 as named hypotheses

These are NOT Lean theorems (PLAN 3.1). They are stated as named `Prop`s so that every
theorem which needs one takes it as an explicit argument, and so that `docs/properties.md` can
point at a definition instead of prose. Nothing here is an axiom.
-/

namespace K8sAuthz

variable {M : Type}

/-- **A-5 `consistency_established`** (Go-side conformance property, checked by the stage-3
corpus): decoding the admission request and recomputing the attributes gives a consistent pair,
for every `(verb, operation)` pair the corpus covers. `Req` is the type of classified write
requests, `attrsOf`/`dataOf` the two decoders. A `Consistent` that is empty on real pairs would
make A-4 vacuous (`lawful_of_empty_consistent`), so this must be shown non-empty on them. -/
def ConsistencyEstablished (W : World M) (Req : Type) (attrsOf : Req → W.Attrs)
    (dataOf : Req → W.Data) : Prop :=
  ∀ r, W.Consistent (attrsOf r) (dataOf r)

/-- **A-7 `status_agreement`** (mirror-level): filter and enforcer map `(decision, hasError)`
to an HTTP status with one function. `statusF`, `statusE` are the two mappings. -/
def StatusAgreement (statusF statusE : Dec → Bool → Nat) : Prop :=
  ∀ d e, statusF d e = statusE d e

/-- **L6 purity** (implementation obligation, reviewed in Rust): `evaluateConditions` reads
nothing but `(x, d)`. Every Lean function is pure, so this cannot be stated about a Lean
`Authorizer`; the statement that has content is stability under a store snapshot `S`:
the authorizer family `A_S` indexed by snapshots has the same `eval` for all snapshots that
agree on the residual policies embedded in `x`. `Snapshot` is the store type. -/
def EvalSnapshotIndependent {W : World M} (Snapshot : Type) (A : Snapshot → Authorizer W) : Prop :=
  ∀ s t x d, (A s).eval x d = (A t).eval x d

/-- **Evaluator equals issuer** (mirror `P_72`, reload hypothesis): the authorizer that
evaluates a decision is the one that issued it. In the spec this is built into the statements
of A-4 (the same `A` appears in `served`). Stated for completeness. -/
def EvaluatorIsIssuer {W : World M} (issue evalr : Authorizer W) : Prop :=
  issue.caa = evalr.caa ∧ issue.eval = evalr.eval

/-- **Committed object is the validated object** (A-4, request level): the data `d` used in
the last admission invocation describes the object that is stored. A request-level statement,
not an authorizer-level one. -/
def CommittedIsValidated (Obj : Type) (validated committed : Obj) : Prop := validated = committed

/-- **Failure policy is Deny** (A-9 at deployment level): a webhook member whose failure policy
is `NoOpinion` is fail-open (`fail_closed_to_noOp_is_fail_open`); the Cedar webhook must be
configured with `failurePolicy: Deny`, i.e. its fail-closed result is Deny-faithful (S4). -/
def FailClosedIsDeny {W : World M} {full : W.Attrs → W.Data → Dec} (A : Authorizer W) : Prop :=
  ∀ a d, W.Consistent a d → full a d = .deny → sem (W.truth d) (A.caa a) = .deny

/-- `Sound.S4` is exactly `FailClosedIsDeny`. -/
theorem failClosedIsDeny_of_sound {W : World M} {full : W.Attrs → W.Data → Dec}
    {A : Authorizer W} (h : Sound full A) : FailClosedIsDeny (full := full) A :=
  fun a d hc hf => h.S4 a d hc hf

end K8sAuthz
