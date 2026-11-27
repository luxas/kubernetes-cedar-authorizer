import K8sAuthz.Spec.Chain

/-!
# `K8sAuthz.Spec.ChainN`: n-member chains by induction (A-1)

`chainN` composes members as nested two-member unions, innermost last (a union authorizer can
itself be a member of another union, as in Go). The flat n-member union is not mechanised:
names are then compared pairwise across all members, here only against the inner chain's
fixed name; see docs/properties.md.
-/

namespace K8sAuthz

variable {M : Type}

/-- A member together with its domain, reference semantics and lawfulness proof. -/
structure Member (W : World M) where
  A : Authorizer W
  Dom : W.Attrs → W.Data → Prop
  full : W.Attrs → W.Data → Dec
  lawful : Lawful Dom full A

/-- The empty chain: always `NoOpinion`. -/
def nilAuth (W : World M) : Authorizer W where
  name := "chain"
  authorize _ := .noOp
  caa _ := .un .noOp
  eval x _ := FD x

theorem nilAuth_lawful (W : World M) :
    Lawful (fun _ _ => True) (fun _ _ => Dec.noOp) (nilAuth W) where
  sound := by
    refine ⟨fun _ => rfl, fun _ => ⟨Nat.le_refl _, fun h => by simp [nilAuth, foldDown] at h⟩, ?_, ?_, ?_, ?_⟩
    · intro a d _ h; simp [nilAuth, sem] at h
    · intro a d _ x hx hr; exact absurd (steps_un hr ▸ hx) (by simp [isUn])
    · intro a d _ h; exact absurd h (by decide)
    · intro a d _ x hx hr; exact absurd (steps_un hr ▸ hx) (by simp [isUn])
  L2 _ _ _ _ := rfl
  L3 _ _ _ _ := rfl
  L4 a d _ _ x hx hr := by
    have := steps_un hr
    subst this; simp [isUn] at hx

/-- Nested chain of members. -/
def chainN {W : World M} : List (Member W) → Authorizer W
  | [] => nilAuth W
  | m :: rest => chain2 m.A (chainN rest)

def domN {W : World M} : List (Member W) → W.Attrs → W.Data → Prop
  | [] => fun _ _ => True
  | m :: rest => fun a d => m.Dom a d ∧ domN rest a d

def fullN {W : World M} : List (Member W) → W.Attrs → W.Data → Dec
  | [] => fun _ _ => .noOp
  | m :: rest => chainFull m.full (fullN rest)

/-- Names of the members: non-empty and different from the fixed name of the inner chain. -/
def NamesOkN {W : World M} (ms : List (Member W)) : Prop :=
  ∀ m ∈ ms, m.A.name ≠ "" ∧ m.A.name ≠ "chain"

theorem chainN_name {W : World M} (ms : List (Member W)) : (chainN ms).name = "chain" := by
  cases ms <;> rfl

theorem namesOk_chainN {W : World M} (m : Member W) (rest : List (Member W))
    (h : m.A.name ≠ "" ∧ m.A.name ≠ "chain") : namesOk m.A (chainN rest) = true := by
  simp [namesOk, chainN_name, h.1, h.2]

/-- **A-1 (n members, by induction)**: a chain of `Lawful` members with valid names is
`Lawful`, with `full = firstNonNoOpinion (members.map full)` on the conjunction of the domains. -/
theorem chainN_lawful {W : World M} (ms : List (Member W)) (h : NamesOkN ms) :
    Lawful (domN ms) (fullN ms) (chainN ms) := by
  induction ms with
  | nil => exact nilAuth_lawful W
  | cons m rest ih =>
    have hn := namesOk_chainN m rest (h m (by simp))
    exact chain_lawful m.A (chainN rest) m.lawful (ih (fun x hx => h x (by simp [hx]))) hn

end K8sAuthz
