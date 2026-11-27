import K8sAuthz.Spec.Authorizer

/-!
# `K8sAuthz.Spec.Chain`: the union authorizer (A-1)

Ported from the review-A sketch and adapted to `Sound` / `Lawful Dom`.
-/

namespace K8sAuthz

variable {M : Type}

/-! ## A-1: the two-member union authorizer -/

def build (ok : Bool) (u : CAD M) : CAD M :=
  if !ok then .un (FD u) else
  match (pd u).theOnly with
  | some d => .un d
  | none => u

def namesOk {W : World M} (A B : Authorizer W) : Bool :=
  A.name != "" && B.name != "" && A.name != B.name

/-- evaluation walk (`union.go:144-185`): leaves are returned as is; conditional children are routed
by name and clamped into their own PossibleDecisions. -/
def leaf (route : String → CAD M → Dec) (n : String) : CAD M → Dec
  | .un d => d
  | c => let q := route n c; if (pd c).has q then q else FD c

def evalL (route : String → CAD M → Dec) : CAD M → Dec
  | .ucons n c r =>
    let v := leaf route n c
    if v = .noOp then evalL route r else v
  | _ => .noOp

def route {W : World M} (A B : Authorizer W) (d : W.Data) (n : String) (c : CAD M) : Dec :=
  if n == A.name then A.eval c d else if n == B.name then B.eval c d else FD c

def chain2 {W : World M} (A B : Authorizer W) : Authorizer W where
  name := "chain"
  authorize a := if A.authorize a = .noOp then B.authorize a else A.authorize a
  caa a :=
    let xa := A.caa a
    if cua xa then build (namesOk A B) (CAD.ucons A.name xa .unil)
    else build (namesOk A B) (CAD.ucons A.name xa (CAD.ucons B.name (B.caa a) .unil))
  eval x d := match x with
    | .ucons _ _ _ => evalL (route A B d) x
    | _ => FD x                      -- non-union input: fail closed (`union.go:134-136`)

def chainFull {W : World M} (fA fB : W.Attrs → W.Data → Dec) : W.Attrs → W.Data → Dec :=
  fun a d => if fA a d = .noOp then fB a d else fA a d

/-! ### facts about good decisions -/

theorem fold_allow {x : CAD M} (h : foldDown x = .allow) : x = .un .allow := by
  cases x with
  | un d => simpa [foldDown] using h
  | cond hd ha id => exact absurd h (FD_ne_allow _)
  | unil => exact absurd h (FD_ne_allow _)
  | ucons n c r => exact absurd h (FD_ne_allow _)

theorem fold_deny {x : CAD M} (h : foldDown x = .deny) : (pd x).d = true := by
  cases x with
  | un d => cases d <;> simp_all [foldDown, pd, info, DS.one]
  | cond hd ha id => simp only [foldDown, FD] at h; split at h <;> simp_all
  | unil => simp only [foldDown, FD] at h; split at h <;> simp_all
  | ucons n c r => simp only [foldDown, FD] at h; split at h <;> simp_all

theorem n_not_cua {x : CAD M} (h : (pd x).n = true) (hu : isUn x = false) : cua x = false := by
  cases x with
  | un d => simp [isUn] at hu
  | cond hd ha id => rfl
  | unil => rfl
  | ucons n c r => simp [pd, info, cua] at h ⊢; exact h

theorem fold_noOp {x : CAD M} (hg : good x = true) (h : foldDown x = .noOp) :
    (pd x).d = false ∧ cua x = false := by
  cases hu : isUn x with
  | true =>
    cases x with
    | un d => cases d <;> simp_all [foldDown, pd, info, cua, DS.one]
    | cond _ _ _ => simp [isUn] at hu
    | unil => simp [isUn] at hu
    | ucons _ _ _ => simp [isUn] at hu
  | false =>
    have h1 : foldDown x = FD x := by cases x <;> simp_all [isUn, foldDown]
    rw [h1] at h
    have hd : (pd x).d = false := by
      unfold FD at h; split at h <;> simp_all
    have hh := good_FD hg hu
    rw [h] at hh
    exact ⟨hd, n_not_cua hh hu⟩

theorem un_facts {d : Dec} : pd (CAD.un (M := M) d) = DS.one d ∧ cua (CAD.un (M := M) d) = (d != .noOp) := ⟨rfl, rfl⟩


theorem build_fold (u : CAD M) (hu : isUn u = false) :
    foldDown (build true u) =
      (if (pd u).d = true then .deny else if (pd u).a = true ∧ (pd u).n = false then .allow else .noOp) := by
  have hfd : foldDown u = if (pd u).d = true then Dec.deny else Dec.noOp := by
    cases u <;> simp_all [isUn, foldDown, FD]
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  revert hfd
  generalize pd u = s
  rcases s with ⟨a, d, n⟩
  cases a <;> cases d <;> cases n <;> simp [DS.theOnly, foldDown]

theorem ucons_isUn (n : String) (c r : CAD M) : isUn (CAD.ucons n c r) = false := rfl

/-- The fold-down of a two-member chain is the first non-`NoOpinion` fold-down of the members.
Needs: members `good`, names ok. -/
theorem chain_foldDown {W : World M} (A B : Authorizer W) (hn : namesOk A B = true) (a : W.Attrs)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true) :
    firstNo (foldDown (A.caa a)) (foldDown (B.caa a)) = foldDown ((chain2 A B).caa a) := by
  simp only [chain2, hn, firstNo]
  generalize A.caa a = xa at *
  generalize B.caa a = xb at *
  have fa := fold_allow (x := xa)
  have da := fold_deny (x := xa)
  have na := fold_noOp hA (x := xa)
  have fb := fold_allow (x := xb)
  have db := fold_deny (x := xb)
  have nb := fold_noOp hB (x := xb)
  simp only [pd, cua] at da na db nb
  by_cases cA : cua xa = true
  · simp only [cA, ite_true]
    rw [build_fold _ (ucons_isUn _ _ _)]
    cases hxa : foldDown xa with
    | allow =>
      have := fa hxa; subst this; simp [pd, info, DS.union, DS.one, DS.empty]
    | deny =>
      have := da hxa
      simp [hxa, pd, info, DS.union, DS.empty, this]
    | noOp => have := (na hxa).2; exact absurd cA (by simp [cua, this])
  · have cA' : (info xa).cua = false := by simpa [cua] using cA
    simp only [cA, Bool.false_eq_true, ite_false]
    rw [build_fold _ (ucons_isUn _ _ _)]
    cases hxa : foldDown xa with
    | allow => have := fa hxa; subst this; simp [cua, info] at cA'
    | deny =>
      have := da hxa
      simp [hxa, pd, info, DS.union, DS.empty, this]
    | noOp =>
      have h1 := na hxa
      cases hxb : foldDown xb with
      | allow =>
        have := fb hxb; subst this
        simp [hxa, pd, info, DS.union, DS.one, DS.empty, h1.1, cA']
      | deny =>
        have := db hxb
        simp [hxa, hxb, pd, info, DS.union, DS.empty, this]
      | noOp =>
        have h3 := nb hxb
        simp [hxa, hxb, pd, info, DS.union, DS.empty, h1.1, h3.1, h1.2, h3.2]


theorem cua_ab : ∀ x : CAD M, wf x = true → cua x = true → ((pd x).a || (pd x).d) = true := by
  intro x
  induction x with
  | un d => intro _ h; cases d <;> simp_all [cua, info, pd, DS.one]
  | cond hd ha id => intro _ h; simp [cua, info] at h
  | unil => intro _ h; simp [cua, info] at h
  | ucons n c r ihc ihr =>
    intro hw h
    simp only [wf, Bool.and_eq_true] at hw
    have e := pd_list r hw.1.2
    simp only [cua, info, Bool.or_eq_true] at h
    simp only [pd, info, DS.union]
    rcases h with h | h
    · have := ihc hw.1.1 h
      simp only [pd, Bool.or_eq_true] at this
      rcases this with h1 | h1 <;> simp [h1]
    · have := ihr hw.2 h
      rw [e] at this
      simp only [Bool.or_eq_true] at this
      rcases this with h1 | h1 <;> simp [h1]

theorem pd_n (x : CAD M) (hu : isUn x = false) : (pd x).n = !(cua x) := by
  cases x with
  | un d => simp [isUn] at hu
  | cond hd ha id => rfl
  | unil => rfl
  | ucons n c r => simp [pd, cua, info]

theorem FD_mem_of_none (u : CAD M) (hw : wf u = true) (hu : isUn u = false)
    (hs : (pd u).theOnly = none) : (pd u).has (FD u) = true := by
  have hne : ¬ (cua u = true ∧ (pd u).a = false ∧ (pd u).d = false) := by
    rintro ⟨h1, h2, h3⟩
    have := cua_ab u hw h1; simp [h2, h3] at this
  have hn := pd_n u hu
  unfold FD
  revert hs hne hn
  generalize pd u = s
  generalize cua u = c
  rcases s with ⟨a, d, n⟩
  cases a <;> cases d <;> cases n <;> cases c <;> simp [DS.theOnly, DS.has]

theorem wf_build (ok : Bool) (u : CAD M) (hw : wf u = true) : wf (build ok u) = true := by
  unfold build
  split
  · rfl
  · split <;> first | rfl | exact hw

theorem good_build (u : CAD M) (hw : wf u = true) (hu : isUn u = false) : good (build true u) = true := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases hs : (pd u).theOnly with
  | some d => simp [good, wf, isUn]
  | none => simp only [good, hw, Bool.true_and]; simp [hu, FD_mem_of_none u hw hu hs]

theorem chain_L1 {W : World M} (A B : Authorizer W) (hn : namesOk A B = true) (a : W.Attrs)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true) :
    good ((chain2 A B).caa a) = true := by
  have wA : wf (A.caa a) = true := by simp [good] at hA; exact hA.1
  have wB : wf (B.caa a) = true := by simp [good] at hB; exact hB.1
  simp only [chain2, hn]
  split
  · exact good_build (CAD.ucons A.name (A.caa a) .unil) (by simp [wf, isList, wA]) rfl
  · exact good_build (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) .unil))
      (by simp [wf, isList, wA, wB]) rfl



/-! ### Exactness (L3, L4) -/

theorem sem_build (t : M → Dec) (u : CAD M) (hw : wf u = true) : sem t (build true u) = sem t u := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases hs : (pd u).theOnly with
  | none => rfl
  | some d =>
    have := theOnly_has hs (sem_mem t u hw)
    simp [sem, this]

theorem chain_L3 {W : World M} (A B : Authorizer W) (fA fB : W.Attrs → W.Data → Dec)
    (hn : namesOk A B = true) (a : W.Attrs) (d : W.Data)
    (hA : good (A.caa a) = true) (hB : good (B.caa a) = true)
    (h3A : fA a d = sem (W.truth d) (A.caa a)) (h3B : fB a d = sem (W.truth d) (B.caa a)) :
    chainFull fA fB a d = sem (W.truth d) ((chain2 A B).caa a) := by
  have wA : wf (A.caa a) = true := good_wf hA
  have wB : wf (B.caa a) = true := good_wf hB
  have hcc : (chain2 A B).caa a =
      (if cua (A.caa a) = true then build true (CAD.ucons A.name (A.caa a) CAD.unil)
       else build true (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) CAD.unil))) := by
    simp [chain2, hn]
  rw [hcc]
  by_cases hcu : cua (A.caa a) = true
  · rw [if_pos hcu, sem_build _ _ (by simp [wf, isList, wA])]
    have := cua_sem (W.truth d) _ wA hcu
    have h' : fA a d ≠ .noOp := by rw [h3A]; exact this
    simp only [chainFull, h', ite_false, h3A, sem]
    simp [this]
  · rw [if_neg hcu, sem_build _ _ (by simp [wf, isList, wA, wB])]
    simp only [chainFull, h3A, h3B]
    by_cases h : sem (W.truth d) (A.caa a) = .noOp <;> by_cases h' : sem (W.truth d) (B.caa a) = .noOp <;>
      simp [sem, h, h']

theorem theOnly_mem {s : DS} {d : Dec} (h : s.theOnly = some d) : s.has d = true := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [DS.theOnly, DS.has]

theorem steps_un {o : M → Dec} {d : Dec} {y : CAD M} (h : Steps o (.un d) y) : y = .un d := by
  cases h with
  | refl => rfl
  | cons s _ => cases s with
    | norm hu _ => simp [isUn] at hu

theorem step_cua {o : M → Dec} {x y : CAD M} (h : Step o x y) : cua x = true → cua y = true := by
  induction h with
  | resolve => intro h; simp [cua, info] at h
  | shrink => intro h; simp [cua, info] at h
  | head hs ih =>
    intro h
    simp only [cua, info, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (ih (by simpa [cua] using h))
    · exact Or.inr h
  | tail hs hl ih =>
    intro h
    simp only [cua, info, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih (by simpa [cua] using h))
  | trunc hc =>
    intro h
    simp only [cua, info, Bool.or_eq_true] at h ⊢
    exact Or.inl (by simpa [cua] using hc)
  | norm hu ho =>
    intro h
    rename_i x d
    have hn := pd_n x hu
    rw [h] at hn
    have := theOnly_mem ho
    simp only [Bool.not_true] at hn
    cases d <;> simp_all [cua, info, DS.has]

theorem steps_cua {o : M → Dec} {x y : CAD M} (h : Steps o x y) : cua x = true → cua y = true := by
  induction h with
  | refl => exact id
  | cons s _ ih => exact fun h => ih (step_cua s h)

theorem step_unil_not_list {o : M → Dec} {y : CAD M} (h : Step o .unil y) : isList y = false := by
  cases h with
  | norm hu ho => rfl

theorem steps_unil {o : M → Dec} {y : CAD M} (h : Steps o .unil y) (hl : isList y = true) : y = .unil := by
  cases h with
  | refl => rfl
  | cons s rest =>
    have := step_unil_not_list s
    cases s with
    | norm hu ho =>
      have := steps_un rest
      subst this; simp [isList] at hl

/-- Inversion of refinement for a union cons cell. After a `trunc` the tail is `unil` and the
head still contains an unconditional Allow/Deny. -/
theorem steps_ucons {o : M → Dec} {x z : CAD M} (h : Steps o x z) :
    ∀ n c r, x = .ucons n c r → isList r = true →
    (∃ c' r', z = .ucons n c' r' ∧ Steps o c c' ∧ isList r' = true ∧
      (Steps o r r' ∨ (r' = .unil ∧ cua c' = true))) ∨ ∃ d, z = .un d := by
  induction h with
  | refl x =>
    intro n c r hx hl; subst hx
    exact Or.inl ⟨c, r, rfl, Steps.refl _, hl, Or.inl (Steps.refl _)⟩
  | cons s rest ih =>
    intro n c r hx hl; subst hx
    cases s with
    | head hs =>
      rcases ih n _ r rfl hl with ⟨c', r', hz, h1, h2, h3⟩ | h
      · exact Or.inl ⟨c', r', hz, Steps.cons hs h1, h2, h3⟩
      · exact Or.inr h
    | tail hs hl' =>
      rename_i r1
      rcases ih n c r1 rfl hl' with ⟨c', r', hz, h1, h2, h3 | ⟨h3, h4⟩⟩ | h
      · exact Or.inl ⟨c', r', hz, h1, h2, Or.inl (Steps.cons hs h3)⟩
      · exact Or.inl ⟨c', r', hz, h1, h2, Or.inr ⟨h3, h4⟩⟩
      · exact Or.inr h
    | trunc hc =>
      rcases ih n c .unil rfl rfl with ⟨c', r', hz, h1, h2, h3 | ⟨h3, h4⟩⟩ | h
      · have := steps_unil h3 h2
        exact Or.inl ⟨c', r', hz, h1, h2, Or.inr ⟨this, steps_cua h1 hc⟩⟩
      · exact Or.inl ⟨c', r', hz, h1, h2, Or.inr ⟨h3, h4⟩⟩
      · exact Or.inr h
    | norm hu ho =>
      exact Or.inr ⟨_, steps_un rest⟩

theorem leaf_eq {W : World M} {Dom : W.Attrs → W.Data → Prop} {fQ : W.Attrs → W.Data → Dec}
    (Q : Authorizer W) (hL : Lawful Dom fQ Q)
    (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d) (hD : Dom a d)
    (rt : String → CAD M → Dec) (n : String)
    (hrt : ∀ c, rt n c = Q.eval c d) (c : CAD M) (hr : Steps (W.truth d) (Q.caa a) c) :
    leaf rt n c = fQ a d := by
  have hwf : wf (Q.caa a) = true := good_wf (hL.sound.S1 a)
  obtain ⟨hwc, hsc⟩ := refines_sem hr hwf
  have h3 := hL.L3 a d hc hD
  cases c with
  | un dd => simp [leaf, sem] at hsc ⊢; rw [h3]; exact hsc
  | cond hd ha m | unil | ucons _ _ _ =>
    all_goals
      first
      | (have h4 := hL.L4 a d hc hD _ rfl hr
         have hm := sem_mem (W.truth d) _ hwc
         rw [hsc, ← h3] at hm
         simp only [leaf, hrt, h4, hm, ite_true])

theorem build_cases (u : CAD M) : build true u = u ∨ ∃ d, build true u = .un d := by
  unfold build
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases (pd u).theOnly with
  | none => exact Or.inl rfl
  | some d => exact Or.inr ⟨d, rfl⟩

theorem evalL_one (rt : String → CAD M → Dec) (t : M → Dec) (n : String) (c : CAD M)
    (h : leaf rt n c = sem t c) : evalL rt (.ucons n c .unil) = sem t (.ucons n c .unil) := by
  simp [evalL, sem, h]

theorem evalL_two (rt : String → CAD M → Dec) (t : M → Dec) (n1 n2 : String) (c1 c2 : CAD M)
    (h1 : leaf rt n1 c1 = sem t c1) (h2 : leaf rt n2 c2 = sem t c2) :
    evalL rt (.ucons n1 c1 (.ucons n2 c2 .unil)) = sem t (.ucons n1 c1 (.ucons n2 c2 .unil)) := by
  simp [evalL, sem, h1, h2]

/-- Shape of every conditional refinement of a two-member chain decision. -/
theorem chain_refine_shape {W : World M} (A B : Authorizer W) (hn : namesOk A B = true)
    (a : W.Attrs) (d : W.Data) (x : CAD M) (hx : isUn x = false)
    (hr : Refines (W.truth d) x ((chain2 A B).caa a)) :
    (∃ c1, x = .ucons A.name c1 .unil ∧ Steps (W.truth d) (A.caa a) c1) ∨
    (∃ c1 c2, x = .ucons A.name c1 (.ucons B.name c2 .unil) ∧ Steps (W.truth d) (A.caa a) c1 ∧
        Steps (W.truth d) (B.caa a) c2) := by
  have hcc : (chain2 A B).caa a =
      (if cua (A.caa a) = true then build true (CAD.ucons A.name (A.caa a) CAD.unil)
       else build true (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) CAD.unil))) := by
    simp [chain2, hn]
  unfold Refines at hr
  rw [hcc] at hr
  by_cases hcu : cua (A.caa a) = true
  · rw [if_pos hcu] at hr
    rcases build_cases (CAD.ucons A.name (A.caa a) CAD.unil) with hb | ⟨dd, hb⟩
    · rw [hb] at hr
      rcases steps_ucons hr A.name _ _ rfl rfl with ⟨c1, r', hz, h1, h2, h3 | ⟨h3, h4⟩⟩ | ⟨dd, hz⟩
      · have := steps_unil h3 h2; subst this; subst hz; exact Or.inl ⟨c1, rfl, h1⟩
      · subst h3; subst hz; exact Or.inl ⟨c1, rfl, h1⟩
      · subst hz; simp [isUn] at hx
    · rw [hb] at hr; have := steps_un hr; subst this; simp [isUn] at hx
  · rw [if_neg hcu] at hr
    rcases build_cases (CAD.ucons A.name (A.caa a) (CAD.ucons B.name (B.caa a) CAD.unil)) with hb | ⟨dd, hb⟩
    · rw [hb] at hr
      rcases steps_ucons hr A.name _ _ rfl (by simp [isList]) with ⟨c1, r', hz, h1, h2, h3 | ⟨h3, h4⟩⟩ | ⟨dd, hz⟩
      · rcases steps_ucons h3 B.name _ _ rfl rfl with ⟨c2, r'', hz2, h5, h6, h7 | ⟨h7, h8⟩⟩ | ⟨dd, hz2⟩
        · have := steps_unil h7 h6; subst this; subst hz2; subst hz
          exact Or.inr ⟨c1, c2, rfl, h1, h5⟩
        · subst h7; subst hz2; subst hz; exact Or.inr ⟨c1, c2, rfl, h1, h5⟩
        · rw [hz2] at h2; simp [isList] at h2
      · subst h3; subst hz; exact Or.inl ⟨c1, rfl, h1⟩
      · subst hz; simp [isUn] at hx
    · rw [hb] at hr; have := steps_un hr; subst this; simp [isUn] at hx

theorem chain_L4 {W : World M} {DA DB : W.Attrs → W.Data → Prop} (A B : Authorizer W)
    (fA fB : W.Attrs → W.Data → Dec)
    (hLA : Lawful DA fA A) (hLB : Lawful DB fB B)
    (hn : namesOk A B = true) (a : W.Attrs) (d : W.Data) (hc : W.Consistent a d)
    (hDA : DA a d) (hDB : DB a d)
    (x : CAD M) (hx : isUn x = false)
    (hr : Refines (W.truth d) x ((chain2 A B).caa a)) :
    (chain2 A B).eval x d = chainFull fA fB a d := by
  have hA := hLA.sound.S1 a
  have hB := hLB.sound.S1 a
  have hn' := hn
  simp only [namesOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn'
  have hAB : (B.name == A.name) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hn'.2 h.symm
  have hrtA : ∀ c, route A B d A.name c = A.eval c d := by intro c; simp [route]
  have hrtB : ∀ c, route A B d B.name c = B.eval c d := by intro c; simp [route, hAB]
  have wch : wf ((chain2 A B).caa a) = true := good_wf (chain_L1 A B hn a hA hB)
  obtain ⟨_, hsz⟩ := refines_sem hr wch
  have h3 := chain_L3 A B fA fB hn a d hA hB (hLA.L3 a d hc hDA) (hLB.L3 a d hc hDB)
  have hev : ∀ n c r, (chain2 A B).eval (.ucons n c r) d = evalL (route A B d) (.ucons n c r) :=
    fun _ _ _ => rfl
  rcases chain_refine_shape A B hn a d x hx hr with ⟨c1, hz, h1⟩ | ⟨c1, c2, hz, h1, h2⟩
  · subst hz
    rw [hev, evalL_one _ (W.truth d) _ _ ?_, hsz, h3]
    have e1 := leaf_eq A hLA a d hc hDA (route A B d) A.name hrtA c1 h1
    rw [e1, hLA.L3 a d hc hDA, (refines_sem h1 (good_wf hA)).2]
  · subst hz
    rw [hev, evalL_two _ (W.truth d) _ _ _ _ ?_ ?_, hsz, h3]
    · have e1 := leaf_eq A hLA a d hc hDA (route A B d) A.name hrtA c1 h1
      rw [e1, hLA.L3 a d hc hDA, (refines_sem h1 (good_wf hA)).2]
    · have e2 := leaf_eq B hLB a d hc hDB (route A B d) B.name hrtB c2 h2
      rw [e2, hLB.L3 a d hc hDB, (refines_sem h2 (good_wf hB)).2]

end K8sAuthz
