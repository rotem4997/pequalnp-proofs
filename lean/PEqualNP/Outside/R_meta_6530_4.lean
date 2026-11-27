import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_6530_4
    (toTopForm :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → ∃ C' : Circuit, IsLeastAO G C' ∧ TopForm G C' ∧ C'.size = C.size)
    (cleanTopForm :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card ≤ 1 → 64 ≤ C.size)
    (dirtyLowTopForm :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 3 → 64 ≤ C.size)
    (dirtyHighTopForm :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        4 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card → 64 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size := by
  classical
  intro x1 x2 hmono hlen heval
  let pgG : SimpleGraph (Fin 26) := SimpleGraph.fromRel (fun u v : Fin 26 =>
    u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
  let evalOp : GateOp → List Bool → Bool := fun op l =>
    GateOp.casesOn op (l.all id) (l.any id) (!(l.headD false)) (fun m => decide (l.count true % m = 0))
      (decide (l.length ≤ 2 * l.count true))
  have hevalOp : ∀ op l, GateOp.eval op l = evalOp op l := by
    intro op l
    cases op <;> rfl
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [evalOp g.op (g.inputs.map fun i => w.getD i false)]
  have hwires_eq : ∀ (C : Circuit) (x : List Bool),
      C.wires x = C.gates.foldl step x := by
    intro C x
    have hstep_eq : (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = step := by
      funext w g
      rw [hevalOp]
    change C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = _
    rw [hstep_eq]
  have hwires_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g rest ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hgetD_snoc_lt : ∀ (w : List Bool) (b : Bool) (i : ℕ),
      i < w.length → (w ++ [b]).getD i false = w.getD i false := by
    intro w b i hi
    exact List.getD_append _ _ _ _ hi
  have hgetD_snoc_eq : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp [List.getD_eq_getElem?_getD]
  have hgetD_snoc_gt : ∀ (w : List Bool) (b : Bool) (i : ℕ),
      w.length < i → (w ++ [b]).getD i false = false := by
    intro w b i hi
    rw [List.getD_eq_default]
    simp
    omega
  let vecFn (x5 x6 : Finset (Fin 13)) : Fin 26 → Bool := fun x8 =>
    if (x8 : ℕ) < 13 then Decidable.decide (Fin.ofNat 13 (x8 : ℕ) ∈ x5)
    else Decidable.decide (Fin.ofNat 13 (x8 : ℕ) ∈ x6)
  have hvec_eq : ∀ (x : Fin 26 → Bool),
      vecFn (Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true)
            (Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true) = x := by
    intro x
    funext i
    dsimp [vecFn]
    by_cases hi : (i : ℕ) < 13
    · have hcast : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := by
        ext; simp [Nat.mod_eq_of_lt hi]
      have hmem : (Fin.ofNat 13 i.val ∈ Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true) ↔
          x i = true := by
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        exact eq_iff_iff.mp (congrArg (fun z => x z = true) hcast)
      simp only [hi, ↓reduceIte]
      cases hxi : x i
      · exact decide_eq_false (fun h => Bool.noConfusion (hxi.symm.trans (hmem.mp h)))
      · exact decide_eq_true (hmem.mpr hxi)
    · simp only [hi, ↓reduceIte]
      have h13 : 13 ≤ (i : ℕ) := Nat.le_of_not_lt hi
      have hnat : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := by
        ext
        simp only [Fin.val_natAdd, Fin.val_ofNat]
        have hlt : (i : ℕ) < 26 := i.isLt
        have hmod : i.val % 13 = i.val - 13 := by omega
        omega
      have hmem : (Fin.ofNat 13 i.val ∈ Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true) ↔
          x i = true := by
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        exact eq_iff_iff.mp (congrArg (fun z => x z = true) hnat)
      cases hxi : x i
      · exact decide_eq_false (fun h => Bool.noConfusion (hxi.symm.trans (hmem.mp h)))
      · exact decide_eq_true (hmem.mpr hxi)
  have hpg_iff : ∀ (x : Fin 26 → Bool),
      graphFun pgG ∅ x = true ↔
        ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ u v, pgG.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and,
      exists_false, false_or]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have hrel : (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
          (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) :=
        huv.2
      rcases hrel with ⟨hu, hv, hinc⟩ | ⟨hv, hu, hinc⟩
      · refine ⟨⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩, ?_, ?_, ?_⟩
        · have heq : (u.val + (v.val - 13)) % 13 = (u.val + v.val) % 13 := by omega
          rwa [heq]
        · convert hxu using 2; ext; rfl
        · convert hxv using 2; ext; simp; omega
      · refine ⟨⟨v.val, hv⟩, ⟨u.val - 13, by omega⟩, ?_, ?_, ?_⟩
        · have heq : (v.val + (u.val - 13)) % 13 = (v.val + u.val) % 13 := by omega
          rwa [heq]
        · convert hxv using 2; ext; rfl
        · convert hxu using 2; ext; simp; omega
    · rintro ⟨p, l, hinc, hxp, hxl⟩
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ⟨?_, Or.inl ⟨p.isLt, by simp, ?_⟩⟩, hxp, hxl⟩
      · intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · simp only [Fin.val_castAdd, Fin.val_natAdd]
        have heq : (p.val + (13 + l.val)) % 13 = (p.val + l.val) % 13 := by omega
        rwa [heq]
  have hsingle : ∃ C1 : Circuit, Monotone2 C1 ∧ C1.size ≤ x1.size + 1 ∧
      ∀ x : Fin 26 → Bool, C1.eval (List.ofFn x) = graphFun pgG ∅ x := by
    have hfun : ∀ x : Fin 26 → Bool,
        evalOp GateOp.and (x2.map fun k => (x1.wires (List.ofFn x)).getD k false) =
          graphFun pgG ∅ x := by
      intro x
      change GateOp.and.eval (x2.map fun k => (x1.wires (List.ofFn x)).getD k false) = _
      have hx56 := heval (Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true)
                        (Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true)
      have hv : (fun x8 : Fin 26 =>
          if (x8 : ℕ) < 13 then Decidable.decide (Fin.ofNat 13 (x8 : ℕ) ∈
            Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true)
          else Decidable.decide (Fin.ofNat 13 (x8 : ℕ) ∈
            Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true)) = x := hvec_eq x
      rw [hv] at hx56
      apply Bool.eq_iff_iff.mpr
      rw [hx56, hpg_iff]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, hp, l, hl, hinc⟩
        exact ⟨p, l, hinc, hp, hl⟩
      · rintro ⟨p, l, hinc, hp, hl⟩
        exact ⟨p, hp, l, hl, hinc⟩
    rcases x2 with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
    · exfalso
      have h0 := hfun (fun _ => false)
      have hf : graphFun pgG ∅ (fun _ => false) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p, l, _, hp, _⟩ := (hpg_iff _).1 h
        exact Bool.noConfusion hp
      change true = _ at h0
      rw [hf] at h0
      exact Bool.noConfusion h0
    · refine ⟨⟨x1.gates, w1⟩, hmono, Nat.le_succ _, fun x => ?_⟩
      change ((⟨x1.gates, w1⟩ : Circuit).wires (List.ofFn x)).getD w1 false = _
      have hw : (⟨x1.gates, w1⟩ : Circuit).wires (List.ofFn x) = x1.wires (List.ofFn x) := rfl
      rw [hw]
      have h0 := hfun x
      change ((x1.wires (List.ofFn x)).getD w1 false && true) = graphFun pgG ∅ x at h0
      rw [Bool.and_true] at h0
      exact h0
    · refine ⟨⟨x1.gates ++ [⟨GateOp.and, [w1, w2]⟩], 26 + x1.size⟩, ?_, ?_, fun x => ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hmono g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨Or.inl rfl, by simp⟩
      · change (x1.gates ++ [({ op := GateOp.and, inputs := [w1, w2] } : Gate)]).length ≤ x1.gates.length + 1
        simp
      · change ((⟨x1.gates ++ [⟨GateOp.and, [w1, w2]⟩], 26 + x1.size⟩ : Circuit).wires (List.ofFn x)).getD (26 + x1.size) false = _
        rw [hwires_eq, List.foldl_append]
        change (step (x1.gates.foldl step (List.ofFn x)) ⟨GateOp.and, [w1, w2]⟩).getD (26 + x1.size) false = _
        have hl : (x1.gates.foldl step (List.ofFn x)).length = 26 + x1.size := by
          rw [hwires_len, List.length_ofFn]; rfl
        dsimp only [step]
        rw [← hl, hgetD_snoc_eq]
        have h0 := hfun x
        rw [← hwires_eq]
        change ((x1.wires (List.ofFn x)).getD w1 false && ((x1.wires (List.ofFn x)).getD w2 false && true)) = graphFun pgG ∅ x at h0
        change ((x1.wires (List.ofFn x)).getD w1 false && ((x1.wires (List.ofFn x)).getD w2 false && true)) = graphFun pgG ∅ x
        exact h0
    · simp at hlen
  obtain ⟨C1, hC1_mono, hC1_sz, hC1_eval⟩ := hsingle
  let evalRep : List Bool → Sum Bool ℕ → Bool := fun w v =>
    Sum.elim id (fun i => w.getD i false) v
  let isOk : List Gate → Sum Bool ℕ → Prop := fun gs v =>
    Sum.elim (fun _ => True) (fun i => i < 26 + gs.length) v
  let combRep : Bool → List Gate → Sum Bool ℕ → Sum Bool ℕ → List Gate × Sum Bool ℕ :=
    fun isOr gs v1 v2 =>
      if isOr then
        Sum.elim
          (fun b1 => if b1 then (gs, Sum.inl true) else (gs, v2))
          (fun a => Sum.elim
            (fun b2 => if b2 then (gs, Sum.inl true) else (gs, Sum.inr a))
            (fun b => if a = b then (gs, Sum.inr a)
              else (gs ++ [⟨GateOp.or, [a, b]⟩], Sum.inr (26 + gs.length)))
            v2)
          v1
      else
        Sum.elim
          (fun b1 => if b1 then (gs, v2) else (gs, Sum.inl false))
          (fun a => Sum.elim
            (fun b2 => if b2 then (gs, Sum.inr a) else (gs, Sum.inl false))
            (fun b => if a = b then (gs, Sum.inr a)
              else (gs ++ [⟨GateOp.and, [a, b]⟩], Sum.inr (26 + gs.length)))
            v2)
          v1
  let cleanStep : List Gate × List (Sum Bool ℕ) → Gate → List Gate × List (Sum Bool ℕ) :=
    fun st g =>
      let gs := st.1
      let env := st.2
      let rd := fun i => env.getD i (Sum.inl false)
      let isOr : Bool := GateOp.casesOn (motive := fun _ => Bool) g.op false true false (fun _ => false) false
      let res : List Gate × Sum Bool ℕ :=
        List.casesOn (motive := fun _ => List Gate × Sum Bool ℕ) g.inputs (gs, Sum.inl (!isOr))
          (fun i rest => List.casesOn (motive := fun _ => List Gate × Sum Bool ℕ) rest (gs, rd i)
            (fun j _ => combRep isOr gs (rd i) (rd j)))
      (res.1, env ++ [res.2])
  let validEnv (gs : List Gate) (env : List (Sum Bool ℕ)) : Prop :=
    ∀ v ∈ env, isOk gs v
  have validRd (gs : List Gate) (env : List (Sum Bool ℕ)) (h : validEnv gs env) (i : ℕ) :
      isOk gs (env.getD i (Sum.inl false)) := by
    by_cases hi : i < env.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      trivial
  have hcomb_struct : ∀ (isOr : Bool) (gs : List Gate) (v1 v2 : Sum Bool ℕ),
      IsAO2 26 ⟨gs, 0⟩ →
      isOk gs v1 →
      isOk gs v2 →
      (combRep isOr gs v1 v2).1.length ≤ gs.length + 1 ∧
      IsAO2 26 ⟨(combRep isOr gs v1 v2).1, 0⟩ ∧
      (∀ v : Sum Bool ℕ, isOk gs v → isOk (combRep isOr gs v1 v2).1 v) ∧
      isOk (combRep isOr gs v1 v2).1 (combRep isOr gs v1 v2).2 := by
    intro isOr gs v1 v2 hao hv1 hv2
    have hmono_gs : ∀ {gs' : List Gate} {v : Sum Bool ℕ}, gs.length ≤ gs'.length →
        isOk gs v → isOk gs' v := by
      intro gs' v hle hv
      cases v with
      | inl _ => trivial
      | inr i => exact Nat.lt_of_lt_of_le hv (Nat.add_le_add_left hle 26)
    have hsnoc_ao : ∀ (op' : GateOp) (a b : ℕ), (op' = GateOp.and ∨ op' = GateOp.or) →
        a < 26 + gs.length → b < 26 + gs.length →
        IsAO2 26 ⟨gs ++ [⟨op', [a, b]⟩], 0⟩ := by
      intro op' a b hop' ha hb
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hao.1 g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact hop'
      · intro j hj i hi
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hlt : j < gs.length
        · have hgate : gateAt ⟨gs ++ [⟨op', [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
            change List.getD (gs ++ [({ op := op', inputs := [a, b] } : Gate)]) j ({ op := GateOp.or, inputs := [] } : Gate) =
              List.getD gs j ({ op := GateOp.or, inputs := [] } : Gate)
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [hgate] at hi
          exact hao.2.1 j hlt i hi
        · have hj_eq : j = gs.length := by omega
          subst hj_eq
          have hgate : gateAt ⟨gs ++ [⟨op', [a, b]⟩], 0⟩ gs.length = ⟨op', [a, b]⟩ := by
            change List.getD (gs ++ [({ op := op', inputs := [a, b] } : Gate)]) gs.length ({ op := GateOp.or, inputs := [] } : Gate) =
              ({ op := op', inputs := [a, b] } : Gate)
            simp [List.getD_eq_getElem?_getD]
          rw [hgate] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> assumption
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hao.2.2 g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          rfl
    cases isOr
    · rcases v1 with b1 | a
      · cases b1
        · dsimp only [combRep]; exact ⟨Nat.le_succ _, hao, fun _ h => h, trivial⟩
        · dsimp only [combRep]; exact ⟨Nat.le_succ _, hao, fun _ h => h, hv2⟩
      · rcases v2 with b2 | b
        · cases b2 <;> dsimp only [combRep] <;> exact ⟨Nat.le_succ _, hao, fun _ h => h, by simp [isOk, hv1]⟩
        · by_cases hab : a = b
          · subst hab
            simp only [combRep, Bool.false_eq_true, ↓reduceIte, Sum.elim_inr]
            exact ⟨Nat.le_succ _, hao, fun _ h => h, hv1⟩
          · simp only [combRep, Bool.false_eq_true, ↓reduceIte, Sum.elim_inr, hab]
            refine ⟨by simp, hsnoc_ao GateOp.and a b (Or.inl rfl) hv1 hv2, ?_, by simp [isOk]⟩
            intro v hv
            exact hmono_gs (by simp) hv
    · rcases v1 with b1 | a
      · cases b1
        · dsimp only [combRep]; exact ⟨Nat.le_succ _, hao, fun _ h => h, hv2⟩
        · dsimp only [combRep]; exact ⟨Nat.le_succ _, hao, fun _ h => h, trivial⟩
      · rcases v2 with b2 | b
        · cases b2 <;> dsimp only [combRep] <;> exact ⟨Nat.le_succ _, hao, fun _ h => h, by simp [isOk, hv1]⟩
        · by_cases hab : a = b
          · subst hab
            simp only [combRep, ↓reduceIte, Sum.elim_inr]
            exact ⟨Nat.le_succ _, hao, fun _ h => h, hv1⟩
          · simp only [combRep, ↓reduceIte, Sum.elim_inr, hab]
            refine ⟨by simp, hsnoc_ao GateOp.or a b (Or.inr rfl) hv1 hv2, ?_, by simp [isOk]⟩
            intro v hv
            exact hmono_gs (by simp) hv
  have hclean_step_struct : ∀ (g : Gate) (gs : List Gate) (env : List (Sum Bool ℕ)),
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) → g.inputs.length ≤ 2 →
      IsAO2 26 ⟨gs, 0⟩ → validEnv gs env →
      (cleanStep (gs, env) g).1.length ≤ gs.length + 1 ∧
      IsAO2 26 ⟨(cleanStep (gs, env) g).1, 0⟩ ∧
      validEnv (cleanStep (gs, env) g).1 (cleanStep (gs, env) g).2 := by
    intro g gs env hgop hglen hao henv
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgop
    have hv := validRd gs env henv
    rcases hop with hop_eq | hop_eq <;> rcases g with ⟨gop, gins⟩ <;> simp only at hop_eq <;> subst hop_eq
    · rcases gins with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · refine ⟨Nat.le_succ _, hao, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact henv v hvmem
        · simp only [List.mem_singleton] at hvmem; subst hvmem; trivial
      · refine ⟨Nat.le_succ _, hao, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact henv v hvmem
        · simp only [List.mem_singleton] at hvmem; subst hvmem; exact hv i
      · have hc := hcomb_struct false gs (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
          hao (hv i) (hv j)
        refine ⟨hc.1, hc.2.1, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact hc.2.2.1 v (henv v hvmem)
        · simp only [List.mem_singleton] at hvmem; subst hvmem; exact hc.2.2.2
      · exfalso; simp at hglen
    · rcases gins with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · refine ⟨Nat.le_succ _, hao, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact henv v hvmem
        · simp only [List.mem_singleton] at hvmem; subst hvmem; trivial
      · refine ⟨Nat.le_succ _, hao, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact henv v hvmem
        · simp only [List.mem_singleton] at hvmem; subst hvmem; exact hv i
      · have hc := hcomb_struct true gs (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
          hao (hv i) (hv j)
        refine ⟨hc.1, hc.2.1, ?_⟩
        intro v hvmem
        rcases List.mem_append.mp hvmem with hvmem | hvmem
        · exact hc.2.2.1 v (henv v hvmem)
        · simp only [List.mem_singleton] at hvmem; subst hvmem; exact hc.2.2.2
      · exfalso; simp at hglen
  have hclean_struct : ∀ (rem gs : List Gate) (env : List (Sum Bool ℕ)),
      IsAO2 26 ⟨gs, 0⟩ →
      validEnv gs env →
      (∀ g ∈ rem, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (rem.foldl cleanStep (gs, env)).1.length ≤ gs.length + rem.length ∧
      IsAO2 26 ⟨(rem.foldl cleanStep (gs, env)).1, 0⟩ ∧
      validEnv (rem.foldl cleanStep (gs, env)).1 (rem.foldl cleanStep (gs, env)).2 := by
    intro rem
    induction rem with
    | nil =>
      intro gs env hao henv _
      exact ⟨Nat.le_refl _, hao, henv⟩
    | cons g rest ih =>
      intro gs env hao henv hrem
      have hg := hrem g (by simp)
      have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hrem g' (by simp [hg'])
      have hstep := hclean_step_struct g gs env hg.1 hg.2 hao henv
      have hst1 := ih (cleanStep (gs, env) g).1 (cleanStep (gs, env) g).2 hstep.2.1 hstep.2.2 hrest
      have hlen1 := hstep.1
      have hlen2 := hst1.1
      rw [List.foldl_cons]
      have heta : cleanStep (gs, env) g = ((cleanStep (gs, env) g).1, (cleanStep (gs, env) g).2) := rfl
      rw [heta]
      exact ⟨by simp only [List.length_cons]; omega, hst1.2.1, hst1.2.2⟩
  have hcomb_sem : ∀ (isOr : Bool) (gs : List Gate) (v1 v2 : Sum Bool ℕ) (x : Fin 26 → Bool),
      isOk gs v1 →
      isOk gs v2 →
      let w := gs.foldl step (List.ofFn x)
      let res := combRep isOr gs v1 v2
      let w' := res.1.foldl step (List.ofFn x)
      (∀ v : Sum Bool ℕ, isOk gs v → evalRep w' v = evalRep w v) ∧
      evalRep w' res.2 = (if isOr then evalRep w v1 || evalRep w v2 else evalRep w v1 && evalRep w v2) := by
    intro isOr gs v1 v2 x hv1 hv2
    have hwlen : (gs.foldl step (List.ofFn x)).length = 26 + gs.length := by
      rw [hwires_len, List.length_ofFn]
    have hsnoc_keep : ∀ (g : Gate) (v : Sum Bool ℕ), isOk gs v →
        evalRep ((gs ++ [g]).foldl step (List.ofFn x)) v = evalRep (gs.foldl step (List.ofFn x)) v := by
      intro g v hv
      cases v with
      | inl _ => rfl
      | inr i =>
        change (List.foldl step (List.ofFn x) (gs ++ [g])).getD i false = (List.foldl step (List.ofFn x) gs).getD i false
        rw [List.foldl_append]
        change (step (gs.foldl step (List.ofFn x)) g).getD i false = _
        dsimp only [step]
        exact hgetD_snoc_lt _ _ _ (by rw [hwlen]; exact hv)
    have hsnoc_new : ∀ (g : Gate),
        evalRep ((gs ++ [g]).foldl step (List.ofFn x)) (Sum.inr (26 + gs.length)) =
          evalOp g.op (g.inputs.map fun i => (gs.foldl step (List.ofFn x)).getD i false) := by
      intro g
      change (List.foldl step (List.ofFn x) (gs ++ [g])).getD (26 + gs.length) false = _
      rw [List.foldl_append]
      change (step (gs.foldl step (List.ofFn x)) g).getD (26 + gs.length) false = _
      dsimp only [step]
      rw [← hwlen, hgetD_snoc_eq]
    cases isOr
    · rcases v1 with b1 | a
      · cases b1
        · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
        · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
      · rcases v2 with b2 | b
        · cases b2
          · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
          · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
        · by_cases hab : a = b
          · subst hab
            refine ⟨fun _ _ => ?_, ?_⟩
            · simp only [combRep, Bool.false_eq_true, ↓reduceIte, Sum.elim_inr]
            · simp [combRep, evalRep]
          · simp only [combRep, Bool.false_eq_true, ↓reduceIte, Sum.elim_inr, hab]
            refine ⟨fun v hv => hsnoc_keep _ v hv, ?_⟩
            rw [hsnoc_new]
            simp [evalOp, evalRep]
    · rcases v1 with b1 | a
      · cases b1
        · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
        · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
      · rcases v2 with b2 | b
        · cases b2
          · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
          · exact ⟨fun _ _ => rfl, by simp [combRep, evalRep]⟩
        · by_cases hab : a = b
          · subst hab
            refine ⟨fun _ _ => ?_, ?_⟩
            · simp only [combRep, ↓reduceIte, Sum.elim_inr]
            · simp [combRep, evalRep]
          · simp only [combRep, ↓reduceIte, Sum.elim_inr, hab]
            refine ⟨fun v hv => hsnoc_keep _ v hv, ?_⟩
            rw [hsnoc_new]
            simp [evalOp, evalRep]
  have hclean_sem : ∀ (x : Fin 26 → Bool) (rem gs : List Gate) (env : List (Sum Bool ℕ)) (wOrig : List Bool),
      IsAO2 26 ⟨gs, 0⟩ →
      validEnv gs env →
      wOrig.length = env.length →
      (∀ i, wOrig.getD i false = evalRep (gs.foldl step (List.ofFn x)) (env.getD i (Sum.inl false))) →
      (∀ g ∈ rem, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ i, (rem.foldl step wOrig).getD i false =
        evalRep ((rem.foldl cleanStep (gs, env)).1.foldl step (List.ofFn x)) ((rem.foldl cleanStep (gs, env)).2.getD i (Sum.inl false)) := by
    intro x rem
    induction rem with
    | nil =>
      intro gs env wOrig _ _ _ hagree _ i
      exact hagree i
    | cons g rest ih =>
      intro gs env wOrig hao henv hlen_eq hagree hrem i
      have hg := hrem g (by simp)
      have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hrem g' (by simp [hg'])
      have hstep := hclean_step_struct g gs env hg.1 hg.2 hao henv
      have hlen_next : (step wOrig g).length = (cleanStep (gs, env) g).2.length := by
        simp [step, cleanStep, hlen_eq]
      have hagree_next : ∀ k, (step wOrig g).getD k false =
          evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x))
            ((cleanStep (gs, env) g).2.getD k (Sum.inl false)) := by
        intro k
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
        have hv := validRd gs env henv
        have keep_env_val : ∀ (k : ℕ), k < env.length →
            (∀ v : Sum Bool ℕ, isOk gs v →
              evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x)) v =
                evalRep (gs.foldl step (List.ofFn x)) v) →
            (step wOrig g).getD k false =
              evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x))
                ((cleanStep (gs, env) g).2.getD k (Sum.inl false)) := by
          intro k hk hkeep
          have hk_orig : k < wOrig.length := by rw [hlen_eq]; exact hk
          dsimp only [step, cleanStep]
          rw [hgetD_snoc_lt _ _ _ hk_orig, List.getD_append _ _ _ _ hk, hagree k]
          exact (hkeep _ (hv k)).symm
        have gt_env_val : ∀ (k : ℕ), env.length < k →
            (step wOrig g).getD k false =
              evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x))
                ((cleanStep (gs, env) g).2.getD k (Sum.inl false)) := by
          intro k hk
          have hk_orig : wOrig.length < k := by rw [hlen_eq]; exact hk
          dsimp only [step, cleanStep]
          rw [hgetD_snoc_gt _ _ _ hk_orig]
          rw [List.getD_eq_default _ _ (by simp; omega)]
          rfl
        have at_env_len : ∀ (res2 : Sum Bool ℕ),
            (cleanStep (gs, env) g).2 = env ++ [res2] →
            evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x)) res2 =
              evalOp g.op (g.inputs.map fun idx => wOrig.getD idx false) →
            (step wOrig g).getD env.length false =
              evalRep ((cleanStep (gs, env) g).1.foldl step (List.ofFn x))
                ((cleanStep (gs, env) g).2.getD env.length (Sum.inl false)) := by
          intro res2 hres2 hev
          dsimp only [step]
          rw [← hlen_eq, hgetD_snoc_eq, hres2, hlen_eq]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some]
          exact hev.symm
        rcases Nat.lt_trichotomy k env.length with hk | rfl | hk
        · apply keep_env_val k hk
          rcases hop with hop_eq | hop_eq <;> rcases g with ⟨gop, gins⟩ <;> simp only at hop_eq <;> subst hop_eq
          · rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · intro v _; rfl
            · intro v _; rfl
            · exact (hcomb_sem false gs (env.getD a (Sum.inl false)) (env.getD b (Sum.inl false)) x
                (hv a) (hv b)).1
            · exfalso; have h2 := hg.2; simp at h2
          · rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · intro v _; rfl
            · intro v _; rfl
            · exact (hcomb_sem true gs (env.getD a (Sum.inl false)) (env.getD b (Sum.inl false)) x
                (hv a) (hv b)).1
            · exfalso; have h2 := hg.2; simp at h2
        · rcases hop with hop_eq | hop_eq <;> rcases g with ⟨gop, gins⟩ <;> simp only at hop_eq <;> subst hop_eq
          · rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · apply at_env_len (Sum.inl true) rfl
              dsimp only [evalRep, cleanStep, evalOp]; simp
            · apply at_env_len (env.getD a (Sum.inl false)) rfl
              dsimp only [cleanStep, evalOp]
              simpa using (hagree a).symm
            · have hs := (hcomb_sem false gs (env.getD a (Sum.inl false)) (env.getD b (Sum.inl false)) x
                (hv a) (hv b)).2
              apply at_env_len _ rfl
              dsimp only [cleanStep]
              rw [← hagree a, ← hagree b] at hs
              simpa [evalOp] using hs
            · exfalso; have h2 := hg.2; simp at h2
          · rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · apply at_env_len (Sum.inl false) rfl
              dsimp only [evalRep, cleanStep, evalOp]; simp
            · apply at_env_len (env.getD a (Sum.inl false)) rfl
              dsimp only [cleanStep, evalOp]
              simpa using (hagree a).symm
            · have hs := (hcomb_sem true gs (env.getD a (Sum.inl false)) (env.getD b (Sum.inl false)) x
                (hv a) (hv b)).2
              apply at_env_len _ rfl
              dsimp only [cleanStep]
              rw [← hagree a, ← hagree b] at hs
              simpa [evalOp] using hs
            · exfalso; have h2 := hg.2; simp at h2
        · exact gt_env_val k hk
      rw [List.foldl_cons, List.foldl_cons]
      have heta : cleanStep (gs, env) g = ((cleanStep (gs, env) g).1, (cleanStep (gs, env) g).2) := rfl
      rw [heta]
      exact ih (cleanStep (gs, env) g).1 (cleanStep (gs, env) g).2 (step wOrig g)
        hstep.2.1 hstep.2.2 hlen_next hagree_next hrest i
  let env0 : List (Sum Bool ℕ) := List.ofFn fun i : Fin 26 => Sum.inr (i : ℕ)
  have hao0 : IsAO2 26 ⟨[], 0⟩ := by
    change AndOrOnly ⟨[], 0⟩ ∧ ReadsBack 26 ⟨[], 0⟩ ∧ ∀ g ∈ ([] : List Gate), g.inputs.length = 2
    refine ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (List.not_mem_nil)⟩
  have henv0 : validEnv [] env0 := by
    intro v hv
    simp only [env0, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact i.isLt
  have hst := hclean_struct C1.gates [] env0 hao0 henv0 hC1_mono
  let finalSt := C1.gates.foldl cleanStep ([], env0)
  let finalGs := finalSt.1
  let finalEnv := finalSt.2
  have hsem_all : ∀ x : Fin 26 → Bool,
      C1.eval (List.ofFn x) =
        evalRep (finalGs.foldl step (List.ofFn x)) (finalEnv.getD C1.output (Sum.inl false)) := by
    intro x
    change (C1.wires (List.ofFn x)).getD C1.output false = _
    rw [hwires_eq]
    apply hclean_sem x C1.gates [] env0 (List.ofFn x) hao0 henv0
    · simp [env0]
    · intro i
      by_cases hi : i < 26
      · simp only [env0, evalRep, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true,
          Option.getD_some, List.foldl_nil]
        rw [Sum.elim_inr]
        simp [hi]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        rw [List.getD_eq_default _ _ (by simp [env0]; omega)]
        rfl
    · exact hC1_mono
  have hD : ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ C1.size ∧
      circuitFun 26 D = graphFun pgG ∅ := by
    cases hres : finalEnv.getD C1.output (Sum.inl false) with
    | inl b =>
      exfalso
      cases b
      · let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))
        have h1 := hC1_eval x
        have h2 := hsem_all x
        rw [hres] at h2
        have ht : graphFun pgG ∅ x = true := (hpg_iff x).2 ⟨0, 0, by decide, by decide, by decide⟩
        rw [h1, ht] at h2
        exact Bool.noConfusion h2
      · let x : Fin 26 → Bool := fun _ => false
        have h1 := hC1_eval x
        have h2 := hsem_all x
        rw [hres] at h2
        have hf : graphFun pgG ∅ x = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          obtain ⟨p, l, _, hp, _⟩ := (hpg_iff x).1 h
          exact Bool.noConfusion hp
        rw [h1, hf] at h2
        exact Bool.noConfusion h2
    | inr w =>
      refine ⟨⟨finalGs, w⟩, hst.2.1, ?_, ?_⟩
      · change finalGs.length ≤ C1.gates.length
        have hlen0 := hst.1
        rw [List.length_nil, Nat.zero_add] at hlen0
        exact hlen0
      · funext x
        have h1 := hC1_eval x
        have h2 := hsem_all x
        rw [hres] at h2
        change ((⟨finalGs, w⟩ : Circuit).wires (List.ofFn x)).getD w false = _
        rw [hwires_eq]
        exact h2.symm.trans h1
  obtain ⟨D, hD_ao, hD_sz, hD_fun⟩ := hD
  let P : ℕ → Prop := fun s => ∃ C : Circuit, IsAO2 26 C ∧ circuitFun 26 C = graphFun pgG ∅ ∧ C.size = s
  have hP_ex : ∃ s, P s := ⟨D.size, D, hD_ao, hD_fun, rfl⟩
  let sMin := Nat.find hP_ex
  have hsMin_spec : P sMin := Nat.find_spec hP_ex
  have hsMin_le : sMin ≤ D.size := Nat.find_min' hP_ex ⟨D, hD_ao, hD_fun, rfl⟩
  obtain ⟨Cmin, hCmin_ao, hCmin_fun, hCmin_sz⟩ := hsMin_spec
  have hCmin_least : IsLeastAO pgG Cmin := by
    refine ⟨hCmin_ao, hCmin_fun, ?_⟩
    intro C' hC'_ao hC'_fun
    have hle := Nat.find_min' hP_ex ⟨C', hC'_ao, hC'_fun, rfl⟩
    omega
  obtain ⟨Ctop, hCtop_least, hCtop_top, hCtop_sz⟩ := toTopForm Cmin hCmin_least
  have h64 : 64 ≤ Ctop.size := by
    by_cases hj1 : (junk pgG Ctop).card ≤ 1
    · exact cleanTopForm Ctop hCtop_least hCtop_top hj1
    · have hj2 : 2 ≤ (junk pgG Ctop).card := Nat.succ_le_of_lt (Nat.lt_of_not_ge hj1)
      by_cases hlow : 2 * (centreless pgG Ctop).card + (junk pgG Ctop).card + (orN pgG Ctop \ lam pgG Ctop).card ≤ 3
      · exact dirtyLowTopForm Ctop hCtop_least hCtop_top hj2 hlow
      · exact dirtyHighTopForm Ctop hCtop_least hCtop_top hj2 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hlow))
  omega
