import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4752_270
    (size27 :
      ∀ C : Circuit, IsAO2 14 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, p ∈ fanoLines l ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        27 ≤ C.size)
    (cleanG :
      ∀ C : Circuit,
        let F : (Fin 14 → Bool) → Prop := fun x =>
          ∃ p l : Fin 7, p ∈ fanoLines l ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
        let V := wireVal 14 C
        let B : ℕ → Prop := fun w => ∀ x : Fin 14 → Bool, V w x = true → F x
        let P : Fin 14 → Fin 14 → Fin 14 → Bool := pairInput
        let M : ℕ → Prop := fun w => V w (P 0 7) = true ∧ V w (P 0 0) = false ∧ V w (P 7 7) = false
        let A : ℕ → Prop := fun j => (gateAt C j).op = .and
        let O := opnd C
        let R := OrReaches 14 C
        C.size = 27 → IsAO2 14 C →
        (∀ j < 27, O j 0 ≠ O j 1) →
        (∀ x : Fin 14 → Bool, V C.output x = true ↔ F x) →
        (∀ j < 27, 14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
        (∀ j < 27, A j → ∀ b : Fin 2, ¬ B (O j b)) →
        (∀ j < 27, B (14 + j) → (readers 14 C j).card ≤ 1) →
        ∀ g a0 a1 : ℕ, A g → B (14 + g) → InCone 14 C g (C.output - 14) →
        M (O g 0) → M (O g 1) →
        A a0 → A a1 → a0 ≠ a1 → M (14 + a0) → M (14 + a1) →
        R (O g 0) a0 → R (O g 1) a1 → False)
    (dirtyG :
      ∀ C : Circuit,
        let F : (Fin 14 → Bool) → Prop := fun x =>
          ∃ p l : Fin 7, p ∈ fanoLines l ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
        let V := wireVal 14 C
        let B : ℕ → Prop := fun w => ∀ x : Fin 14 → Bool, V w x = true → F x
        let P : Fin 14 → Fin 14 → Fin 14 → Bool := pairInput
        let M : ℕ → Prop := fun w => V w (P 0 7) = true ∧ V w (P 0 0) = false ∧ V w (P 7 7) = false
        let A : ℕ → Prop := fun j => (gateAt C j).op = .and
        let O := opnd C
        let R := OrReaches 14 C
        let K : ℕ → Prop := fun j => 14 + j = C.output ∨ InCone 14 C j (C.output - 14)
        C.size = 27 → IsAO2 14 C →
        (∀ j < 27, O j 0 ≠ O j 1) →
        (∀ x : Fin 14 → Bool, V C.output x = true ↔ F x) →
        (∀ j < 27, K j) →
        (∀ j < 27, A j → ∀ b : Fin 2, ¬ B (O j b)) →
        (∀ j < 27, B (14 + j) → (readers 14 C j).card ≤ 1) →
        ∀ g a0 a1 h : ℕ, A g → ¬ B (14 + g) →
        M (O g 0) → M (O g 1) →
        A a0 → A a1 → M (14 + a0) → M (14 + a1) →
        R (O g 0) a0 → R (O g 1) a1 →
        A h → K h →
        (∃ b : Fin 2, R (O h b) g) → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ)) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C, hSizeLe, hShape, hEval, g, hgAnd, hgCone, hgVal, hgOpnds⟩
  letI : DecidableEq GateOp := gateOpDecEq
  let F : (Fin 14 → Bool) → Prop := fun x =>
    ∃ p l : Fin 7, p ∈ fanoLines l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
  have hFanoGeom : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by
    decide +kernel
  have hEvalF : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x := by
    intro x
    rw [hEval x]
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, l, (hFanoGeom p l).mpr hpl, hp, hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, l, (hFanoGeom p l).mp hpl, hp, hl⟩
  have hGateGet : ∀ (D : Circuit) (j : ℕ) (hj : j < D.gates.length), gateAt D j = D.gates[j] := by
    intro D j hj
    exact List.getD_eq_getElem _ _ hj
  have hShapeAt : ∀ j < C.gates.length,
      ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      ∃ a b : ℕ, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
    intro j hj
    rw [hGateGet C j hj]
    exact hShape j C.gates[j] (List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩)
  have hAO : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro gt hgt
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgt
      rw [← hGateGet C j hj]
      exact (hShapeAt j hj).1
    · intro j hj w hw
      obtain ⟨a, b, hab, _, ha, hb⟩ := (hShapeAt j hj).2
      rw [hab] at hw
      rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
    · intro gt hgt
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgt
      rw [← hGateGet C j hj]
      obtain ⟨a, b, hab, _, _, _⟩ := (hShapeAt j hj).2
      simp [hab]
  have hSizeGe : 27 ≤ C.size := size27 C hAO hEvalF
  have hSizeEq : C.size = 27 := Nat.le_antisymm hSizeLe hSizeGe
  have hLenEq : C.gates.length = 27 := hSizeEq
  have hDistinct : ∀ j < 27, opnd C j 0 ≠ opnd C j 1 := by
    intro j hj
    obtain ⟨a, b, hab, hne, _, _⟩ := (hShapeAt j (by omega)).2
    change (gateAt C j).inputs.getD 0 0 ≠ (gateAt C j).inputs.getD 1 0
    rw [hab]
    exact hne
  let wstep : List Bool → Gate → List Bool :=
    fun ws gt => ws ++ [gt.op.eval (gt.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons gt rest ih =>
      intro xs
      rw [List.foldl_cons, ih]
      dsimp only [wstep]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons gt rest ih =>
      intro xs r hr
      rw [List.foldl_cons]
      have hr' : r < (wstep xs gt).length := by
        dsimp only [wstep]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (wstep xs gt) r hr']
      dsimp only [wstep]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hr]
  have wfold_gate : ∀ (gs : List Gate) (xs : List Bool) (j : ℕ) (hj : j < gs.length),
      (∀ i ∈ gs[j].inputs, i < xs.length + j) →
      (gs.foldl wstep xs).getD (xs.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl wstep xs).getD i false) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro xs j hj; cases hj
    | append_singleton gs gt ih =>
      intro xs j hj hrb
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl wstep xs).length = xs.length + gs.length := wfold_len gs xs
      have hkeep : ∀ r, r < xs.length + gs.length →
          (wstep (gs.foldl wstep xs) gt).getD r false = (gs.foldl wstep xs).getD r false := by
        intro r hr
        change ((gs.foldl wstep xs) ++ [gt.op.eval (gt.inputs.map fun i => (gs.foldl wstep xs).getD i false)]).getD r false = _
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hlt : j < gs.length
      · have hgj : (gs ++ [gt])[j] = gs[j] := List.getElem_append_left hlt
        rw [hgj] at hrb ⊢
        rw [hkeep (xs.length + j) (by omega), ih xs j hlt hrb]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (hkeep i (by have := hrb i hi; omega)).symm
      · have heq : j = gs.length := by omega
        subst heq
        have hgj : (gs ++ [gt])[gs.length] = gt := by simp
        rw [hgj] at hrb ⊢
        have hval : (wstep (gs.foldl wstep xs) gt).getD (xs.length + gs.length) false =
            gt.op.eval (gt.inputs.map fun i => (gs.foldl wstep xs).getD i false) := by
          change ((gs.foldl wstep xs) ++ [gt.op.eval (gt.inputs.map fun i => (gs.foldl wstep xs).getD i false)]).getD (xs.length + gs.length) false = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [hval]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (hkeep i (hrb i hi)).symm
  have wireVal_input : ∀ (D : Circuit) (r : ℕ) (hr : r < 14) (x : Fin 14 → Bool),
      wireVal 14 D r x = x ⟨r, hr⟩ := by
    intro D r hr x
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r (by simp [hr]), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_ge : ∀ (D : Circuit) (r : ℕ) (hr : 14 + D.gates.length ≤ r) (x : Fin 14 → Bool),
      wireVal 14 D r x = false := by
    intro D r hr x
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = false
    apply List.getD_eq_default
    rw [wfold_len, List.length_ofFn]
    omega
  have ao_inputs : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.gates.length,
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
      opnd D j 0 < 14 + j ∧ opnd D j 1 < 14 + j := by
    intro D hD j hj
    have hlen : (gateAt D j).inputs.length = 2 := by
      rw [hGateGet D j hj]
      exact hD.2.2 D.gates[j] (List.getElem_mem hj)
    generalize hli : (gateAt D j).inputs = ins at hlen
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have ha0 : opnd D j 0 = a := by
        change (gateAt D j).inputs.getD 0 0 = a; rw [hli]; rfl
      have hb1 : opnd D j 1 = b := by
        change (gateAt D j).inputs.getD 1 0 = b; rw [hli]; rfl
      rw [ha0, hb1]
      refine ⟨rfl, ?_, ?_⟩
      · exact hD.2.1 j hj a (by rw [hli]; simp)
      · exact hD.2.1 j hj b (by rw [hli]; simp)
    · simp at hlen
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have wireVal_gate : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.gates.length, ∀ x : Fin 14 → Bool,
      ((gateAt D j).op = .and →
        wireVal 14 D (14 + j) x = (wireVal 14 D (opnd D j 0) x && wireVal 14 D (opnd D j 1) x)) ∧
      ((gateAt D j).op = .or →
        wireVal 14 D (14 + j) x = (wireVal 14 D (opnd D j 0) x || wireVal 14 D (opnd D j 1) x)) := by
    intro D hD j hj x
    have hrb : ∀ i ∈ D.gates[j].inputs, i < (List.ofFn x).length + j := by
      intro i hi
      rw [List.length_ofFn]
      exact hD.2.1 j hj i (by rw [hGateGet D j hj]; exact hi)
    have hwg := wfold_gate D.gates (List.ofFn x) j hj hrb
    rw [List.length_ofFn] at hwg
    have hgi : D.gates[j] = gateAt D j := (hGateGet D j hj).symm
    have hins := (ao_inputs D hD j hj).1
    change ((gateAt D j).op = .and → (D.gates.foldl wstep (List.ofFn x)).getD (14 + j) false = _) ∧
      ((gateAt D j).op = .or → (D.gates.foldl wstep (List.ofFn x)).getD (14 + j) false = _)
    rw [hwg, hgi, hins]
    constructor
    · intro hop; rw [hop]; exact eval_and _ _
    · intro hop; rw [hop]; exact eval_or _ _
  have gate_op_cases : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.gates.length,
      (gateAt D j).op = .and ∨ (gateAt D j).op = .or := by
    intro D hD j hj
    rw [hGateGet D j hj]
    exact hD.1 D.gates[j] (List.getElem_mem hj)
  have and_lt_len : ∀ (D : Circuit) (j : ℕ), (gateAt D j).op = .and → j < D.gates.length := by
    intro D j hj
    by_contra h
    have hge : D.gates.length ≤ j := by omega
    have : gateAt D j = ⟨GateOp.or, []⟩ := List.getD_eq_default _ _ hge
    rw [this] at hj
    cases hj
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons gt rest ih =>
      intro cs
      rw [List.foldl_cons, ih]
      dsimp only [coneStep]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_char : ∀ (D : Circuit) (i j : ℕ),
      InCone 14 D i j ↔
        j < D.gates.length ∧ ∃ w ∈ (gateAt D j).inputs, 14 ≤ w ∧ w < 14 + j ∧
          (i = w - 14 ∨ InCone 14 D i (w - 14)) := by
    intro D
    suffices h : ∀ (gs : List Gate) (i j : ℕ),
        i ∈ (gs.foldl (coneStep 14) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 14 ≤ w ∧ w < 14 + j ∧
            (i = w - 14 ∨ i ∈ (gs.foldl (coneStep 14) []).getD (w - 14) []) by
      exact h D.gates
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs gt ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 14) []).length = gs.length := by
        rw [cones_len]; simp
      have hkeep : ∀ k, k < gs.length →
          (coneStep 14 (gs.foldl (coneStep 14) []) gt).getD k [] =
            (gs.foldl (coneStep 14) []).getD k [] := by
        intro k hk
        dsimp only [coneStep]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with hlt | heq | hgt
      · have eg : (gs ++ [gt]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left hlt]
        rw [hkeep j hlt, ih i j, eg]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [hkeep (w - 14) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨hlt, w, hw, h1, h2, ?_⟩
          rw [hkeep (w - 14) (by omega)] at h3
          exact h3
      · subst heq
        have eg : (gs ++ [gt]).getD gs.length ⟨.or, []⟩ = gt := by
          simp [List.getD_eq_getElem?_getD]
        have ec : (coneStep 14 (gs.foldl (coneStep 14) []) gt).getD gs.length [] =
            (gt.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
              (fun w => (w - 14) :: (gs.foldl (coneStep 14) []).getD (w - 14) []) := by
          dsimp only [coneStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [eg, ec, List.mem_flatMap]
        constructor
        · rintro ⟨w, hw, hm⟩
          rw [List.mem_filter, decide_eq_true_eq] at hw
          refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
          rw [hkeep (w - 14) (by omega)]
          simpa using hm
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, ?_⟩
          rw [hkeep (w - 14) (by omega)] at h3
          simpa using h3
      · have ec : (coneStep 14 (gs.foldl (coneStep 14) []) gt).getD j [] = [] := by
          apply List.getD_eq_default
          dsimp only [coneStep]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [ec]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hj
        simp only [List.length_append, List.length_cons, List.length_nil] at hj
        omega
  have inCone_lt : ∀ (D : Circuit) (i j : ℕ), InCone 14 D i j → i < j ∧ j < D.gates.length := by
    intro D i j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro h
      rw [cones_char] at h
      obtain ⟨hj, w, _, h1, h2, h3 | h3⟩ := h
      · exact ⟨by omega, hj⟩
      · have := (ih (w - 14) (by omega) h3).1
        exact ⟨by omega, hj⟩
  have inCone_trans : ∀ (D : Circuit) (i j k : ℕ),
      InCone 14 D i j → InCone 14 D j k → InCone 14 D i k := by
    intro D i j k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hij hjk
      rw [cones_char] at hjk ⊢
      obtain ⟨hk, w, hw, h1, h2, h3 | h3⟩ := hjk
      · refine ⟨hk, w, hw, h1, h2, Or.inr ?_⟩
        rw [← h3]
        exact hij
      · exact ⟨hk, w, hw, h1, h2, Or.inr (ih (w - 14) (by omega) hij h3)⟩
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons gt rest ih =>
      intro cs
      rw [List.foldl_cons, ih]
      dsimp only [orStep]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orSets_char : ∀ (D : Circuit) (j a : ℕ),
      OrReaches 14 D (14 + j) a ↔
        j < D.gates.length ∧
        (a = j ∨ ((gateAt D j).op = .or ∧
          ∃ w ∈ (gateAt D j).inputs, 14 ≤ w ∧ w < 14 + j ∧ OrReaches 14 D w a)) := by
    intro D
    suffices h : ∀ (gs : List Gate) (j a : ℕ),
        a ∈ (gs.foldl (orStep 14) []).getD j [] ↔
          j < gs.length ∧
          (a = j ∨ ((gs.getD j ⟨.or, []⟩).op = .or ∧
            ∃ w ∈ (gs.getD j ⟨.or, []⟩).inputs, 14 ≤ w ∧ w < 14 + j ∧
              a ∈ (gs.foldl (orStep 14) []).getD (w - 14) [])) by
      intro j a
      have hsub : 14 + j - 14 = j := by omega
      change (14 ≤ 14 + j ∧ a ∈ (orSets 14 D).getD (14 + j - 14) []) ↔ _
      rw [hsub]
      simp only [Nat.le_add_right, true_and]
      unfold orSets
      rw [h D.gates j a]
      constructor
      · rintro ⟨hj, rfl | ⟨hop, w, hw, h1, h2, hm⟩⟩
        · exact ⟨hj, Or.inl rfl⟩
        · exact ⟨hj, Or.inr ⟨hop, w, hw, h1, h2, h1, hm⟩⟩
      · rintro ⟨hj, rfl | ⟨hop, w, hw, h1, h2, _, hm⟩⟩
        · exact ⟨hj, Or.inl rfl⟩
        · exact ⟨hj, Or.inr ⟨hop, w, hw, h1, h2, hm⟩⟩
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro j a; simp
    | append_singleton gs gt ih =>
      intro j a
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 14) []).length = gs.length := by
        rw [orSets_len]; simp
      have hkeep : ∀ k, k < gs.length →
          (orStep 14 (gs.foldl (orStep 14) []) gt).getD k [] =
            (gs.foldl (orStep 14) []).getD k [] := by
        intro k hk
        dsimp only [orStep]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with hlt | heq | hgt
      · have eg : (gs ++ [gt]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left hlt]
        rw [hkeep j hlt, ih j a, eg]
        constructor
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, hm⟩⟩
          · exact ⟨by simp; omega, Or.inl rfl⟩
          · refine ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [hkeep (w - 14) (by omega)]
            exact hm
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, hm⟩⟩
          · exact ⟨hlt, Or.inl rfl⟩
          · refine ⟨hlt, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [hkeep (w - 14) (by omega)] at hm
            exact hm
      · subst heq
        have eg : (gs ++ [gt]).getD gs.length ⟨.or, []⟩ = gt := by
          simp [List.getD_eq_getElem?_getD]
        have eo : (orStep 14 (gs.foldl (orStep 14) []) gt).getD gs.length [] =
            gs.length :: (if gt.op = .or then
              (gt.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
                (fun w => (gs.foldl (orStep 14) []).getD (w - 14) [])
              else []) := by
          dsimp only [orStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [eg, eo, List.mem_cons]
        constructor
        · rintro (rfl | hm)
          · exact ⟨by simp, Or.inl rfl⟩
          · split_ifs at hm with hop
            · rw [List.mem_flatMap] at hm
              obtain ⟨w, hw, hmw⟩ := hm
              rw [List.mem_filter, decide_eq_true_eq] at hw
              refine ⟨by simp, Or.inr ⟨hop, w, hw.1, hw.2.1, hw.2.2, ?_⟩⟩
              rw [hkeep (w - 14) (by omega)]
              exact hmw
            · simp at hm
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, hm⟩⟩
          · exact Or.inl rfl
          · right
            rw [if_pos hop, List.mem_flatMap]
            refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, ?_⟩
            rw [hkeep (w - 14) (by omega)] at hm
            exact hm
      · have eo : (orStep 14 (gs.foldl (orStep 14) []) gt).getD j [] = [] := by
          apply List.getD_eq_default
          dsimp only [orStep]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [eo]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hj
        simp only [List.length_append, List.length_cons, List.length_nil] at hj
        omega
  have orReaches_lt : ∀ (D : Circuit) (w a : ℕ),
      OrReaches 14 D w a → 14 ≤ w ∧ w < 14 + D.gates.length ∧ a ≤ w - 14 ∧ a < D.gates.length := by
    intro D w a
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hr
      have hw14 : 14 ≤ w := hr.1
      have hwEq : 14 + (w - 14) = w := by omega
      rw [← hwEq, orSets_char] at hr
      obtain ⟨hjl, rfl | ⟨_, u, _, hu1, hu2, hru⟩⟩ := hr
      · exact ⟨hw14, by omega, le_refl _, hjl⟩
      · have ihu := ih u (by omega) hru
        exact ⟨hw14, by omega, by omega, ihu.2.2.2⟩
  have orReaches_mono : ∀ (D : Circuit), IsAO2 14 D → ∀ w a : ℕ,
      OrReaches 14 D w a → ∀ x : Fin 14 → Bool,
      wireVal 14 D (14 + a) x = true → wireVal 14 D w x = true := by
    intro D hD w a
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hr x hax
      have hw14 : 14 ≤ w := hr.1
      have hwEq : 14 + (w - 14) = w := by omega
      rw [← hwEq] at hr ⊢
      rw [orSets_char] at hr
      obtain ⟨hjl, rfl | ⟨hop, u, hu, hu1, hu2, hru⟩⟩ := hr
      · exact hax
      · have hux : wireVal 14 D u x = true := ih u (by omega) hru x hax
        have hins := (ao_inputs D hD (w - 14) hjl).1
        rw [hins] at hu
        rw [(wireVal_gate D hD (w - 14) hjl x).2 hop]
        rcases (show u = opnd D (w - 14) 0 ∨ u = opnd D (w - 14) 1 by simpa using hu) with rfl | rfl
        · simp [hux]
        · simp [hux]
  have orReaches_inCone : ∀ (D : Circuit) (j a : ℕ),
      OrReaches 14 D (14 + j) a → a = j ∨ InCone 14 D a j := by
    intro D j a
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hr
      rw [orSets_char] at hr
      obtain ⟨hj, rfl | ⟨_, u, hu, hu1, hu2, hru⟩⟩ := hr
      · exact Or.inl rfl
      · right
        have huEq : 14 + (u - 14) = u := by omega
        rw [← huEq] at hru
        have ihu := ih (u - 14) (by omega) hru
        rw [cones_char]
        exact ⟨hj, u, hu, hu1, hu2, ihu⟩
  let remap : ℕ → ℕ → ℕ → ℕ := fun k w u =>
    if u < 14 + k then u else if u = 14 + k then w else u - 1
  let bypass : Circuit → ℕ → ℕ → Circuit := fun D k w =>
    ⟨(D.gates.eraseIdx k).map (fun gt => ⟨gt.op, gt.inputs.map (remap k w)⟩), remap k w D.output⟩
  have bypass_size : ∀ (D : Circuit) (k w : ℕ), k < D.gates.length →
      (bypass D k w).size = D.size - 1 := by
    intro D k w hk
    change ((D.gates.eraseIdx k).map _).length = D.gates.length - 1
    rw [List.length_map, List.length_eraseIdx_of_lt hk]
  have bypass_gateAt : ∀ (D : Circuit) (k w j : ℕ), k < D.gates.length → j < D.gates.length - 1 →
      gateAt (bypass D k w) j =
        let orig := gateAt D (if j < k then j else j + 1)
        ⟨orig.op, orig.inputs.map (remap k w)⟩ := by
    intro D k w j hk hj
    have hj' : j < (bypass D k w).gates.length := by
      change j < ((D.gates.eraseIdx k).map _).length
      rw [List.length_map, List.length_eraseIdx_of_lt hk]
      exact hj
    rw [hGateGet (bypass D k w) j hj']
    change ((D.gates.eraseIdx k).map (fun gt : Gate => (⟨gt.op, gt.inputs.map (remap k w)⟩ : Gate)))[j]'hj' = _
    rw [List.getElem_map]
    have hje : j < (D.gates.eraseIdx k).length := by rw [List.length_eraseIdx_of_lt hk]; exact hj
    rw [List.getElem_eraseIdx hje]
    split_ifs with hlt
    · rw [hGateGet D j (by omega)]
    · rw [hGateGet D (j + 1) (by omega)]
  have bypass_ao : ∀ (D : Circuit) (k w : ℕ), IsAO2 14 D → k < D.gates.length → w < 14 + k →
      IsAO2 14 (bypass D k w) := by
    intro D k w hD hk hw
    have hlenB : (bypass D k w).gates.length = D.gates.length - 1 := bypass_size D k w hk
    refine ⟨?_, ?_, ?_⟩
    · intro gt hgt
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgt
      rw [← hGateGet (bypass D k w) j hj, bypass_gateAt D k w j hk (by omega)]
      split_ifs with hlt
      · exact gate_op_cases D hD j (by omega)
      · exact gate_op_cases D hD (j + 1) (by omega)
    · intro j hj u hu
      rw [bypass_gateAt D k w j hk (by omega)] at hu
      simp only [List.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      dsimp only [remap]
      split_ifs at hv with hlt
      · have hvlt : v < 14 + j := hD.2.1 j (by omega) v hv
        split_ifs <;> omega
      · have hvlt : v < 14 + (j + 1) := hD.2.1 (j + 1) (by omega) v hv
        split_ifs <;> omega
    · intro gt hgt
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgt
      rw [← hGateGet (bypass D k w) j hj, bypass_gateAt D k w j hk (by omega)]
      simp only [List.length_map]
      split_ifs with hlt
      · rw [hGateGet D j (by omega)]; exact hD.2.2 D.gates[j] (List.getElem_mem (by omega))
      · rw [hGateGet D (j + 1) (by omega)]; exact hD.2.2 D.gates[j + 1] (List.getElem_mem (by omega))
  have bypass_opnd : ∀ (D : Circuit) (k w j : ℕ) (b : Fin 2),
      IsAO2 14 D → k < D.gates.length → j < D.gates.length - 1 →
      opnd (bypass D k w) j b = remap k w (opnd D (if j < k then j else j + 1) b) := by
    intro D k w j b hD hk hj
    unfold opnd
    rw [bypass_gateAt D k w j hk hj]
    have hidx : (if j < k then j else j + 1) < D.gates.length := by split_ifs <;> omega
    have hins := (ao_inputs D hD _ hidx).1
    dsimp only
    rw [hins]
    fin_cases b <;> rfl
  have bypass_eq : ∀ (D : Circuit) (k w : ℕ) (x : Fin 14 → Bool),
      IsAO2 14 D → k < D.gates.length → w < 14 + k →
      wireVal 14 D (14 + k) x = wireVal 14 D w x →
      ∀ u < 14 + D.gates.length,
        wireVal 14 (bypass D k w) (remap k w u) x = wireVal 14 D u x := by
    intro D k w x hD hk hw hkw u
    have hAO' := bypass_ao D k w hD hk hw
    have hlenB : (bypass D k w).gates.length = D.gates.length - 1 := bypass_size D k w hk
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hu14 : u < 14
      · have hru : remap k w u = u := by dsimp only [remap]; rw [if_pos (by omega)]
        rw [hru, wireVal_input _ u hu14 x, wireVal_input _ u hu14 x]
      · set j := u - 14 with hjdef
        have huEq : 14 + j = u := by omega
        have hjlt : j < D.gates.length := by omega
        rw [← huEq]
        by_cases hjk : j = k
        · subst hjk
          have hrk : remap j w (14 + j) = w := by
            dsimp only [remap]; rw [if_neg (by omega), if_pos rfl]
          have hrw : remap j w w = w := by dsimp only [remap]; rw [if_pos hw]
          rw [hrk, hkw]
          have hih := ih w (by omega) (by omega)
          rwa [hrw] at hih
        · set j' := if j < k then j else j - 1 with hj'def
          have hj'lt : j' < D.gates.length - 1 := by dsimp only [j']; split_ifs <;> omega
          have hif : (if j' < k then j' else j' + 1) = j := by dsimp only [j']; split_ifs <;> omega
          have hrj : remap k w (14 + j) = 14 + j' := by
            dsimp only [remap, j']; split_ifs <;> omega
          have hopEq : (gateAt (bypass D k w) j').op = (gateAt D j).op := by
            rw [bypass_gateAt D k w j' hk hj'lt, hif]
          have hop0 : opnd (bypass D k w) j' 0 = remap k w (opnd D j 0) := by
            rw [bypass_opnd D k w j' 0 hD hk hj'lt, hif]
          have hop1 : opnd (bypass D k w) j' 1 = remap k w (opnd D j 1) := by
            rw [bypass_opnd D k w j' 1 hD hk hj'lt, hif]
          have h0lt : opnd D j 0 < 14 + j := (ao_inputs D hD j hjlt).2.1
          have h1lt : opnd D j 1 < 14 + j := (ao_inputs D hD j hjlt).2.2
          have ih0 := ih (opnd D j 0) (by omega) (by omega)
          have ih1 := ih (opnd D j 1) (by omega) (by omega)
          rw [hrj]
          rcases gate_op_cases D hD j hjlt with hop | hop
          · rw [(wireVal_gate (bypass D k w) hAO' j' (by omega) x).1 (hopEq.trans hop),
              (wireVal_gate D hD j hjlt x).1 hop, hop0, hop1, ih0, ih1]
          · rw [(wireVal_gate (bypass D k w) hAO' j' (by omega) x).2 (hopEq.trans hop),
              (wireVal_gate D hD j hjlt x).2 hop, hop0, hop1, ih0, ih1]
  have bypass_mono : ∀ (D : Circuit) (k w : ℕ) (x : Fin 14 → Bool),
      IsAO2 14 D → k < D.gates.length → w < 14 + k →
      (wireVal 14 D (14 + k) x = true → wireVal 14 D w x = true) →
      ∀ u < 14 + D.gates.length,
        wireVal 14 D u x = true → wireVal 14 (bypass D k w) (remap k w u) x = true := by
    intro D k w x hD hk hw hkw u
    have hAO' := bypass_ao D k w hD hk hw
    have hlenB : (bypass D k w).gates.length = D.gates.length - 1 := bypass_size D k w hk
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu hux
      by_cases hu14 : u < 14
      · have hru : remap k w u = u := by dsimp only [remap]; rw [if_pos (by omega)]
        rw [hru, wireVal_input _ u hu14 x]
        rwa [wireVal_input _ u hu14 x] at hux
      · set j := u - 14 with hjdef
        have huEq : 14 + j = u := by omega
        have hjlt : j < D.gates.length := by omega
        rw [← huEq] at hux ⊢
        by_cases hjk : j = k
        · subst hjk
          have hrk : remap j w (14 + j) = w := by
            dsimp only [remap]; rw [if_neg (by omega), if_pos rfl]
          have hrw : remap j w w = w := by dsimp only [remap]; rw [if_pos hw]
          rw [hrk]
          have hih := ih w (by omega) (by omega) (hkw hux)
          rwa [hrw] at hih
        · set j' := if j < k then j else j - 1 with hj'def
          have hj'lt : j' < D.gates.length - 1 := by dsimp only [j']; split_ifs <;> omega
          have hif : (if j' < k then j' else j' + 1) = j := by dsimp only [j']; split_ifs <;> omega
          have hrj : remap k w (14 + j) = 14 + j' := by
            dsimp only [remap, j']; split_ifs <;> omega
          have hopEq : (gateAt (bypass D k w) j').op = (gateAt D j).op := by
            rw [bypass_gateAt D k w j' hk hj'lt, hif]
          have hop0 : opnd (bypass D k w) j' 0 = remap k w (opnd D j 0) := by
            rw [bypass_opnd D k w j' 0 hD hk hj'lt, hif]
          have hop1 : opnd (bypass D k w) j' 1 = remap k w (opnd D j 1) := by
            rw [bypass_opnd D k w j' 1 hD hk hj'lt, hif]
          have h0lt : opnd D j 0 < 14 + j := (ao_inputs D hD j hjlt).2.1
          have h1lt : opnd D j 1 < 14 + j := (ao_inputs D hD j hjlt).2.2
          rw [hrj]
          rcases gate_op_cases D hD j hjlt with hop | hop
          · rw [(wireVal_gate D hD j hjlt x).1 hop, Bool.and_eq_true] at hux
            rw [(wireVal_gate (bypass D k w) hAO' j' (by omega) x).1 (hopEq.trans hop),
              hop0, hop1, Bool.and_eq_true]
            exact ⟨ih _ (by omega) (by omega) hux.1, ih _ (by omega) (by omega) hux.2⟩
          · rw [(wireVal_gate D hD j hjlt x).2 hop, Bool.or_eq_true] at hux
            rw [(wireVal_gate (bypass D k w) hAO' j' (by omega) x).2 (hopEq.trans hop),
              hop0, hop1, Bool.or_eq_true]
            rcases hux with h0 | h1
            · exact Or.inl (ih _ (by omega) (by omega) h0)
            · exact Or.inr (ih _ (by omega) (by omega) h1)
  have hOutLt : C.output < 14 + C.gates.length := by
    by_contra h
    have hge : 14 + C.gates.length ≤ C.output := by omega
    have h07 : F (pairInput (0 : Fin 14) 7) := ⟨0, 0, (hFanoGeom 0 0).mpr (Or.inl rfl),
      by decide, by decide⟩
    have htr : C.eval (List.ofFn (pairInput (0 : Fin 14) 7)) = true := (hEvalF _).mpr h07
    have hfl : wireVal 14 C C.output (pairInput (0 : Fin 14) 7) = false :=
      wireVal_ge C C.output hge _
    exact Bool.false_ne_true (hfl.symm.trans htr)
  have hOutGe : 14 ≤ C.output := by
    by_contra h
    have hlt : C.output < 14 := by omega
    let i : Fin 14 := ⟨C.output, hlt⟩
    have htr : C.eval (List.ofFn (pairInput i i)) = true := by
      change wireVal 14 C C.output (pairInput i i) = true
      rw [wireVal_input C C.output hlt]
      dsimp only [pairInput, i]
      simp
    obtain ⟨p, l, _, hp, hl⟩ := (hEvalF _).mp htr
    dsimp only [pairInput] at hp hl
    simp only [decide_eq_true_eq, or_self] at hp hl
    have heq := hp.trans hl.symm
    have hval := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  let B : ℕ → Prop := fun w => ∀ x : Fin 14 → Bool, wireVal 14 C w x = true → F x
  have hNoAndBelow : ∀ j < 27, (gateAt C j).op = .and → ∀ b : Fin 2, ¬ B (opnd C j b) := by
    intro j hj hjAnd b hbBelow
    have hjlt : j < C.gates.length := by omega
    set w := opnd C j b
    have hwlt : w < 14 + j := by
      fin_cases b
      · exact (ao_inputs C hAO j hjlt).2.1
      · exact (ao_inputs C hAO j hjlt).2.2
    let C' := bypass C j w
    have hAO' : IsAO2 14 C' := bypass_ao C j w hAO hjlt hwlt
    have hEval' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔ F x := by
      intro x
      constructor
      · intro htr
        by_contra hnf
        have hwf : wireVal 14 C w x = false := by
          rcases Bool.eq_false_or_eq_true (wireVal 14 C w x) with h | h
          · exact False.elim (hnf (hbBelow x h))
          · exact h
        have hkf : wireVal 14 C (14 + j) x = false := by
          rw [(wireVal_gate C hAO j hjlt x).1 hjAnd]
          fin_cases b
          · change (wireVal 14 C w x && _) = false; rw [hwf]; rfl
          · change (_ && wireVal 14 C w x) = false; rw [hwf]; simp
        have heq := bypass_eq C j w x hAO hjlt hwlt (hkf.trans hwf.symm) C.output hOutLt
        have hcf : wireVal 14 C C.output x = false := by
          rcases Bool.eq_false_or_eq_true (wireVal 14 C C.output x) with h | h
          · exact False.elim (hnf ((hEvalF x).mp h))
          · exact h
        change wireVal 14 C' (remap j w C.output) x = true at htr
        rw [heq, hcf] at htr
        exact Bool.false_ne_true htr
      · intro hfx
        have hkw : wireVal 14 C (14 + j) x = true → wireVal 14 C w x = true := by
          intro htr
          rw [(wireVal_gate C hAO j hjlt x).1 hjAnd, Bool.and_eq_true] at htr
          fin_cases b
          · exact htr.1
          · exact htr.2
        exact bypass_mono C j w x hAO hjlt hwlt hkw C.output hOutLt ((hEvalF x).mpr hfx)
    have hsz := size27 C' hAO' hEval'
    have hsz' : C'.size = 26 := by rw [bypass_size C j w hjlt, hSizeEq]
    omega
  have hLive : ∀ j < 27, 14 + j = C.output ∨ InCone 14 C j (C.output - 14) := by
    intro j hj
    by_contra hdead
    push_neg at hdead
    obtain ⟨hne, hnc⟩ := hdead
    have hjlt : j < C.gates.length := by omega
    let C' := bypass C j 0
    have hAO' : IsAO2 14 C' := bypass_ao C j 0 hAO hjlt (by omega)
    have hAgree : ∀ x : Fin 14 → Bool, ∀ u < 14 + C.gates.length,
        (u < 14 ∨ (14 ≤ u ∧ u ≠ 14 + j ∧ ¬ InCone 14 C j (u - 14))) →
        wireVal 14 C' (remap j 0 u) x = wireVal 14 C u x := by
      intro x u
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        intro hu hok
        rcases hok with hu14 | ⟨hu14, hunj, hunc⟩
        · have hru : remap j 0 u = u := by dsimp only [remap]; rw [if_pos (by omega)]
          rw [hru, wireVal_input _ u hu14 x, wireVal_input _ u hu14 x]
        · set k := u - 14
          have huEq : 14 + k = u := by omega
          have hklt : k < C.gates.length := by omega
          have hknj : k ≠ j := by omega
          set k' := if k < j then k else k - 1
          have hk'lt : k' < C.gates.length - 1 := by dsimp only [k']; split_ifs <;> omega
          have hif : (if k' < j then k' else k' + 1) = k := by dsimp only [k']; split_ifs <;> omega
          have hrk : remap j 0 (14 + k) = 14 + k' := by dsimp only [remap, k']; split_ifs <;> omega
          have hopEq : (gateAt C' k').op = (gateAt C k).op := by
            rw [bypass_gateAt C j 0 k' hjlt hk'lt, hif]
          have hop0 : opnd C' k' 0 = remap j 0 (opnd C k 0) := by
            rw [bypass_opnd C j 0 k' 0 hAO hjlt hk'lt, hif]
          have hop1 : opnd C' k' 1 = remap j 0 (opnd C k 1) := by
            rw [bypass_opnd C j 0 k' 1 hAO hjlt hk'lt, hif]
          have hokOp : ∀ b : Fin 2, opnd C k b < 14 ∨
              (14 ≤ opnd C k b ∧ opnd C k b ≠ 14 + j ∧ ¬ InCone 14 C j (opnd C k b - 14)) := by
            intro b
            by_cases hb14 : opnd C k b < 14
            · exact Or.inl hb14
            · right
              have hmem : opnd C k b ∈ (gateAt C k).inputs := by
                rw [(ao_inputs C hAO k hklt).1]; fin_cases b <;> simp
              have hblt : opnd C k b < 14 + k := by
                fin_cases b
                · exact (ao_inputs C hAO k hklt).2.1
                · exact (ao_inputs C hAO k hklt).2.2
              refine ⟨by omega, ?_, ?_⟩
              · intro heq
                apply hunc
                rw [cones_char]
                exact ⟨hklt, opnd C k b, hmem, by omega, hblt, Or.inl (by omega)⟩
              · intro hic
                apply hunc
                rw [cones_char]
                exact ⟨hklt, opnd C k b, hmem, by omega, hblt, Or.inr hic⟩
          have h0lt : opnd C k 0 < 14 + k := (ao_inputs C hAO k hklt).2.1
          have h1lt : opnd C k 1 < 14 + k := (ao_inputs C hAO k hklt).2.2
          have ih0 := ih (opnd C k 0) (by omega) (by omega) (hokOp 0)
          have ih1 := ih (opnd C k 1) (by omega) (by omega) (hokOp 1)
          rw [← huEq, hrk]
          have hlenB : C'.gates.length = C.gates.length - 1 := bypass_size C j 0 hjlt
          rcases gate_op_cases C hAO k hklt with hop | hop
          · rw [(wireVal_gate C' hAO' k' (by omega) x).1 (hopEq.trans hop),
              (wireVal_gate C hAO k hklt x).1 hop, hop0, hop1, ih0, ih1]
          · rw [(wireVal_gate C' hAO' k' (by omega) x).2 (hopEq.trans hop),
              (wireVal_gate C hAO k hklt x).2 hop, hop0, hop1, ih0, ih1]
    have hEval' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔ F x := by
      intro x
      change wireVal 14 C' (remap j 0 C.output) x = true ↔ F x
      rw [hAgree x C.output hOutLt (Or.inr ⟨hOutGe, Ne.symm hne, hnc⟩)]
      exact hEvalF x
    have hsz := size27 C' hAO' hEval'
    have hsz' : C'.size = 26 := by rw [bypass_size C j 0 hjlt, hSizeEq]
    omega
  have hFanout : ∀ j < 27, B (14 + j) → (readers 14 C j).card ≤ 1 := by
    intro a ha haB
    by_contra hgt1
    have hlt : 1 < (readers 14 C a).card := by omega
    obtain ⟨r1, hr1, r2, hr2, hrne⟩ := Finset.one_lt_card.mp hlt
    have hpair : ∃ h1 h2 : ℕ, h1 ∈ readers 14 C a ∧ h2 ∈ readers 14 C a ∧ h1 < h2 := by
      rcases Nat.lt_or_gt_of_ne hrne with h | h
      · exact ⟨r1, r2, hr1, hr2, h⟩
      · exact ⟨r2, r1, hr2, hr1, h⟩
    obtain ⟨h1, h2, hh1, hh2, h12⟩ := hpair
    dsimp only [readers] at hh1 hh2
    simp only [Finset.mem_filter, Finset.mem_range] at hh1 hh2
    obtain ⟨hh1lt, hh1mem⟩ := hh1
    obtain ⟨hh2lt, hh2mem⟩ := hh2
    have ha_lt_h1 : a < h1 := by
      have := hAO.2.1 h1 hh1lt (14 + a) hh1mem
      omega
    have hOr1 : (gateAt C h1).op = .or := by
      rcases gate_op_cases C hAO h1 hh1lt with hop | hop
      · rw [(ao_inputs C hAO h1 hh1lt).1] at hh1mem
        rcases (show 14 + a = opnd C h1 0 ∨ 14 + a = opnd C h1 1 by simpa using hh1mem) with h | h
        · exact False.elim (hNoAndBelow h1 (by omega) hop 0 (h ▸ haB))
        · exact False.elim (hNoAndBelow h1 (by omega) hop 1 (h ▸ haB))
      · exact hop
    have hOr2 : (gateAt C h2).op = .or := by
      rcases gate_op_cases C hAO h2 hh2lt with hop | hop
      · rw [(ao_inputs C hAO h2 hh2lt).1] at hh2mem
        rcases (show 14 + a = opnd C h2 0 ∨ 14 + a = opnd C h2 1 by simpa using hh2mem) with h | h
        · exact False.elim (hNoAndBelow h2 (by omega) hop 0 (h ▸ haB))
        · exact False.elim (hNoAndBelow h2 (by omega) hop 1 (h ▸ haB))
      · exact hop
    have getOther : ∀ h < C.gates.length, 14 + a ∈ (gateAt C h).inputs →
        ∃ w, w < 14 + h ∧
          ((opnd C h 0 = 14 + a ∧ opnd C h 1 = w) ∨ (opnd C h 1 = 14 + a ∧ opnd C h 0 = w)) := by
      intro h hh hmem
      rw [(ao_inputs C hAO h hh).1] at hmem
      rcases (show 14 + a = opnd C h 0 ∨ 14 + a = opnd C h 1 by simpa using hmem) with heq | heq
      · exact ⟨opnd C h 1, (ao_inputs C hAO h hh).2.2, Or.inl ⟨heq.symm, rfl⟩⟩
      · exact ⟨opnd C h 0, (ao_inputs C hAO h hh).2.1, Or.inr ⟨heq.symm, rfl⟩⟩
    obtain ⟨w1, hw1lt, hw1⟩ := getOther h1 hh1lt hh1mem
    obtain ⟨w2, hw2lt, hw2⟩ := getOther h2 hh2lt hh2mem
    let C1 := bypass C h2 w2
    have hAO1 : IsAO2 14 C1 := bypass_ao C h2 w2 hAO hh2lt hw2lt
    have hlen1 : C1.gates.length = C.gates.length - 1 := bypass_size C h2 w2 hh2lt
    have hh1lt1 : h1 < C1.gates.length := by omega
    have hw1lt1 : w1 < 14 + h1 := hw1lt
    let C2 := bypass C1 h1 w1
    have hAO2 : IsAO2 14 C2 := bypass_ao C1 h1 w1 hAO1 hh1lt1 hw1lt1
    have hlen2 : C2.gates.length = C.gates.length - 2 := by
      have hsz2 : C2.size = C1.size - 1 := bypass_size C1 h1 w1 hh1lt1
      change C2.gates.length = C1.gates.length - 1 at hsz2
      omega
    have hOut1Lt : C1.output < 14 + C1.gates.length := by
      change remap h2 w2 C.output < 14 + C1.gates.length
      dsimp only [remap]; split_ifs <;> omega
    have hOut2Lt : C2.output < 14 + C2.gates.length := by
      change remap h1 w1 C1.output < 14 + C2.gates.length
      dsimp only [remap]; split_ifs <;> omega
    have haLt2 : 14 + a < 14 + C2.gates.length := by omega
    let C3 : Circuit := ⟨C2.gates ++ [⟨.or, [C2.output, 14 + a]⟩], 14 + C2.gates.length⟩
    have hAO3 : IsAO2 14 C3 := by
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [C3, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with h | rfl
        · exact hAO2.1 gt h
        · exact Or.inr rfl
      · intro j hj u hu
        simp only [C3, List.length_append, List.length_cons, List.length_nil] at hj
        by_cases hltj : j < C2.gates.length
        · have hg3 : gateAt C3 j = gateAt C2 j := by
            dsimp only [gateAt, C3]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left hltj]
          rw [hg3] at hu
          exact hAO2.2.1 j hltj u hu
        · have hjeq : j = C2.gates.length := by omega
          subst hjeq
          have hg3 : gateAt C3 C2.gates.length = ⟨.or, [C2.output, 14 + a]⟩ := by
            dsimp only [gateAt, C3]
            simp [List.getD_eq_getElem?_getD]
          rw [hg3] at hu
          rcases (show u = C2.output ∨ u = 14 + a by simpa using hu) with rfl | rfl
          · exact hOut2Lt
          · exact haLt2
      · intro gt hgt
        simp only [C3, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with h | rfl
        · exact hAO2.2.2 gt h
        · rfl
    have hPreEq : ∀ (D : Circuit) (k w u : ℕ) (x : Fin 14 → Bool),
        IsAO2 14 D → k < D.gates.length → w < 14 + k → u < 14 + k →
        wireVal 14 (bypass D k w) u x = wireVal 14 D u x := by
      intro D k w u x hD hk hw hu
      have hAO' := bypass_ao D k w hD hk hw
      have hlenB : (bypass D k w).gates.length = D.gates.length - 1 := bypass_size D k w hk
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        by_cases hu14 : u < 14
        · rw [wireVal_input _ u hu14 x, wireVal_input _ u hu14 x]
        · set j := u - 14
          have huEq : 14 + j = u := by omega
          have hjk : j < k := by omega
          have hjlt : j < D.gates.length := by omega
          have hj'lt : j < D.gates.length - 1 := by omega
          have hopEq : (gateAt (bypass D k w) j).op = (gateAt D j).op := by
            rw [bypass_gateAt D k w j hk hj'lt, if_pos hjk]
          have h0lt : opnd D j 0 < 14 + j := (ao_inputs D hD j hjlt).2.1
          have h1lt : opnd D j 1 < 14 + j := (ao_inputs D hD j hjlt).2.2
          have hop0 : opnd (bypass D k w) j 0 = opnd D j 0 := by
            rw [bypass_opnd D k w j 0 hD hk hj'lt, if_pos hjk]
            dsimp only [remap]; rw [if_pos (by omega)]
          have hop1 : opnd (bypass D k w) j 1 = opnd D j 1 := by
            rw [bypass_opnd D k w j 1 hD hk hj'lt, if_pos hjk]
            dsimp only [remap]; rw [if_pos (by omega)]
          rw [← huEq]
          rcases gate_op_cases D hD j hjlt with hop | hop
          · rw [(wireVal_gate (bypass D k w) hAO' j (by omega) x).1 (hopEq.trans hop),
              (wireVal_gate D hD j hjlt x).1 hop, hop0, hop1,
              ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
          · rw [(wireVal_gate (bypass D k w) hAO' j (by omega) x).2 (hopEq.trans hop),
              (wireVal_gate D hD j hjlt x).2 hop, hop0, hop1,
              ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
    have hEval3 : ∀ x : Fin 14 → Bool, C3.eval (List.ofFn x) = true ↔ F x := by
      intro x
      have hC3val : C3.eval (List.ofFn x) =
          (wireVal 14 C2 C2.output x || wireVal 14 C2 (14 + a) x) := by
        change wireVal 14 C3 (14 + C2.gates.length) x = _
        have hlen3 : C3.gates.length = C2.gates.length + 1 := by
          simp [C3]
        have hg3 : gateAt C3 C2.gates.length = ⟨.or, [C2.output, 14 + a]⟩ := by
          dsimp only [gateAt, C3]
          simp [List.getD_eq_getElem?_getD]
        have hop3 : (gateAt C3 C2.gates.length).op = .or := by rw [hg3]
        have ho0 : opnd C3 C2.gates.length 0 = C2.output := by
          unfold opnd; rw [hg3]; rfl
        have ho1 : opnd C3 C2.gates.length 1 = 14 + a := by
          unfold opnd; rw [hg3]; rfl
        rw [(wireVal_gate C3 hAO3 C2.gates.length (by omega) x).2 hop3, ho0, ho1]
        have hkeep3 : ∀ u, u < 14 + C2.gates.length → wireVal 14 C3 u x = wireVal 14 C2 u x := by
          intro u hu
          change (C3.gates.foldl wstep (List.ofFn x)).getD u false =
            (C2.gates.foldl wstep (List.ofFn x)).getD u false
          dsimp only [C3]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlen2w : (C2.gates.foldl wstep (List.ofFn x)).length = 14 + C2.gates.length := by
            rw [wfold_len, List.length_ofFn]
          change ((C2.gates.foldl wstep (List.ofFn x)) ++ [_]).getD u false = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rw [hkeep3 C2.output hOut2Lt, hkeep3 (14 + a) haLt2]
      have haEq2 : wireVal 14 C2 (14 + a) x = wireVal 14 C (14 + a) x := by
        rw [hPreEq C1 h1 w1 (14 + a) x hAO1 hh1lt1 hw1lt1 (by omega),
          hPreEq C h2 w2 (14 + a) x hAO hh2lt hw2lt (by omega)]
      rw [hC3val, haEq2]
      by_cases havt : wireVal 14 C (14 + a) x = true
      · rw [havt, Bool.or_true]
        exact ⟨fun _ => haB x havt, fun _ => rfl⟩
      · have hav : wireVal 14 C (14 + a) x = false := Bool.eq_false_iff.mpr havt
        rw [hav, Bool.or_false]
        have hh2eq : wireVal 14 C (14 + h2) x = wireVal 14 C w2 x := by
          rw [(wireVal_gate C hAO h2 hh2lt x).2 hOr2]
          rcases hw2 with ⟨p0, p1⟩ | ⟨p1, p0⟩
          · rw [p0, p1, hav]; rfl
          · rw [p0, p1, hav]; simp
        have h1eq : wireVal 14 C1 C1.output x = wireVal 14 C C.output x :=
          bypass_eq C h2 w2 x hAO hh2lt hw2lt hh2eq C.output hOutLt
        have hh1eq : wireVal 14 C1 (14 + h1) x = wireVal 14 C1 w1 x := by
          have hop1eq : (gateAt C1 h1).op = .or := by
            rw [bypass_gateAt C h2 w2 h1 hh2lt (by omega), if_pos h12]; exact hOr1
          have ho10 : opnd C1 h1 0 = opnd C h1 0 := by
            rw [bypass_opnd C h2 w2 h1 0 hAO hh2lt (by omega), if_pos h12]
            dsimp only [remap]; rw [if_pos (by have := (ao_inputs C hAO h1 hh1lt).2.1; omega)]
          have ho11 : opnd C1 h1 1 = opnd C h1 1 := by
            rw [bypass_opnd C h2 w2 h1 1 hAO hh2lt (by omega), if_pos h12]
            dsimp only [remap]; rw [if_pos (by have := (ao_inputs C hAO h1 hh1lt).2.2; omega)]
          rw [(wireVal_gate C1 hAO1 h1 hh1lt1 x).2 hop1eq, ho10, ho11]
          have ha1f : wireVal 14 C1 (14 + a) x = false := by
            rw [hPreEq C h2 w2 (14 + a) x hAO hh2lt hw2lt (by omega)]; exact hav
          rcases hw1 with ⟨p0, p1⟩ | ⟨p1, p0⟩
          · rw [p0, p1, ha1f]; rfl
          · rw [p0, p1, ha1f]; simp
        have h2eq : wireVal 14 C2 C2.output x = wireVal 14 C1 C1.output x :=
          bypass_eq C1 h1 w1 x hAO1 hh1lt1 hw1lt1 hh1eq C1.output hOut1Lt
        rw [h2eq, h1eq]
        exact hEvalF x
    have hsz := size27 C3 hAO3 hEval3
    have hsz3 : C3.size = 26 := by
      change (C2.gates ++ [(⟨.or, [C2.output, 14 + a]⟩ : Gate)]).length = 26
      rw [List.length_append, List.length_singleton, hlen2, hLenEq]
    omega
  let M : ℕ → Prop := fun w =>
    wireVal 14 C w (pairInput (0 : Fin 14) 7) = true ∧
    wireVal 14 C w (pairInput (0 : Fin 14) 0) = false ∧
    wireVal 14 C w (pairInput (7 : Fin 14) 7) = false
  have hglt : g < C.gates.length := and_lt_len C g hgAnd
  have hgVal07 : wireVal 14 C (14 + g) (pairInput (0 : Fin 14) 7) = true := hgVal
  rw [(wireVal_gate C hAO g hglt _).1 hgAnd, Bool.and_eq_true] at hgVal07
  have hM0 : M (opnd C g 0) := ⟨hgVal07.1, (hgOpnds 0).1, (hgOpnds 0).2⟩
  have hM1 : M (opnd C g 1) := ⟨hgVal07.2, (hgOpnds 1).1, (hgOpnds 1).2⟩
  have findMarkedAnd : ∀ w < 14 + C.gates.length, M w →
      ∃ a : ℕ, (gateAt C a).op = .and ∧ M (14 + a) ∧ OrReaches 14 C w a := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwlt hMw
      have h07 := hMw.1
      have h00 := hMw.2.1
      have h77 := hMw.2.2
      by_cases hw14 : w < 14
      · rw [wireVal_input C w hw14] at h07 h00 h77
        dsimp only [pairInput] at h07 h00 h77
        simp only [decide_eq_true_eq, decide_eq_false_iff_not, or_self] at h07 h00 h77
        rcases h07 with h | h
        · exact False.elim (h00 h)
        · exact False.elim (h77 h)
      · set k := w - 14
        have hwEq : 14 + k = w := by omega
        have hklt : k < C.gates.length := by omega
        rw [← hwEq] at h07 h00 h77 ⊢
        rcases gate_op_cases C hAO k hklt with hop | hop
        · refine ⟨k, hop, ⟨h07, h00, h77⟩, ?_⟩
          rw [orSets_char]
          exact ⟨hklt, Or.inl rfl⟩
        · rw [(wireVal_gate C hAO k hklt _).2 hop, Bool.or_eq_true] at h07
          rw [(wireVal_gate C hAO k hklt _).2 hop, Bool.or_eq_false_iff] at h00 h77
          rcases h07 with h0 | h1
          · have h0lt : opnd C k 0 < 14 + k := (ao_inputs C hAO k hklt).2.1
            obtain ⟨a, haAnd, haM, haR⟩ := ih (opnd C k 0) (by omega) (by omega) ⟨h0, h00.1, h77.1⟩
            refine ⟨a, haAnd, haM, ?_⟩
            rw [orSets_char]
            refine ⟨hklt, Or.inr ⟨hop, opnd C k 0, ?_, haR.1, h0lt, haR⟩⟩
            rw [(ao_inputs C hAO k hklt).1]; simp
          · have h1lt : opnd C k 1 < 14 + k := (ao_inputs C hAO k hklt).2.2
            obtain ⟨a, haAnd, haM, haR⟩ := ih (opnd C k 1) (by omega) (by omega) ⟨h1, h00.2, h77.2⟩
            refine ⟨a, haAnd, haM, ?_⟩
            rw [orSets_char]
            refine ⟨hklt, Or.inr ⟨hop, opnd C k 1, ?_, haR.1, h1lt, haR⟩⟩
            rw [(ao_inputs C hAO k hklt).1]; simp
  have hOp0Lt : opnd C g 0 < 14 + g := (ao_inputs C hAO g hglt).2.1
  have hOp1Lt : opnd C g 1 < 14 + g := (ao_inputs C hAO g hglt).2.2
  obtain ⟨a0, ha0And, ha0M, ha0R⟩ := findMarkedAnd (opnd C g 0) (by omega) hM0
  obtain ⟨a1, ha1And, ha1M, ha1R⟩ := findMarkedAnd (opnd C g 1) (by omega) hM1
  by_cases hgB : B (14 + g)
  · have haNe : a0 ≠ a1 := by
      intro heq
      subst heq
      have hMax : ∀ n : ℕ, (∃ k < n, OrReaches 14 C (opnd C g 0) k ∧ OrReaches 14 C (opnd C g 1) k) →
          ∃ m < n, OrReaches 14 C (opnd C g 0) m ∧ OrReaches 14 C (opnd C g 1) m ∧
            ∀ j < n, OrReaches 14 C (opnd C g 0) j → OrReaches 14 C (opnd C g 1) j → j ≤ m := by
        intro n
        induction n with
        | zero => rintro ⟨k, hk, _⟩; omega
        | succ n ih =>
          intro hex
          by_cases htop : OrReaches 14 C (opnd C g 0) n ∧ OrReaches 14 C (opnd C g 1) n
          · refine ⟨n, Nat.lt_succ_self n, htop.1, htop.2, fun j hj _ _ => by omega⟩
          · have hex' : ∃ k < n, OrReaches 14 C (opnd C g 0) k ∧ OrReaches 14 C (opnd C g 1) k := by
              obtain ⟨k, hk, h0, h1⟩ := hex
              by_cases hkn : k = n
              · subst hkn; exact False.elim (htop ⟨h0, h1⟩)
              · exact ⟨k, by omega, h0, h1⟩
            obtain ⟨m, hm, hm0, hm1, hmax⟩ := ih hex'
            refine ⟨m, by omega, hm0, hm1, fun j hj hj0 hj1 => ?_⟩
            by_cases hjn : j = n
            · subst hjn; exact False.elim (htop ⟨hj0, hj1⟩)
            · exact hmax j (by omega) hj0 hj1
      have ha0lt : a0 < 27 := by have := (orReaches_lt C _ a0 ha0R).2.2.2; omega
      obtain ⟨m, hmlt, hm0, hm1, hmMax⟩ := hMax 27 ⟨a0, ha0lt, ha0R, ha1R⟩
      have hmB : B (14 + m) := by
        intro x hmx
        have h0x := orReaches_mono C hAO (opnd C g 0) m hm0 x hmx
        have h1x := orReaches_mono C hAO (opnd C g 1) m hm1 x hmx
        have hgx : wireVal 14 C (14 + g) x = true := by
          rw [(wireVal_gate C hAO g hglt x).1 hgAnd, h0x, h1x]; rfl
        exact hgB x hgx
      have hStep : ∀ w : ℕ, OrReaches 14 C w m →
          w = 14 + m ∨ ∃ r < 27, r ∈ readers 14 C m ∧ OrReaches 14 C w r := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hr
          have hw14 := hr.1
          have hwEq : 14 + (w - 14) = w := by omega
          rw [← hwEq, orSets_char] at hr
          obtain ⟨hjl, heqm | ⟨hop, u, hu, hu1, hu2, hru⟩⟩ := hr
          · left; omega
          · right
            rcases ih u (by omega) hru with rfl | ⟨r, hrlt, hrMem, hrR⟩
            · refine ⟨w - 14, by omega, ?_, ?_⟩
              · dsimp only [readers]
                simp only [Finset.mem_filter, Finset.mem_range]
                exact ⟨hjl, hu⟩
              · rw [← hwEq, orSets_char]
                exact ⟨hjl, Or.inl (by omega)⟩
            · refine ⟨r, hrlt, hrMem, ?_⟩
              rw [← hwEq, orSets_char]
              exact ⟨hjl, Or.inr ⟨hop, u, hu, hu1, hu2, hrR⟩⟩
      rcases hStep (opnd C g 0) hm0 with h0eq | ⟨r0, hr0lt, hr0Mem, hr0R⟩
      · exact hNoAndBelow g (by omega) hgAnd 0 (h0eq.symm ▸ hmB)
      · rcases hStep (opnd C g 1) hm1 with h1eq | ⟨r1, hr1lt, hr1Mem, hr1R⟩
        · exact hNoAndBelow g (by omega) hgAnd 1 (h1eq.symm ▸ hmB)
        · have hr0gt : m < r0 := by
            dsimp only [readers] at hr0Mem
            simp only [Finset.mem_filter, Finset.mem_range] at hr0Mem
            have := hAO.2.1 r0 hr0Mem.1 (14 + m) hr0Mem.2
            omega
          have hrne : r0 ≠ r1 := by
            intro hreq
            subst hreq
            have hle := hmMax r0 hr0lt hr0R hr1R
            omega
          have hcard : 2 ≤ (readers 14 C m).card := by
            have h1lt : 1 < (readers 14 C m).card :=
              Finset.one_lt_card.mpr ⟨r0, hr0Mem, r1, hr1Mem, hrne⟩
            omega
          have hle1 := hFanout m hmlt hmB
          omega
    exact cleanG C hSizeEq hAO hDistinct hEvalF hLive hNoAndBelow hFanout g a0 a1
      hgAnd hgB hgCone hM0 hM1 ha0And ha1And haNe ha0M ha1M ha0R ha1R
  · have hFindH : ∀ k < C.gates.length, InCone 14 C g k →
        OrReaches 14 C (14 + k) g ∨
        ∃ h : ℕ, (gateAt C h).op = .and ∧ (h = k ∨ InCone 14 C h k) ∧
          ∃ b : Fin 2, OrReaches 14 C (opnd C h b) g := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hklt hgk
        rw [cones_char] at hgk
        obtain ⟨_, w, hw, hw14, hwlt, hwg⟩ := hgk
        have hins := (ao_inputs C hAO k hklt).1
        rw [hins] at hw
        have hb : ∃ b : Fin 2, opnd C k b = w := by
          rcases (show w = opnd C k 0 ∨ w = opnd C k 1 by simpa using hw) with rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
        obtain ⟨b, hbEq⟩ := hb
        set j := w - 14
        have hwEq : 14 + j = w := by omega
        have hjlt : j < C.gates.length := by omega
        have hSub : OrReaches 14 C w g ∨
            ∃ h : ℕ, (gateAt C h).op = .and ∧ (h = j ∨ InCone 14 C h j) ∧
              ∃ b' : Fin 2, OrReaches 14 C (opnd C h b') g := by
          rcases hwg with h | h
          · left
            rw [← hwEq, ← h, orSets_char]
            exact ⟨hglt, Or.inl rfl⟩
          · rw [← hwEq]
            exact ih j (by omega) hjlt h
        rcases hSub with hRg | ⟨h, hhAnd, hhJ, hhR⟩
        · rcases gate_op_cases C hAO k hklt with hop | hop
          · right
            exact ⟨k, hop, Or.inl rfl, b, hbEq.symm ▸ hRg⟩
          · left
            rw [orSets_char]
            exact ⟨hklt, Or.inr ⟨hop, w, by rw [hins]; exact hw, hw14, hwlt, hRg⟩⟩
        · right
          refine ⟨h, hhAnd, Or.inr ?_, hhR⟩
          rw [cones_char]
          exact ⟨hklt, w, by rw [hins]; exact hw, hw14, hwlt, hhJ⟩
    have houtLt : C.output - 14 < C.gates.length := by omega
    rcases hFindH (C.output - 14) houtLt hgCone with hOrOut | ⟨h, hhAnd, hhCone, hhR⟩
    · exfalso
      apply hgB
      intro x hgx
      have hEqOut : 14 + (C.output - 14) = C.output := by omega
      rw [hEqOut] at hOrOut
      exact (hEvalF x).mp (orReaches_mono C hAO C.output g hOrOut x hgx)
    · have hhOut : 14 + h = C.output ∨ InCone 14 C h (C.output - 14) := by
        rcases hhCone with heq | hic
        · left; omega
        · right; exact hic
      exact dirtyG C hSizeEq hAO hDistinct hEvalF hLive hNoAndBelow hFanout g a0 a1 h
        hgAnd hgB hM0 hM1 ha0And ha1And ha0M ha1M ha0R ha1R hhAnd hhOut hhR
