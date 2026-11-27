import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1967_1
    (hClean : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      let ic := PEqualNP.EdgeOwnership.InCone 14 C
      let gv := PEqualNP.EdgeOwnership.gateVal 14 C
      let wv := PEqualNP.CleanedNonEdge.wireVal 14 C
      let p07 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
      let p00 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0
      let p77 := PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k0 k1 k2 : ℕ, ic k0 k1 ∧ ic k1 k2 ∧
        (14 + k2 = C.output ∨ ic k2 (C.output - 14)) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        gv k0 p07 = true ∧ gv k0 p00 = false ∧ gv k0 p77 = false ∧
        gv k1 p07 = true ∧ gv k1 p77 = false ∧ (∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k1 b) p00 = false) ∧
        gv k2 p07 = true ∧ ∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k2 b) p77 = false)
    (hDirtyClean : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      let ic := PEqualNP.EdgeOwnership.InCone 14 C
      let gv := PEqualNP.EdgeOwnership.gateVal 14 C
      let wv := PEqualNP.CleanedNonEdge.wireVal 14 C
      let p07 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
      let p00 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0
      let p77 := PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k1 m k2 : ℕ, ic k1 m ∧ ic m k2 ∧
        (14 + k2 = C.output ∨ ic k2 (C.output - 14)) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        gv k1 p07 = true ∧ gv k1 p77 = true ∧ (∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k1 b) p00 = false) ∧
        gv m p77 = false ∧
        gv k2 p07 = true ∧ gv k2 p00 = false ∧ ∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k2 b) p77 = false)
    (hFourChain : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      let ic := PEqualNP.EdgeOwnership.InCone 14 C
      let gv := PEqualNP.EdgeOwnership.gateVal 14 C
      let wv := PEqualNP.CleanedNonEdge.wireVal 14 C
      let p07 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
      let p00 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0
      let p77 := PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7
      let isAnd := fun k =>
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k1 m k2 k3 : ℕ, ic k1 m ∧ ic m k2 ∧ ic k2 k3 ∧
        (14 + k3 = C.output ∨ ic k3 (C.output - 14)) ∧
        isAnd k1 ∧ isAnd m ∧ isAnd k2 ∧ isAnd k3 ∧
        gv k1 p07 = true ∧ gv k1 p77 = true ∧ (∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k1 b) p00 = false) ∧
        gv m p77 = false ∧ gv k3 p00 = false ∧
        gv k2 p07 = true ∧ gv k2 p00 = true ∧ ∀ b : Fin 2, wv (PEqualNP.TopForm.opnd C k2 b) p77 = false) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  let wstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have wireVal_input : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (r : ℕ)
      (hr : r < 14), PEqualNP.CleanedNonEdge.wireVal 14 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hlt : r < (List.ofFn x).length := by omega
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_ge : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (r : ℕ),
      14 + D.gates.length ≤ r → PEqualNP.CleanedNonEdge.wireVal 14 D r x = false := by
    intro D x r hr
    have hlen : (D.wires (List.ofFn x)).length = 14 + D.gates.length := by
      change (D.gates.foldl wstep (List.ofFn x)).length = _
      rw [wfold_len, List.length_ofFn]
    exact List.getD_eq_default _ _ (by omega)
  have wireVal_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (k : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
      PEqualNP.CleanedNonEdge.wireVal 14 D (14 + k) x =
        g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 14 D i x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hg_eq : D.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hgk)
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (D.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + k := by
      dsimp only [pref]
      rw [wfold_len, List.length_ofFn, List.length_take]
      omega
    have hwires_eq : D.wires (List.ofFn x) =
        (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + k, pref.getD i false = PEqualNP.CleanedNonEdge.wireVal 14 D i x := by
      intro i hi
      change pref.getD i false = (D.wires (List.ofFn x)).getD i false
      rw [hwires_eq]
      have hi1 : i < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ i hi1]
      have hi0 : i < pref.length := by omega
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    change (D.wires (List.ofFn x)).getD (14 + k) false = _
    rw [hwires_eq]
    have hidx : 14 + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref g).getD (14 + k) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
  have cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      dsimp only [PEqualNP.EdgeOwnership.coneStep]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_char : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ),
      i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
          14 ≤ w ∧ w < 14 + j ∧
          (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
        rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD k [] =
            (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
        intro k hk
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 14) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 14) (by omega)] at h3; exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (PEqualNP.EdgeOwnership.coneStep 14
            (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
              (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
          dsimp only [PEqualNP.EdgeOwnership.coneStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e1, e2, List.mem_flatMap]
        constructor
        · rintro ⟨w, hw, hmem⟩
          rw [List.mem_filter, decide_eq_true_eq] at hw
          refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
          rw [key (w - 14) (by omega)]
          simpa using hmem
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 14) (by omega)] at h3
          exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, by simpa using h3⟩
      · have e3 : (PEqualNP.EdgeOwnership.coneStep 14
            (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD j [] = [] := by
          apply List.getD_eq_default
          dsimp only [PEqualNP.EdgeOwnership.coneStep]
          simp only [List.length_append, List.length_singleton, hlen]
          omega
        rw [e3]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hlt
        simp only [List.length_append, List.length_singleton] at hlt
        omega
  have inCone_iff : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      PEqualNP.EdgeOwnership.InCone 14 D i j ↔
        j < D.gates.length ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
          14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 D i (w - 14)) :=
    fun D i j => cones_char D.gates i j
  have eval_and : ∀ b1 b2 : Bool,
      PEqualNP.CircuitLowerBounds.GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool,
      PEqualNP.CircuitLowerBounds.GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have oriented : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (k1 k2 : ℕ),
      D.size ≤ 27 →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      PEqualNP.EdgeOwnership.InCone 14 D k1 k2 →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k1).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      PEqualNP.EdgeOwnership.gateVal 14 D k1 (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 D (PEqualNP.TopForm.opnd D k1 b)
        (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) = false) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k2).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (14 + k2 = D.output ∨ PEqualNP.EdgeOwnership.InCone 14 D k2 (D.output - 14)) →
      PEqualNP.EdgeOwnership.gateVal 14 D k2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 D (PEqualNP.TopForm.opnd D k2 b)
        (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = false) →
      False := by
    intro D k1 k2 hSize hGates hFano hCone12 hk1And hk1_07 hk1_00 hk2And hk2Live hk2_07 hk2_77
    let p07 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
    let p00 := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0
    let p77 := PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7
    have gate_spec : ∀ j < D.gates.length,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [a, b] ∧
          a < 14 + j ∧ b < 14 + j ∧
          ∀ x : Fin 14 → Bool, PEqualNP.EdgeOwnership.gateVal 14 D j x =
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op.eval
              [PEqualNP.CleanedNonEdge.wireVal 14 D a x, PEqualNP.CleanedNonEdge.wireVal 14 D b x] := by
      intro j hj
      have hgj : D.gates[j]? = some D.gates[j] := List.getElem?_eq_getElem hj
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates[j] := by
        change D.gates.getD j _ = D.gates[j]
        simp [List.getD_eq_getElem?_getD, hgj]
      obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hGates j D.gates[j] hgj
      rw [hga]
      refine ⟨hop, a, b, hin, ha, hb, fun x => ?_⟩
      have hlt : ∀ i ∈ D.gates[j].inputs, i < 14 + j := by
        intro i hi; rw [hin] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
      have hw := wireVal_gate D x j D.gates[j] hgj hlt
      rw [hin] at hw
      exact hw
    have kill_along_cone : ∀ (s : ℕ) (x0 : Fin 14 → Bool),
        PEqualNP.EdgeOwnership.gateVal 14 D s x0 = true →
        ∀ j : ℕ, PEqualNP.EdgeOwnership.InCone 14 D s j →
          PEqualNP.EdgeOwnership.gateVal 14 D j x0 = true ∨
          ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.gateVal 14 D j x0 = false) ∨
          ∃ m : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D m).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone 14 D s m ∧ PEqualNP.EdgeOwnership.InCone 14 D m j ∧
            PEqualNP.EdgeOwnership.gateVal 14 D m x0 = false := by
      intro s x0 hs j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hcj
        obtain ⟨hj, w, hw, hw14, hwlt, hsw⟩ := (inCone_iff D s j).mp hcj
        obtain ⟨hop, a, b, hin, _, _, hev⟩ := gate_spec j hj
        by_cases hwv : PEqualNP.CleanedNonEdge.wireVal 14 D w x0 = true
        · cases hjv : PEqualNP.EdgeOwnership.gateVal 14 D j x0
          · right; left
            refine ⟨?_, rfl⟩
            rcases hop with hand | hor
            · exact hand
            · exfalso
              have he := hev x0
              rw [hjv, hor, eval_or] at he
              rw [hin] at hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> simp [hwv] at he
          · exact Or.inl rfl
        · have hwv_f : PEqualNP.CleanedNonEdge.wireVal 14 D w x0 = false :=
            Bool.eq_false_iff.mpr hwv
          have hgw_f : PEqualNP.EdgeOwnership.gateVal 14 D (w - 14) x0 = false := by
            change PEqualNP.CleanedNonEdge.wireVal 14 D (14 + (w - 14)) x0 = false
            rwa [show 14 + (w - 14) = w by omega]
          rcases hsw with rfl | hcone_sw
          · rw [hs] at hgw_f; cases hgw_f
          · rcases ih (w - 14) (by omega) hcone_sw with h1 | ⟨hand_w, _⟩ | ⟨m, hmAnd, hsm, hmw, hmf⟩
            · rw [h1] at hgw_f; cases hgw_f
            · right; right
              refine ⟨w - 14, hand_w, hcone_sw, ?_, hgw_f⟩
              exact (inCone_iff D (w - 14) j).mpr ⟨hj, w, hw, hw14, hwlt, Or.inl rfl⟩
            · right; right
              refine ⟨m, hmAnd, hsm, ?_, hmf⟩
              exact (inCone_iff D m j).mpr ⟨hj, w, hw, hw14, hwlt, Or.inr hmw⟩
    cases hk1_77 : PEqualNP.EdgeOwnership.gateVal 14 D k1 p77
    · have hk1_lt : k1 < D.gates.length := by
        by_contra h
        have hf := wireVal_ge D p07 (14 + k1) (by omega)
        change PEqualNP.EdgeOwnership.gateVal 14 D k1 p07 = false at hf
        rw [hk1_07] at hf; cases hf
      obtain ⟨_, a, b, hin1, ha1, hb1, hev1⟩ := gate_spec k1 hk1_lt
      have he07 := (hev1 p07).symm
      rw [hk1_07, hk1And, eval_and, Bool.and_eq_true] at he07
      have he77 := (hev1 p77).symm
      rw [hk1_77, hk1And, eval_and, Bool.and_eq_false_iff] at he77
      have hop0 : PEqualNP.TopForm.opnd D k1 0 = a := by
        dsimp only [PEqualNP.TopForm.opnd]; simp [hin1]
      have hop1 : PEqualNP.TopForm.opnd D k1 1 = b := by
        dsimp only [PEqualNP.TopForm.opnd]; simp [hin1]
      have hex_u : ∃ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k1).inputs,
          u < 14 + k1 ∧ PEqualNP.CleanedNonEdge.wireVal 14 D u p07 = true ∧
          PEqualNP.CleanedNonEdge.wireVal 14 D u p00 = false ∧
          PEqualNP.CleanedNonEdge.wireVal 14 D u p77 = false := by
        rcases he77 with hfa | hfb
        · refine ⟨a, by rw [hin1]; simp, ha1, he07.1, ?_, hfa⟩
          have h0 := hk1_00 0; rwa [hop0] at h0
        · refine ⟨b, by rw [hin1]; simp, hb1, he07.2, ?_, hfb⟩
          have h0 := hk1_00 1; rwa [hop1] at h0
      have trace_back : ∀ u : ℕ, u < 14 + D.gates.length →
          PEqualNP.CleanedNonEdge.wireVal 14 D u p07 = true →
          PEqualNP.CleanedNonEdge.wireVal 14 D u p00 = false →
          PEqualNP.CleanedNonEdge.wireVal 14 D u p77 = false →
          14 ≤ u ∧ ∃ k0 : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D k0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (k0 = u - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 D k0 (u - 14)) ∧
            PEqualNP.EdgeOwnership.gateVal 14 D k0 p07 = true ∧
            PEqualNP.EdgeOwnership.gateVal 14 D k0 p00 = false ∧
            PEqualNP.EdgeOwnership.gateVal 14 D k0 p77 = false := by
        intro u
        induction u using Nat.strong_induction_on with
        | _ u ih =>
          intro hult hu07 hu00 hu77
          by_cases hu14 : u < 14
          · exfalso
            rw [wireVal_input D p07 u hu14] at hu07
            rw [wireVal_input D p00 u hu14] at hu00
            rw [wireVal_input D p77 u hu14] at hu77
            have habs : ∀ i : Fin 14, ¬ (p07 i = true ∧ p00 i = false ∧ p77 i = false) := by decide
            exact habs ⟨u, hu14⟩ ⟨hu07, hu00, hu77⟩
          · have hge14 : 14 ≤ u := by omega
            refine ⟨hge14, ?_⟩
            let j := u - 14
            have hj : j < D.gates.length := by omega
            have huj : u = 14 + j := by omega
            obtain ⟨hop, c, d, hinj, hc, hd, hevj⟩ := gate_spec j hj
            rcases hop with hand | hor
            · refine ⟨j, hand, Or.inl rfl, ?_, ?_, ?_⟩
              · change PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p07 = true; rwa [← huj]
              · change PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p00 = false; rwa [← huj]
              · change PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p77 = false; rwa [← huj]
            · have hj07 := (hevj p07).symm
              have hj00 := (hevj p00).symm
              have hj77 := (hevj p77).symm
              change _ = PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p07 at hj07
              change _ = PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p00 at hj00
              change _ = PEqualNP.CleanedNonEdge.wireVal 14 D (14 + j) p77 at hj77
              rw [← huj, hu07, hor, eval_or, Bool.or_eq_true] at hj07
              rw [← huj, hu00, hor, eval_or, Bool.or_eq_false_iff] at hj00
              rw [← huj, hu77, hor, eval_or, Bool.or_eq_false_iff] at hj77
              rcases hj07 with hc07 | hd07
              · obtain ⟨hw14, k0, hk0And, hk0c, h0, h1, h2⟩ :=
                  ih c (by omega) (by omega) hc07 hj00.1 hj77.1
                refine ⟨k0, hk0And, Or.inr ?_, h0, h1, h2⟩
                exact (inCone_iff D k0 j).mpr ⟨hj, c, by rw [hinj]; simp, hw14, hc, hk0c⟩
              · obtain ⟨hw14, k0, hk0And, hk0d, h0, h1, h2⟩ :=
                  ih d (by omega) (by omega) hd07 hj00.2 hj77.2
                refine ⟨k0, hk0And, Or.inr ?_, h0, h1, h2⟩
                exact (inCone_iff D k0 j).mpr ⟨hj, d, by rw [hinj]; simp, hw14, hd, hk0d⟩
      obtain ⟨u, hu_in, hu_lt, hu07, hu00, hu77⟩ := hex_u
      obtain ⟨hu14, k0, hk0And, hk0u, h0, h1, h2⟩ :=
        trace_back u (by omega) hu07 hu00 hu77
      have hCone01 : PEqualNP.EdgeOwnership.InCone 14 D k0 k1 :=
        (inCone_iff D k0 k1).mpr ⟨hk1_lt, u, hu_in, hu14, hu_lt, hk0u⟩
      exact hClean ⟨D, hSize, hGates, hFano, k0, k1, k2, hCone01, hCone12, hk2Live,
        hk0And, hk1And, hk2And, h0, h1, h2, hk1_07, hk1_77, hk1_00, hk2_07, hk2_77⟩
    · have hk2_lt : k2 < D.gates.length := (inCone_iff D k1 k2).mp hCone12 |>.1
      obtain ⟨_, a2, b2, hin2, _, _, hev2⟩ := gate_spec k2 hk2_lt
      have hop20 : PEqualNP.TopForm.opnd D k2 0 = a2 := by
        dsimp only [PEqualNP.TopForm.opnd]; simp [hin2]
      have hop21 : PEqualNP.TopForm.opnd D k2 1 = b2 := by
        dsimp only [PEqualNP.TopForm.opnd]; simp [hin2]
      have hk2_77_val : PEqualNP.EdgeOwnership.gateVal 14 D k2 p77 = false := by
        have he := hev2 p77
        have h0 := hk2_77 0; rw [hop20] at h0
        have h1 := hk2_77 1; rw [hop21] at h1
        rw [hk2And, eval_and, h0, h1] at he
        exact he
      obtain ⟨_, w, hw, hw14, hwlt, h1w⟩ := (inCone_iff D k1 k2).mp hCone12
      have hw_77 : PEqualNP.CleanedNonEdge.wireVal 14 D w p77 = false := by
        rw [hin2] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have h0 := hk2_77 0; rwa [hop20] at h0
        · have h1 := hk2_77 1; rwa [hop21] at h1
      have hgw_77 : PEqualNP.EdgeOwnership.gateVal 14 D (w - 14) p77 = false := by
        change PEqualNP.CleanedNonEdge.wireVal 14 D (14 + (w - 14)) p77 = false
        rwa [show 14 + (w - 14) = w by omega]
      have hcone_1w : PEqualNP.EdgeOwnership.InCone 14 D k1 (w - 14) := by
        rcases h1w with rfl | hc
        · rw [hk1_77] at hgw_77; cases hgw_77
        · exact hc
      have hex_m : ∃ m : ℕ,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D m).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone 14 D k1 m ∧
          PEqualNP.EdgeOwnership.InCone 14 D m k2 ∧
          PEqualNP.EdgeOwnership.gateVal 14 D m p77 = false := by
        rcases kill_along_cone k1 p77 hk1_77 (w - 14) hcone_1w with h1 | ⟨hand_w, _⟩ | ⟨m, hmAnd, h1m, hmw, hmf⟩
        · rw [h1] at hgw_77; cases hgw_77
        · exact ⟨w - 14, hand_w, hcone_1w,
            (inCone_iff D (w - 14) k2).mpr ⟨hk2_lt, w, hw, hw14, hwlt, Or.inl rfl⟩, hgw_77⟩
        · exact ⟨m, hmAnd, h1m,
            (inCone_iff D m k2).mpr ⟨hk2_lt, w, hw, hw14, hwlt, Or.inr hmw⟩, hmf⟩
      obtain ⟨m, hmAnd, h1m, hmk2, hmf⟩ := hex_m
      cases hk2_00 : PEqualNP.EdgeOwnership.gateVal 14 D k2 p00
      · exact hDirtyClean ⟨D, hSize, hGates, hFano, k1, m, k2, h1m, hmk2, hk2Live,
          hk1And, hmAnd, hk2And, hk1_07, hk1_77, hk1_00, hmf, hk2_07, hk2_00, hk2_77⟩
      · have hOut00 : D.eval (List.ofFn p00) = false := by
          cases h : D.eval (List.ofFn p00)
          · rfl
          · exfalso
            obtain ⟨u, t, _, hu, ht⟩ := (hFano p00).mp h
            have habs : ∀ u t : Fin 7, ¬ (p00 (Fin.castAdd 7 u) = true ∧ p00 (Fin.natAdd 7 t) = true) :=
              by decide
            exact habs u t ⟨hu, ht⟩
        have hCone2Out : PEqualNP.EdgeOwnership.InCone 14 D k2 (D.output - 14) := by
          rcases hk2Live with heq | hc
          · exfalso
            have hv : PEqualNP.EdgeOwnership.gateVal 14 D k2 p00 = D.eval (List.ofFn p00) := by
              change (D.wires (List.ofFn p00)).getD (14 + k2) false = _
              rw [heq]; rfl
            rw [hk2_00, hOut00] at hv; cases hv
          · exact hc
        have ho_lt : D.output - 14 < D.gates.length := (inCone_iff D k2 (D.output - 14)).mp hCone2Out |>.1
        have ho_ge14 : 14 ≤ D.output := by
          by_contra h
          have h07_true : D.eval (List.ofFn p07) = true :=
            (hFano p07).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
          have h77_false : D.eval (List.ofFn p77) = false := by
            cases h7 : D.eval (List.ofFn p77)
            · rfl
            · exfalso
              obtain ⟨u, t, _, hu, ht⟩ := (hFano p77).mp h7
              have habs : ∀ u t : Fin 7, ¬ (p77 (Fin.castAdd 7 u) = true ∧ p77 (Fin.natAdd 7 t) = true) :=
                by decide
              exact habs u t ⟨hu, ht⟩
          have ho14 : D.output < 14 := by omega
          have e1 : p07 ⟨D.output, ho14⟩ = true := by
            rw [← wireVal_input D p07 D.output ho14]; exact h07_true
          have e2 : p00 ⟨D.output, ho14⟩ = false := by
            rw [← wireVal_input D p00 D.output ho14]; exact hOut00
          have e3 : p77 ⟨D.output, ho14⟩ = false := by
            rw [← wireVal_input D p77 D.output ho14]; exact h77_false
          have habs : ∀ i : Fin 14, ¬ (p07 i = true ∧ p00 i = false ∧ p77 i = false) := by decide
          exact habs ⟨D.output, ho14⟩ ⟨e1, e2, e3⟩
        have ho_00 : PEqualNP.EdgeOwnership.gateVal 14 D (D.output - 14) p00 = false := by
          change (D.wires (List.ofFn p00)).getD (14 + (D.output - 14)) false = false
          rw [show 14 + (D.output - 14) = D.output by omega]
          exact hOut00
        have hex_k3 : ∃ k3 : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D k3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone 14 D k2 k3 ∧
            (14 + k3 = D.output ∨ PEqualNP.EdgeOwnership.InCone 14 D k3 (D.output - 14)) ∧
            PEqualNP.EdgeOwnership.gateVal 14 D k3 p00 = false := by
          rcases kill_along_cone k2 p00 hk2_00 (D.output - 14) hCone2Out with
            h1 | ⟨hand_o, _⟩ | ⟨k3, hk3And, h23, h3o, hk3f⟩
          · rw [h1] at ho_00; cases ho_00
          · exact ⟨D.output - 14, hand_o, hCone2Out, Or.inl (by omega), ho_00⟩
          · exact ⟨k3, hk3And, h23, Or.inr h3o, hk3f⟩
        obtain ⟨k3, hk3And, h23, hk3Live, hk3f⟩ := hex_k3
        exact hFourChain ⟨D, hSize, hGates, hFano, k1, m, k2, k3, h1m, hmk2, h23, hk3Live,
          hk1And, hmAnd, hk2And, hk3And, hk1_07, hk1_77, hk1_00, hmf, hk3f, hk2_07, hk2_00, hk2_77⟩
  rintro ⟨C, hSize, hGates, hFano, k1, k2, hConeOr, hk1And, hk1Live, hk1_07, hk1_00,
    hk2And, hk2Live, hk2_07, hk2_77⟩
  rcases hConeOr with h12 | h21
  · exact oriented C k1 k2 hSize hGates hFano h12 hk1And hk1_07 hk1_00 hk2And hk2Live hk2_07 hk2_77
  · let pol : Fin 14 → Fin 14 := fun i =>
      Fin.ofNat 14 (if i.val < 7 then 7 + (7 - i.val) % 7 else (14 - i.val) % 7)
    have hpol_inv : ∀ i : Fin 14, pol (pol i) = i := by dsimp only [pol]; decide
    have hpol_cast : ∀ u : Fin 7, pol (Fin.castAdd 7 u) = Fin.natAdd 7 (-u) := by
      dsimp only [pol]; decide
    have hpol_nat : ∀ t : Fin 7, pol (Fin.natAdd 7 t) = Fin.castAdd 7 (-t) := by
      dsimp only [pol]; decide
    have hpol_inc : ∀ u t : Fin 7,
        ((-t) = (-u) ∨ (-t) = (-u) + 1 ∨ (-t) = (-u) + 3) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3) := by decide
    let mapW : ℕ → ℕ := fun r => if h : r < 14 then (pol ⟨r, h⟩).val else r
    have hmapW_inj : ∀ a b : ℕ, mapW a = mapW b → a = b := by
      intro a b hab
      by_cases ha : a < 14 <;> by_cases hb : b < 14
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have h2 := congrArg pol (Fin.ext hab)
        rw [hpol_inv, hpol_inv] at h2
        exact congrArg Fin.val h2
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have := (pol ⟨a, ha⟩).isLt; omega
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have := (pol ⟨b, hb⟩).isLt; omega
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab; exact hab
    have hmapW_lt : ∀ a j : ℕ, a < 14 + j → mapW a < 14 + j := by
      intro a j haj
      by_cases ha : a < 14
      · simp only [mapW, ha, ↓reduceDIte]
        have := (pol ⟨a, ha⟩).isLt; omega
      · simp only [mapW, ha, ↓reduceDIte]; exact haj
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩, mapW C.output⟩
    have hSize' : C'.size ≤ 27 := by
      change (C.gates.map _).length ≤ 27
      rw [List.length_map]; exact hSize
    have hGates' : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C'.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
      intro j g hgj
      simp only [C', List.getElem?_map] at hgj
      rcases hCgj : C.gates[j]? with _ | g0
      · rw [hCgj] at hgj; simp at hgj
      · rw [hCgj] at hgj
        have hge := Option.some.inj hgj
        subst hge
        obtain ⟨hop, a, b, hinp, hne, ha, hb⟩ := hGates j g0 hCgj
        exact ⟨hop, mapW a, mapW b, by simp [hinp], fun heq => hne (hmapW_inj a b heq),
          hmapW_lt a j ha, hmapW_lt b j hb⟩
    have hWireMap : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.gates.length →
        PEqualNP.CleanedNonEdge.wireVal 14 C' (mapW r) x =
          PEqualNP.CleanedNonEdge.wireVal 14 C r (fun i => x (pol i)) := by
      intro x r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr
        by_cases hr14 : r < 14
        · simp only [mapW, hr14, ↓reduceDIte]
          rw [wireVal_input C' x _ (pol ⟨r, hr14⟩).isLt, wireVal_input C _ r hr14]
        · have hmap_eq : mapW r = r := by simp [mapW, hr14]
          rw [hmap_eq]
          let k := r - 14
          have hk : k < C.gates.length := by omega
          have hrk : r = 14 + k := by omega
          rw [hrk]
          have hCgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
          have hC'gk : C'.gates[k]? = some ⟨C.gates[k].op, C.gates[k].inputs.map mapW⟩ := by
            simp [C', List.getElem?_map, hCgk]
          obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates k C.gates[k] hCgk
          have hltC : ∀ i ∈ C.gates[k].inputs, i < 14 + k := by
            intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
          have hltC' : ∀ i ∈ (C.gates[k].inputs.map mapW), i < 14 + k := by
            intro i hi
            obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
            exact hmapW_lt i0 k (hltC i0 hi0)
          rw [wireVal_gate C' x k _ hC'gk hltC', wireVal_gate C _ k _ hCgk hltC, List.map_map]
          congr 1
          exact List.map_congr_left fun i hi =>
            ih i (by have := hltC i hi; omega) (by have := hltC i hi; omega)
    have hEvalMap : ∀ x : Fin 14 → Bool,
        C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (pol i))) := by
      intro x
      by_cases ho : C.output < 14 + C.gates.length
      · exact hWireMap x C.output ho
      · have ho' : 14 + C'.gates.length ≤ C'.output := by
          have h14 : ¬ C.output < 14 := by omega
          simp [C', mapW, h14]; omega
        change PEqualNP.CleanedNonEdge.wireVal 14 C' C'.output x =
          PEqualNP.CleanedNonEdge.wireVal 14 C C.output (fun i => x (pol i))
        rw [wireVal_ge C' x C'.output ho', wireVal_ge C _ C.output (by omega)]
    have hFano' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
      intro x
      rw [hEvalMap x, hFano (fun i => x (pol i))]
      constructor
      · rintro ⟨u, t, hinc, hu, ht⟩
        rw [hpol_cast] at hu
        rw [hpol_nat] at ht
        exact ⟨-t, -u, (hpol_inc u t).mpr hinc, ht, hu⟩
      · rintro ⟨u, t, hinc, hu, ht⟩
        refine ⟨-t, -u, ?_, ?_, ?_⟩
        · have h := (hpol_inc (-t) (-u)).mp
          simp only [neg_neg] at h
          exact h hinc
        · rw [hpol_cast, neg_neg]; exact ht
        · rw [hpol_nat, neg_neg]; exact hu
    have hfilt_mapW : ∀ (l : List ℕ) (m : ℕ),
        (l.map mapW).filter (fun w => decide (14 ≤ w ∧ w < m)) =
          l.filter (fun w => decide (14 ≤ w ∧ w < m)) := by
      intro l m
      induction l with
      | nil => rfl
      | cons a as ih =>
        simp only [List.map_cons]
        by_cases ha : a < 14
        · have hm : mapW a < 14 := by simp only [mapW, ha, ↓reduceDIte]; exact (pol ⟨a, ha⟩).isLt
          have d1 : decide (14 ≤ mapW a ∧ mapW a < m) = false := decide_eq_false (by omega)
          have d2 : decide (14 ≤ a ∧ a < m) = false := decide_eq_false (by omega)
          rw [List.filter_cons, List.filter_cons, d1, d2]
          exact ih
        · have hm : mapW a = a := by simp [mapW, ha]
          rw [hm, List.filter_cons, List.filter_cons, ih]
    have hcones_eq : PEqualNP.EdgeOwnership.cones 14 C' = PEqualNP.EdgeOwnership.cones 14 C := by
      change (C.gates.map fun g => (⟨g.op, g.inputs.map mapW⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
          (PEqualNP.EdgeOwnership.coneStep 14) [] =
        C.gates.foldl (PEqualNP.EdgeOwnership.coneStep 14) []
      have gen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
          (gs.map fun g => (⟨g.op, g.inputs.map mapW⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
            (PEqualNP.EdgeOwnership.coneStep 14) cs =
          gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs := by
        intro gs
        induction gs with
        | nil => intro cs; rfl
        | cons g gs ih =>
          intro cs
          simp only [List.map_cons, List.foldl_cons]
          have hcs : PEqualNP.EdgeOwnership.coneStep 14 cs ⟨g.op, g.inputs.map mapW⟩ =
              PEqualNP.EdgeOwnership.coneStep 14 cs g := by
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
            rw [hfilt_mapW]
          rw [hcs, ih]
      exact gen C.gates []
    have hInCone_eq : ∀ i j : ℕ,
        PEqualNP.EdgeOwnership.InCone 14 C' i j ↔ PEqualNP.EdgeOwnership.InCone 14 C i j := by
      intro i j
      unfold PEqualNP.EdgeOwnership.InCone
      rw [hcones_eq]
    have hgateAt_op : ∀ j : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op =
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op := by
      intro j
      by_cases hj : j < C.gates.length
      · have h1 : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
        have h2 : C'.gates[j]? = some ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
          simp [C', List.getElem?_map, h1]
        change (C'.gates.getD j _).op = (C.gates.getD j _).op
        simp [List.getD_eq_getElem?_getD, h1, h2]
      · have h1 : C.gates[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : C'.gates[j]? = none := List.getElem?_eq_none (by simp [C']; omega)
        change (C'.gates.getD j _).op = (C.gates.getD j _).op
        simp [List.getD_eq_getElem?_getD, h1, h2]
    have hopnd_eq : ∀ j < C.gates.length, ∀ b : Fin 2,
        PEqualNP.TopForm.opnd C' j b = mapW (PEqualNP.TopForm.opnd C j b) ∧
        PEqualNP.TopForm.opnd C j b < 14 + C.gates.length := by
      intro j hj b
      have h1 : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have h2 : C'.gates[j]? = some ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
        simp [C', List.getElem?_map, h1]
      obtain ⟨_, a0, b0, hinp, _, ha0, hb0⟩ := hGates j C.gates[j] h1
      have ga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j _ = _; simp [List.getD_eq_getElem?_getD, h1]
      have ga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
        change C'.gates.getD j _ = _; simp [List.getD_eq_getElem?_getD, h2]
      fin_cases b <;> dsimp only [PEqualNP.TopForm.opnd] <;> simp [ga1, ga2, hinp] <;> omega
    have hk1_lt : k1 < C.gates.length := (inCone_iff C k2 k1).mp h21 |>.1
    have hk2_lt : k2 < C.gates.length := by
      by_contra h
      have hf := wireVal_ge C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k2) (by omega)
      change PEqualNP.EdgeOwnership.gateVal 14 C k2 _ = false at hf
      rw [hk2_07] at hf; cases hf
    have hp07_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 := by
      funext i; dsimp only [pol]; revert i; decide
    have hp00_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 := by
      funext i; dsimp only [pol]; revert i; decide
    have hp77_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 := by
      funext i; dsimp only [pol]; revert i; decide
    have hout_eq : C'.output = C.output := by
      by_cases ho14 : C.output < 14
      · exfalso
        have h07_t : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = true :=
          (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
        have h00_f : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0)) = false := by
          cases h : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0))
          · rfl
          · obtain ⟨u, t, _, hu, ht⟩ := (hFano _).mp h
            have habs : ∀ u t : Fin 7, ¬ (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (Fin.castAdd 7 u) = true ∧
              PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (Fin.natAdd 7 t) = true) := by decide
            exact False.elim (habs u t ⟨hu, ht⟩)
        have h77_f : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7)) = false := by
          cases h : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7))
          · rfl
          · obtain ⟨u, t, _, hu, ht⟩ := (hFano _).mp h
            have habs : ∀ u t : Fin 7, ¬ (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (Fin.castAdd 7 u) = true ∧
              PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (Fin.natAdd 7 t) = true) := by decide
            exact False.elim (habs u t ⟨hu, ht⟩)
        have e1 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 ⟨C.output, ho14⟩ = true := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) C.output ho14]
          exact h07_t
        have e2 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 ⟨C.output, ho14⟩ = false := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) C.output ho14]
          exact h00_f
        have e3 : PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 ⟨C.output, ho14⟩ = false := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) C.output ho14]
          exact h77_f
        have habs : ∀ i : Fin 14, ¬ (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 i = true ∧
          PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 i = false ∧
          PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 i = false) := by decide
        exact habs ⟨C.output, ho14⟩ ⟨e1, e2, e3⟩
      · simp [C', mapW, ho14]
    refine oriented C' k2 k1 hSize' hGates' hFano' ((hInCone_eq k2 k1).mpr h21)
      (by rw [hgateAt_op]; exact hk2And) ?_ ?_ (by rw [hgateAt_op]; exact hk1And) ?_ ?_ ?_
    · have hw := hWireMap (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k2) (by omega)
      have hm : mapW (14 + k2) = 14 + k2 := by simp [mapW]
      rw [hm, hp07_pol] at hw
      exact hw.trans hk2_07
    · intro b
      obtain ⟨heq, hlt⟩ := hopnd_eq k2 hk2_lt b
      rw [heq, hWireMap _ _ hlt, hp00_pol]
      exact hk2_77 b
    · rw [hout_eq]
      rcases hk1Live with heq | hc
      · exact Or.inl heq
      · exact Or.inr ((hInCone_eq k1 (C.output - 14)).mpr hc)
    · have hw := hWireMap (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k1) (by omega)
      have hm : mapW (14 + k1) = 14 + k1 := by simp [mapW]
      rw [hm, hp07_pol] at hw
      exact hw.trans hk1_07
    · intro b
      obtain ⟨heq, hlt⟩ := hopnd_eq k1 hk1_lt b
      rw [heq, hWireMap _ _ hlt, hp77_pol]
      exact hk1_00 b
