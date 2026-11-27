import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3302_7
    (h1 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 → (∀ g : PEqualNP.CircuitLowerBounds.Gate, x2.gates[0]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs ≤ g.inputs.map (fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k)) →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))))
    (h2 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 → (∀ g : PEqualNP.CircuitLowerBounds.Gate, x2.gates[0]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs ≤ g.inputs.map (fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k)) →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))))
    (h3 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 → (∀ g : PEqualNP.CircuitLowerBounds.Gate, x2.gates[0]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs ≤ g.inputs.map (fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k)) →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  intro E P Q w hP hQ hs1 hs2 hw1 hw2 x11 x12 hA hB
  have hwi : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.wires l = D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := fun _ _ => rfl
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      (b3 && b2 || b2 && b1 || b1 && b0 || b3 && b7 || b2 && b6 || b1 && b5 || b0 && b4 ||
        b7 && b5 || b6 && b4 || b4 && b7) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b0 && b4 || b1 && b5 || b2 && b6 || b3 && b7 ||
        b4 && b6 || b5 && b7 || b7 && b4) := by
    decide
  -- the symmetry (0 3)(1 2)(4 7)(5 6) of the graph, which swaps the inputs 0 and 3
  have hE : ∀ y : Fin 8 → Bool, E (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)) = E y := fun y =>
    hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  have hlt : ∀ j : ℕ, j < 8 → List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j < 8 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 8 ≤ j → List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hinv : ∀ j : ℕ, List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) = j := by
    intro j
    by_cases hj : j < 8
    · interval_cases j <;> decide
    · rw [hge j (by omega), hge j (by omega)]
  have hfl : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).length = W.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro W
      rfl
    | cons g gs ih =>
      intro W
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have happ : ∀ (W W' : List Bool) (u : Bool), W.length = W'.length → 8 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ, (W' ++ [u]).getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false = (W ++ [u]).getD j false := by
    intro W W' u hl h9 hW j
    by_cases hj : j < W.length
    · have hj' : List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j < W'.length := by
        by_cases h : j < 8
        · have := hlt j h
          omega
        · rw [hge j (by omega)]
          omega
      have hWj := hW j
      generalize List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j = r at hj' hWj ⊢
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hj', List.getElem?_append_left hj]
      simpa only [List.getD_eq_getElem?_getD] using hWj
    · rw [hge j (by omega)]
      by_cases hj2 : j = W.length
      · subst hj2
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
          List.getElem?_append_right (le_refl _), ← hl,
          List.getElem?_append_right (le_refl _)]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 8 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp
        omega
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        exact happ W W' _ hl h9 hW j
  have hin : ∀ y : Fin 8 → Bool, ∀ j : ℕ,
      (List.ofFn y).getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false = (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i))).getD j false := by
    intro y j
    by_cases hj : j < 8
    · interval_cases j <;> rfl
    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hlen : 0 < P.gates.length := by
    have h2 : w < 8 + P.gates.length := hw2
    omega
  have hg : P.gates[0]? = some P.gates[0] := List.getElem?_eq_getElem hlen
  generalize P.gates[0] = g at hg
  have hop := (hP g (List.mem_of_getElem? hg)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hcase : ∀ P' Q' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo P' →
      PEqualNP.MetaComplexity.FanInTwo Q' →
      (∀ d : PEqualNP.CircuitLowerBounds.Gate, P'.gates[0]? = some d →
        d.op = g.op ∧ d.inputs ≤ d.inputs.map (fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k)) →
      P'.size ≤ 4 → P'.size + Q'.size ≤ 13 → w < 8 + P'.size →
      (∀ x : Fin 8 → Bool, E x = false → (x 0 || x 3) = true →
        (P'.wires (List.ofFn x)).getD w false = true) →
      (∀ x : Fin 8 → Bool,
        Q'.eval (P'.wires (List.ofFn x) ++ [(P'.wires (List.ofFn x)).getD w false]) = E x) →
      ∃ x : Fin 8 → Bool, Q'.eval (P'.wires (List.ofFn x) ++ [false]) ≠ (E x || x 0 || x 3) := by
    intro P' Q' hP' hQ' hd h1' h2' h3' hA' hB'
    rcases hop with hop | hop | hop
    · exact h1 P' Q' w hP' hQ' (fun d hdd => ⟨(hd d hdd).1.trans hop, (hd d hdd).2⟩)
        h1' h2' hw1 h3' hA' hB'
    · exact h2 P' Q' w hP' hQ' (fun d hdd => ⟨(hd d hdd).1.trans hop, (hd d hdd).2⟩)
        h1' h2' hw1 h3' hA' hB'
    · exact h3 P' Q' w hP' hQ' (fun d hdd => ⟨(hd d hdd).1.trans hop, (hd d hdd).2⟩)
        h1' h2' hw1 h3' hA' hB'
  rcases le_total g.inputs (g.inputs.map fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k) with hc | hc
  · refine hcase P Q hP hQ ?_ hs1 hs2 hw2 hA hB
    intro d hd
    rw [hg] at hd
    cases hd
    exact ⟨rfl, hc⟩
  · have hWP : ∀ (y : Fin 8 → Bool) (j : ℕ),
        ((PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output).wires (List.ofFn y)).getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false =
          (P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)))).getD j false := by
      intro y j
      rw [hwi, hwi]
      exact hpre P.gates _ _ (by simp) (by simp) (hin y) j
    have hlenP : ∀ y : Fin 8 → Bool,
        (P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)))).length = ((PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output).wires (List.ofFn y)).length := by
      intro y
      rw [hwi, hwi, hfl, hfl]
      simp
    have h8P : ∀ y : Fin 8 → Bool, 8 ≤ (P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)))).length := by
      intro y
      rw [hwi, hfl]
      simp
    have hWQ : ∀ (y : Fin 8 → Bool) (u : Bool) (j : ℕ),
        ((PEqualNP.CircuitLowerBounds.Circuit.mk (Q.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) Q.output Q.output)).wires ((PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output).wires (List.ofFn y) ++ [u])).getD (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) j j) false =
          (Q.wires (P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i))) ++ [u])).getD j false := by
      intro y u j
      rw [hwi (PEqualNP.CircuitLowerBounds.Circuit.mk (Q.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) Q.output Q.output)), hwi Q]
      exact hpre Q.gates _ _
        (by rw [List.length_append, List.length_append, hlenP y])
        (by
          rw [List.length_append]
          have := h8P y
          omega)
        (happ _ _ u (hlenP y) (h8P y) (hWP y)) j
    have hgg : ∀ y : Fin 8 → Bool, ((PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output).wires (List.ofFn y)).getD w false =
        (P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)))).getD w false := by
      intro y
      have h := hWP y w
      rw [hge w hw1] at h
      exact h
    have hsize := hcase (PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output) (PEqualNP.CircuitLowerBounds.Circuit.mk (Q.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) (List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) Q.output Q.output)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · obtain ⟨y, hy⟩ := hsize
      refine ⟨(fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)), ?_⟩
      intro hcon
      apply hy
      have e := hWQ y false Q.output
      have hor : (E (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)) || y 3 || y 0) = (E y || y 0 || y 3) := by
        rw [hE y]
        generalize E y = a
        generalize y 0 = b
        generalize y 3 = c
        cases a <;> cases b <;> cases c <;> rfl
      exact e.trans (hcon.trans hor)
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      refine ⟨(hP d0 hd0).1, ?_⟩
      simpa using (hP d0 hd0).2
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      refine ⟨(hQ d0 hd0).1, ?_⟩
      simpa using (hQ d0 hd0).2
    · intro d hd
      have h0 : (PEqualNP.CircuitLowerBounds.Circuit.mk (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))) P.output).gates[0]? = some ((fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i)) g) := by simp [hg]
      have hd' : (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i)) g = d := Option.some.inj (h0.symm.trans hd)
      subst hd'
      refine ⟨rfl, ?_⟩
      show g.inputs.map (fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i) ≤
        (g.inputs.map (fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i)).map (fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k)
      rw [List.map_map]
      have hid : ((fun k => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) k k) ∘ fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i) = id := by
        funext k
        exact hinv k
      rw [hid, List.map_id]
      exact hc
    · show (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))).length ≤ 4
      rw [List.length_map]
      exact hs1
    · show (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))).length + (Q.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))).length ≤ 13
      rw [List.length_map, List.length_map]
      exact hs2
    · show w < 8 + (P.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([3, 2, 1, 0, 7, 6, 5, 4] : List ℕ) i i))).length
      rw [List.length_map]
      exact hw2
    · intro y hEy h03
      rw [hgg y]
      apply hA (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i))
      · rw [hE y]
        exact hEy
      · show (y 3 || y 0) = true
        rw [Bool.or_comm]
        exact h03
    · intro y
      rw [hgg y]
      have e := hWQ y ((P.wires (List.ofFn (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i)))).getD w false) Q.output
      exact e.trans ((hB (fun i => y (![3, 2, 1, 0, 7, 6, 5, 4] i))).trans (hE y))
