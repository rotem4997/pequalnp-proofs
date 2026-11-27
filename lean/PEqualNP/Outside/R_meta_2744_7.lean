import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2744_7
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      g.inputs ≤ g.inputs.map (fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k) →
      16 ≤ C.size)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      g.inputs ≤ g.inputs.map (fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k) →
      16 ≤ C.size)
    (h3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      (PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[1]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      g.inputs ≤ g.inputs.map (fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k) →
      16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C hfan h9 hfun hg1
  have hwi : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.wires l =
      D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l :=
    fun _ _ => rfl
  have hcf : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool),
      PEqualNP.MetaComplexity.circuitFun 9 D x =
        (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD D.output false := fun _ _ => rfl
  have hsz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  obtain ⟨g, hg⟩ := hg1
  -- the symmetry (0 1)(2 5)(3 8)(4 6) of the graph, which fixes the first gate x4 OR x6
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b1 && b0 || b0 && b5 || b5 && b8 || b8 && b6 || b6 && b1 || b1 && b2 ||
        b0 && b4 || b5 && b7 || b8 && b3 || b2 && b7 || b4 && b3 || b3 && b2) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hinv : ∀ j : ℕ, List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3]
      (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) = j := by
    intro j
    by_cases hj : j < 9
    · interval_cases j <;> decide
    · rw [hge j (by omega), hge j (by omega)]
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          j false := by
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
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        by_cases hj : j < W.length
        · have hj' : List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j < W'.length := by
            by_cases h : j < 9
            · have := hlt j h
              omega
            · rw [hge j (by omega)]
              omega
          have hWj := hW j
          generalize List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j = r at hj' hWj ⊢
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
  have hin : ∀ y : Fin 9 → Bool, ∀ j : ℕ,
      (List.ofFn y).getD (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false =
        (List.ofFn fun i => y (![1, 0, 5, 8, 6, 2, 4, 7, 3] i)).getD j false := by
    intro y j
    by_cases hj : j < 9
    · interval_cases j <;> rfl
    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hop := (hfan g (List.mem_of_getElem? hg)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hcase : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      (PEqualNP.MetaComplexity.circuitFun 9 D = fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      ∀ d : PEqualNP.CircuitLowerBounds.Gate, D.gates[1]? = some d → d.op = g.op →
      d.inputs ≤ d.inputs.map (fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k) →
      16 ≤ D.size := by
    intro D hD hD9 hDf d hd hdo hdc
    rcases hop with hop | hop | hop
    · exact h1 D hD hD9 hDf d hd (hdo.trans hop) hdc
    · exact h2 D hD hD9 hDf d hd (hdo.trans hop) hdc
    · exact h3 D hD hD9 hDf d hd (hdo.trans hop) hdc
  rcases le_total g.inputs (g.inputs.map fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k)
    with hc | hc
  · exact hcase C hfan h9 hfun g hg rfl hc
  · have hW : ∀ y : Fin 9 → Bool, ∀ j : ℕ,
        ((C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)).getD
            (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn fun i => y (![1, 0, 5, 8, 6, 2, 4, 7, 3] i))).getD j false := by
      intro y j
      apply hpre
      · simp
      · simp
      · exact hin y
    have hsize := hcase
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i))
        (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] C.output C.output))
      ?_ ?_ ?_
      (PEqualNP.CircuitLowerBounds.Gate.mk g.op
        (g.inputs.map fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i))
      ?_ rfl ?_
    · rw [hsz] at hsize
      rw [hsz]
      simpa using hsize
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      refine ⟨(hfan d0 hd0).1, ?_⟩
      simpa using (hfan d0 hd0).2
    · intro y
      have e := hW y 9
      rw [hge 9 (le_refl _)] at e
      rw [hwi]
      dsimp only
      rw [e]
      refine (h9 _).trans ?_
      show (y 6 || y 4) = (y 4 || y 6)
      exact Bool.or_comm _ _
    · funext y
      have e := hW y C.output
      have hf := congrFun hfun (fun i => y (![1, 0, 5, 8, 6, 2, 4, 7, 3] i))
      rw [hcf] at hf
      rw [hcf]
      dsimp only at hf ⊢
      rw [e]
      rw [hf]
      exact hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    · simp [hg]
    · rw [List.map_map]
      have : ((fun k => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] k k) ∘
          fun i => List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] i i) = id := by
        funext k
        exact hinv k
      rw [this, List.map_id]
      exact hc
