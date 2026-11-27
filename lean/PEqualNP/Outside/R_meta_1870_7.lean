import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1870_7
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [true]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (h3 : ∀ i ∈ ([0, 1, 4] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!x i]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (h4 : ∀ i ∈ ([5, 6] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!x i]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C L hfan hlen hC
  have hE : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++
      [PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (L.map fun k : Fin 11 => (List.ofFn x ++ [x 0 && x 3]).getD (↑k) false)]) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) :=
    fun x => hC x
  -- the symmetry (0 3)(1 2)(5 8)(6 7) of the graph, which fixes the pair {0, 3}
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b3 && b2 || b2 && b1 || b1 && b0 || b0 && b4 || b4 && b3 || b3 && b8 ||
        b2 && b7 || b1 && b6 || b0 && b5 || b8 && b6 || b7 && b5 || b5 && b8) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD ([3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            ({ op := g.op, inputs := g.inputs.map fun i => [3, 2, 1, 0, 4, 8, 7, 6, 5].getD i i } :
              PEqualNP.CircuitLowerBounds.Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            ([3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          j false := by
    have hlt : ∀ j : ℕ, j < 9 → [3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j < 9 := by
      intro j hj
      interval_cases j <;> decide
    have hge : ∀ j : ℕ, 9 ≤ j → [3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j = j := by
      intro j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
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
      · have hv : g.op.eval ((g.inputs.map fun i => [3, 2, 1, 0, 4, 8, 7, 6, 5].getD i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        by_cases hj : j < W.length
        · have hj' : [3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j < W'.length := by
            by_cases h : j < 9
            · have := hlt j h
              omega
            · rw [hge j (by omega)]
              omega
          have hWj := hW j
          generalize [3, 2, 1, 0, 4, 8, 7, 6, 5].getD j j = r at hj' hWj ⊢
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
  have sym : ∀ k : Fin 9,
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!x k]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧
        C'.size = C.size ∧
        ∀ y : Fin 9 → Bool,
          C'.eval (List.ofFn y ++ [y 0 && y 3] ++ [!y (![3, 2, 1, 0, 4, 8, 7, 6, 5] k)]) =
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
            y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5) := by
    intro k hk
    refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk
      (C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.Gate.mk g.op
          (g.inputs.map fun i => List.getD [3, 2, 1, 0, 4, 8, 7, 6, 5] i i)))
      (List.getD [3, 2, 1, 0, 4, 8, 7, 6, 5] C.output C.output), ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      refine ⟨(hfan g0 hg0).1, ?_⟩
      simpa using (hfan g0 hg0).2
    · delta PEqualNP.CircuitLowerBounds.Circuit.size
      simp
    · intro y
      have e := hk (fun i => y (![3, 2, 1, 0, 4, 8, 7, 6, 5] i))
      have hfy := hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
      refine Eq.trans ?_ (e.trans hfy)
      delta PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      apply hpre
      · simp
      · simp
      · intro j
        by_cases hj : j < 11
        · interval_cases j
          all_goals first
            | rfl
            | (show (y 0 && y 3) = (y 3 && y 0); exact Bool.and_comm _ _)
            | (simp [Fin.ext_iff]; fin_cases k <;> rfl)
        · have hj9 : List.getD [3, 2, 1, 0, 4, 8, 7, 6, 5] j j = j := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
            rfl
          rw [hj9]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  rcases L with _ | ⟨k, rest⟩
  · apply h1 C hfan
    intro x
    exact hE x
  · have hk : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++
        [!((List.ofFn x ++ [x 0 && x 3]).getD (↑k) false)]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x
      exact hE x
    fin_cases k
    · exact h3 0 (by decide) C hfan (fun x => hk x)
    · exact h3 1 (by decide) C hfan (fun x => hk x)
    · obtain ⟨C', hf', hs, hc⟩ := sym 2 (fun x => hk x)
      rw [← hs]
      exact h3 1 (by decide) C' hf' hc
    · obtain ⟨C', hf', hs, hc⟩ := sym 3 (fun x => hk x)
      rw [← hs]
      exact h3 0 (by decide) C' hf' hc
    · exact h3 4 (by decide) C hfan (fun x => hk x)
    · exact h4 5 (by decide) C hfan (fun x => hk x)
    · exact h4 6 (by decide) C hfan (fun x => hk x)
    · obtain ⟨C', hf', hs, hc⟩ := sym 7 (fun x => hk x)
      rw [← hs]
      exact h4 6 (by decide) C' hf' hc
    · obtain ⟨C', hf', hs, hc⟩ := sym 8 (fun x => hk x)
      rw [← hs]
      exact h4 5 (by decide) C' hf' hc
    · exact h2 C hfan (fun x => hk x)
    · exact h1 C hfan (fun x => hk x)
