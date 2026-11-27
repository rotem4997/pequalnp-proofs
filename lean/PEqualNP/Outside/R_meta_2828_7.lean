import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2828_7
    (h1 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, C.gates[0]? = some g →
        (∃ d : Bool, g.op = fun u v : Bool => u == true && v == d) ∧
        [g.left, g.right] ≤ [List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left,
          List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right]) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (h2 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, C.gates[0]? = some g →
        (∃ d : Bool, g.op = fun u v : Bool => u == false && v == d) ∧
        [g.left, g.right] ≤ [List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left,
          List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right]) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b hops hfun
  -- the symmetry (0 1)(2 5)(3 8)(4 6) of the graph, which fixes the wire x0 OR x1
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
  have hpre : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.MetaComplexity.BinaryGate =>
            PEqualNP.MetaComplexity.BinaryGate.mk g.op
              (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left)
              (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right)).foldl
          (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) W').getD
            (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] j j) false =
        (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) W).getD
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
      · have hv : g.op (W'.getD (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left) false)
            (W'.getD (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right) false) =
            g.op (W.getD g.left false) (W.getD g.right false) := by
          rw [hW g.left, hW g.right]
        intro j
        rw [hv]
        generalize g.op (W.getD g.left false) (W.getD g.right false) = v
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
  have hcase : ∀ D : PEqualNP.MetaComplexity.BinaryCircuit,
      (∀ g ∈ D.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        [g.left, g.right] ≤ [List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left,
          List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right]) →
      (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ D.size := by
    intro D hD hcan hDf
    cases hg0 : D.gates[0]? with
    | none =>
      apply h1 D b hD _ hDf
      intro g hg
      rw [hg0] at hg
      exact absurd hg (by simp)
    | some g0 =>
      obtain ⟨c, d, hcd⟩ := hD g0 (List.mem_of_getElem? hg0)
      cases c
      · apply h2 D b hD _ hDf
        intro g hg
        rw [hg0] at hg
        cases hg
        exact ⟨⟨d, hcd⟩, hcan g0 hg0⟩
      · apply h1 D b hD _ hDf
        intro g hg
        rw [hg0] at hg
        cases hg
        exact ⟨⟨d, hcd⟩, hcan g0 hg0⟩
  cases hg : C.gates[0]? with
  | none =>
    apply hcase C hops _ hfun
    intro g h
    rw [hg] at h
    exact absurd h (by simp)
  | some g =>
    rcases le_total [g.left, g.right] [List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left,
        List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right] with hc | hc
    · apply hcase C hops _ hfun
      intro g' h
      rw [hg] at h
      cases h
      exact hc
    · have hsize := hcase
        (PEqualNP.MetaComplexity.BinaryCircuit.mk
          (C.gates.map fun g : PEqualNP.MetaComplexity.BinaryGate =>
            PEqualNP.MetaComplexity.BinaryGate.mk g.op
              (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.left g.left)
              (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] g.right g.right))
          (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] C.output C.output)) ?_ ?_ ?_
      · have hszB : ∀ D : PEqualNP.MetaComplexity.BinaryCircuit, D.size = D.gates.length :=
          fun _ => rfl
        rw [hszB] at hsize
        rw [hszB]
        simpa using hsize
      · intro g' hg'
        simp only [List.mem_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := hg'
        exact hops g0 hg0
      · intro g' h
        simp only [List.getElem?_map, hg, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [hinv]
        exact hc
      · intro y
        have hf := hfun (fun i => y (![1, 0, 5, 8, 6, 2, 4, 7, 3] i))
        have e := hpre C.gates
          (List.ofFn (fun i => y (![1, 0, 5, 8, 6, 2, 4, 7, 3] i)) ++
            [y (![1, 0, 5, 8, 6, 2, 4, 7, 3] 0) || y (![1, 0, 5, 8, 6, 2, 4, 7, 3] 1), false])
          (List.ofFn y ++ [y 0 || y 1, false]) (by simp) (by simp) ?_ C.output
        · have hevB : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit) (l : List Bool), D.eval l =
              (D.gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)])
                l).getD D.output false := fun _ _ => rfl
          rw [hevB] at hf
          rw [hevB]
          dsimp only at hf ⊢
          rw [e, hf]
          exact hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
        · intro j
          by_cases hj : j < 11
          · interval_cases j
            all_goals first
              | rfl
              | (show (y 0 || y 1) = (y 1 || y 0); exact Bool.or_comm _ _)
          · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
