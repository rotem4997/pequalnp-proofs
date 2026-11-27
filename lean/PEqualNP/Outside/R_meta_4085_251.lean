import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix vertex zero to false. The eleven inputs then have eleven distinct wire functions:
-- the nine remaining variables and the two constants. Count distinct functions on all
-- wires, including internal wires, so later repetitions also count against the budget.
-- The nine-vertex bound is the statement already proved in L_meta_2331.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4085_251
    (compress : ∀ C : Circuit, FanInTwo C →
      (∃ y : Fin 9 → Bool, C.eval [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true] = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 11 ≤
        (Finset.univ.image (fun w : Fin (11 + C.size) => fun y : Fin 9 → Bool =>
          (C.wires [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true]).getD w.val false)).card ∧
        ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = C.eval [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true])
    (nine : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (remaining : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      26 ≤ (Finset.univ.image (fun w : Fin (11 + C.size) => fun y : Fin 9 → Bool =>
          (C.wires [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true]).getD w.val false)).card →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5 := by
  intro C fan budget _
  by_contra! computes
  let embed (y : Fin 9 → Bool) (i : Fin 10) : Bool :=
    ([false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] : List Bool).getD i.val false
  have input (y : Fin 9 → Bool) : List.ofFn (embed y) ++ [!(embed y 0)] =
      [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true] := by rfl
  have graph : ∀ y : Fin 9 → Bool, (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) (embed y) = (fun y : Fin 9 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) y := by
    decide +kernel
  have restricted (y : Fin 9 → Bool) : C.eval [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8, true] = (fun y : Fin 9 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) y := by
    rw [← input y]
    exact (computes (embed y)).trans (graph y)
  obtain ⟨D, fanD, countD, simD⟩ := compress C fan ⟨fun _ => false, restricted (fun _ => false)⟩
  have sizeD := nine D fanD (funext (fun y => (simD y).trans (restricted y)))
  obtain ⟨x, different⟩ := remaining C fan budget (by omega)
  exact different (computes x)
