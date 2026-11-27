import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A block of inputs produces different residual functions on the remaining vertices.
-- Every circuit must distinguish these residuals on wires leaving the block.
-- The second child restricts the search to circuits satisfying all of these bounds.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2598_704
    (topology : ∀ C : Circuit, (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) → (∀ (S : Finset (Fin 10)) (A B : Finset ℕ),
      (∀ i : Fin 10, i.val ∈ A ↔ i ∈ S) → (10 ∈ A ↔ 0 ∈ S) →
      (∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
        (11 + t.val ∈ A → i ∈ A) ∧ (11 + t.val ∉ A → i ∈ A → i ∈ B)) →
      (C.output ∈ A → C.output ∈ B) →
      ([1,2,4,6,9,12,9,9,5,3,2] : List ℕ).getD S.card 0 ≤
        (Finset.univ.image (fun x : Fin 10 → Bool => fun i : ↥B =>
          (C.wires (List.ofFn x ++ [!x 0])).getD i.val false)).card))
    (residual : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → (∀ (S : Finset (Fin 10)) (A B : Finset ℕ),
      (∀ i : Fin 10, i.val ∈ A ↔ i ∈ S) → (10 ∈ A ↔ 0 ∈ S) →
      (∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
        (11 + t.val ∈ A → i ∈ A) ∧ (11 + t.val ∉ A → i ∈ A → i ∈ B)) →
      (C.output ∈ A → C.output ∈ B) →
      ([1,2,4,6,9,12,9,9,5,3,2] : List ℕ).getD S.card 0 ≤
        (Finset.univ.image (fun x : Fin 10 → Bool => fun i : ↥B =>
          (C.wires (List.ofFn x ++ [!x 0])).getD i.val false)).card) → ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hf hs
  by_contra! h
  have eqf : ∀ x : Fin 10 → Bool, (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x = (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x := by decide +kernel
  have hc : (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) := fun x => (h x).trans (eqf x)
  obtain ⟨x, hx⟩ := residual C hf hs (topology C hc)
  exact hx (hc x)
