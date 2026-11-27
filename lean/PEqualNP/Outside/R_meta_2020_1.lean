import Mathlib
import PEqualNP.Defs

-- Fix input four to false. The forced wire nine and the AND gate reading it become false,
-- and some other gate must read input four, since with input six false the edge function
-- still depends on input four. Two gates disappear and what is left computes the edge
-- function of the Petersen graph without both ends of one edge, on eight inputs.
theorem PEqualNP.Outside.R_meta_2020_1
    (cofactor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (eliminate : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 9 ∈ g.inputs) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) (C.size - 2)) :
    ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List ℕ) (x4 : ℕ),   x1.length + x2.length ≤ (13 : ℕ) →     (∀ x6 ∈ x1, (9 : ℕ) ∉ x6.inputs) →       (9 : ℕ) ∈ x3 →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.FanInTwo x8 → x4 ≤ (24 : ℕ) → x4 ≠ (9 : ℕ) → (∀ x12 ∈ x8.gates, ∀ x14 ∈ x12.inputs, x14 ≤ (24 : ℕ)) → ∃ (x13 : Fin (9 : ℕ) → Bool), x8.eval (List.ofFn x13 ++ [x13 (4 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ))]) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 x3 x4 hlen _ h9 x8 hfan _ _ _
  by_contra hcon
  push Not at hcon
  obtain ⟨D, hD, hs, hv⟩ := eliminate x8 hfan
    ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.and, x3⟩, by simp [x8], rfl, h9⟩ hcon
  have hsize : x8.size = x1.length + 1 + x2.length := by
    show (x1 ++ _ :: x2).length = _
    rw [List.length_append, List.length_cons]; omega
  exact cofactor ⟨D, hD, by omega, hv⟩
