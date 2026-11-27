import Mathlib
import PEqualNP.Defs

-- The 12-edge graph on 9 vertices given by adjacency rows: no circuit of AND, OR and NOT gates
-- of fan-in at most two with at most 15 gates computes its edge function.
-- lower: the checked L_meta_670 (the same bound for the graph in its standard numbering).
-- relabel: the checked L_meta_9109 (a circuit of at most 15 gates for the rows form gives one of
-- exactly 15 gates for the standard numbering).
-- The glue only matches the two ways the standard function is written.
theorem PEqualNP.Outside.R_meta_8133_11
    (lower : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (relabel : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = (15 : ℕ) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)))) x6) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)), x1 x2 = Bool.true ∧ x1 x3 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true)) (15 : ℕ) := by
  intro hC
  obtain ⟨C, hF, hs, hf⟩ := hC
  obtain ⟨D, hD, hDs, hDf⟩ := relabel C hF hs hf
  have key : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      ((a0 && a1) || ((a1 && a2) || ((a2 && a3) || ((a3 && a4) || ((a4 && a0) || ((a0 && a5) || ((a1 && a6) || ((a2 && a7) || ((a3 && a8) || ((a5 && a7) || ((a6 && a8) || ((a8 && a5) || false)))))))))))) =
      ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
    decide
  exact lower (Exists.intro D (And.intro hD (And.intro (le_of_eq hDs)
    (fun x => (hDf x).trans (key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8))))))
