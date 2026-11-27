import Mathlib
import PEqualNP.Defs

-- Remove invalid wire reads and unused operands of negation gates, and trim the output.
theorem PEqualNP.Outside.R_meta_2592_408
    (normalize :
      let computes := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
        ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
            x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
      let legal := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ j : ℕ,
        let g := D.gates.getD j ⟨.or, []⟩
        (∀ i ∈ g.inputs, i < 10 + j) ∧ (g.op = .not → g.inputs.length ≤ 1)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → computes C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size ∧
          D.output + 1 = 10 + D.size ∧ legal D ∧
          ((∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∨ D.size < C.size) ∧ computes D)
    (bound :
      let computes := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
        ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
            x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
      let legal := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ j : ℕ,
        let g := D.gates.getD j ⟨.or, []⟩
        (∀ i ∈ g.inputs, i < 10 + j) ∧ (g.op = .not → g.inputs.length ≤ 1)
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 19 →
        D.output + 1 = 10 + D.size → legal D →
        (D.size < 19 ∨ ∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬ computes D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C hfan hsize hnot hcompute
  obtain ⟨D, hfanD, hsizeD, hout, hlegal, hcases, hcomputeD⟩ :=
    normalize C hfan hnot hcompute
  have hbudget : D.size < 19 ∨ ∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    rcases hcases with hneg | hlt
    · exact Or.inr hneg
    · exact Or.inl (hlt.trans_le hsize)
  exact bound D hfanD (hsizeD.trans hsize) hout hlegal hbudget hcomputeD
