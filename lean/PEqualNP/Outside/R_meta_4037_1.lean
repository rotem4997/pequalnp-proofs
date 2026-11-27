import Mathlib
import PEqualNP.Defs

-- Reduction 1 for L-meta-4037: the two halves of the uniqueness condition.
-- hZero: input 0 is never read by exactly one gate, and that gate an OR gate.
-- hTen: input 10 is never read by exactly one gate, and that gate an AND gate.
-- Each half is the argument for one wire; the step's statement is the claim that not
-- both halves fail at once.
theorem PEqualNP.Outside.R_meta_4037_1
    (hZero : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin C.gates.length),
      PEqualNP.MetaComplexity.FanInTwo C → C.size = (18 : ℕ) →
      (∀ (x4 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) →
      (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (0 : ℕ) ∈ (C.gates.get x5).inputs →
      ∃ (x9 : Fin C.gates.length), x9 ≠ x5 ∧
        (((C.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (C.gates.get x9).inputs.head? = Option.some (0 : ℕ)) ∧
          ((C.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∈ (C.gates.get x9).inputs)))
    (hTen : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin C.gates.length),
      PEqualNP.MetaComplexity.FanInTwo C → C.size = (18 : ℕ) →
      (∀ (x4 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) →
      (C.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (10 : ℕ) ∈ (C.gates.get x6).inputs →
      ∃ (x9 : Fin C.gates.length), x9 ≠ x6 ∧
        (((C.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (C.gates.get x9).inputs.head? = Option.some (10 : ℕ)) ∧
          ((C.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (C.gates.get x9).inputs))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → ¬∃ (x5 : Fin x1.gates.length) (x6 : Fin x1.gates.length), x5 ≠ x6 ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∈ (x1.gates.get x5).inputs ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (10 : ℕ) ∈ (x1.gates.get x6).inputs ∧ ∀ x7 ∈ [((0 : ℕ), x5), ((10 : ℕ), x6)], ∀ (x9 : Fin x1.gates.length), ((x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x9).inputs.head? = Option.some x7.1 → x9 = x7.2) ∧ ((x1.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.1 ∈ (x1.gates.get x9).inputs → x9 = x7.2) := by
  intro x1 hfan hsize hcomp
  rintro ⟨x5, x6, hne, h5op, h5in, h6op, h6in, huniq⟩
  obtain ⟨x9, hne9, hA, hB⟩ := hZero x1 x5 hfan hsize hcomp h5op h5in
  have _ := hTen x1 x6 hfan hsize hcomp h6op h6in
  have hmem : (((0 : ℕ), x5) : ℕ × Fin x1.gates.length) ∈
      [((0 : ℕ), x5), ((10 : ℕ), x6)] := by simp
  have hinst := huniq ((0 : ℕ), x5) hmem x9
  by_cases h : (x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact hne9 (hinst.1 h (hA h))
  · exact hne9 (hinst.2 h (hB h))
