import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce L-meta-4328 (the testBound child of R_meta_1894_2) by support size.
-- An AND gate firing on the ten-position test input has a firing support
-- of at most two input bits (take the first firing AND gate; its operands
-- trace back through OR gates only, to input bits in the test set). The
-- remaining case is an AND gate firing on such a small support, which is
-- handled by the counting bound (boundSparse of R_meta_1894_1) together
-- with the pair tests and the closed-set tests.
theorem PEqualNP.Outside.R_meta_4328_1
    (support : ∀ (C : Circuit), Monotone2 C →
      (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        (C.wires (List.ofFn fun (i : Fin (42 : ℕ)) => Decidable.decide (↑i ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + j) Bool.false = Bool.true) →
      ∃ (Y : Finset (Fin (42 : ℕ))), (∀ (v : Fin (42 : ℕ)), v ∈ Y → v.val ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) ∧ Y.card ≤ (2 : ℕ) ∧
        (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun (i : Fin (42 : ℕ)) => Decidable.decide (i ∈ Y))).getD ((42 : ℕ) + j) Bool.false = Bool.true))
    (smallFalse : ∀ (C : Circuit), Monotone2 C → C.size ≤ (124 : ℕ) →
      ∀ (Y : Finset (Fin (42 : ℕ))), (∀ (v : Fin (42 : ℕ)), v ∈ Y → v.val ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → Y.card ≤ (2 : ℕ) →
      (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun (i : Fin (42 : ℕ)) => Decidable.decide (i ∈ Y))).getD ((42 : ℕ) + j) Bool.false = Bool.true) →
      (∀ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → C.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u ∨ w = v)) = Bool.true) →
      (∀ (x : Fin (42 : ℕ) → Bool), (∀ (u : Fin (42 : ℕ)), x u = Bool.true ↔ ∀ (v : Fin (42 : ℕ)), x v = Bool.true → ¬((↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∨ (↑v < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑u ∧ (↑u + (21 : ℕ) - ↑v) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]))) → C.eval (List.ofFn x) = Bool.false) →
      False) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (124 : ℕ) → (∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) → (∀ (x7 x8 : Fin (42 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7 ∨ x10 = x8)) = Bool.true) → (∀ (x8 : Fin (42 : ℕ) → Bool), x2 x8 → x3.eval (List.ofFn x8) = Bool.false) → False := by
  intro x1 x2 C hmono hsize hactive hpair hclosed
  obtain ⟨Y, hYT, hcard, hY⟩ := support C hmono hactive
  exact smallFalse C hmono hsize Y hYT hcard hY hpair hclosed
