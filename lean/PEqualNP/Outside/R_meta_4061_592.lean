import Mathlib
import PEqualNP.Defs

-- The singleton test input lies below both two-point test inputs, so by monotonicity of AND/OR
-- circuits it follows from either; what remains is two points, and a nonincident point and line.
theorem PEqualNP.Outside.R_meta_4061_592
    (h1 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C →
      ∀ (j : ℕ) (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) →
        PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.EdgeOwnership.gateVal n C j y = true)
    (h2 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 1) = false)
    (h3 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 14) = false) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x9 : Fin (26 : ℕ)), x9 = (0 : Fin (26 : ℕ)) ∨ x9 = (1 : Fin (26 : ℕ)) ∨ x9 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x9) = Bool.false := by
  intro G _ adj C least j hj hop v hv
  rcases hv with rfl | rfl | rfl
  · have hsub : ∀ i : Fin 26, PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (0 : Fin 26) i = true →
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (1 : Fin 26) i = true := by
      intro i hi
      have hi' : decide (i = (0 : Fin 26) ∨ i = (0 : Fin 26)) = true := hi
      show decide (i = (0 : Fin 26) ∨ i = (1 : Fin 26)) = true
      rw [decide_eq_true_eq] at hi' ⊢
      exact Or.inl (hi'.elim id id)
    have h12 := h2 G adj C least j hj hop
    cases hval : PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 0) with
    | false => rfl
    | true =>
      have := h1 26 C least.1.1 j _ _ hsub hval
      rw [h12] at this
      exact absurd this (by decide)
  · exact h2 G adj C least j hj hop
  · exact h3 G adj C least j hj hop
