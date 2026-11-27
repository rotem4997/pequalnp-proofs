import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4061_417
    (h0 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 0) = false)
    (h1 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 1) = false)
    (h14 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
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
  · exact h0 G adj C least j hj hop
  · exact h1 G adj C least j hj hop
  · exact h14 G adj C least j hj hop
