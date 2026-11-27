import PEqualNP.Defs

-- Separate a circuit transformation from the size accounting on its result.
-- Soundness is a statement about every assignment on which a gate fires.
theorem PEqualNP.Outside.R_meta_18023_1
    (hSound :
      ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ z : Fin (n + m) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C z =
            Decidable.decide (∃ (a : Fin n) (b : Fin m),
              R a b ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true)) →
        (∀ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ z : Fin (n + m) → Bool,
            PEqualNP.EdgeOwnership.gateVal (n + m) C j z = true →
              PEqualNP.MetaComplexity.circuitFun (n + m) C z = true) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, R a b) ∧
          (∀ a b, R a b → ∃ i, a ∈ A i ∧ b ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + 1)
    (hNormalize :
      ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ z : Fin (n + m) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C z =
            Decidable.decide (∃ (a : Fin n) (b : Fin m),
              R a b ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (n + m) D ∧ D.size ≤ C.size ∧
          PEqualNP.MetaComplexity.circuitFun (n + m) D =
            PEqualNP.MetaComplexity.circuitFun (n + m) C ∧
          ∀ j < D.size,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
              PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ z : Fin (n + m) → Bool,
              PEqualNP.EdgeOwnership.gateVal (n + m) D j z = true →
                PEqualNP.MetaComplexity.circuitFun (n + m) D z = true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ) := by
  intro n m R _ C hC4 hAO hFun
  obtain ⟨D, hDAO, hSize, hEquiv, hGates⟩ :=
    hNormalize n m R C hC4 hAO hFun
  have hDFun (z : Fin (n + m) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (n + m) D z =
        Decidable.decide (∃ (a : Fin n) (b : Fin m),
          R a b ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true) :=
    (congrFun hEquiv z).trans (hFun z)
  obtain ⟨k, A, B, hNonempty, hContained, hCovers, hCost⟩ :=
    hSound n m R D hC4 hDAO hDFun hGates
  exact ⟨k, A, B, hNonempty, hContained, hCovers,
    hCost.trans (Nat.add_le_add_right hSize 1)⟩
