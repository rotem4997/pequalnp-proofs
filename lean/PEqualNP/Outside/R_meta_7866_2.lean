import PEqualNP.Defs

-- Credit: the case-split reduction of foudress (R_meta_1710_64, #23768): split the range, keep the larger constant.
theorem PEqualNP.Outside.R_meta_7866_2
    (caseA : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), x2 < (50 : ℕ) → PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt)
    (caseB : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), (50 : ℕ) ≤ x2 → PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt := by
  obtain ⟨cA, hA⟩ := caseA
  obtain ⟨cB, hB⟩ := caseB
  refine ⟨max cA cB, ?_⟩
  intro x2 x3 x4 x5 x6 v_0 v_1 v_2 v_3 v_4 v_5 v_6
  rcases Nat.lt_or_ge x2 (50 : ℕ) with h | h
  · exact Nat.le_trans (@hA x2 x3 x4 x5 x6 h v_0 v_1 v_2 v_3 v_4 v_5 v_6) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_max_left cA cB)) _)
  · exact Nat.le_trans (@hB x2 x3 x4 x5 x6 h v_0 v_1 v_2 v_3 v_4 v_5 v_6) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_max_right cA cB)) _)
