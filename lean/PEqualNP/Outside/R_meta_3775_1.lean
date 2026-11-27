import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3775_1
    (hTwo :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (PEqualNP.TopForm.junk x3 x7).card = (2 : ℕ) →
          (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))
    (hCluster :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
          (∃ j ∈ PEqualNP.TopForm.junk x3 x7, ∀ i ∈ PEqualNP.TopForm.junk x3 x7,
            i = j ∨ PEqualNP.EdgeOwnership.InCone x2 x7 i j) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))
    (hMulti :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
          (¬ ∃ j ∈ PEqualNP.TopForm.junk x3 x7, ∀ i ∈ PEqualNP.TopForm.junk x3 x7,
            i = j ∨ PEqualNP.EdgeOwnership.InCone x2 x7 i j) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, h1⟩ := hTwo
  obtain ⟨c2, h2⟩ := hCluster
  obtain ⟨c3, h3⟩ := hMulti
  refine ⟨max c1 (max c2 c3), ?_⟩
  intro x2 x3 x4 hg he x7 hL hT hj hnest hno
  by_cases hj2 : (PEqualNP.TopForm.junk x3 x7).card = 2
  · exact le_trans (h1 x2 x3 hg he x7 hL hT hj2 hnest hno)
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · have hj3 : 3 ≤ (PEqualNP.TopForm.junk x3 x7).card := by omega
    by_cases hdom : ∃ j ∈ PEqualNP.TopForm.junk x3 x7,
        ∀ i ∈ PEqualNP.TopForm.junk x3 x7, i = j ∨ PEqualNP.EdgeOwnership.InCone x2 x7 i j
    · exact le_trans (h2 x2 x3 hg he x7 hL hT hj3 hdom hno)
        (Nat.mul_le_mul_right _ (le_trans (le_max_left _ _) (le_max_right _ _)))
    · exact le_trans (h3 x2 x3 hg he x7 hL hT hj3 hdom hno)
        (Nat.mul_le_mul_right _ (le_trans (le_max_right _ _) (le_max_right _ _)))
