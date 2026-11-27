import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1735_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         PEqualNP.TopForm.junk G C = ∅ → PEqualNP.TopForm.Ustar G C = ∅) →
    (∃ k1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         PEqualNP.TopForm.junk G C = {g} → (PEqualNP.TopForm.Ustar G C).card ≤ k1 * (C.size + 1)) →
    (∃ k2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         2 ≤ (PEqualNP.TopForm.junk G C).card →
         (∀ i ∈ PEqualNP.TopForm.junk G C, ∀ j ∈ PEqualNP.TopForm.junk G C, ¬ PEqualNP.EdgeOwnership.InCone n C i j) →
         (PEqualNP.TopForm.Ustar G C).card ≤ k2 * (C.size + 1)) →
    (∃ k3 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         2 ≤ (PEqualNP.TopForm.junk G C).card →
         (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.InCone n C i j) →
         (PEqualNP.TopForm.Ustar G C).card ≤ k3 * (C.size + 1)) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro c0 hc1 hc2 hc3
  obtain ⟨k1, h1⟩ := hc1
  obtain ⟨k2, h2⟩ := hc2
  obtain ⟨k3, h3⟩ := hc3
  refine ⟨max k1 (max k2 k3), ?_⟩
  intro n G _ hgirth hne C hL hT
  by_cases hj0 : (PEqualNP.TopForm.junk G C).card = 0
  · rw [c0 n G hgirth hne C hL hT (Finset.card_eq_zero.mp hj0)]
    simp
  · by_cases hj1 : (PEqualNP.TopForm.junk G C).card = 1
    · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
      exact (h1 n G hgirth hne C g hL hT hg).trans (Nat.mul_le_mul_right _ (le_max_left _ _))
    · have hj2 : 2 ≤ (PEqualNP.TopForm.junk G C).card := by omega
      by_cases hnest : ∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.InCone n C i j
      · exact (h3 n G hgirth hne C hL hT hj2 hnest).trans
          (Nat.mul_le_mul_right _ ((le_max_right k2 k3).trans (le_max_right k1 _)))
      · refine (h2 n G hgirth hne C hL hT hj2 ?_).trans
          (Nat.mul_le_mul_right _ ((le_max_left k2 k3).trans (le_max_right k1 _)))
        intro i hi j hj hic
        exact hnest ⟨i, hi, j, hj, hic⟩
