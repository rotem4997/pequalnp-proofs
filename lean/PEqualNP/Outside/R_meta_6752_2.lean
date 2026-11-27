import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6752_2
    (h_two :
      let x1 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
          have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2
          have x7 : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar x1 x2
          x6.card = 2 →
          x6.card < x7.card →
          ∀ x9 ⊆ x7, x9.Nonempty →
          (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card →
          (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ 1) →
          (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) →
          x9.card ≤ 2 * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) +
            (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (h_many :
      let x1 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
          have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2
          have x7 : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar x1 x2
          3 ≤ x6.card →
          x6.card < x7.card →
          ∀ x9 ⊆ x7, x9.Nonempty →
          (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card →
          (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ 1) →
          (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) →
          x9.card ≤ 2 * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) +
            (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → ∀ x9 ⊆ x7, x9.Nonempty → (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card → (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ (1 : ℕ)) → (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) → x9.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro x1 x2 hsize hleast htop x6 x7 hjunk x9 hsub hnon hdisj hcard1 hcover
  by_cases hle : x7.card ≤ x6.card
  · have hpart : x7.card = x9.card + (x7 \ x9).card := by
      rw [← Finset.card_sdiff_add_card_eq_card hsub, add_comm]
    omega
  · have hlt : x6.card < x7.card := by omega
    rcases eq_or_lt_of_le hjunk with heq | hgt
    · exact h_two x2 hsize hleast htop heq.symm hlt x9 hsub hnon hdisj hcard1 hcover
    · have h3 : 3 ≤ x6.card := by omega
      exact h_many x2 hsize hleast htop h3 hlt x9 hsub hnon hdisj hcard1 hcover
