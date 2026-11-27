import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2382_1 :
    (let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 21 →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).card = 2 →
      (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G C →
        ∃ g ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true) →
      3 ≤ (PEqualNP.TopForm.Ustar G C).card →
      2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
          2 * (PEqualNP.TopForm.Ustar G C).card →
      (PEqualNP.TopForm.Ustar G C).card ≤
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) →
    (let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 21 →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      3 ≤ (PEqualNP.TopForm.junk G C).card →
      (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G C →
        ∃ g ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true) →
      3 ≤ (PEqualNP.TopForm.Ustar G C).card →
      2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
          2 * (PEqualNP.TopForm.Ustar G C).card →
      (PEqualNP.TopForm.Ustar G C).card ≤
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) →
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  intro twoJunk manyJunk
  dsimp only
  intro C hsize hleast htop hjunk
  intro hcover hdouble
  by_cases hsmall : (PEqualNP.TopForm.Ustar
      (PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card ≤ 2
  · omega
  · have hU3 : 3 ≤ (PEqualNP.TopForm.Ustar
        (PEqualNP.EdgeOwnership.edgeGraph 11
          [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
            (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card := by omega
    by_cases heq : (PEqualNP.TopForm.junk
        (PEqualNP.EdgeOwnership.edgeGraph 11
          [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
            (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card = 2
    · exact twoJunk C hsize hleast htop heq hcover hU3 hdouble
    · have hJ3 : 3 ≤ (PEqualNP.TopForm.junk
          (PEqualNP.EdgeOwnership.edgeGraph 11
            [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
              (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card := by omega
      exact manyJunk C hsize hleast htop hJ3 hcover hU3 hdouble
