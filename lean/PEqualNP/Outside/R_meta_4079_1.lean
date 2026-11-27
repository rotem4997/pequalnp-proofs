import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- First bound the edges supported by the two junk gates; then finish the
-- charge by the finitely many possible cardinalities of U*.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4079_1
    (supportBound : ∀ (G : SimpleGraph (Fin 11)) [_inst : DecidableRel G.Adj],
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      ∀ C : Circuit, IsLeastAO G C → (junk G C).card = 2 →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
          ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
        (Ustar G C).card ≤ 6)
    (boundedCharge : ∀ (G : SimpleGraph (Fin 11)) [_inst : DecidableRel G.Adj],
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        (junk G C).card = 2 →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
          ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
        3 ≤ (Ustar G C).card →
        2 * (centreless G C).card + (junk G C).card +
          (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (Ustar G C).card ≤ 6 →
        (Ustar G C).card ≤
          2 * (centreless G C).card + (junk G C).card +
            (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let G : SimpleGraph (Fin 11) := edgeGraph 11
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  dsimp only
  intro C hsize hleast htop hjunk hcover hthree hdouble
  exact boundedCharge G rfl C hsize hleast htop hjunk hcover hthree hdouble
    (supportBound G rfl C hleast hjunk hcover)
