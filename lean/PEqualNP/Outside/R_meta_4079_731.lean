import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Two junk gates: either the charge p = 2 Z + R is at least two, or the junk gates are nested in
-- the normal form of the first statement (no centreless top, g read by h alone, h read by one
-- gate m, and m the only OR gate outside Lambda that is not below F; every edge of U* makes g and
-- h true). The first statement holds for every graph and is proved. In the normal form B = 3,
-- so the second statement asks for at most three edges in U*. With p at least two, B is at least
-- four and the third statement is the step for at least five edges in U*.
theorem PEqualNP.Outside.R_meta_4079_731
    (dich : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C → (junk G C).card = 2 →
      2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card ∨
      ∃ g h m : ℕ, junk G C = {g, h} ∧ InCone n C g h ∧ centreless G C = ∅ ∧
        readers n C g = {h} ∧ readers n C h = {m} ∧ orN G C \ lam G C = {m} ∧
        ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true)
    (nf : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
        (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : Circuit) (g h m : ℕ), C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        junk G C = {g, h} → InCone 11 C g h → centreless G C = ∅ → readers 11 C g = {h} →
        readers 11 C h = {m} → orN G C \ lam G C = {m} →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
          gateVal 11 C g (pairInput u v) = true ∧ gateVal 11 C h (pairInput u v) = true) →
        (Ustar G C).card ≤ 3)
    (two : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
        (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → (junk G C).card = 2 →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C → ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
        5 ≤ (Ustar G C).card → 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
          2 * (Ustar G C).card →
        (Ustar G C).card ≤
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  dsimp only at nf two ⊢
  intro C hsize hleast htop hjunk hcover hU3 hlt
  have hE : (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
      (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9),
      (8, 9)]).edgeFinset.Nonempty := by
    refine ⟨s(8, 9), SimpleGraph.mem_edgeFinset.mpr ?_⟩
    decide +kernel
  rcases dich 11 _ C hE hleast htop hjunk with hp | ⟨g, h, m, hJ, hc, hZ, hrg, hrh, hR, hU⟩
  · by_cases hU5 : 5 ≤ (Ustar (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card
    · exact two C hsize hleast htop hjunk hcover hU5 hp hlt
    · omega
  · have key := nf C g h m hsize hleast htop hJ hc hZ hrg hrh hR hU
    rw [hZ, hR, Finset.card_empty, Finset.card_singleton]
    omega
