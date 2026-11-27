import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2382_168
    
(h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        (∀ x9 x10 : Fin n, s(x9, x10) ∈ PEqualNP.TopForm.Ustar G C →
          ∃ x12 ∈ PEqualNP.TopForm.junk G C,
            PEqualNP.EdgeOwnership.gateVal n C x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        (PEqualNP.TopForm.Ustar G C).card ≤
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          ((PEqualNP.TopForm.orN G C) \ (PEqualNP.TopForm.lam G C)).card)

(h2 : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.NoFourCycle G)
 :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8

  := by
    intro x1def x2 hsize hleast htop hjunk x7def x8def hcover hlt
    exact h1 (11 : ℕ) x1def x2 (h2 x1def (by decide)) hleast htop hjunk hcover
