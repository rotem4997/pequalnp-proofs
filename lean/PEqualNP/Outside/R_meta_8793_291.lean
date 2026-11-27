import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8793_291
    (count : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun (p l : Fin 26) => p.val < 13 ∧ 13 ≤ l.val ∧ (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      52 + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1)
    (balance : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun (p l : Fin 26) => p.val < 13 ∧ 13 ≤ l.val ∧ (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card → C.size ≤ 63 →
      13 + (PEqualNP.TopForm.Ustar G C).card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → (64 : ℕ) ≤ x3.size := by
  intro G _ C hG least top junk
  by_contra! hsmall
  have hc := count G C hG least top
  have hb := balance G C hG least top junk (by omega)
  omega
