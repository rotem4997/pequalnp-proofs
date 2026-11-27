import PEqualNP.Search.Helpers.SemanticWeakening

/-- The bit pigeonhole formula with `2 ^ l + 1` pigeons has dag-like refutations in Res(lin)
over the integers of size polynomial in `2 ^ l`: the weakening rule is semantic, so the line
"some two pigeons sit in the same hole" costs one step, and each of its equations is cut
against one clause of the formula. -/
theorem PEqualNP.Search.L004Refutation : ¬ (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.Search.IsResLinQRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < PEqualNP.Search.resLinQSize π) := by
  intro h
  obtain ⟨l, hl⟩ := h PEqualNP.Search.Helpers.bphpPoly
  obtain ⟨π, hπ, hs⟩ := PEqualNP.Search.Helpers.bphp_short l
  exact absurd (hl π hπ) (not_lt.mpr hs)
