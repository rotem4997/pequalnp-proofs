import PEqualNP.Search.Helpers.BWTri.Bridge

/-- Beame-Whitmeyer: triangle dags for the bit pigeonhole search problem are superpolynomial. -/
theorem PEqualNP.Library.L105 : ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ ρ : List (Set (Fin (2 ^ l + 1) × Fin l → Bool)),
    PEqualNP.Search.IsTriDagFor (fun v : Fin (2 ^ l + 1) × Fin l => decide (2 * v.2.val < l))
      (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) ρ → p.eval (2 ^ l) < ρ.length :=
  PEqualNP.Search.Helpers.BWTri.bwtri_superpoly
