import PEqualNP.Search.Helpers.BW.Restricted

/-- Restricted resolution over linear equations (width at most `4 l`, coefficients at most
`2 ^ l`) needs superpolynomially many lines to refute bit pigeonhole. -/
theorem PEqualNP.Library.L091 : ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.Search.IsResLinQRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → (∀ L ∈ π, L.length ≤ 4 * l ∧ ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ 2 ^ l) → p.eval (2 ^ l) < π.length :=
  PEqualNP.Search.Helpers.BW.restricted_superpoly
