import PEqualNP.Search.Helpers.Width.Walk

/-- Res(lin) over the integers needs lines of n^Omega(1) equations on bit PHP. -/
theorem PEqualNP.Library.L102 : ∀ m : ℕ, 8 ≤ m →
    ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ (8 * m) + 1) × Fin (8 * m))),
    PEqualNP.Search.IsResLinQRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ (8 * m) + 1) (8 * m)) π →
    ∃ L ∈ π, 2 ^ m < L.length :=
  fun m hm π hπ => PEqualNP.Search.Helpers.Width.width_lower m hm π hπ
