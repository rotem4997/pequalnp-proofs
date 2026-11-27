import PEqualNP.Search.Helpers.Flatten.Basic
import PEqualNP.Library.L104

/-- The bit pigeonhole formula with `2 ^ (8 m) + 1` pigeons and `2 ^ (8 m)` holes has a
dag-like Res(lin) refutation over the integers: the witness for L-lib-102, obtained by
flattening the tree-like refutation of L-lib-104. -/
theorem PEqualNP.Library.L116 : ∀ m : ℕ, ∃ π : List (PEqualNP.Search.QLine (Fin (2 ^ (8 * m) + 1) × Fin (8 * m))), PEqualNP.Search.IsResLinQRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ (8 * m) + 1) (8 * m)) π :=
  fun m =>
    let ⟨t⟩ := PEqualNP.Library.L104 (8 * m)
    ⟨PEqualNP.Search.Helpers.Flatten.flatten t, PEqualNP.Search.Helpers.Flatten.refutation t⟩
