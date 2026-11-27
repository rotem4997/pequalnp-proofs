import PEqualNP.Search.Helpers.Tree.Delayer

/-- Tree-like Res(lin) over the integers needs superpolynomially many lines on the bit
pigeonhole principle with `2 ^ l + 1` pigeons and `2 ^ l` holes. -/
theorem PEqualNP.Library.L103 : ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ T : PEqualNP.Search.ResLinQTree (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) [], p.eval (2 ^ l) < T.size :=
  PEqualNP.Search.Helpers.Tree.tree_superpoly
