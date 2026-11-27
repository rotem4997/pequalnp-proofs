import PEqualNP.MetaComplexity.Helpers.MachinePair

/-- The length of the code of a CNF formula, as a one-entry list of unary numbers, is
computable in polynomial time from the code. -/
theorem PEqualNP.MetaComplexity.L506 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (fun φ : PEqualNP.Search.CNF => [(PEqualNP.Search.encodeCNF φ).length]) :=
  PEqualNP.MetaComplexity.Helpers.MachinePair.cpt_codeLength
