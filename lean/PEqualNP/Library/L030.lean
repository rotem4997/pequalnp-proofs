import PEqualNP.Library.SearchHelpers.TwoSatCPT

/-- 2-SAT is in P (Krom 1967): a formula whose clauses have one or two literals is satisfiable
exactly when no literal reaches its negation and is reached from it in the implication graph,
and the closures are computed by a polynomial number of rotations of the encoded formula. -/
theorem PEqualNP.Library.L030 : PEqualNP.Search.KSAT 2 ∈ PEqualNP.Library.P :=
  PEqualNP.Library.SearchHelpers.TwoSat.ksat2_in_P
