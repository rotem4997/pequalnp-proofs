import PEqualNP.MetaComplexity.Helpers.Machines.StrEq

/-- Equality of two binary strings, given as a pair, is decided in polynomial time. -/
theorem PEqualNP.MetaComplexity.L022 :
    PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair
      {p : List Bool × List Bool | p.1 = p.2} :=
  ⟨fun p => decide (p.1 = p.2), fun p => by simp,
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)⟩
