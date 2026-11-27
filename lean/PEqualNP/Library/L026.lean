import PEqualNP.Library.SearchHelpers.Encoding

/-- The binary encoding of CNF formulas is injective. -/
theorem PEqualNP.Library.L026 : Function.Injective PEqualNP.Search.encodeCNF :=
  PEqualNP.Library.SearchHelpers.encodeCNF_injective
