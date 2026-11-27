import PEqualNP.Library.SearchHelpers.SatVerifierCPT

/-- SAT is in NP. -/
theorem PEqualNP.Library.L029 : PEqualNP.Search.SAT ∈ PEqualNP.Library.NP :=
  PEqualNP.Library.SearchHelpers.SatV.SAT_in_NP_of PEqualNP.Library.SearchHelpers.SatV.cpt_SV
