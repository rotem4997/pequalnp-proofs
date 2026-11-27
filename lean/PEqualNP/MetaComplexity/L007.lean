import PEqualNP.MetaComplexity.Helpers.McspReduce

/-- MCSP is in NP: a truth table is a partial truth table with every entry defined, so MCSP
reduces in polynomial time to partial MCSP, which is in NP. -/
theorem PEqualNP.MetaComplexity.L007 :
    PEqualNP.MetaComplexity.MCSP ∈ PEqualNP.Library.NP :=
  PEqualNP.MetaComplexity.Helpers.mcsp_mem_NP
