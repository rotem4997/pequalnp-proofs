import PEqualNP.MetaComplexity.Helpers.McspReduce

/-- If P equals NP then MCSP is in P, because MCSP is in NP. -/
theorem PEqualNP.MetaComplexity.L010 :
    PEqualNP.Library.P = PEqualNP.Library.NP →
      PEqualNP.MetaComplexity.MCSP ∈ PEqualNP.Library.P := by
  intro h
  rw [h]
  exact PEqualNP.MetaComplexity.Helpers.mcsp_mem_NP
