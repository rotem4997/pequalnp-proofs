import PEqualNP.Library.L014

/-- NP is inside EXP: restatement of the brute-force bound on the class EXP. -/
theorem PEqualNP.Library.L052 : PEqualNP.Library.NP ⊆ PEqualNP.Library.EXP :=
  fun L hL => PEqualNP.Library.L014 L hL
