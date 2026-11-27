import PEqualNP.MetaComplexity.Helpers.Machines.VerifierPoly

/-- Partial MCSP is in NP: the witness lists, for every input, a copy of the circuit with that
input hardwired, and a polynomial-time verifier evaluates all copies at once. -/
theorem PEqualNP.MetaComplexity.L021 :
    PEqualNP.MetaComplexity.PartialMCSP ∈ PEqualNP.Library.NP :=
  PEqualNP.MetaComplexity.Helpers.Machines.partialMCSP_mem_NP
