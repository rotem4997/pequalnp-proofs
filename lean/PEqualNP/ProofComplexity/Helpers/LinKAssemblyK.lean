import PEqualNP.ProofComplexity.Helpers.LinKAssembly
import PEqualNP.ProofComplexity.Helpers.DegSizeArithK

/-!
# Degree to size for Res(k,+), with one hypothesis left

The general theorem of `LinKAssembly.lean` with the arithmetic statement discharged; only the
simulation of a refutation stays a hypothesis.
-/

namespace PEqualNP.ProofComplexity.LinKAsm

theorem degree_to_size_k_of_sim (hSim : StmtSimRefutation) : StmtGeneral :=
  degree_to_size_k hSim PEqualNP.ProofComplexity.DegSizeArithK.final_of_assembly_plan

end PEqualNP.ProofComplexity.LinKAsm
