import PEqualNP.ProofComplexity.Helpers.LinKSimA
import PEqualNP.ProofComplexity.Helpers.LinKSimAnd
import PEqualNP.ProofComplexity.Helpers.LinKSimWeak
import PEqualNP.ProofComplexity.Helpers.LinKSimDrv
import PEqualNP.ProofComplexity.Helpers.LinKAssembly

/-!
# The simulation of a Res(k, ⊕) refutation in polynomial calculus

Helper module (proofs only, no statement may use it). The composition of the rule steps
(transfer, axiom and cut in `LinKSimA`, and-introduction in `LinKSimAnd`, termwise weakening in
`LinKSimWeak`) with the induction over a derivation (`LinKSimDrv`): the statement of the plan
for a derivation and for a refutation.
-/

namespace PEqualNP.ProofComplexity.LinKSim

open PEqualNP.ProofComplexity.LinKPlan PEqualNP.ProofComplexity.LinKSimA

/-- The and-introduction rule. -/
theorem step_andIntro : AndRule := step_andIntro_of transfer_k

/-- The termwise weakening rule. -/
theorem step_weak : WeakRule := step_weak_of transfer_k

/-- The simulation of a derivation. -/
theorem simulation : SimDrv := simulation_of step_ax_k step_cut_k step_andIntro step_weak

/-- The simulation of a refutation: the plan's statement, as `LinKAsm.StmtSimRefutation`. -/
theorem simulation_refutation : PEqualNP.ProofComplexity.LinKAsm.StmtSimRefutation :=
  simulation_refutation_of step_ax_k step_cut_k step_andIntro step_weak

end PEqualNP.ProofComplexity.LinKSim
