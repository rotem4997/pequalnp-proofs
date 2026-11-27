import PEqualNP.ProofComplexity.Helpers.LinKAssembly
import PEqualNP.ProofComplexity.Helpers.LinKFinal
import PEqualNP.ProofComplexity.Helpers.DegSizeArithK

/-!
# Wiring of L-pcx-054 (Res(k, ⊕) on functional pigeonhole)

Everything except the simulation of a refutation is proved: the counting core
(`DegSizeGainK`), the arithmetic and soundness (`DegSizeArithK`), the assembly inequality and
the general theorem (`LinKAssembly`), and the final assembly on the expander (`LinKFinal`).
This file composes them, with the simulation of a refutation as the one hypothesis.
-/

namespace PEqualNP.ProofComplexity.LinKWire

/-- The general degree-to-size theorem for Res(k, ⊕), from the simulation of a refutation. -/
theorem general (hSim : LinKAsm.StmtSimRefutation) : LinKFinal.StmtLinK :=
  LinKAsm.degree_to_size_k hSim DegSizeArithK.final_of_assembly_plan

/-- L-pcx-054 from the simulation of a refutation. -/
theorem fun_not_poly (hSim : LinKAsm.StmtSimRefutation) :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), N < m ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length :=
  LinKFinal.fun_not_poly (general hSim)

end PEqualNP.ProofComplexity.LinKWire
