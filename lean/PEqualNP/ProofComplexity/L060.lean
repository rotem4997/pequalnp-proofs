import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamilyK
import PEqualNP.ProofComplexity.Helpers.LinKWire
import PEqualNP.ProofComplexity.Helpers.LinKSim
import PEqualNP.ProofComplexity.L046

namespace PEqualNP.ProofComplexity

/-- L-pcx-060: for every `k ≥ 1`, some unsatisfiable 3-CNFs have no polynomially bounded
refutations in resolution over conjunctions of at most `k` parity equations (termwise
weakening). -/
theorem L060 : ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) ∧ ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (Fin n)), PEqualNP.ProofComplexity.IsLinKRefutation k (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → p.eval n < π.length :=
  ThreeCnfFamilyK.three_cnf_hard_k L046 (LinKWire.general LinKSim.simulation_refutation)

end PEqualNP.ProofComplexity
