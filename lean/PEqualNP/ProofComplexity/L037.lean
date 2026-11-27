import PEqualNP.ProofComplexity.Helpers.ExpBeatsPoly
import PEqualNP.Defs.ProofComplexityLin
import PEqualNP.Defs.ProofComplexityBit

namespace PEqualNP.ProofComplexity

/-- L-pcx-037: an exponential size lower bound for refutations of the bit pigeonhole
principle beats every polynomial in the number of pigeons. -/
theorem L037 : (∀ (l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l))), 32 ≤ l → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) < (π.length : ℝ)) → ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < π.length :=
  fun h p => by
    obtain ⟨l, hl, hle⟩ := Helpers.exists_exp_beats_poly p
    refine ⟨l, fun π hπ => ?_⟩
    have := lt_of_le_of_lt hle (h l π hl hπ)
    exact_mod_cast this

end PEqualNP.ProofComplexity
