import PEqualNP.ProofComplexity.Helpers.LinKStrength

namespace PEqualNP.ProofComplexity

/-- L-pcx-058: termwise weakening contains both syntactic weakenings: adding terms to a line,
and replacing one term of a line by a part of it. -/
theorem L058 : ∀ (V : Type) [DecidableEq V] (L M : PEqualNP.ProofComplexity.LinKLine V), ((L ⊆ M) → PEqualNP.ProofComplexity.IsLinKWeakening L M) ∧ (∀ T T' : PEqualNP.ProofComplexity.LinTerm V, T ∈ L → T' ⊆ T → M = L.erase T ∪ {T'} → PEqualNP.ProofComplexity.IsLinKWeakening L M) :=
  fun _ _ _ _ => ⟨Helpers.LinKStrength.weak_of_subset,
    fun _ _ _ hsub hM => Helpers.LinKStrength.weak_of_andElim hsub hM⟩

end PEqualNP.ProofComplexity
