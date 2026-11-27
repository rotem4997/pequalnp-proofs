import PEqualNP.ProofComplexity.Helpers.LinKSplit

namespace PEqualNP.ProofComplexity

/-- L-pcx-063: in Res(k, ⊕) a term with one equation to spare is split on any linear form in
exactly five further lines. -/
theorem L063 : ∀ (V : Type) [DecidableEq V] (k : ℕ) (F : Set (PEqualNP.ProofComplexity.LinKLine V)) (π : List (PEqualNP.ProofComplexity.LinKLine V)) (L : PEqualNP.ProofComplexity.LinKLine V) (T : PEqualNP.ProofComplexity.LinTerm V) (f : Finset V), PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.IsLinKWeakening F π → L ∈ π → T ∈ L → T.card + 1 ≤ k → ∃ new : List (PEqualNP.ProofComplexity.LinKLine V), new.length = 5 ∧ PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.IsLinKWeakening F (new ++ π) ∧ L.erase T ∪ {T ∪ {(f, false)}, T ∪ {(f, true)}} ∈ new :=
  fun _ _ _ _ _ _ _ f h hL hT hc => Helpers.LinKSplit.split_one h hL hT hc f

end PEqualNP.ProofComplexity
