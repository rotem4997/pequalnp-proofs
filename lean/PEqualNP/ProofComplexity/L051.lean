import PEqualNP.ProofComplexity.Helpers.LinKTrivial

namespace PEqualNP.ProofComplexity

/-- L-pcx-051: with full semantic weakening, Res(k, ⊕) refutes every unsatisfiable formula of
`m` clauses of width at most `k` in at most `2 * m + 1` lines. -/
theorem L051 : ∀ (V : Type) [DecidableEq V] (F : Finset (PEqualNP.ProofComplexity.Clause V)) (k : ℕ), (∀ C ∈ F, C.card ≤ k) → ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause V)) → ∃ π : List (PEqualNP.ProofComplexity.LinKLine V), PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.LinKSemWeak ((fun C => PEqualNP.ProofComplexity.linKOfClause C) '' (↑F : Set (PEqualNP.ProofComplexity.Clause V))) π ∧ (∅ : PEqualNP.ProofComplexity.LinKLine V) ∈ π ∧ π.length ≤ 2 * F.card + 1 :=
  fun _ _ F k hk hunsat => Helpers.LinKTrivial.trivial_refutation F k hk hunsat

end PEqualNP.ProofComplexity
