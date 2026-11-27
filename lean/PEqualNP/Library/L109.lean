import PEqualNP.Search.Helpers.PCSim.Sim

/-- Width `k` Res(⊕) refutations become polynomial calculus refutations over F2: a refutation
of a CNF of width at most `w` whose lines have at most `k` equations gives a polynomial
calculus refutation of degree `max (2 k + 2) (k + w)`. -/
theorem PEqualNP.Library.L109 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w k : ℕ), (∀ C ∈ F, C.card ≤ w) → PEqualNP.ProofComplexity.IsLinRefutation F π → (∀ L ∈ π, L.card ≤ k) → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem F) (max (2 * k + 2) (k + w)) :=
  fun V _ _ F π w k hw href hk => PEqualNP.Search.Helpers.PCSim.sim V F π w k hw href hk
