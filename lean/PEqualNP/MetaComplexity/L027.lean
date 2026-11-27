import PEqualNP.MetaComplexity.Helpers.Coding

/-- The satisfiability coding lemma, weak integer form, stated without CNFs: a set of points of
the cube with no two neighbours, each of whose non-members is excluded by a subcube fixing at
most `k` coordinates, has at most `2 k 2 ^ (m - m / (2 k))` points. -/
theorem PEqualNP.MetaComplexity.L027 : ∀ (m k : ℕ) (S : Finset (Fin m → Bool)), 0 < k → (∀ x : Fin m → Bool, x ∉ S → ∃ V : Finset (Fin m), V.card ≤ k ∧ ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ S) → (∀ x ∈ S, ∀ i : Fin m, Function.update x i (!x i) ∉ S) → S.card ≤ 2 * k * 2 ^ (m - m / (2 * k)) :=
  PEqualNP.MetaComplexity.Helpers.Coding.coding_bound
