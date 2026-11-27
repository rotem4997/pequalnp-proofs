import PEqualNP.Search.Helpers.RectConv

/-- Narrow, small-coefficient Res(lin) refutations become small rectangle dags. -/
theorem PEqualNP.Library.L089 : ∀ {V : Type} [Fintype V] [DecidableEq V] (side : V → Bool)
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.Search.QLine V)) (M w : ℕ),
    PEqualNP.Search.IsResLinQRefutation F π →
    (∀ L ∈ π, L.length ≤ w ∧ ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ M) →
    ∃ ρ : List (Set (V → Bool)), PEqualNP.Search.IsRectDagFor side F ρ ∧
      ρ.length ≤ π.length * (8 * (2 * Fintype.card V * M + 1) ^ w) ^ 3 :=
  fun side F π M w hπ hb => PEqualNP.Search.Helpers.resLinQ_to_rectDag side F π M w hπ hb
