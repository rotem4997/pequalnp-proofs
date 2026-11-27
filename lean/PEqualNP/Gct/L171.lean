import PEqualNP.Gct.Helpers.RadoLinear

/-- L-gct-171: Rado's transversal theorem for linear matroids. If every set `U` of indices has
at most as many elements as the dimension of the span of `⋃ j ∈ U, A j`, then one can pick
`f j ∈ A j` with `f` linearly independent. -/
theorem PEqualNP.Gct.L171 :
    ∀ (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Finset W), (∀ U : Finset ι, U.card ≤ Module.finrank K (Submodule.span K (⋃ j ∈ U, (A j : Set W)))) → ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro K _ W _ _ ι _ _ A hA
  classical
  exact PEqualNP.Gct.RadoLinear.rado_aux _ A rfl hA
