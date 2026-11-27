import PEqualNP.Gct.Helpers.ColumnCore

/-- L-gct-175: column-product core for any number of rows. If the all-ones function lies in
`V`, `lam` takes the value 1 on it, and every `x ∈ V` satisfies
`∑_j ∏_i x (i, j) = q * lam x ^ p`, then `dim V ≤ q`. -/
theorem PEqualNP.Gct.L175 :
    ∀ (p q : ℕ) (V : Submodule ℂ (Fin p × Fin q → ℂ)) (lam : (Fin p × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V → lam (fun _ => (1 : ℂ)) = 1 → (∀ x ∈ V, (∑ j, ∏ i, x (i, j)) = (q : ℂ) * lam x ^ p) → Module.finrank ℂ V ≤ q :=
  PEqualNP.Gct.Helpers.ColumnCore.column_core
