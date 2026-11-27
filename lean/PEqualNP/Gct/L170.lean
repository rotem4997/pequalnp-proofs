import PEqualNP.Gct.Helpers.ThreeRowCore

/-- The three-row core: a linear space of complex `3 × q` matrices containing the all ones
matrix, with a functional taking the value `1` on it, on which the sum of the column products is
`q` times the cube of the functional, has dimension at most `q`. -/
theorem PEqualNP.Gct.L170 : ∀ (q : ℕ) (V : Submodule ℂ (Fin 3 × Fin q → ℂ)) (lam : (Fin 3 × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V → lam (fun _ => (1 : ℂ)) = 1 → (∀ x ∈ V, (∑ j, x (0, j) * x (1, j) * x (2, j)) = (q : ℂ) * lam x ^ 3) → Module.finrank ℂ V ≤ q :=
  PEqualNP.Gct.Helpers.ThreeRowCore.three_row_core
