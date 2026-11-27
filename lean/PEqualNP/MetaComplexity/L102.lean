import PEqualNP.MetaComplexity.Helpers.PathSizeUpper

/-- The path function on `n` inputs (the OR, over consecutive pairs `i, i + 1`, of `x i AND
x (i + 1)`) has a fan-in two circuit with `s` gates exactly when `n + n / 2 ≤ s + 2`: its
circuit size is `n + n / 2 - 2` for `n ≥ 2`. -/
theorem PEqualNP.MetaComplexity.L102 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) s ↔ n + n / 2 ≤ s + 2 :=
  PEqualNP.MetaComplexity.Helpers.PathSize.path_size
