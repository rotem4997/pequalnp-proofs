import PEqualNP.MetaComplexity.L107
import PEqualNP.MetaComplexity.Helpers.CycleCore

/-- The cycle function on `n ≥ 5` inputs (the OR, over cyclically consecutive pairs
`i, i + 1 mod n`, of `x i AND x (i + 1 mod n)`) has a fan-in two circuit with `s` gates
exactly when `n + ceil(n / 2) ≤ s + 1`: its circuit size is `n + ceil(n / 2) - 1`. -/
theorem PEqualNP.MetaComplexity.L106 : ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔ n + (n + 1) / 2 ≤ s + 1) :=
  PEqualNP.MetaComplexity.Helpers.CycleSize.cyc_exact_of_readers PEqualNP.MetaComplexity.L107
