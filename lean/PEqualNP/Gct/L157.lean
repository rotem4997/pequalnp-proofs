import Mathlib
import PEqualNP.Gct.L171
import PEqualNP.Gct.Helpers.ThreeRow
import PEqualNP.Gct.Helpers.ThreeRowRado

/-- L-gct-157: three-row level spaces with every row sum zero have dimension at most q - 1.
Elementary proof: induction on the number of columns and Rado's theorem for linear
independence (L-gct-171). -/
theorem PEqualNP.Gct.L157 : ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)), 1 ≤ q → (∀ t ∈ L, (∀ i : Fin 3, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) → Module.finrank ℂ L + 1 ≤ q :=
  PEqualNP.Gct.Helpers.ThreeRowRado.centred_of_rado PEqualNP.Gct.L171
