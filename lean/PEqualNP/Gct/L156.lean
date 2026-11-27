import Mathlib
import PEqualNP.Gct.L157
import PEqualNP.Gct.Helpers.ThreeRow

/-- L-gct-156: level spaces of 3 by q matrices have dimension at most q + 1. From the
row-centred bound L-gct-157 by rank-nullity on the row-sum map. -/
theorem PEqualNP.Gct.L156 : ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)), (∀ t ∈ L, (∑ i : Fin 3, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) → Module.finrank ℂ L ≤ q + 1 :=
  PEqualNP.Gct.Helpers.ThreeRow.ls3_of_centred PEqualNP.Gct.L157
