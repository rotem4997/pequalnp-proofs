import PEqualNP.Library.Evasion.RungOfBudget
import PEqualNP.Library.Evasion.MBudget

/-- Conditional: the fixed-pair link at three alternations refutes a collapse of nondeterministic
linear time into deterministic time of order `n^(u/v)` whenever `p * u^3 < q * v^3`. The
hypothesis `FP3` is open. -/
theorem PEqualNP.Library.L122 : ∀ p q u v : ℕ, 1 ≤ p → 1 ≤ v → v ≤ u → p * u ^ 3 < q * v ^ 3 → PEqualNP.Library.FP3 p q → PEqualNP.Library.Coll u v → False :=
  PEqualNP.Library.Evasion.rung_of_budget PEqualNP.Library.Evasion.budget
