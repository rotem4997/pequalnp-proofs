import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18882 : PEqualNP.TopForm.NoFourCycle (SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) := by
  simp +decide
