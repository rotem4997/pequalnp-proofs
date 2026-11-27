import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4227_2
    (h : ∃ n : ℕ, ∀ m : ℕ, n ≤ m)
    (hn : ¬ ∃ n : ℕ, ∀ m : ℕ, n ≤ m) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (42 : ℕ) x1 ∧ x1.output < (42 : ℕ) + x1.size ∧ x1.size ≤ (118 : ℕ) ∧ (∀ (x2 : Fin (42 : ℕ)), ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (14 : ℕ)] → ∃ x4 ∈ x1.gates, ↑x2 ∈ x4.inputs) ∧ ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) < ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  exact absurd h hn
