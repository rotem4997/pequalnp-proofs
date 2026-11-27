import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8021 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x3 ∈ x2.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x8 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x8) = x1 x8 := by
  intro x1 C hC _ _ h1 _
  exfalso
  have h0 : PEqualNP.NotBracket.notCount C = 0 := by
    unfold PEqualNP.NotBracket.notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    simpa using hC g hg
  omega
