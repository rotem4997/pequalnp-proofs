import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6963 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x2 = Decidable.decide (∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (∃ x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x3 = x4 + x5) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true)) → ∀ (x3 : Fin (26 : ℕ) → Bool), (∀ (x4 x5 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true → x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true → ¬∃ x8 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x4 = x5 + x8) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x3 = Bool.false := by
  intro C h x hx
  rw [h x, decide_eq_false_iff_not]
  rintro ⟨a, b, ⟨d, hd, hab⟩, h1, h2⟩
  exact hx a b h1 h2 ⟨d, hd, hab⟩
