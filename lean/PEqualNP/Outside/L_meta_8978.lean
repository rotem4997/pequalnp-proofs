import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8978
open PEqualNP.CircuitLowerBounds



theorem tsum : ∀ (k n : ℕ), (∑ i : Fin k, if n.testBit (i : ℕ) = true then 2 ^ (i : ℕ) else 0) = n % 2 ^ k := by
  intro k
  induction k with
  | zero => intro n; simp [Nat.mod_one]
  | succ k ih =>
    intro n
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih n, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

end PEqualNP.Outside.L_meta_8978

open PEqualNP.Outside.L_meta_8978 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8978 : ∀ (k : ℕ) (u : Fin (2 ^ k)), PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => (u : ℕ).testBit i) = (u : ℕ) := by
  intro k u
  unfold PEqualNP.MetaComplexity.tableIndex
  rw [tsum k u.val]
  exact Nat.mod_eq_of_lt u.isLt
