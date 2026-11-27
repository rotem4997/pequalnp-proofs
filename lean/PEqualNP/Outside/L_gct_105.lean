import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_105 :
    ∀ (p q : ℕ) (t : Fin p → Fin q → ℂ), (∀ i, ∑ j, t i j = 0) → (∀ j, ∑ i, t i j = 0) → (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else t i j * t k l) = ∑ i, ∑ j, t i j ^ 2 := by
  classical
  intro p q t hrow hcol
  have omit_one {n : ℕ} (f : Fin n → ℂ) (a : Fin n) (h : ∑ b, f b = 0) :
      (∑ b, if a = b then 0 else f b) = -f a := by
    calc
      _ = ∑ b, (f b - (if a = b then f b else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases e : a = b <;> simp [e]
      _ = -f a := by simp [Finset.sum_sub_distrib, h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm (f := fun k j => ∑ l, if i = k ∨ j = l then 0 else t i j * t k l)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = ∑ k, t i j * (-(if i = k then 0 else t k j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases e : i = k
      · simp [e]
      · simp only [e, false_or, ite_false]
        rw [← omit_one (t k) j (hrow k), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        by_cases d : j = l <;> simp [d]
    _ = t i j ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_neg_distrib, omit_one (fun k => t k j) i (hcol j)]
      simp [pow_two]
