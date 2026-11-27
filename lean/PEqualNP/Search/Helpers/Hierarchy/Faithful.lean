import Mathlib
import PEqualNP.Search.Helpers.Hierarchy.Draft

/-!
# Helper module: the sign encoding of a parity system is faithful (proofs only)

The polynomial system `xorSystem F` has a common real zero exactly when the parity system `F`
has a satisfying assignment. A zero has every coordinate `1` or `-1` by the sign equations, and
`-1` is read as `true`.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft

open MvPolynomial PEqualNP.ProofComplexity

/-- The product of the signs of an assignment over an equation is the sign of its right-hand
side exactly when the assignment satisfies the equation. -/
theorem prod_sign_eq_iff_linEqSat {V : Type} (a : V → Bool)
    (e : PEqualNP.ProofComplexity.LinEq V) :
    (∏ v ∈ e.1, (if a v = true then (-1 : ℝ) else 1)) = (if e.2 = true then -1 else 1) ↔
      LinEqSat a e := by
  unfold LinEqSat
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  generalize (e.1.filter (fun v => a v = true)).card = n
  rcases Nat.even_or_odd n with h | h
  · have hn : ¬ Odd n := Nat.not_odd_iff_even.2 h
    rw [h.neg_one_pow]
    cases e.2 <;> simp [hn] <;> norm_num
  · rw [h.neg_one_pow]
    cases e.2 <;> simp [h] <;> norm_num

theorem xorSystemFaithful : XorSystemFaithful := by
  intro V _ F
  constructor
  · rintro ⟨x, hx⟩
    have hsq : ∀ v, x v = 1 ∨ x v = -1 := by
      intro v
      have h := hx (X v * X v - 1) (Or.inl ⟨v, rfl⟩)
      simp only [map_sub, map_mul, eval_X, map_one] at h
      have h' : (x v - 1) * (x v + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h1 | h1
      · left; linarith
      · right; linarith
    have hval : ∀ v, x v = if decide (x v = -1) = true then (-1 : ℝ) else 1 := by
      intro v
      rcases hsq v with h | h
      · rw [h]; norm_num
      · rw [h]; simp
    refine ⟨fun v => decide (x v = -1), fun e he => ?_⟩
    have h := hx (xorPoly e) (Or.inr ⟨e, he, rfl⟩)
    rw [xorPoly, map_sub, map_prod, eval_C, sub_eq_zero] at h
    simp only [eval_X] at h
    rw [← prod_sign_eq_iff_linEqSat, ← h]
    exact Finset.prod_congr rfl fun v _ => (hval v).symm
  · rintro ⟨a, ha⟩
    refine ⟨fun v => if a v = true then (-1 : ℝ) else 1, ?_⟩
    rintro p (⟨v, rfl⟩ | ⟨e, he, rfl⟩)
    · simp only [map_sub, map_mul, eval_X, map_one]
      split_ifs <;> norm_num
    · rw [xorPoly, map_sub, map_prod, eval_C, sub_eq_zero]
      simp only [eval_X]
      exact (prod_sign_eq_iff_linEqSat a e).2 (ha e he)

end PEqualNP.Search.Helpers.HierarchyDraft
