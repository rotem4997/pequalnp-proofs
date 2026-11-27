import PEqualNP.Defs

/-! Helpers for L-gct-035 (subspace reduction): a polynomial of total degree at most one is
affine, so its value at `y + t` is its value at `y` plus a linear function of `t`. -/

namespace PEqualNP.Gct.Helpers.SubspaceReduction

open Finset MvPolynomial

theorem single_of_sum_le_one {τ : Type} (s : τ →₀ ℕ) (a : τ)
    (hs : (s.sum fun _ e => e) ≤ 1) (ha : s a ≠ 0) : s = Finsupp.single a 1 := by
  classical
  have hle : ∀ x, s x ≤ s.sum fun _ e => e := fun x => by
    by_cases hx : x ∈ s.support
    · exact Finset.single_le_sum (f := fun x => s x) (fun _ _ => Nat.zero_le _) hx
    · rw [Finsupp.notMem_support_iff.mp hx]; exact Nat.zero_le _
  ext x
  by_cases hx : x = a
  · subst hx; have := hle x; simp; omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hx)]
    by_contra hne
    have h2 : s a + s x ≤ s.sum fun _ e => e := by
      have hsub : ({a, x} : Finset τ) ⊆ s.support := by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl <;> simpa
      have := Finset.sum_le_sum_of_subset (f := fun y => s y) hsub
      rw [sum_pair (Ne.symm hx)] at this
      exact this
    omega

/-- A polynomial of total degree at most one is its constant term plus its linear terms. -/
theorem eq_affine {τ : Type} [Fintype τ] (q : MvPolynomial τ ℂ) (hq : q.totalDegree ≤ 1) :
    q = C (q.coeff 0) + ∑ v, C (q.coeff (Finsupp.single v 1)) * X v := by
  classical
  ext s
  simp only [MvPolynomial.coeff_add, coeff_C, coeff_sum, coeff_C_mul, coeff_X']
  by_cases h0 : s = 0
  · subst h0
    simp
  · rw [if_neg (Ne.symm h0), zero_add]
    obtain ⟨a, ha⟩ : ∃ a, s a ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (Finsupp.ext h)
    by_cases hmem : s ∈ q.support
    · have hs := single_of_sum_le_one s a ((le_totalDegree hmem).trans hq) ha
      subst hs
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Finsupp.single_left_injective one_ne_zero h)), mul_zero]
      · simp
    · rw [Finsupp.notMem_support_iff.mp (by simpa using hmem)]
      symm
      apply Finset.sum_eq_zero
      intro v _
      split_ifs with h
      · subst h
        simpa using hmem
      · exact mul_zero _

theorem eval_add_of_totalDegree_le_one {τ : Type} [Fintype τ] (q : MvPolynomial τ ℂ)
    (hq : q.totalDegree ≤ 1) (y t : τ → ℂ) :
    eval (y + t) q = eval y q + ∑ v, q.coeff (Finsupp.single v 1) * t v := by
  have e : ∀ x : τ → ℂ, eval x q = q.coeff 0 + ∑ v, q.coeff (Finsupp.single v 1) * x v := by
    intro x
    conv_lhs => rw [eq_affine q hq]
    simp
  rw [e, e]
  simp only [Pi.add_apply, mul_add, sum_add_distrib]
  ring

end PEqualNP.Gct.Helpers.SubspaceReduction
