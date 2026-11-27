import Mathlib

/-!
# Helper module: a signed block kernel is positive semidefinite (proofs only)

A real kernel `K` with `K i i = 1`, symmetric, and multiplicative along nonzero entries
(`K i k = K i j * K j k` when both factors are nonzero) is a direct sum of rank one blocks
`s i * s j`. Its quadratic form is therefore a sum of squares, one for each block.

The proof picks a representative `rep i` of the block of `i` and shows
`∑ i, ∑ j, c i * c j * K i j = ∑ q, (∑ i, if rep i = q then c i * K i q else 0) ^ 2`.
The hypothesis that the entries are `0`, `1` or `-1` is not used.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft.Kernel

open Finset

/-- The quadratic form of a block kernel is a sum of squares over block representatives. -/
theorem kernel_sum_eq_sum_sq (ι : Type) [Fintype ι] [DecidableEq ι] (K : ι → ι → ℝ)
    (c : ι → ℝ) (rep : ι → ι)
    (hsymm : ∀ i j, K i j = K j i)
    (hmul : ∀ i j k, K i j ≠ 0 → K j k ≠ 0 → K i k = K i j * K j k)
    (hrep1 : ∀ i, K (rep i) i ≠ 0) (hrep2 : ∀ i j, K i j ≠ 0 → rep i = rep j) :
    ∑ i, ∑ j, c i * c j * K i j =
      ∑ q, (∑ i, if rep i = q then c i * K i q else 0) ^ 2 := by
  have key : ∀ i j, c i * c j * K i j =
      ∑ q, (if rep i = q then c i * K i q else 0) * (if rep j = q then c j * K j q else 0) := by
    intro i j
    rw [Finset.sum_eq_single (rep i)]
    · by_cases h : rep j = rep i
      · have h1 : K i (rep i) ≠ 0 := by rw [hsymm]; exact hrep1 i
        have h2 : K (rep i) j ≠ 0 := by rw [← h]; exact hrep1 j
        have h3 : K i j = K i (rep i) * K (rep i) j := hmul i (rep i) j h1 h2
        rw [if_pos rfl, if_pos h, h3, hsymm j (rep i)]
        ring
      · have h0 : K i j = 0 := by
          by_contra hne
          exact h (hrep2 i j hne).symm
        rw [if_neg h, h0]
        ring
    · intro q _ hq
      rw [if_neg (Ne.symm hq), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc ∑ i, ∑ j, c i * c j * K i j
      = ∑ i, ∑ j, ∑ q, (if rep i = q then c i * K i q else 0) *
          (if rep j = q then c j * K j q else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = ∑ q, ∑ i, ∑ j, (if rep i = q then c i * K i q else 0) *
          (if rep j = q then c j * K j q else 0) :=
        (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ q, (∑ i, if rep i = q then c i * K i q else 0) ^ 2 := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [sq, Finset.sum_mul_sum]

/-- A real kernel with unit diagonal, symmetric, and multiplicative along its nonzero entries
has a nonnegative quadratic form. -/
theorem kernelPSD : ∀ (ι : Type) [Fintype ι] (K : ι → ι → ℝ) (c : ι → ℝ),
    (∀ i j, K i j = 0 ∨ K i j = 1 ∨ K i j = -1) → (∀ i j, K i j = K j i) → (∀ i, K i i = 1) →
    (∀ i j k, K i j ≠ 0 → K j k ≠ 0 → K i k = K i j * K j k) →
    0 ≤ ∑ i, ∑ j, c i * c j * K i j := by
  classical
  intro ι _ K c _ hsymm hrefl hmul
  let s : Setoid ι :=
    { r := fun i j => K i j ≠ 0
      iseqv :=
        { refl := fun i => by rw [hrefl]; exact one_ne_zero
          symm := fun {i j} h => by rw [hsymm]; exact h
          trans := fun {i j k} h1 h2 => by rw [hmul i j k h1 h2]; exact mul_ne_zero h1 h2 } }
  have hrep1 : ∀ i, K (Quotient.mk s i).out i ≠ 0 := fun i => Quotient.mk_out (s := s) i
  have hrep2 : ∀ i j, K i j ≠ 0 → (Quotient.mk s i).out = (Quotient.mk s j).out := by
    intro i j h
    have hq : Quotient.mk s i = Quotient.mk s j := Quotient.sound h
    rw [hq]
  rw [kernel_sum_eq_sum_sq ι K c (fun i => (Quotient.mk s i).out) hsymm hmul hrep1 hrep2]
  exact Finset.sum_nonneg fun q _ => sq_nonneg _

end PEqualNP.Search.Helpers.HierarchyDraft.Kernel
