import Mathlib

/-!
# Helper module: finitely many subalgebras of a finite product of fields

Helper module, proofs only. It serves the Kneser-type theorem for coordinatewise products of
subspaces of `ℂ^n` (Mirandola and Zemor 2015, Theorem 3.3).

The algebra is `ι → K` with pointwise multiplication, `ι` finite and `K` a field. A unital
subalgebra `A` contains, for every `x ∈ A` and every scalar `c`, the indicator of the level set
`{j | x j = c}`: it is the Lagrange product `∏ μ ≠ c, (c - μ)⁻¹ • (x - μ)` over the values `μ` of
`x`. Every `x ∈ A` is the combination `∑ c, c • indicator {j | x j = c}` over its values, so `A`
is determined by the set of subsets of `ι` whose indicator lies in `A`. There are finitely many
such sets of subsets.

Main statement: `PEqualNP.Gct.Helpers.Kneser.finite_subalgebra`.
-/

namespace PEqualNP.Gct.Helpers.Kneser

namespace Fin

open scoped Classical in
/-- The indicator of a level set of a member of a unital subalgebra of `ι → K` is a member. -/
theorem levelSet_indicator_mem {K ι : Type*} [Field K] [Fintype ι]
    (A : Subalgebra K (ι → K)) {x : ι → K} (hx : x ∈ A) (c : K) :
    Set.indicator {j | x j = c} (1 : ι → K) ∈ A := by
  have key : Set.indicator {j | x j = c} (1 : ι → K)
      = ∏ μ ∈ (Finset.univ.image x).erase c,
          ((c - μ)⁻¹ • (x - algebraMap K (ι → K) μ)) := by
    funext j
    rw [Finset.prod_apply]
    by_cases h : x j = c
    · rw [Set.indicator_of_mem (by exact h)]
      symm
      apply Finset.prod_eq_one
      intro μ hμ
      have hne : c - μ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ).symm
      simp [h, hne]
    · rw [Set.indicator_of_notMem (by exact h)]
      symm
      apply Finset.prod_eq_zero (i := x j)
      · exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem x (Finset.mem_univ j)⟩
      · simp
  rw [key]
  exact A.prod_mem fun μ _ => A.smul_mem (A.sub_mem hx (A.algebraMap_mem μ)) _

open scoped Classical in
/-- A member of `ι → K` is the combination of the indicators of its level sets. -/
theorem eq_sum_levelSet_indicator {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) :
    x = ∑ c ∈ Finset.univ.image x, c • Set.indicator {j | x j = c} (1 : ι → K) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (x j)]
  · simp
  · intro c _ hc
    have : j ∉ {j | x j = c} := fun h => hc (Eq.symm h)
    simp [Set.indicator_of_notMem this]
  · intro h
    exact absurd (Finset.mem_image_of_mem x (Finset.mem_univ j)) h

/-- The set of subsets of `ι` whose indicator lies in the subalgebra. -/
def indicatorSets {K ι : Type*} [Field K] (A : Subalgebra K (ι → K)) : Set (Set ι) :=
  {S | Set.indicator S (1 : ι → K) ∈ A}

/-- A subalgebra is contained in any subalgebra holding at least the same indicators. -/
theorem le_of_indicatorSets_subset {K ι : Type*} [Field K] [Fintype ι]
    {A B : Subalgebra K (ι → K)} (h : indicatorSets A ⊆ indicatorSets B) : A ≤ B := by
  classical
  intro x hx
  rw [eq_sum_levelSet_indicator x]
  exact B.sum_mem fun c _ => B.smul_mem (h (levelSet_indicator_mem A hx c)) c

/-- A subalgebra of `ι → K` is determined by the subsets whose indicator it holds. -/
theorem indicatorSets_injective {K ι : Type*} [Field K] [Fintype ι] :
    Function.Injective (indicatorSets : Subalgebra K (ι → K) → Set (Set ι)) :=
  fun _ _ h => le_antisymm (le_of_indicatorSets_subset h.le) (le_of_indicatorSets_subset h.ge)

/-- A finite product of copies of a field has finitely many unital subalgebras. -/
theorem finite_subalgebra_pi (K ι : Type*) [Field K] [Fintype ι] :
    Finite (Subalgebra K (ι → K)) :=
  Finite.of_injective _ indicatorSets_injective

end Fin

/-- The algebra `ℂ^n` with pointwise multiplication has finitely many unital subalgebras. -/
theorem finite_subalgebra (n : ℕ) : Finite (Subalgebra ℂ (Fin n → ℂ)) :=
  Fin.finite_subalgebra_pi ℂ (_root_.Fin n)

end PEqualNP.Gct.Helpers.Kneser
