import Mathlib

/-! Helper module, proofs only. The off-row, off-column product sum of a `p × q` array equals
the square of the total sum, minus the squared row sums, minus the squared column sums, plus
the squared entries. Over the reals, a linear space of arrays on which both the total sum and
this product sum vanish is mapped injectively by the row and column sum map into the pairs of
sum-zero vectors, so its dimension is at most `p + q - 2`. -/

namespace PEqualNP.Gct.Helpers.RealLevel

open Module

/-- The inclusion-exclusion identity. -/
theorem ident (R : Type) [CommRing R] (p q : ℕ) (t : Fin p × Fin q → R) :
    (∑ i, ∑ i', ∑ j, ∑ j', if i = i' ∨ j = j' then 0 else t (i, j) * t (i', j')) =
      (∑ i, ∑ j, t (i, j)) ^ 2 - (∑ i, (∑ j, t (i, j)) ^ 2) - (∑ j, (∑ i, t (i, j)) ^ 2) +
        ∑ i, ∑ j, t (i, j) ^ 2 := by
  have key : ∀ i i' j j', (if i = i' ∨ j = j' then (0 : R) else t (i, j) * t (i', j')) =
      t (i, j) * t (i', j') - (if i = i' then t (i, j) * t (i', j') else 0)
        - (if j = j' then t (i, j) * t (i', j') else 0)
        + (if i = i' then (if j = j' then t (i, j) * t (i', j') else 0) else 0) := by
    intro i i' j j'
    by_cases h1 : i = i' <;> by_cases h2 : j = j' <;> simp [h1, h2]
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : (∑ i : Fin p, ∑ i' : Fin p, ∑ j : Fin q, ∑ j' : Fin q, t (i, j) * t (i', j')) =
      (∑ i, ∑ j, t (i, j)) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_mul_sum]
  have hB : (∑ i : Fin p, ∑ i' : Fin p, ∑ j : Fin q, ∑ j' : Fin q,
      (if i = i' then t (i, j) * t (i', j') else 0)) = ∑ i, (∑ j, t (i, j)) ^ 2 := by
    have e : ∀ i i' : Fin p, (∑ j : Fin q, ∑ j' : Fin q,
        (if i = i' then t (i, j) * t (i', j') else 0)) =
          if i = i' then ∑ j : Fin q, ∑ j' : Fin q, t (i, j) * t (i', j') else 0 := by
      intro i i'
      by_cases h : i = i' <;> simp [h]
    simp_rw [e, Finset.sum_ite_eq, Finset.mem_univ, ite_true, pow_two, Finset.sum_mul_sum]
  have hC : (∑ i : Fin p, ∑ i' : Fin p, ∑ j : Fin q, ∑ j' : Fin q,
      (if j = j' then t (i, j) * t (i', j') else 0)) = ∑ j, (∑ i, t (i, j)) ^ 2 := by
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true, pow_two, Finset.sum_mul_sum]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hD : (∑ i : Fin p, ∑ i' : Fin p, ∑ j : Fin q, ∑ j' : Fin q,
      (if i = i' then (if j = j' then t (i, j) * t (i', j') else 0) else 0)) =
        ∑ i, ∑ j, t (i, j) ^ 2 := by
    have e : ∀ i i' : Fin p, (∑ j : Fin q, ∑ j' : Fin q,
        (if i = i' then (if j = j' then t (i, j) * t (i', j') else 0) else 0)) =
          if i = i' then ∑ j : Fin q, t (i, j) * t (i', j) else 0 := by
      intro i i'
      by_cases h : i = i' <;> simp [h]
    simp_rw [e, Finset.sum_ite_eq, Finset.mem_univ, ite_true, pow_two]
  rw [hA, hB, hC, hD]

variable {p q : ℕ}

/-- Row sums and column sums. -/
def F : (Fin p × Fin q → ℝ) →ₗ[ℝ] (Fin p → ℝ) × (Fin q → ℝ) where
  toFun t := (fun i => ∑ j, t (i, j), fun j => ∑ i, t (i, j))
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext <;> simp [Finset.mul_sum]

/-- Sum of a pair of vectors, componentwise. -/
def G : ((Fin p → ℝ) × (Fin q → ℝ)) →ₗ[ℝ] ℝ × ℝ where
  toFun rc := (∑ i, rc.1 i, ∑ j, rc.2 j)
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext <;> simp [Finset.mul_sum]

lemma G_surj (hp : 1 ≤ p) (hq : 1 ≤ q) : Function.Surjective (G (p := p) (q := q)) := by
  rintro ⟨a, b⟩
  refine ⟨(Pi.single ⟨0, hp⟩ a, Pi.single ⟨0, hq⟩ b), ?_⟩
  simp [G]

lemma finrank_ker (hp : 1 ≤ p) (hq : 1 ≤ q) :
    finrank ℝ (LinearMap.ker (G (p := p) (q := q))) + 2 = p + q := by
  have h := LinearMap.finrank_range_add_finrank_ker (G (p := p) (q := q))
  rw [LinearMap.range_eq_top.mpr (G_surj hp hq), finrank_top] at h
  simp only [finrank_prod, finrank_fin_fun, finrank_self] at h
  omega

lemma zero_of (t : Fin p × Fin q → ℝ)
    (hQ : (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else t (i, j) * t (k, l)) = 0)
    (hF : F t = 0) : t = 0 := by
  have hr : ∀ i, ∑ j, t (i, j) = 0 := fun i => congrFun (congrArg Prod.fst hF) i
  have hc : ∀ j, ∑ i, t (i, j) = 0 := fun j => congrFun (congrArg Prod.snd hF) j
  rw [ident] at hQ
  simp only [hr, hc, Finset.sum_const_zero] at hQ
  have h2 : ∑ i, ∑ j, t (i, j) ^ 2 = 0 := by simpa using hQ
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    at h2
  funext ⟨i, j⟩
  have h3 := h2 i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at h3
  simpa using h3 j (Finset.mem_univ _)

theorem main : ∀ (p q : ℕ) (L : Submodule ℝ (Fin p × Fin q → ℝ)), 1 ≤ p → 1 ≤ q →
    (∀ t ∈ L, (∑ i, ∑ j, t (i, j)) = 0 ∧
      (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else t (i, j) * t (k, l)) = 0) →
    Module.finrank ℝ L + 2 ≤ p + q := by
  intro p q L hp hq hL
  have hinj : Function.Injective (F.domRestrict L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨t, ht⟩ h0
    have := zero_of t (hL t ht).2 h0
    simp [this]
  have hle : LinearMap.range (F.domRestrict L) ≤ LinearMap.ker (G (p := p) (q := q)) := by
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    have hS := (hL t ht).1
    have hS' : ∑ j, ∑ i, t (i, j) = 0 := by rw [Finset.sum_comm]; exact hS
    simp [LinearMap.mem_ker, G, F, hS, hS']
  have h1 := LinearMap.finrank_range_of_inj hinj
  have h2 := Submodule.finrank_mono hle
  have h3 := finrank_ker hp hq
  omega

end PEqualNP.Gct.Helpers.RealLevel
