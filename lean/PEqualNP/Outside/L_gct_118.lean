import Mathlib
import PEqualNP.Gct.L099

open Finset MvPolynomial

private theorem prod_linear_exp (n : ℕ) (x : Fin n → ℂ) :
  (∏ j : Fin n, (1 + C (x j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)) =
    ∑ S : Finset (Fin n), C (∏ j ∈ S, x j) * X (0 : Fin 1) ^ S.card := by
  classical
  rw [Finset.prod_one_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]

private theorem coeff_prod_linear (n : ℕ) (x : Fin n → ℂ) (k : ℕ) :
  (∏ j : Fin n, (1 + C (x j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)).coeff
      (Finsupp.single (0 : Fin 1) k) =
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ j ∈ S, x j := by
  classical
  rw [prod_linear_exp, coeff_sum]
  rw [Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  have heq : Finsupp.single (0 : Fin 1) S.card = Finsupp.single 0 k ↔ S.card = k :=
    (Finsupp.single_injective (0 : Fin 1)).eq_iff
  by_cases h : S.card = k <;> simp [h, heq]

private theorem special_L099 (n : ℕ) (u v : Fin n → ℂ) (μ : ℂ) :
  MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2)
      (PEqualNP.Gct.permPoly ℂ n) =
    ∑ α ∈ (∏ j : Fin n,
      (1 + C (v j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)).support,
      ((n - α 0).factorial : ℂ) * ((α 0).factorial : ℂ) *
      (∏ j : Fin n, (1 + C (u j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)).coeff α *
      (∏ j : Fin n, (1 + C (v j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)).coeff α *
      μ ^ (α 0) := by
  simpa only [Fin.sum_univ_one, Fin.prod_univ_one] using
    (PEqualNP.Gct.L099 n 1 (fun _ => u) (fun _ => v) (fun _ => μ))

private theorem finsupp_fin1_single (α : Fin 1 →₀ ℕ) :
    α = Finsupp.single (0 : Fin 1) (α 0) := by
  apply Finsupp.ext
  intro i
  fin_cases i
  simp

private theorem support_subset (n : ℕ) (v : Fin n → ℂ) :
    (∏ j : Fin n, (1 + C (v j) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)).support ⊆
       (Finset.range (n + 1)).image (Finsupp.single (0 : Fin 1)) := by
  classical
  intro α hα
  have hk : α 0 ≤ n := by
    by_contra hh
    have hgt : n < α 0 := Nat.lt_of_not_ge hh
    have he : (Finset.univ : Finset (Fin n)).powersetCard (α 0) = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      simpa using hgt
    rw [MvPolynomial.mem_support_iff] at hα
    apply hα
    rw [finsupp_fin1_single α, coeff_prod_linear n v (α 0), he]
    simp
  exact Finset.mem_image.mpr ⟨α 0, Finset.mem_range.mpr (Nat.lt_succ_of_le hk),
    (finsupp_fin1_single α).symm⟩

theorem PEqualNP.Outside.L_gct_118 :
    ∀ (n : ℕ) (u v : Fin n → ℂ) (μ : ℂ),
      MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2)
          (PEqualNP.Gct.permPoly ℂ n) =
        ∑ k ∈ Finset.range (n + 1), μ ^ k * (Nat.factorial k : ℂ) *
          (Nat.factorial (n - k) : ℂ) *
          (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, u i) *
          (∑ T ∈ Finset.univ.powersetCard k, ∏ j ∈ T, v j) := by
  intro n u v μ
  classical
  let A : MvPolynomial (Fin 1) ℂ :=
    ∏ j : Fin n, (1 + C (u j) * X (0 : Fin 1))
  let B : MvPolynomial (Fin 1) ℂ :=
    ∏ j : Fin n, (1 + C (v j) * X (0 : Fin 1))
  let F : (Fin 1 →₀ ℕ) → ℂ := fun α =>
    ((n - α 0).factorial : ℂ) * ((α 0).factorial : ℂ) *
      A.coeff α * B.coeff α * μ ^ (α 0)
  let I : Finset (Fin 1 →₀ ℕ) :=
    (Finset.range (n + 1)).image (Finsupp.single (0 : Fin 1))
  have hsub : B.support ⊆ I := support_subset n v
  have hzero : ∀ α ∈ I, α ∉ B.support → F α = 0 := by
    intro α _ ha
    have hc : B.coeff α = 0 := MvPolynomial.notMem_support_iff.mp ha
    simp [F, hc]
  have hinj : Set.InjOn (Finsupp.single (0 : Fin 1))
      (↑(Finset.range (n + 1)) : Set ℕ) := by
    intro k _ l _ h
    exact Finsupp.single_injective (0 : Fin 1) h
  have hterm (k : ℕ) : F (Finsupp.single (0 : Fin 1) k) =
      μ ^ k * (Nat.factorial k : ℂ) * (Nat.factorial (n - k) : ℂ) *
        (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, u i) *
        (∑ T ∈ Finset.univ.powersetCard k, ∏ j ∈ T, v j) := by
    dsimp [F, A, B]
    simp only [Finsupp.single_eq_same]
    rw [coeff_prod_linear n u k, coeff_prod_linear n v k]
    ring
  calc
    _ = ∑ α ∈ B.support, F α := special_L099 n u v μ
    _ = ∑ α ∈ I, F α := Finset.sum_subset hsub hzero
    _ = ∑ k ∈ Finset.range (n + 1), F (Finsupp.single (0 : Fin 1) k) :=
      Finset.sum_image hinj
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
