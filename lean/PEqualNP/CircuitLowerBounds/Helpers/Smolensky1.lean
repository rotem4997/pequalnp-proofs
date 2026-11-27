import Mathlib

/-!
# Smolensky's counting step

Helper module (proofs only, no statement may use it). If a polynomial `G` of total degree at
most `D` over a field agrees, on a set `A` of 0/1 points, with `x ↦ ∏ i, (if x i then ω else 1)`
for some `ω` other than `0` and `1`, then `A` has at most `∑ i ≤ n / 2 + D, C(n, i)` points.
The reason: on `A` every function is then the restriction of a polynomial of degree at most
`n / 2 + D`, and such restrictions are spanned by the multilinear monomials of that degree.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open MvPolynomial

section

variable {K : Type*} [Field K] {n : ℕ}

/-- The multilinear monomial of `S`, as a function on the points of `A`. -/
noncomputable def smolE (A : Finset (Fin n → Bool)) (S : Finset (Fin n)) : A → K :=
  fun x => ∏ i ∈ S, (if x.1 i = true then (1 : K) else 0)

open Classical in
/-- The span of the multilinear monomials of degree at most `t`, as functions on `A`. -/
noncomputable def smolW (A : Finset (Fin n → Bool)) (t : ℕ) : Submodule K (A → K) :=
  Submodule.span K
    (((Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ t).image (smolE A) :
      Finset (A → K)) : Set (A → K))

theorem smol_card_filter_le (n t : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ t).card ≤
      ∑ i ∈ Finset.range (t + 1), n.choose i := by
  classical
  have hsub : (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ t) ⊆
      (Finset.range (t + 1)).biUnion fun i => Finset.powersetCard i Finset.univ := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨S.card, by omega, rfl⟩
  calc _ ≤ ((Finset.range (t + 1)).biUnion fun i =>
        Finset.powersetCard i (Finset.univ : Finset (Fin n))).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (t + 1), (Finset.powersetCard i (Finset.univ : Finset (Fin n))).card :=
        Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (t + 1), n.choose i := by simp

/-- Multilinearization: on 0/1 points a polynomial of total degree at most `t` is a
combination of multilinear monomials of degree at most `t`. -/
theorem smol_restrict_mem (A : Finset (Fin n → Bool)) (t : ℕ) (P : MvPolynomial (Fin n) K)
    (hP : P.totalDegree ≤ t) :
    (fun x : A => eval (fun i => if x.1 i = true then (1 : K) else 0) P) ∈ smolW (K := K) A t := by
  classical
  have h : (fun x : A => eval (fun i => if x.1 i = true then (1 : K) else 0) P) =
      ∑ d ∈ P.support, P.coeff d • smolE (K := K) A d.support := by
    funext x
    rw [eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, smolE]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finsupp.mem_support_iff.mp hi
    split_ifs <;> simp [this]
  rw [h]
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
    Set.mem_setOf_eq]
  refine ⟨d.support, ?_, rfl⟩
  calc d.support.card = ∑ i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ ≤ P.totalDegree := le_totalDegree hd
    _ ≤ t := hP

theorem smol_affprod_deg (α β : Fin n → K) (T : Finset (Fin n)) :
    (∏ i ∈ T, (C (α i) * X i + C (β i)) : MvPolynomial (Fin n) K).totalDegree ≤ T.card := by
  calc _ ≤ ∑ i ∈ T, (C (α i) * X i + C (β i) : MvPolynomial (Fin n) K).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ T, 1 := Finset.sum_le_sum fun i _ => by
        refine (totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, totalDegree_X]
        · rw [totalDegree_C]; exact Nat.zero_le _
    _ = T.card := by simp

theorem smol_affprod_eval (α β : Fin n → K) (T : Finset (Fin n)) (f : Fin n → K) :
    eval f (∏ i ∈ T, (C (α i) * X i + C (β i)) : MvPolynomial (Fin n) K) =
      ∏ i ∈ T, (α i * f i + β i) := by
  simp [map_prod]

/-- Smolensky's counting step. -/
theorem smolensky_card_le (ω : K) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (D : ℕ) (G : MvPolynomial (Fin n) K) (hG : G.totalDegree ≤ D)
    (A : Finset (Fin n → Bool))
    (hA : ∀ x ∈ A, eval (fun i => if x i = true then (1 : K) else 0) G
        = ∏ i, (if x i = true then ω else 1)) :
    A.card ≤ ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i := by
  classical
  have hω' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  -- every product of the `y i` over a set of coordinates is in the span
  have hB : ∀ S : Finset (Fin n),
      (fun x : A => ∏ i ∈ S, (if x.1 i = true then ω else 1)) ∈ smolW (K := K) A (n / 2 + D) := by
    intro S
    by_cases hS : S.card ≤ n / 2
    · have h := smol_restrict_mem A (n / 2 + D) (∏ i ∈ S, (C (ω - 1) * X i + C 1))
        ((smol_affprod_deg _ _ S).trans (by omega))
      convert h using 1
      funext x
      rw [smol_affprod_eval]
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · have hdeg : (G * ∏ i ∈ Sᶜ, (C (ω⁻¹ - 1) * X i + C 1)).totalDegree ≤ n / 2 + D := by
        refine (totalDegree_mul _ _).trans ?_
        have h1 := smol_affprod_deg (fun _ => ω⁻¹ - 1) (fun _ => (1 : K)) Sᶜ
        have h2 : Sᶜ.card = n - S.card := by simp [Finset.card_compl]
        have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
        omega
      have h := smol_restrict_mem A (n / 2 + D) _ hdeg
      convert h using 1
      funext x
      rw [map_mul, hA x.1 x.2, smol_affprod_eval]
      have h1 := Finset.prod_mul_prod_compl S (fun i => if x.1 i = true then ω else 1)
      have h2 : (∏ i ∈ Sᶜ, (if x.1 i = true then ω else 1)) *
          ∏ i ∈ Sᶜ, ((ω⁻¹ - 1) * (if x.1 i = true then (1 : K) else 0) + 1) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun i _ => ?_
        split_ifs
        · field_simp
          ring
        · simp
      rw [← h1, mul_assoc, h2, mul_one]
  -- every product of affine forms in the `y i` is in the span
  have hC : ∀ α β : Fin n → K,
      (fun x : A => ∏ i, (α i * (if x.1 i = true then ω else 1) + β i)) ∈
        smolW (K := K) A (n / 2 + D) := by
    intro α β
    have h : (fun x : A => ∏ i, (α i * (if x.1 i = true then ω else 1) + β i)) =
        ∑ S : Finset (Fin n), ((∏ i ∈ S, α i) * ∏ i ∈ Sᶜ, β i) •
          (fun x : A => ∏ i ∈ S, (if x.1 i = true then ω else 1)) := by
      funext x
      rw [Fintype.prod_add, Finset.sum_apply]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
      ring
    rw [h]
    exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (hB S)
  -- hence every function is
  have hD : ∀ f : A → K, f ∈ smolW (K := K) A (n / 2 + D) := by
    intro f
    have h : f = ∑ a : A, f a • (fun x : A => ∏ i,
        ((if a.1 i = true then (ω - 1)⁻¹ else -(ω - 1)⁻¹) * (if x.1 i = true then ω else 1) +
          (if a.1 i = true then -(ω - 1)⁻¹ else ω * (ω - 1)⁻¹))) := by
      funext x
      have hx : ∀ a : A, (∏ i,
          ((if a.1 i = true then (ω - 1)⁻¹ else -(ω - 1)⁻¹) * (if x.1 i = true then ω else 1) +
            (if a.1 i = true then -(ω - 1)⁻¹ else ω * (ω - 1)⁻¹))) =
          if x = a then (1 : K) else 0 := by
        intro a
        have : ∀ i, ((if a.1 i = true then (ω - 1)⁻¹ else -(ω - 1)⁻¹) *
              (if x.1 i = true then ω else 1) +
            (if a.1 i = true then -(ω - 1)⁻¹ else ω * (ω - 1)⁻¹)) =
            if x.1 i = a.1 i then (1 : K) else 0 := by
          intro i
          cases hxi : x.1 i <;> cases hai : a.1 i <;> simp <;> field_simp <;> ring
        simp only [this]
        rw [Fintype.prod_boole]
        congr 1
        rw [eq_iff_iff]
        constructor
        · intro h; exact Subtype.ext (funext h)
        · intro h i; rw [h]
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, hx]
      simp
    rw [h]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hC _ _)
  have htop : smolW (K := K) A (n / 2 + D) = ⊤ := Submodule.eq_top_iff'.mpr hD
  calc A.card = Module.finrank K (A → K) := by simp
    _ = Module.finrank K (smolW (K := K) A (n / 2 + D)) := by rw [htop, finrank_top]
    _ ≤ ((Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D).image
          (smolE (K := K) A)).card := finrank_span_finset_le_card _
    _ ≤ (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D).card :=
        Finset.card_image_le
    _ ≤ _ := smol_card_filter_le n _

end

end PEqualNP.CircuitLowerBounds.Helpers
