import Mathlib
import PEqualNP.Defs

open Finset

theorem PEqualNP.Outside.L_gct_121 : ∀ (n : ℕ) (u v : Fin n → ℂ), u ≠ 0 → v ≠ 0 → (∀ μ : ℂ, MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → (Finset.univ.filter (fun i => u i ≠ 0)).card ≠ (Finset.univ.filter (fun j => v j ≠ 0)).card := by
  intro n u v hu hv hconst hcard
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ 0)
  let B : Finset (Fin n) := Finset.univ.filter (fun j => v j ≠ 0)
  have hAB : A.card = B.card := hcard
  let r : ℕ := B.card
  have hA_nonempty : A.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hr_pos : 0 < r := by
    dsimp [r]
    rw [← hAB]
    exact Finset.card_pos.mpr hA_nonempty
  have hr_ne : r ≠ 0 := Nat.ne_of_gt hr_pos
  have hr_le : r ≤ n := by
    have := Finset.card_le_univ B
    simpa [r] using this
  let c : ℕ → ℂ := fun k =>
    ∑ π : Equiv.Perm (Fin n), ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∏ j ∈ S, (u (π j) * v j)
  let P : Polynomial ℂ :=
    ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k
  have hPeval : ∀ μ : ℂ, P.eval μ = (Nat.factorial n : ℂ) := by
    intro μ
    have heval : MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2)
        (PEqualNP.Gct.permPoly ℂ n) =
        ∑ π : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
          μ ^ S.card * ∏ j ∈ S, (u (π j) * v j) := by
      simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum,
        map_prod, MvPolynomial.eval_X]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [Finset.prod_one_add, Finset.powerset_univ]
      refine Finset.sum_congr rfl fun S _ => ?_
      have hmul : ∀ j ∈ S, μ * u (π j) * v j = μ * (u (π j) * v j) := fun j _ => by ring
      rw [Finset.prod_congr rfl hmul, Finset.prod_mul_distrib, Finset.prod_const]
    have hpoly : P.eval μ =
        ∑ π : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
          μ ^ S.card * ∏ j ∈ S, (u (π j) * v j) := by
      dsimp [P]
      rw [← Polynomial.coe_evalRingHom, map_sum]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hstep : ∑ k ∈ Finset.range (n + 1), c k * μ ^ k =
          ∑ π : Equiv.Perm (Fin n), ∑ k ∈ Finset.range (n + 1),
            ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              μ ^ S.card * ∏ j ∈ S, (u (π j) * v j) := by
        dsimp [c]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [(Finset.mem_powersetCard.mp hS).2, mul_comm]
      rw [hstep]
      refine Finset.sum_congr rfl fun π _ => ?_
      have hpart : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
          S.card ∈ Finset.range (n + 1) := by
        intro S _
        rw [Finset.mem_range]
        have := Finset.card_le_univ S
        simp only [Fintype.card_fin] at this
        omega
      symm
      rw [← Finset.sum_fiberwise_of_maps_to hpart]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr ?_ fun S _ => rfl
      ext S
      simp [Finset.mem_powersetCard]
    rw [hpoly, ← heval, hconst μ]
  have hPeq : P = Polynomial.C (Nat.factorial n : ℂ) := by
    apply Polynomial.funext
    intro μ
    rw [hPeval μ, Polynomial.eval_C]
  have hcr_zero : c r = 0 := by
    have hcoeff := congrArg (fun q : Polynomial ℂ => (Polynomial.lcoeff ℂ r) q) hPeq
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C, hr_ne, ↓reduceIte] at hcoeff
    dsimp [P] at hcoeff
    rw [← Polynomial.lcoeff_apply (R := ℂ), map_sum] at hcoeff
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    have hr_mem : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hr_le)
    simp only [hr_mem, ↓reduceIte] at hcoeff
    exact hcoeff
  have hinner : ∀ π : Equiv.Perm (Fin n),
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ j ∈ S, (u (π j) * v j) =
        (∏ j ∈ B, u (π j)) * (∏ j ∈ B, v j) := by
    intro π
    have hBmem : B ∈ (Finset.univ : Finset (Fin n)).powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, rfl⟩
    rw [Finset.sum_eq_single B]
    · rw [Finset.prod_mul_distrib]
    · intro S hS hSB
      have hScard : S.card = B.card := (Finset.mem_powersetCard.mp hS).2
      have hnsub : ¬ (S ⊆ B) := fun hsub =>
        hSB (Finset.eq_of_subset_of_card_le hsub (le_of_eq hScard.symm))
      obtain ⟨j, hjS, hjB⟩ := Finset.not_subset.mp hnsub
      have hvj : v j = 0 := by
        by_contra hne
        exact hjB (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
      exact Finset.prod_eq_zero hjS (by simp [hvj])
    · intro h
      exact absurd hBmem h
  let M : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π : Equiv.Perm (Fin n) => B.image π = A)
  have hcr_val : c r = (M.card : ℂ) * ((∏ i ∈ A, u i) * (∏ j ∈ B, v j)) := by
    dsimp [c]
    simp_rw [hinner]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun π : Equiv.Perm (Fin n) => B.image π = A)]
    have hrest : ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ¬ B.image π = A),
        (∏ j ∈ B, u (π j)) * (∏ j ∈ B, v j) = 0 := by
      apply Finset.sum_eq_zero
      intro π hπ
      have hne : B.image π ≠ A := (Finset.mem_filter.mp hπ).2
      have hcard_img : (B.image π).card = A.card := by
        rw [Finset.card_image_of_injective B π.injective, hAB]
      have hnsub : ¬ (B.image π ⊆ A) := fun hsub =>
        hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_img.symm))
      obtain ⟨i, hi_img, hiA⟩ := Finset.not_subset.mp hnsub
      obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hi_img
      have huj : u (π j) = 0 := by
        by_contra hne'
        exact hiA (Finset.mem_filter.mpr ⟨Finset.mem_univ (π j), hne'⟩)
      rw [Finset.prod_eq_zero hjB huj, zero_mul]
    rw [hrest, add_zero]
    have hmain : ∀ π ∈ M,
        (∏ j ∈ B, u (π j)) * (∏ j ∈ B, v j) = (∏ i ∈ A, u i) * (∏ j ∈ B, v j) := by
      intro π hπ
      have himg : B.image π = A := (Finset.mem_filter.mp hπ).2
      rw [← himg, Finset.prod_image (fun x _ y _ hxy => π.injective hxy)]
    rw [Finset.sum_congr rfl hmain, Finset.sum_const, nsmul_eq_mul]
  have hM_nonempty : M.Nonempty := by
    have he1 : Nonempty ({x : Fin n // x ∈ B} ≃ {y : Fin n // y ∈ A}) := by
      apply Fintype.card_eq.mp
      simp only [Fintype.card_coe]
      exact hAB.symm
    have he2 : Nonempty ({x : Fin n // x ∉ B} ≃ {y : Fin n // y ∉ A}) := by
      apply Fintype.card_eq.mp
      have h1 : Fintype.card {x : Fin n // x ∉ B} = Bᶜ.card := by
        simpa [Finset.mem_compl] using (Fintype.card_coe Bᶜ)
      have h2 : Fintype.card {y : Fin n // y ∉ A} = Aᶜ.card := by
        simpa [Finset.mem_compl] using (Fintype.card_coe Aᶜ)
      rw [h1, h2, Finset.card_compl, Finset.card_compl, hAB]
    obtain ⟨e1⟩ := he1
    obtain ⟨e2⟩ := he2
    let f : Fin n → Fin n := fun x =>
      if hx : x ∈ B then (e1 ⟨x, hx⟩).1 else (e2 ⟨x, hx⟩).1
    let g : Fin n → Fin n := fun y =>
      if hy : y ∈ A then (e1.symm ⟨y, hy⟩).1 else (e2.symm ⟨y, hy⟩).1
    have hleft : Function.LeftInverse g f := by
      intro x
      dsimp [f, g]
      by_cases hx : x ∈ B
      · simp [hx, (e1 ⟨x, hx⟩).2]
      · simp [hx, (e2 ⟨x, hx⟩).2]
    have hright : Function.RightInverse g f := by
      intro y
      dsimp [f, g]
      by_cases hy : y ∈ A
      · simp [hy, (e1.symm ⟨y, hy⟩).2]
      · simp [hy, (e2.symm ⟨y, hy⟩).2]
    let π : Equiv.Perm (Fin n) := ⟨f, g, hleft, hright⟩
    refine ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ π, ?_⟩⟩
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxB, rfl⟩
      simp [π, f, hxB]
    · intro hyA
      refine ⟨(e1.symm ⟨y, hyA⟩).1, (e1.symm ⟨y, hyA⟩).2, ?_⟩
      simp [π, f, (e1.symm ⟨y, hyA⟩).2]
  have hM_ne : (M.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.card_pos.mpr hM_nonempty))
  have hprodA : ∏ i ∈ A, u i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (Finset.mem_filter.mp hi).2
  have hprodB : ∏ j ∈ B, v j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Finset.mem_filter.mp hj).2
  have hcr_ne : c r ≠ 0 := by
    rw [hcr_val]
    exact mul_ne_zero hM_ne (mul_ne_zero hprodA hprodB)
  exact hcr_ne hcr_zero
