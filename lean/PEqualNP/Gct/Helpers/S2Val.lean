import Mathlib

/-!
# Lemma T for the two-row S2 route (hard link L-gct-086)

`tlin`: pure linear algebra (route step T6).
`valT`: the valuation lemma (route steps T1 to T6).
-/

namespace PEqualNP.Gct.Helpers.S2Val

open Finset

theorem tlin {ι : Type*} (k F : Type*) [Field k] [Field F] [Algebra k F] (J : Finset ι)
    (c : ι → F) (hc : ∀ j ∈ J, c j ≠ 0)
    (h : ∀ θ : F →ₗ[k] k, ∑ j ∈ J, algebraMap k F (θ (c j)) * (c j)⁻¹ = 0) :
    (J.card : F) = 0 := by
  classical
  set W : Submodule k F := Submodule.span k (c '' (J : Set ι)) with hW
  have : Module.Finite k W := Module.Finite.span_of_finite k ((J.finite_toSet).image c)
  let b := Module.finBasis k W
  have hmem : ∀ j ∈ J, c j ∈ W := fun j hj => Submodule.subset_span ⟨j, hj, rfl⟩
  choose θ hθ using fun i => LinearMap.exists_extend (b.coord i)
  have key : ∀ j (hj : j ∈ J), ∑ i, algebraMap k F (θ i (c j)) * (b i : F) = c j := by
    intro j hj
    have h2 : ∀ i, θ i (c j) = b.repr ⟨c j, hmem j hj⟩ i := by
      intro i
      have := congrArg (fun f => f ⟨c j, hmem j hj⟩) (hθ i)
      simpa using this
    have h3 := congrArg Subtype.val (b.sum_repr ⟨c j, hmem j hj⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    simp_rw [h2, ← Algebra.smul_def]
    exact h3
  calc (J.card : F) = ∑ j ∈ J, c j * (c j)⁻¹ := by
        rw [Finset.sum_congr rfl (fun j hj => mul_inv_cancel₀ (hc j hj))]; simp
    _ = ∑ j ∈ J, (∑ i, algebraMap k F (θ i (c j)) * (b i : F)) * (c j)⁻¹ := by
        refine Finset.sum_congr rfl fun j hj => ?_; rw [key j hj]
    _ = ∑ i, (b i : F) * ∑ j ∈ J, algebraMap k F (θ i (c j)) * (c j)⁻¹ := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 0 := by simp [h]

theorem valT (k K : Type*) [Field k] [CharZero k] [Field K] [Algebra k K]
    (O : ValuationSubring K) (hk : ∀ r : k, algebraMap k K r ∈ O) (q : ℕ) (lam : Fin q → K)
    (hlam : ∀ j, lam j ≠ 0) (hnu : ∃ j, lam j ∈ O.nonunits ∨ (lam j)⁻¹ ∈ O.nonunits) (C : k) :
    ∃ φ ψ : K →ₗ[k] k,
      ∑ j, (φ (lam j) * ψ ((lam j)⁻¹) + ψ (lam j) * φ ((lam j)⁻¹)) ≠ C * φ 1 * ψ 1 := by
  classical
  set v := O.valuation with hv
  -- T1: the elements lam j and their inverses, indexed by `Fin q × Bool`.
  let e : Fin q × Bool → K := fun i => if i.2 then lam i.1 else (lam i.1)⁻¹
  have he0 : ∀ i, e i ≠ 0 := by
    rintro ⟨j, _ | _⟩ <;> simp [e, hlam j]
  have hflip : ∀ i, e (i.1, !i.2) = (e i)⁻¹ := by
    rintro ⟨j, _ | _⟩ <;> simp [e]
  have hve0 : ∀ i, v (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff v).2 (he0 i)
  obtain ⟨j0, hj0⟩ := hnu
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨(j0, true), Finset.mem_univ _⟩
  set x := e i0 with hxdef
  have hx0 : x ≠ 0 := he0 i0
  have hmax : ∀ i, v (e i) ≤ v x := fun i => hi0 i (Finset.mem_univ _)
  have hvx0 : 0 < v x := zero_lt_iff.2 (hve0 i0)
  -- T2: x is not in O.
  have hx1 : 1 < v x := by
    obtain ⟨i, hi⟩ : ∃ i, v (e i) < 1 := by
      rcases hj0 with h | h
      · exact ⟨(j0, true), by simpa [e, ValuationSubring.mem_nonunits_iff] using h⟩
      · exact ⟨(j0, false), by simpa [e, ValuationSubring.mem_nonunits_iff] using h⟩
    by_contra hle
    push Not at hle
    have h1 : v (e i) * v (e (i.1, !i.2)) = 1 := by
      rw [← map_mul, hflip, mul_inv_cancel₀ (he0 i), map_one]
    have h2 : v (e i) * v (e (i.1, !i.2)) ≤ v (e i) * 1 :=
      mul_le_mul_right ((hmax _).trans hle) _
    rw [h1, mul_one] at h2
    exact absurd hi (not_lt.2 h2)
  have hdivO : ∀ y : K, v y ≤ v x → y / x ∈ O := by
    intro y hy
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ hvx0]
    exact hy
  -- k-algebra structures on O and on the residue field.
  let ι : k →+* O := (algebraMap k K).codRestrict O hk
  let _ : Algebra k O := ι.toAlgebra
  have hι : ∀ r : k, ((algebraMap k O r : O) : K) = algebraMap k K r := fun r => rfl
  let κ := IsLocalRing.ResidueField O
  have hκ : ∀ r : k, algebraMap k κ r = IsLocalRing.residue O (algebraMap k O r) :=
    fun r => rfl
  -- The k-submodule P = x • O of K.
  let P : Submodule k K :=
    { carrier := {y | v y ≤ v x}
      add_mem' := fun {a b} (ha : v a ≤ v x) (hb : v b ≤ v x) =>
        show v (a + b) ≤ v x from (v.map_add a b).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun r y hy => by
        simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul]
        calc v (algebraMap k K r) * v y ≤ 1 * v y :=
              mul_le_mul_left ((O.valuation_le_one_iff _).2 (hk r)) _
          _ = v y := one_mul _
          _ ≤ v x := hy }
  let L : P →ₗ[k] κ :=
    { toFun := fun y => IsLocalRing.residue O ⟨(y : K) / x, hdivO _ y.2⟩
      map_add' := fun a b => by
        rw [← map_add]; congr 1; ext; simp [add_div]
      map_smul' := fun r a => by
        rw [Algebra.smul_def, RingHom.id_apply, hκ, ← map_mul]; congr 1; ext
        simp [Algebra.smul_def, mul_div_assoc, hι] }
  have hφ : ∀ θ : κ →ₗ[k] k, ∃ φ : K →ₗ[k] k,
      ∀ y (hy : v y ≤ v x), φ y = θ (IsLocalRing.residue O ⟨y / x, hdivO y hy⟩) := by
    intro θ
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (θ ∘ₗ L)
    refine ⟨φ, fun y hy => ?_⟩
    have := congrArg (fun f => f ⟨y, hy⟩) hφ
    simpa [L] using this
  -- T3: the residues c i of e i / x.
  let c : Fin q × Bool → κ := fun i => IsLocalRing.residue O ⟨e i / x, hdivO _ (hmax i)⟩
  have hci0 : c i0 = 1 := by
    have : (⟨e i0 / x, hdivO _ (hmax i0)⟩ : O) = 1 := by
      ext; simp [← hxdef, div_self hx0]
    simp only [c, this, map_one]
  have hlt : ∀ (y : K) (hy : v y ≤ v x), v y < v x →
      IsLocalRing.residue O ⟨y / x, hdivO y hy⟩ = 0 := by
    intro y hy hlt
    rw [IsLocalRing.residue_eq_zero_iff, O.valuation_lt_one_iff]
    show v (y / x) < 1
    rw [map_div₀, div_lt_one₀ hvx0]; exact hlt
  -- the elements a i of O with residue (c i)⁻¹
  have haO : ∀ i, v (e i) = v x → x / e i ∈ O := by
    intro i h
    rw [← O.valuation_le_one_iff, map_div₀, h, div_self (hve0 i0)]
  let a : Fin q × Bool → O := fun i =>
    if h : v (e i) = v x then ⟨x / e i, haO i h⟩ else 0
  have hres_a : ∀ i, IsLocalRing.residue O (a i) = (c i)⁻¹ := by
    intro i
    by_cases h : v (e i) = v x
    · have hmul : a i * ⟨e i / x, hdivO _ (hmax i)⟩ = 1 := by
        ext
        simp only [a, h, ↓reduceDIte, MulMemClass.coe_mul, OneMemClass.coe_one]
        field_simp [he0 i, hx0]
      have := congrArg (IsLocalRing.residue O) hmul
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_left this
    · have hc : c i = 0 := hlt _ (hmax i) (lt_of_le_of_ne (hmax i) h)
      simp [a, h, hc]
  -- T4, T5: the hypothesis of `tlin`.
  by_contra hall
  push Not at hall
  have hT : ∀ θ : κ →ₗ[k] k, ∑ i, algebraMap k κ (θ (c i)) * (c i)⁻¹ = 0 := by
    intro θ
    obtain ⟨φ, hφθ⟩ := hφ θ
    have hφe : ∀ i, φ (e i) = θ (c i) := fun i => hφθ (e i) (hmax i)
    have hφ1 : φ 1 = 0 := by
      have h1 : v 1 ≤ v x := by rw [map_one]; exact hx1.le
      rw [hφθ 1 h1, hlt 1 h1 (by rw [map_one]; exact hx1), map_zero]
    have hψ : ∀ ψ : K →ₗ[k] k, ψ (∑ i, φ (e i) • (e i)⁻¹) = 0 := by
      intro ψ
      have := hall φ ψ
      rw [hφ1, mul_zero, zero_mul] at this
      rw [← this, map_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [e, map_smul, smul_eq_mul, mul_comm]
    have hz : ∑ i, φ (e i) • (e i)⁻¹ = 0 :=
      (Module.forall_dual_apply_eq_zero_iff k _).1 hψ
    have hs : ∑ i, algebraMap k O (φ (e i)) * a i = 0 := by
      ext
      simp only [ZeroMemClass.coe_zero]
      rw [← mul_zero x, ← hz, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hι, Algebra.smul_def]
      by_cases h : v (e i) = v x
      · simp only [a, h, ↓reduceDIte]; field_simp
      · have hc : c i = 0 := hlt _ (hmax i) (lt_of_le_of_ne (hmax i) h)
        simp [a, h, hφe, hc]
    have := congrArg (IsLocalRing.residue O) hs
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hκ, hres_a, hφe]
  -- T6
  have hJ := tlin k κ (Finset.univ.filter fun i => c i ≠ 0) c (fun i hi => (Finset.mem_filter.1 hi).2)
    (fun θ => by
      rw [Finset.sum_filter]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (hT θ)
      split_ifs with h
      · rfl
      · push Not at h; simp [h])
  have : CharZero κ := charZero_of_injective_algebraMap (algebraMap k κ).injective
  rw [Nat.cast_eq_zero, Finset.card_eq_zero] at hJ
  have hi0J : i0 ∈ Finset.univ.filter fun i => c i ≠ 0 := by
    simp [hci0]
  rw [hJ] at hi0J
  exact absurd hi0J (Finset.notMem_empty _)

end PEqualNP.Gct.Helpers.S2Val
