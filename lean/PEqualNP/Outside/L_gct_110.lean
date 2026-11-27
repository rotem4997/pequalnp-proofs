import Mathlib
import PEqualNP.Defs

open Finset Equiv

namespace PEqualNP.Outside.L_gct_110_aux

/-- Sum over all permutations of the product of the entries `h (σ k) k` over the columns in `S`. -/
noncomputable def colSum {n : ℕ} (h : Fin n → Fin n → ℂ) (S : Finset (Fin n)) : ℂ :=
  ∑ σ : Perm (Fin n), ∏ k ∈ S, h (σ k) k

/-- The part of a sum over permutations where column `i` goes to row `r`. -/
noncomputable def fiberSum {n : ℕ} (G : Perm (Fin n) → ℂ) (i r : Fin n) : ℂ :=
  ∑ σ : Perm (Fin n), if σ i = r then G σ else 0

/-- `h` with row `r` set to zero. -/
def zeroRow {n : ℕ} (h : Fin n → Fin n → ℂ) (r : Fin n) : Fin n → Fin n → ℂ :=
  fun r' k => if r' = r then 0 else h r' k

theorem sum_split {n : ℕ} (G : Perm (Fin n) → ℂ) (i : Fin n) :
    ∑ σ, G σ = ∑ r : Fin n, fiberSum G i r := by
  unfold fiberSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- If `G` only reads the columns in `U` and vanishes when one of them goes to row `r`, then
every row `r'` gets the same share as `r` from the permutations avoiding `r'` on `U`, so the
full sum is `n - #U` times the fiber over `σ i = r`. The proof swaps rows `r` and `r'`. -/
theorem sum_eq_mul_fiberSum {n : ℕ} (G : Perm (Fin n) → ℂ) (U : Finset (Fin n)) (i r : Fin n)
    (hi : i ∉ U)
    (h1 : ∀ σ τ : Perm (Fin n), (∀ k ∈ U, σ k = τ k) → G σ = G τ)
    (h2 : ∀ σ : Perm (Fin n), ∀ k ∈ U, σ k = r → G σ = 0) :
    ∑ σ, G σ = ((n - U.card : ℕ) : ℂ) * fiberSum G i r := by
  rw [sum_split G i]
  have hre : ∀ r' : Fin n, fiberSum G i r'
      = ∑ σ : Perm (Fin n), if σ i = r then G (swap r r' * σ) else 0 := by
    intro r'
    refine (Fintype.sum_equiv (Equiv.mulLeft (swap r r')) _ _ (fun σ => ?_)).symm
    simp only [Equiv.coe_mulLeft, Perm.mul_apply, swap_apply_eq_iff, swap_apply_right]
  rw [Finset.sum_congr rfl fun r' _ => hre r']
  unfold fiberSum
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ i = r
  · simp only [hσ, ite_true]
    have hval : ∀ r' : Fin n, G (swap r r' * σ) = if r' ∈ U.image σ then 0 else G σ := by
      intro r'
      split_ifs with hr'
      · obtain ⟨k, hk, hkr⟩ := Finset.mem_image.mp hr'
        exact h2 _ k hk (by simp [Perm.mul_apply, hkr])
      · refine h1 _ _ fun k hk => ?_
        have hne1 : σ k ≠ r := by
          intro h
          have hki : k = i := σ.injective (h.trans hσ.symm)
          exact hi (hki ▸ hk)
        have hne2 : σ k ≠ r' := fun h => hr' (Finset.mem_image.mpr ⟨k, hk, h⟩)
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne hne1 hne2]
    simp_rw [hval]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    congr 2
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ σ.injective]
  · simp [hσ]

/-- The key identity. `f` lives on the rows in `A` and `g` on the rows outside `A`; for disjoint
column sets `S` and `T`,
`(n - #S)! (n - #T)! Σ_σ Π_S f Π_T g = (n - #S - #T)! (Σ_σ Π_S f) (Σ_σ Π_T g)`. -/
theorem core {n : ℕ} (A : Finset (Fin n)) (g : Fin n → Fin n → ℂ)
    (hg : ∀ r k, g r k ≠ 0 → r ∉ A) (T S : Finset (Fin n)) :
    ∀ f : Fin n → Fin n → ℂ, (∀ r k, f r k ≠ 0 → r ∈ A) → Disjoint S T →
      (((n - S.card).factorial * (n - T.card).factorial : ℕ) : ℂ) *
        ∑ σ : Perm (Fin n), (∏ k ∈ S, f (σ k) k) * ∏ k ∈ T, g (σ k) k
      = ((n - S.card - T.card).factorial : ℂ) * colSum f S * colSum g T := by
  induction S using Finset.induction_on with
  | empty =>
    intro f _ _
    simp only [Finset.prod_empty, one_mul, Finset.card_empty, Nat.sub_zero, colSum,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    push_cast
    ring
  | insert i S' hiS ih =>
    intro f hf hdisj
    rw [Finset.disjoint_insert_left] at hdisj
    obtain ⟨hiT, hdisj'⟩ := hdisj
    have hcard : S'.card + T.card + 1 ≤ n := by
      have h := Finset.card_le_univ (insert i (S' ∪ T))
      rw [Finset.card_insert_of_notMem (by simp [hiS, hiT]),
        Finset.card_union_eq_card_add_card.mpr hdisj', Fintype.card_fin] at h
      exact h
    rw [Finset.card_insert_of_notMem hiS]
    obtain ⟨p, hp⟩ : ∃ p, n - S'.card = p + 1 := ⟨n - S'.card - 1, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, n - S'.card - T.card = q + 1 := ⟨n - S'.card - T.card - 1, by omega⟩
    have e1 : n - (S'.card + 1) = p := by omega
    have e2 : n - (S'.card + 1) - T.card = q := by omega
    rw [e2, e1]
    -- On the fiber `σ i = r` no other column goes to row `r`.
    have hres : ∀ (σ : Perm (Fin n)) (r : Fin n), σ i = r →
        ∏ k ∈ S', f (σ k) k = ∏ k ∈ S', zeroRow f r (σ k) k := by
      intro σ r hσ
      refine Finset.prod_congr rfl fun k hk => ?_
      have hne : σ k ≠ r := by
        intro h
        have hki : k = i := σ.injective (h.trans hσ.symm)
        exact hiS (hki ▸ hk)
      simp [zeroRow, hne]
    have hN : colSum f (insert i S') =
        ∑ r, f r i * fiberSum (fun σ => ∏ k ∈ S', zeroRow f r (σ k) k) i r := by
      unfold colSum
      rw [sum_split _ i]
      refine Finset.sum_congr rfl fun r _ => ?_
      unfold fiberSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with hσ
      · dsimp only
        rw [Finset.prod_insert hiS, hσ, hres σ r hσ]
      · simp
    have hX : ∑ σ : Perm (Fin n), (∏ k ∈ insert i S', f (σ k) k) * ∏ k ∈ T, g (σ k) k =
        ∑ r, f r i * fiberSum
          (fun σ => (∏ k ∈ S', zeroRow f r (σ k) k) * ∏ k ∈ T, g (σ k) k) i r := by
      rw [sum_split _ i]
      refine Finset.sum_congr rfl fun r _ => ?_
      unfold fiberSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with hσ
      · dsimp only
        rw [Finset.prod_insert hiS, hσ, hres σ r hσ]
        ring
      · simp
    have hP : ∀ r, ((p : ℂ) + 1) * fiberSum (fun σ => ∏ k ∈ S', zeroRow f r (σ k) k) i r =
        colSum (zeroRow f r) S' := by
      intro r
      unfold colSum
      rw [sum_eq_mul_fiberSum (fun σ => ∏ k ∈ S', zeroRow f r (σ k) k) S' i r hiS ?_ ?_]
      · rw [hp]
        push_cast
        ring
      · intro σ τ h
        exact Finset.prod_congr rfl fun k hk => by rw [h k hk]
      · intro σ k hk hkr
        exact Finset.prod_eq_zero hk (by simp [zeroRow, hkr])
    have hQ : ∀ r, r ∈ A →
        ((q : ℂ) + 1) * fiberSum
          (fun σ => (∏ k ∈ S', zeroRow f r (σ k) k) * ∏ k ∈ T, g (σ k) k) i r =
        ∑ σ : Perm (Fin n), (∏ k ∈ S', zeroRow f r (σ k) k) * ∏ k ∈ T, g (σ k) k := by
      intro r hr
      rw [sum_eq_mul_fiberSum (fun σ => (∏ k ∈ S', zeroRow f r (σ k) k) * ∏ k ∈ T, g (σ k) k)
        (S' ∪ T) i r (by simp [hiS, hiT]) ?_ ?_]
      · rw [Finset.card_union_eq_card_add_card.mpr hdisj', ← Nat.sub_sub, hq]
        push_cast
        ring
      · intro σ τ h
        have hS : ∏ k ∈ S', zeroRow f r (σ k) k = ∏ k ∈ S', zeroRow f r (τ k) k :=
          Finset.prod_congr rfl fun k hk => by rw [h k (Finset.mem_union_left _ hk)]
        have hT' : ∏ k ∈ T, g (σ k) k = ∏ k ∈ T, g (τ k) k :=
          Finset.prod_congr rfl fun k hk => by rw [h k (Finset.mem_union_right _ hk)]
        rw [hS, hT']
      · intro σ k hk hkr
        rcases Finset.mem_union.mp hk with hk | hk
        · rw [Finset.prod_eq_zero hk (by simp [zeroRow, hkr]), zero_mul]
        · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hk ?_)
          rw [hkr]
          by_contra hne
          exact hg r k hne hr
    rw [hX, hN]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hfr : f r i = 0
    · simp [hfr]
    have hr : r ∈ A := hf r i hfr
    have hfr' : ∀ r' k, zeroRow f r r' k ≠ 0 → r' ∈ A := by
      intro r' k h
      by_cases h' : r' = r
      · simp [zeroRow, h'] at h
      · exact hf r' k (by simpa [zeroRow, h'] using h)
    have ih' := ih (zeroRow f r) hfr' hdisj'
    rw [hq, hp, ← hQ r hr, ← hP r] at ih'
    push_cast [Nat.factorial_succ] at ih'
    have key : ((p : ℂ) + 1) * ((q : ℂ) + 1) *
        ((p.factorial : ℂ) * ((n - T.card).factorial : ℂ) *
          fiberSum (fun σ => (∏ k ∈ S', zeroRow f r (σ k) k) * ∏ k ∈ T, g (σ k) k) i r) =
        ((p : ℂ) + 1) * ((q : ℂ) + 1) *
        ((q.factorial : ℂ) * fiberSum (fun σ => ∏ k ∈ S', zeroRow f r (σ k) k) i r *
          colSum g T) := by
      linear_combination ih'
    have key2 := mul_left_cancel₀
      (mul_ne_zero (Nat.cast_add_one_ne_zero p) (Nat.cast_add_one_ne_zero q)) key
    push_cast
    linear_combination (f r i) * key2

theorem eval_perm {n : ℕ} (x : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + x p) (PEqualNP.Gct.permPoly ℂ n)
      = ∑ σ : Perm (Fin n), ∏ k, (1 + x (σ k, k)) := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

theorem expand {n : ℕ} (h : Fin n → Fin n → ℂ) :
    ∑ σ : Perm (Fin n), ∏ k, (1 + h (σ k) k)
      = ∑ S ∈ (univ : Finset (Fin n)).powerset, colSum h S := by
  unfold colSum
  simp_rw [Finset.prod_one_add]
  rw [Finset.sum_comm]

theorem group_card {n : ℕ} (φ : ℕ → ℂ) (N : Finset (Fin n) → ℂ) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, φ S.card * N S
      = ∑ a ∈ range (n + 1), φ a * ∑ S ∈ powersetCard a (univ : Finset (Fin n)), N S := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.powersetCard_eq_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(Finset.mem_filter.mp hS).2]
  · intro S _
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    simp only [Finset.mem_range]
    omega

theorem colSum_smul {n : ℕ} (c : ℂ) (h : Fin n → Fin n → ℂ) (S : Finset (Fin n)) :
    colSum (fun r k => c * h r k) S = c ^ S.card * colSum h S := by
  unfold colSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- If the permanent of `J + c h` is `n!` for every scalar `c`, every positive degree level of
its expansion vanishes. -/
theorem levels_vanish {n : ℕ} (h : Fin n → Fin n → ℂ)
    (hyp : ∀ c : ℂ, ∑ σ : Perm (Fin n), ∏ k, (1 + c * h (σ k) k) = (n.factorial : ℂ)) :
    ∀ a, 1 ≤ a → ∑ S ∈ powersetCard a (univ : Finset (Fin n)), colSum h S = 0 := by
  intro a ha
  have hev : ∀ c : ℂ, (∑ j ∈ range (n + 1), Polynomial.C
      (∑ S ∈ powersetCard j (univ : Finset (Fin n)), colSum h S) * Polynomial.X ^ j).eval c
      = (Polynomial.C (n.factorial : ℂ)).eval c := by
    intro c
    have hx := expand (fun r k => c * h r k)
    rw [Polynomial.eval_C, ← hyp c, hx]
    simp_rw [colSum_smul]
    rw [group_card (fun a => c ^ a) (colSum h), ← Polynomial.coe_evalRingHom, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hp := Polynomial.funext hev
  by_cases han : a ≤ n
  · have hc := congrArg (fun p : Polynomial ℂ => p.coeff a) hp
    simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range, Nat.lt_succ_of_le han, Nat.one_le_iff_ne_zero.mp ha] using hc
  · rw [Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; omega)]
    simp

end PEqualNP.Outside.L_gct_110_aux

open PEqualNP.Outside.L_gct_110_aux in
theorem PEqualNP.Outside.L_gct_110 : ∀ (n : ℕ) (A B : Finset (Fin n)) (L1 L2 : Submodule ℂ (Fin n × Fin n → ℂ)), (∀ t ∈ L1, ∀ p, t p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B) → (∀ t ∈ L2, ∀ p, t p ≠ 0 → p.1 ∉ A ∧ p.2 ∉ B) → (∀ t ∈ L1, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → (∀ t ∈ L2, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → ∀ t ∈ L1 ⊔ L2, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  intro n A B L1 L2 hs1 hs2 h1 h2 t ht
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ht
  have hyf : ∀ r k, y (r, k) ≠ 0 → r ∈ A ∧ k ∈ B := fun r k h => hs1 y hy (r, k) h
  have hzg : ∀ r k, z (r, k) ≠ 0 → r ∉ A ∧ k ∉ B := fun r k h => hs2 z hz (r, k) h
  -- Every positive level of the expansion for `y` vanishes.
  have hlev := levels_vanish (fun r k => y (r, k)) (fun c => by
    have := h1 (c • y) (L1.smul_mem c hy)
    rw [eval_perm] at this
    simpa using this)
  -- The two parts never share an entry, so `1 + y + z = (1 + y) (1 + z)` entrywise.
  have hmul : ∀ r k, 1 + (y + z) (r, k) = (1 + y (r, k)) * (1 + z (r, k)) := by
    intro r k
    have h0 : y (r, k) * z (r, k) = 0 := by
      by_cases hy0 : y (r, k) = 0
      · simp [hy0]
      · have hz0 : z (r, k) = 0 := by
          by_contra hz0
          exact (hzg r k hz0).1 (hyf r k hy0).1
        simp [hz0]
    simp only [Pi.add_apply]
    linear_combination -h0
  -- For each `T`, the levels of `y` collapse to the `T` term of the expansion for `z`.
  have hT : ∀ T : Finset (Fin n),
      ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ∑ σ : Perm (Fin n), (∏ k ∈ S, y (σ k, k)) * ∏ k ∈ T, z (σ k, k)
      = colSum (fun r k => z (r, k)) T := by
    intro T
    set φ : ℕ → ℂ := fun a => ((n - a - T.card).factorial : ℂ) /
      (((n - a).factorial * (n - T.card).factorial : ℕ) : ℂ) with hφ
    have hX : ∀ S : Finset (Fin n),
        ∑ σ : Perm (Fin n), (∏ k ∈ S, y (σ k, k)) * ∏ k ∈ T, z (σ k, k)
        = φ S.card * colSum (fun r k => y (r, k)) S * colSum (fun r k => z (r, k)) T := by
      intro S
      by_cases hd : Disjoint S T
      · have hc := core A (fun r k => z (r, k)) (fun r k h => (hzg r k h).1) T S
          (fun r k => y (r, k)) (fun r k h => (hyf r k h).1) hd
        have hne : (((n - S.card).factorial * (n - T.card).factorial : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
        rw [hφ, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hne]
        linear_combination hc
      · obtain ⟨k, hkS, hkT⟩ := Finset.not_disjoint_iff.mp hd
        have hl : ∑ σ : Perm (Fin n), (∏ k ∈ S, y (σ k, k)) * ∏ k ∈ T, z (σ k, k) = 0 := by
          refine Finset.sum_eq_zero fun σ _ => ?_
          by_cases hy0 : y (σ k, k) = 0
          · rw [Finset.prod_eq_zero hkS hy0, zero_mul]
          · have hz0 : z (σ k, k) = 0 := by
              by_contra hz0
              exact (hzg _ _ hz0).1 (hyf _ _ hy0).1
            rw [Finset.prod_eq_zero hkT hz0, mul_zero]
        rw [hl]
        by_cases hkB : k ∈ B
        · have : colSum (fun r k => z (r, k)) T = 0 := by
            refine Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero hkT ?_
            by_contra hz0
            exact (hzg _ _ hz0).2 hkB
          rw [this, mul_zero]
        · have : colSum (fun r k => y (r, k)) S = 0 := by
            refine Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero hkS ?_
            by_contra hy0
            exact hkB (hyf _ _ hy0).2
          rw [this, mul_zero, zero_mul]
    simp_rw [hX]
    rw [← Finset.sum_mul, group_card φ (colSum fun r k => y (r, k))]
    rw [Finset.sum_eq_single 0 (fun a _ ha => by
        rw [hlev a (Nat.one_le_iff_ne_zero.mpr ha), mul_zero])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h)]
    simp only [Finset.powersetCard_zero, Finset.sum_singleton, colSum, Finset.prod_empty,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hφ, Nat.sub_zero]
    have hne : (((n.factorial * (n - T.card).factorial : ℕ)) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    field_simp
    push_cast
    ring
  rw [eval_perm]
  calc ∑ σ : Perm (Fin n), ∏ k, (1 + (y + z) (σ k, k))
      = ∑ σ : Perm (Fin n), (∏ k, (1 + y (σ k, k))) * ∏ k, (1 + z (σ k, k)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k _ => hmul (σ k) k
    _ = ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
          ∑ σ : Perm (Fin n), (∏ k ∈ S, y (σ k, k)) * ∏ k ∈ T, z (σ k, k) := by
        simp_rw [Finset.prod_one_add, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ T ∈ (univ : Finset (Fin n)).powerset, colSum (fun r k => z (r, k)) T := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun T _ => hT T
    _ = (Nat.factorial n : ℂ) := by
        rw [← expand (fun r k => z (r, k)), ← h2 z hz, eval_perm]
