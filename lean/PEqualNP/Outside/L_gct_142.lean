import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_142_aux

open Finset

theorem key (n : ℕ) (w : Fin n → ℂ)
    (h : ∀ j : ℕ, 1 ≤ j →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * j), ∏ i ∈ S, w i = 0) :
    ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2 := by
  have h1 : ∏ i, (1 - w i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, (-1) ^ t.card * ∏ i ∈ t, w i := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg]
  have hk : ∀ k : ℕ,
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ((∏ i ∈ t, w i) + (-1) ^ t.card * ∏ i ∈ t, w i) =
      (1 + (-1) ^ k) * ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ t, w i := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.mp ht).2]
    ring
  rw [Finset.prod_one_add, h1, ← Finset.sum_add_distrib,
    ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
      (t := Finset.range ((Finset.univ : Finset (Fin n)).card + 1))
      (fun t _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ t)))]
  simp_rw [← Finset.powersetCard_eq_filter, hk]
  rw [Finset.sum_eq_single 0]
  · simp
    norm_num
  · intro k _ hk0
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by ring, h j (by omega), mul_zero]
    · rw [pow_succ, pow_mul]
      norm_num
  · intro h0
    simp at h0

theorem coord_zero (n : ℕ) (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ w ∈ W, ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2)
    (u : Fin n → ℂ) (hu : u ∈ W) (k : Fin n) (huk : u k ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ W) (hzk : z k = 0) : z = 0 := by
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i0, z i0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  set w0 : Fin n → ℂ := (-1 / u k) • u with hw0
  set s : ℂ := (1 - w0 i0) / z i0 with hs
  have hw : w0 + s • z ∈ W := W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hz)
  have e := hW _ hw
  have hA : ∏ i, (1 + (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hw0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzk, mul_zero, add_zero]
    field_simp
    ring
  have hB : ∏ i, (1 - (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    field_simp
    ring
  rw [hA, hB] at e
  norm_num at e

end PEqualNP.Outside.L_gct_142_aux

open PEqualNP.Outside.L_gct_142_aux in
theorem PEqualNP.Outside.L_gct_142 : ∀ (n : ℕ) (W : Submodule ℂ (Fin n → ℂ)), (∀ w ∈ W, ∀ j : ℕ, 1 ≤ j → ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * j), ∏ i ∈ S, w i = 0) → Module.finrank ℂ W ≤ 1 := by
  intro n W hW
  have hW' : ∀ w ∈ W, ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2 :=
    fun w hw => key n w (hW w hw)
  by_cases hex : ∃ u ∈ W, u ≠ 0
  · obtain ⟨u, hu, hu0⟩ := hex
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (funext hall)
    refine finrank_le_one (⟨u, hu⟩ : W) fun w => ⟨w.1 k / u k, ?_⟩
    have hz := coord_zero n W hW' u hu k hk (u k • w.1 - w.1 k • u)
      (W.sub_mem (W.smul_mem _ w.2) (W.smul_mem _ hu)) (by simp; ring)
    apply Subtype.ext
    simp only [SetLike.val_smul]
    have hz' : u k • w.1 = w.1 k • u := sub_eq_zero.mp hz
    funext i
    have := congrFun hz' i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this.symm
  · push Not at hex
    refine finrank_le_one (0 : W) fun w => ⟨0, ?_⟩
    apply Subtype.ext
    simp [hex w.1 w.2]
