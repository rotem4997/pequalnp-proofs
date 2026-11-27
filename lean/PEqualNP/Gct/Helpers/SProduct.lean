import Mathlib
import PEqualNP.Gct.Helpers.InvisibleBlock

/-! Helper for L-gct-102, proofs only. `p + 1` row subspaces of `ℂ^q`, indexed by
`Option (Fin p)`, on which every level sum (the sum over all `k`-sets of rows of the injective
sums) vanishes, plus a subspace `Y` of `ℂ^p` inside the zero-sum hyperplane.

1. Isolation: putting zero rows outside a set `A` kills every `k`-set other than `A` in the level
   sum with `k = card A`, so every injective sum over a nonempty set of rows vanishes.
2. Transport to `Fin (p + 1)` by `finSuccEquiv` (reindexing the embeddings), then
   `InvisibleBlock.diag_of_inj` (diagonal sums vanish) and `ProdSigmaChain.chain` give
   `∑ dim W_i + dim X + 1 ≤ q`.
3. `Y` lies in the kernel of the nonzero sum functional, so `dim Y + 1 ≤ p`. -/

namespace PEqualNP.Gct.Helpers.SProduct

open Module Finset

/-- Reindexing an injective sum along an equivalence of the index types. -/
theorem embSum_equiv {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq γ] (h : ι ≃ κ) (u : κ → γ → ℂ) :
    ∑ f : κ ↪ γ, ∏ k, u k (f k) = ∑ f : ι ↪ γ, ∏ i, u (h i) (f i) := by
  rw [← (Equiv.embeddingCongr h (Equiv.refl γ)).sum_comp]
  refine Fintype.sum_congr _ _ fun f => ?_
  rw [← h.prod_comp]
  simp [Equiv.embeddingCongr_apply]

/-- Step 1: one injective sum isolated from the level sums. -/
theorem isolate {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (U : α → Submodule ℂ (Fin q → ℂ))
    (hlev : ∀ t : α → Fin q → ℂ, (∀ a, t a ∈ U a) → ∀ k : ℕ, 1 ≤ k →
      ∑ R ∈ (univ : Finset α).powersetCard k, ∑ f : ↥R ↪ Fin q, ∏ r : ↥R, t (r : α) (f r) = 0)
    (A : Finset α) (hA : A.Nonempty) (s : α → Fin q → ℂ) (hs : ∀ a ∈ A, s a ∈ U a) :
    ∑ f : ↥A ↪ Fin q, ∏ r : ↥A, s (r : α) (f r) = 0 := by
  set t : α → Fin q → ℂ := fun a => if a ∈ A then s a else 0 with ht_def
  have ht : ∀ a, t a ∈ U a := by
    intro a
    by_cases ha : a ∈ A
    · simpa [ht_def, ha] using hs a ha
    · simp [ht_def, ha]
  have h := hlev t ht A.card hA.card_pos
  rw [Finset.sum_eq_single_of_mem A (mem_powersetCard.2 ⟨subset_univ _, rfl⟩)] at h
  · have e : ∀ r : ↥A, t (r : α) = s r := fun r => by simp [ht_def, r.2]
    simpa only [e] using h
  · intro R hR hRA
    have hcard := (mem_powersetCard.1 hR).2
    have hns : ¬ R ⊆ A := fun hsub => hRA (Finset.eq_of_subset_of_card_le hsub hcard.ge)
    obtain ⟨r, hr, hrA⟩ := Finset.not_subset.1 hns
    refine Finset.sum_eq_zero fun f _ => ?_
    exact Finset.prod_eq_zero (mem_univ ⟨r, hr⟩) (by simp [ht_def, hrA])

/-- Step 3: a subspace of the zero-sum hyperplane of `ℂ^p` has dimension at most `p - 1`. -/
theorem zeroSum_bound (p : ℕ) (hp : 1 ≤ p) (Y : Submodule ℂ (Fin p → ℂ))
    (hY : ∀ y ∈ Y, ∑ i, y i = 0) : finrank ℂ Y + 1 ≤ p := by
  let φ : (Fin p → ℂ) →ₗ[ℂ] ℂ := ∑ i : Fin p, LinearMap.proj i
  have hφ : ∀ y, φ y = ∑ i, y i := fun y => by simp [φ, LinearMap.sum_apply]
  have hYk : Y ≤ LinearMap.ker φ := fun y hy => by simp [hφ, hY y hy]
  have hne : LinearMap.range φ ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot]
    intro h0
    have := LinearMap.congr_fun h0 (Pi.single (⟨0, hp⟩ : Fin p) 1)
    simp [hφ] at this
  have hr : finrank ℂ (LinearMap.range φ) ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.1 h)
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hmono := Submodule.finrank_mono hYk
  rw [Module.finrank_fin_fun] at hrk
  omega

theorem main : ∀ (p q : ℕ) (W : Fin p → Submodule ℂ (Fin q → ℂ)) (X : Submodule ℂ (Fin q → ℂ)) (Y : Submodule ℂ (Fin p → ℂ)), 1 ≤ p → 1 ≤ q → (∀ t : Option (Fin p) → (Fin q → ℂ), (∀ i, t (some i) ∈ W i) → t none ∈ X → ∀ k : ℕ, 1 ≤ k → ∑ R ∈ (Finset.univ : Finset (Option (Fin p))).powersetCard k, ∑ f : ↥R ↪ Fin q, ∏ r : ↥R, t (r : Option (Fin p)) (f r) = 0) → (∀ y ∈ Y, ∑ i, y i = 0) → ∑ i, Module.finrank ℂ (W i) + Module.finrank ℂ X + Module.finrank ℂ Y + 2 ≤ p + q := by
  intro p q W X Y hp hq hlev hY
  let U : Option (Fin p) → Submodule ℂ (Fin q → ℂ) := fun o => Option.elim o X W
  have hinjO := isolate U (fun t ht k hk => hlev t (fun i => ht (some i)) (ht none) k hk)
  let e : Fin (p + 1) ≃ Option (Fin p) := finSuccEquiv p
  let V : Fin (p + 1) → Submodule ℂ (Fin q → ℂ) := fun j => U (e j)
  have hinj : ∀ Y' : Finset (Fin (p + 1)), Y'.Nonempty → ∀ s : Fin (p + 1) → Fin q → ℂ,
      (∀ y ∈ Y', s y ∈ V y) → ∑ f : ↥Y' ↪ Fin q, ∏ y : ↥Y', s y (f y) = 0 := by
    intro Y' hY' s hs
    have h := hinjO (Y'.map e.toEmbedding) (hY'.map) (fun o => s (e.symm o)) (by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 ha
      simpa [V] using hs y hy)
    have hre := embSum_equiv
      (Equiv.subtypeEquiv e (fun a => (Finset.mem_map' e.toEmbedding).symm) :
        ↥Y' ≃ ↥(Y'.map e.toEmbedding))
      (fun k c => s (e.symm (k : Option (Fin p))) c)
    rw [hre] at h
    simpa using h
  have hdiag := PEqualNP.Gct.Helpers.InvisibleBlock.diag_of_inj V hinj
  have hc := PEqualNP.Gct.Helpers.ProdSigmaChain.chain q (p + 1) hq V hdiag
  have hle := Submodule.finrank_le (Submodule.span ℂ
      {v : Fin q → ℂ | ∃ (S : Finset (Fin (p + 1))) (t : Fin (p + 1) → (Fin q → ℂ)),
        (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i})
  rw [Module.finrank_fin_fun] at hle
  have hsum : ∑ i, finrank ℂ (V i) = finrank ℂ X + ∑ i, finrank ℂ (W i) := by
    rw [Fin.sum_univ_succ]
    refine congrArg₂ (· + ·) rfl (Fintype.sum_congr _ _ fun i => ?_)
    have hV : V i.succ = W i := by
      change Option.elim (finSuccEquiv p i.succ) X W = W i
      rw [finSuccEquiv_succ]
      rfl
    exact congrArg (fun S : Submodule ℂ (Fin q → ℂ) => finrank ℂ S) hV
  have hYb := zeroSum_bound p hp Y hY
  omega

end PEqualNP.Gct.Helpers.SProduct
