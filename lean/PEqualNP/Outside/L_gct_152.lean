import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_152 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V) (v : V) (A : Submodule ℂ V), B.Nondegenerate → B.IsSymm → B v v ≠ 0 → (∀ a ∈ A, B v a = 0) → (∀ a ∈ A, ∀ a' ∈ A, B a a' = 0) → 2 * Module.finrank ℂ A + 1 ≤ Module.finrank ℂ V := by
  intro V _ _ _ B v A hnd hsymm hvv hvA hAA
  -- `v` is nonzero and lies outside `A`, since `B v v ≠ 0` while `A` is totally isotropic.
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvv (by simp)
  have hvnot : v ∉ A := fun hv => hvv (hAA v hv v hv)
  -- Both `A` and `v` lie in the orthogonal complement of `A`.
  have hle : A ⊔ Submodule.span ℂ {v} ≤ B.orthogonal A := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hAA n hn a ha
    · refine Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [hsymm.eq n v]
      exact hvA n hn
  -- `A` and the line through `v` meet only in `0`.
  have hinf : A ⊓ Submodule.span ℂ {v} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxv⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply hvnot
      have h1 := A.smul_mem c⁻¹ hxA
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  -- So `dim (A ⊔ span v) = dim A + 1`.
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span ℂ {v})
  have h0 : Module.finrank ℂ (A ⊓ Submodule.span ℂ {v} : Submodule ℂ V) = 0 := by
    rw [hinf]; simp
  have h1 : Module.finrank ℂ (Submodule.span ℂ {v}) = 1 := finrank_span_singleton hv0
  have hmono : Module.finrank ℂ (A ⊔ Submodule.span ℂ {v} : Submodule ℂ V)
      ≤ Module.finrank ℂ (B.orthogonal A) := Submodule.finrank_mono hle
  -- Nondegeneracy: nothing nonzero is orthogonal to everything, so `dim A + dim A^⊥ = dim V`.
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact hnd.2 x (fun n => hx n Submodule.mem_top)
  have horth := LinearMap.BilinForm.finrank_add_finrank_orthogonal hsymm.isRefl A
  rw [htop, inf_bot_eq, finrank_bot, add_zero] at horth
  omega