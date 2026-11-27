import Mathlib

/-!
# A dimension count for matrices compatible with a corank-one matrix

If `det M = 0` and `adj M ≠ 0`, then `adj M = v uᵀ` with `v, u ≠ 0` and the image of `M` is the
hyperplane `uᵀ y = 0`. Any matrix `D` with `D M = adj(M) X` then has the form `v aᵀ + b uᵀ`, and the
extra constraints `D A0 = 0`, `A0 D = 0` (with `A0 ≠ 0`, `uᵀ A0 = 0`) cut the dimension of a space
of such `D` down to at most `2 n - 3`.
-/

open Matrix Module

namespace PEqualNP.Gct.Helpers

/-- The hyperplane `{y | u ⬝ᵥ y = 0}`. -/
def dotKer {n : ℕ} (u : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | u ⬝ᵥ y = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_smul, ha, smul_zero]

lemma mem_dotKer {n : ℕ} (u y : Fin n → ℂ) : y ∈ dotKer u ↔ u ⬝ᵥ y = 0 := Iff.rfl

/-- The left kernel `{a | a ᵥ* A = 0}`. -/
def leftKer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {a | a ᵥ* A = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [add_vecMul, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_vecMul, ha, smul_zero]

lemma mem_leftKer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    a ∈ leftKer A ↔ a ᵥ* A = 0 := Iff.rfl

lemma vecMulVec_mulVec' {n : ℕ} (v u x : Fin n → ℂ) :
    vecMulVec v u *ᵥ x = (u ⬝ᵥ x) • v := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

/-- If `adj M ≠ 0` then the kernel of `M` has dimension at most one. -/
lemma ker_finrank_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hadj : M.adjugate ≠ 0) :
    finrank ℂ (LinearMap.ker M.mulVecLin) ≤ 1 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, M.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hadj (Matrix.ext h)
  set N := M.updateRow j (Pi.single i 1) with hNdef
  have hN : N.det ≠ 0 := by rwa [adjugate_apply] at hij
  let f : LinearMap.ker M.mulVecLin →ₗ[ℂ] ℂ :=
    (LinearMap.proj j).comp (N.mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ h0
    have hMx : M *ᵥ x = 0 := by simpa using hx
    have h0' : (N *ᵥ x) j = 0 := by simpa [f] using h0
    have hNx : N *ᵥ x = 0 := by
      funext k
      by_cases hk : k = j
      · subst hk; exact h0'
      · have : (N *ᵥ x) k = (M *ᵥ x) k := by
          simp only [mulVec, hNdef, updateRow_ne hk]
        rw [this, hMx]
    by_contra hne
    exact hN ((exists_mulVec_eq_zero_iff).1 ⟨x, fun h => hne (Subtype.ext h), hNx⟩)
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

theorem finrank_le_dimcount {n : ℕ} (M A0 : Matrix (Fin n) (Fin n) ℂ) (hdet : M.det = 0)
    (hadj : M.adjugate ≠ 0) (h1 : M.adjugate * A0 = 0) (h2 : A0 * M.adjugate = 0) (hA0 : A0 ≠ 0)
    (s : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hs : ∀ D ∈ s, D * A0 = 0 ∧ A0 * D = 0 ∧ ∃ X : Matrix (Fin n) (Fin n) ℂ, D * M = M.adjugate * X) :
    Module.finrank ℂ s + 3 ≤ 2 * n := by
  classical
  set K := LinearMap.ker M.mulVecLin with hKdef
  have hK1 := ker_finrank_le_one M hadj
  obtain ⟨i, j, hij⟩ : ∃ i j, M.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hadj (Matrix.ext h)
  have hMadj : M * M.adjugate = 0 := by rw [mul_adjugate, hdet, zero_smul]
  have hadjM : M.adjugate * M = 0 := by rw [adjugate_mul, hdet, zero_smul]
  set v : Fin n → ℂ := fun k => M.adjugate k j with hvdef
  have hv0 : v ≠ 0 := fun h => hij (congrFun h i)
  have hcol : ∀ k, (fun r => M.adjugate r k) ∈ K := by
    intro k
    have : M *ᵥ (fun r => M.adjugate r k) = 0 := by
      have h := congrArg (fun A => A *ᵥ Pi.single k (1 : ℂ)) hMadj
      simp only [mulVec_single_one] at h
      exact h
    simpa [hKdef] using this
  have hvK : v ∈ K := hcol j
  have hKeq : finrank ℂ K = 1 := by
    refine le_antisymm hK1 ?_
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    apply hv0
    have : v ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ hvK
    simpa using this
  have hKv : ∀ x ∈ K, ∃ c : ℂ, c • v = x := by
    intro x hx
    have hne : (⟨v, hvK⟩ : K) ≠ 0 := by
      intro h; exact hv0 (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨v, hvK⟩ : K) hne).1 hKeq ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hex : ∀ k, ∃ c : ℂ, c • v = fun r => M.adjugate r k := fun k => hKv _ (hcol k)
  choose u hu using hex
  have hadj_eq : M.adjugate = vecMulVec v u := by
    ext r k
    have := congrFun (hu k) r
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [vecMulVec_apply, ← this, mul_comm]
  have hu0 : u ≠ 0 := by
    intro h; apply hadj; rw [hadj_eq, h]; simp
  have huA0 : u ᵥ* A0 = 0 := by
    rw [hadj_eq, vecMulVec_mul, vecMulVec_eq_zero] at h1
    exact h1.resolve_left hv0
  have huM : u ᵥ* M = 0 := by
    rw [hadj_eq, vecMulVec_mul, vecMulVec_eq_zero] at hadjM
    exact hadjM.resolve_left hv0
  -- normalising vectors
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push Not at h; exact hu0 (funext h)
  obtain ⟨i1, hi1⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv0 (funext h)
  set w : Fin n → ℂ := Pi.single i0 (u i0)⁻¹ with hwdef
  set f : Fin n → ℂ := Pi.single i1 (v i1)⁻¹ with hfdef
  have huw : u ⬝ᵥ w = 1 := by rw [hwdef, dotProduct_single, mul_inv_cancel₀ hi0]
  have hfv : f ⬝ᵥ v = 1 := by rw [hfdef, single_dotProduct, inv_mul_cancel₀ hi1]
  -- the image of `M` is the hyperplane `u ⬝ᵥ y = 0`
  have hrange : ∀ y, u ⬝ᵥ y = 0 → ∃ z, M *ᵥ z = y := by
    have hle : LinearMap.range M.mulVecLin ≤ dotKer u := by
      rintro _ ⟨z, rfl⟩
      rw [mem_dotKer, mulVecLin_apply, dotProduct_mulVec, huM, zero_dotProduct]
    have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [← hKdef, hKeq, Module.finrank_fin_fun] at hrn
    have hH : finrank ℂ (dotKer u) < n := by
      have hne : dotKer u ≠ ⊤ := by
        intro h
        have : w ∈ dotKer u := h ▸ Submodule.mem_top
        rw [mem_dotKer, huw] at this
        exact one_ne_zero this
      simpa using Submodule.finrank_lt hne
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro y hy
    have : y ∈ LinearMap.range M.mulVecLin := heq ▸ hy
    obtain ⟨z, hz⟩ := this
    exact ⟨z, by simpa using hz⟩
  -- rank-one shape of every `D ∈ s`
  set P : Matrix (Fin n) (Fin n) ℂ := 1 - vecMulVec w u with hPdef
  have hPx : ∀ x, P *ᵥ x = x - (u ⬝ᵥ x) • w := by
    intro x; rw [hPdef, sub_mulVec, one_mulVec, vecMulVec_mulVec']
  have huP : ∀ x, u ⬝ᵥ (P *ᵥ x) = 0 := by
    intro x; rw [hPx, dotProduct_sub, dotProduct_smul, huw, smul_eq_mul, mul_one, sub_self]
  have hDy : ∀ D ∈ s, ∀ y, u ⬝ᵥ y = 0 → D *ᵥ y = (f ⬝ᵥ (D *ᵥ y)) • v := by
    intro D hD y hy
    obtain ⟨z, rfl⟩ := hrange y hy
    obtain ⟨-, -, X, hX⟩ := hs D hD
    have : D *ᵥ (M *ᵥ z) = ((u ᵥ* X) ⬝ᵥ z) • v := by
      rw [mulVec_mulVec, hX, hadj_eq, vecMulVec_mul, vecMulVec_mulVec']
    rw [this, dotProduct_smul, hfv, smul_eq_mul, mul_one]
  have hshape : ∀ D ∈ s, D = vecMulVec v (f ᵥ* (D * P)) + vecMulVec (D *ᵥ w) u := by
    intro D hD
    apply ext_of_mulVec_single
    intro k
    set x : Fin n → ℂ := Pi.single k 1
    rw [add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', ← dotProduct_mulVec, ← mulVec_mulVec,
      ← hDy D hD _ (huP x), hPx, mulVec_sub, mulVec_smul]
    abel
  -- the target subspaces
  set S1 : Submodule ℂ (Fin n → ℂ) := leftKer A0 ⊓ dotKer w with hS1def
  set S2 : Submodule ℂ (Fin n → ℂ) := LinearMap.ker A0.mulVecLin with hS2def
  have hmem1 : ∀ D ∈ s, f ᵥ* (D * P) ∈ S1 := by
    intro D hD
    obtain ⟨hDA, -, -⟩ := hs D hD
    refine ⟨?_, ?_⟩
    · show f ᵥ* (D * P) ᵥ* A0 = 0
      have hPA : P * A0 = A0 := by
        rw [hPdef, sub_mul, one_mul, vecMulVec_mul, huA0]; simp
      rw [vecMul_vecMul, Matrix.mul_assoc, hPA, hDA, vecMul_zero]
    · show w ⬝ᵥ f ᵥ* (D * P) = 0
      rw [dotProduct_comm, ← dotProduct_mulVec, ← mulVec_mulVec, hPx, huw, one_smul, sub_self,
        mulVec_zero, dotProduct_zero]
  have hmem2 : ∀ D ∈ s, D *ᵥ w ∈ S2 := by
    intro D hD
    obtain ⟨-, hAD, -⟩ := hs D hD
    show A0.mulVecLin (D *ᵥ w) = 0
    rw [mulVecLin_apply, mulVec_mulVec, hAD, zero_mulVec]
  let Ψ1 : s →ₗ[ℂ] S1 :=
    { toFun := fun D => ⟨f ᵥ* (D.1 * P), hmem1 D.1 D.2⟩
      map_add' := by
        intro D E; apply Subtype.ext
        simp [add_mul, vecMul_add]
      map_smul' := by
        intro c D; apply Subtype.ext
        simp [vecMul_smul] }
  let Ψ2 : s →ₗ[ℂ] S2 :=
    { toFun := fun D => ⟨D.1 *ᵥ w, hmem2 D.1 D.2⟩
      map_add' := by
        intro D E; apply Subtype.ext
        simp [add_mulVec]
      map_smul' := by
        intro c D; apply Subtype.ext
        simp [smul_mulVec] }
  have hinj : Function.Injective (Ψ1.prod Ψ2) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    have ha : f ᵥ* (D.1 * P) = 0 := congrArg Subtype.val (congrArg Prod.fst hD)
    have hb : D.1 *ᵥ w = 0 := congrArg Subtype.val (congrArg Prod.snd hD)
    apply Subtype.ext
    rw [hshape D.1 D.2, ha, hb]
    simp
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  -- bounds on S1 and S2
  have hS2 : finrank ℂ S2 < n := by
    have hne : S2 ≠ ⊤ := by
      intro h
      apply hA0
      apply ext_of_mulVec_single
      intro k
      have : Pi.single k (1 : ℂ) ∈ S2 := h ▸ Submodule.mem_top
      simpa [hS2def] using this
    simpa using Submodule.finrank_lt hne
  have hL : finrank ℂ (leftKer A0) < n := by
    have hne : leftKer A0 ≠ ⊤ := by
      intro h
      apply hA0
      ext r k
      have : Pi.single r (1 : ℂ) ∈ leftKer A0 := h ▸ Submodule.mem_top
      rw [mem_leftKer, single_one_vecMul] at this
      exact congrFun this k
    simpa using Submodule.finrank_lt hne
  have hS1 : finrank ℂ S1 < finrank ℂ (leftKer A0) := by
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    have : u ∈ S1 := h ▸ (show u ∈ leftKer A0 from huA0)
    have h' : w ⬝ᵥ u = 0 := this.2
    rw [dotProduct_comm, huw] at h'
    exact one_ne_zero h'
  omega

end PEqualNP.Gct.Helpers
