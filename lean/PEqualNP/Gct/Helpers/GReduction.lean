import PEqualNP.Defs

/-! Helpers for L-gct-077, the reduction of the zero-subspace bound at `Sigma_(n+1)` to the
level-space problem for `perm_n`. For `s` an `n x n` matrix and `t` its extension by zeros on
row and column `0`, with `x_i = 1 + c * s (σ i, i)`:
`perm_(n+1) (Sigma + c t) = - c * d/dc perm_n (J + c s)`,
proved permutation by permutation via `Equiv.Perm.decomposeFin`. -/

namespace PEqualNP.Gct.GReduction

open Finset Polynomial

theorem eval_perm {m : ℕ} (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      ∑ σ : Equiv.Perm (Fin m), ∏ i, z (σ i, i) := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- The point `Sigma_(n+1)`: entry `(0,0)` is `-n`, every other entry is `1`. -/
noncomputable def sig (n : ℕ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun q => if q.1 = 0 ∧ q.2 = 0 then -(n : ℂ) else 1

/-- Extension by zeros on row and column `0`. -/
def extF {n : ℕ} (s : Fin n × Fin n → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun q => Fin.cases 0 (fun a => Fin.cases 0 (fun b => s (a, b)) q.2) q.1

theorem extF_zero_left {n : ℕ} (s : Fin n × Fin n → ℂ) (b : Fin (n + 1)) : extF s (0, b) = 0 := by
  simp [extF]

theorem extF_succ_zero {n : ℕ} (s : Fin n × Fin n → ℂ) (a : Fin n) : extF s (a.succ, 0) = 0 := by
  simp [extF]

theorem extF_succ_succ {n : ℕ} (s : Fin n × Fin n → ℂ) (a b : Fin n) :
    extF s (a.succ, b.succ) = s (a, b) := by
  simp [extF]

noncomputable def ext (n : ℕ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) × Fin (n + 1) → ℂ) where
  toFun := extF
  map_add' s t := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Fin.cases <;> induction b using Fin.cases <;> simp [extF]
  map_smul' c s := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Fin.cases <;> induction b using Fin.cases <;> simp [extF]

theorem ext_apply {n : ℕ} (s : Fin n × Fin n → ℂ) : ext n s = extF s := rfl

theorem ext_injective (n : ℕ) : Function.Injective (ext n) := by
  intro s t h
  funext q
  rcases q with ⟨a, b⟩
  have := congrFun h (a.succ, b.succ)
  simpa [ext_apply, extF_succ_succ] using this

theorem sig_zero_zero (n : ℕ) : sig n (0, 0) = -(n : ℂ) := by simp [sig]

theorem sig_succ_left (n : ℕ) (a : Fin n) (b : Fin (n + 1)) : sig n (a.succ, b) = 1 := by
  simp [sig, Fin.succ_ne_zero]

theorem sig_succ_right (n : ℕ) (a : Fin (n + 1)) (b : Fin n) : sig n (a, b.succ) = 1 := by
  simp [sig, Fin.succ_ne_zero]

/-- The per-permutation algebra: `-n Π x + Σ_r Π_{i ≠ r} x = -c Σ_r a_r Π_{i ≠ r} x`. -/
theorem per_perm (n : ℕ) (a : Fin n → ℂ) (c : ℂ) :
    -(n : ℂ) * ∏ i, (1 + c * a i) + ∑ r, ∏ i ∈ univ.erase r, (1 + c * a i) =
      -c * ∑ r, a r * ∏ i ∈ univ.erase r, (1 + c * a i) := by
  have hr : ∀ r, ∏ i, (1 + c * a i) = (1 + c * a r) * ∏ i ∈ univ.erase r, (1 + c * a i) :=
    fun r => (mul_prod_erase univ _ (mem_univ r)).symm
  have hs : (n : ℂ) * ∏ i, (1 + c * a i) =
      ∑ r, (1 + c * a r) * ∏ i ∈ univ.erase r, (1 + c * a i) := by
    rw [← sum_congr rfl (fun r _ => hr r)]
    simp
  rw [neg_mul, hs, mul_sum, ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  ring

theorem term_zero (n : ℕ) (s : Fin n × Fin n → ℂ) (c : ℂ) (σ : Equiv.Perm (Fin n)) :
    (sig n + c • extF s) (0, 0) *
        ∏ i : Fin n, (sig n + c • extF s) (Equiv.swap 0 0 (σ i).succ, i.succ) =
      -(n : ℂ) * ∏ i, (1 + c * s (σ i, i)) := by
  simp only [Equiv.swap_self, Equiv.refl_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sig_zero_zero, extF_zero_left, sig_succ_left, extF_succ_succ, mul_zero, add_zero]

theorem term_succ (n : ℕ) (s : Fin n × Fin n → ℂ) (c : ℂ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (sig n + c • extF s) (k.succ, 0) *
        ∏ i : Fin n, (sig n + c • extF s) (Equiv.swap 0 k.succ (σ i).succ, i.succ) =
      ∏ i, (if σ i = k then 1 else 1 + c * s (σ i, i)) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sig_succ_left, extF_succ_zero, mul_zero,
    add_zero, one_mul]
  refine prod_congr rfl fun i _ => ?_
  by_cases h : σ i = k
  · subst h
    simp [Equiv.swap_apply_right, sig_succ_right, extF_zero_left]
  · have h1 : (σ i).succ ≠ 0 := Fin.succ_ne_zero _
    have h2 : (σ i).succ ≠ k.succ := fun e => h (Fin.succ_injective _ e)
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, if_neg h, sig_succ_left, extF_succ_succ]

theorem sum_reindex (n : ℕ) (x : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ∑ k, ∏ i, (if σ i = k then 1 else x i) = ∑ r, ∏ i ∈ univ.erase r, x i := by
  rw [← Equiv.sum_comp σ]
  refine sum_congr rfl fun r _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ r), if_pos rfl, one_mul]
  refine prod_congr rfl fun i hi => ?_
  have : i ≠ r := ne_of_mem_erase hi
  rw [if_neg (fun e => this (σ.injective e))]

/-- KEY IDENTITY. -/
theorem key (n : ℕ) (s : Fin n × Fin n → ℂ) (c : ℂ) :
    MvPolynomial.eval (sig n + c • extF s) (PEqualNP.Gct.permPoly ℂ (n + 1)) =
      -c * ∑ σ : Equiv.Perm (Fin n), ∑ r, s (σ r, r) * ∏ i ∈ univ.erase r, (1 + c * s (σ i, i)) := by
  rw [eval_perm, ← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [term_zero, term_succ]
  rw [sum_comm, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [sum_reindex n (fun i => 1 + c * s (σ i, i)) σ]
  exact per_perm n (fun i => s (σ i, i)) c

/-- `perm_n (J + X s)` as a polynomial in `X`. -/
noncomputable def F {n : ℕ} (s : Fin n × Fin n → ℂ) : ℂ[X] :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, (1 + X * C (s (σ i, i)))

theorem eval_F {n : ℕ} (s : Fin n × Fin n → ℂ) (c : ℂ) :
    (F s).eval c = ∑ σ : Equiv.Perm (Fin n), ∏ i, (1 + c * s (σ i, i)) := by
  simp only [F, eval_finsetSum, eval_prod, eval_add, eval_one, eval_mul, eval_X, eval_C]

theorem eval_derivative_F {n : ℕ} (s : Fin n × Fin n → ℂ) (c : ℂ) :
    (derivative (F s)).eval c =
      ∑ σ : Equiv.Perm (Fin n), ∑ r, s (σ r, r) * ∏ i ∈ univ.erase r, (1 + c * s (σ i, i)) := by
  simp only [F, derivative_sum, derivative_prod_finset, derivative_add, derivative_one,
    derivative_mul, derivative_X, derivative_C, mul_zero, add_zero, one_mul, zero_add]
  simp only [eval_finsetSum, eval_mul, eval_prod, eval_add, eval_one, eval_X, eval_C]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun r _ => ?_
  ring

theorem level (n : ℕ) (s : Fin n × Fin n → ℂ)
    (h : ∀ c : ℂ, MvPolynomial.eval (sig n + c • extF s) (PEqualNP.Gct.permPoly ℂ (n + 1)) = 0) :
    MvPolynomial.eval (fun p => 1 + s p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  have hD : ∀ c : ℂ, c ≠ 0 → (derivative (F s)).eval c = 0 := by
    intro c hc
    have := h c
    rw [key, ← eval_derivative_F] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (neg_eq_zero.mp h0) hc
    · exact h0
  have hD0 : derivative (F s) = 0 := by
    apply eq_zero_of_infinite_isRoot
    exact (Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun c hc => hD c hc
  have hC := eq_C_of_derivative_eq_zero hD0
  have h1 : (F s).eval 1 = (F s).eval 0 := by rw [hC]; simp
  rw [eval_F, eval_F] at h1
  rw [eval_perm]
  simp only [one_mul, zero_mul, add_zero, prod_const_one, sum_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
  exact h1

theorem bound (n G : ℕ)
    (hG : ∀ L : Submodule ℂ (Fin n × Fin n → ℂ),
      (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        (Nat.factorial n : ℂ)) → Module.finrank ℂ L ≤ G)
    (L : Submodule ℂ (Fin (n + 1) × Fin (n + 1) → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (sig n + t) (PEqualNP.Gct.permPoly ℂ (n + 1)) = 0) :
    Module.finrank ℂ L ≤ G + 2 * n + 1 := by
  set L' := L.comap (ext n)
  have h1 : Module.finrank ℂ L' ≤ G := by
    refine hG L' fun s hs => level n s fun c => hL _ (L.smul_mem c ?_)
    exact hs
  have h2 : Module.finrank ℂ (L'.map (ext n)) = Module.finrank ℂ L' :=
    (Submodule.equivMapOfInjective (ext n) (ext_injective n) L').finrank_eq.symm
  have h3 : L'.map (ext n) = LinearMap.range (ext n) ⊓ L := Submodule.map_comap_eq _ _
  have h4 : Module.finrank ℂ (LinearMap.range (ext n)) = n * n := by
    rw [LinearMap.finrank_range_of_inj (ext_injective n), Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_fin]
  have h5 : Module.finrank ℂ ↥(LinearMap.range (ext n) ⊔ L) ≤ n * n + 2 * n + 1 := by
    calc Module.finrank ℂ ↥(LinearMap.range (ext n) ⊔ L)
        ≤ Module.finrank ℂ (Fin (n + 1) × Fin (n + 1) → ℂ) := Submodule.finrank_le _
      _ = n * n + 2 * n + 1 := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]; ring
  have h6 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (ext n)) L
  rw [← h3, h2, h4] at h6
  linarith

end PEqualNP.Gct.GReduction
