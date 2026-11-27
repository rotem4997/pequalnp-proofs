import Mathlib

/-! Helper module, proofs only. The injection form of the Minc coefficients of `perm (J + t)`
and the rank-one lemma.

For an `n × n` matrix `t` (a function `Fin n × Fin n → ℂ`) let `Mk n k t` be the sum over
`k`-subsets `S` of rows and `T` of columns of the permanent of `t[S, T]`. Then

* `injForm`: `k! * Mk n k t = ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a)`;
* `MkPol n k ts` is the `k`-linear form `∑ i, ∑ j, ∏ a, ts a (i a, j a)` (the full polarization
  of `Mk n k` times `k!`), with `MkPol_diag : MkPol n k (fun _ => t) = k! * Mk n k t`;
* `MkPol_rankOne`: on rank-one arguments `u a ⊗ w a` the form factors as `Inj u * Inj w`, with
  `Inj x = ∑ i : Fin k ↪ Fin n, ∏ a, x a (i a)`;
* `Mk_rankOne`: `Mk n k (x yᵀ) = k! * e_k(x) * e_k(y)`, with `e_k` the elementary symmetric
  polynomial written as a sum over `k`-subsets. -/

namespace PEqualNP.Gct.Helpers.RankOne

open Finset

/-- The `k`-subsets of `Fin n`. -/
abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The sum over `k`-subsets of rows and columns of the subpermanents of `t`. -/
noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : KSub n k, ∑ T : KSub n k,
    Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i,
      T.1.orderEmbOfFin T.2 j))

/-- The embedding `b ↦ S_(σ b)`, with `S_c` the `c`-th element of `S` in increasing order. -/
def emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun b => S.1.orderEmbOfFin S.2 (σ b), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

theorem range_emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) :
    Set.range (emb S σ) = (S.1 : Set (Fin n)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

/-- Every embedding `Fin k ↪ Fin n` is `emb S σ` for exactly one pair `(S, σ)`. -/
theorem emb_bijective (n k : ℕ) :
    Function.Bijective (fun p : KSub n k × Equiv.Perm (Fin k) => emb p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    simp only at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_emb S σ, ← range_emb T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub n k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin n)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]

/-- A sum over embeddings `Fin k ↪ Fin n` as a sum over `k`-subsets and permutations. -/
theorem sum_emb (n k : ℕ) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i, F i = ∑ S : KSub n k, ∑ σ : Equiv.Perm (Fin k), F (emb S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (emb_bijective n k) (fun p => F (emb p.1 p.2)) F
    (fun _ => rfl)).symm

/-- Summing over both a row permutation and a column permutation gives `k!` permanents. -/
theorem sum_perm_perm (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a)
      = (k.factorial : ℂ) * M.permanent := by
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin k),
      ∑ σ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a) = M.permanent := by
    intro τ
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, M (σ a) (τ a) = ∏ b, M ((σ * τ⁻¹) b) b := by
      intro σ
      exact Fintype.prod_equiv τ _ _ (fun a => by simp)
    simp_rw [h1]
    unfold Matrix.permanent
    exact Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ (fun _ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- The injection form of `Mk`. -/
theorem injForm (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    (k.factorial : ℂ) * Mk n k t
      = ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) := by
  rw [sum_emb n k]
  simp_rw [sum_emb n k (fun j => ∏ a, t (_, j a))]
  rw [Mk, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← sum_perm_perm]
  rfl

/-- The `k`-linear form whose diagonal is `k! * Mk n k` (`k!` times the full polarization). -/
noncomputable def MkPol (n k : ℕ) (ts : Fin k → Fin n × Fin n → ℂ) : ℂ :=
  ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, ts a (i a, j a)

theorem MkPol_diag (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    MkPol n k (fun _ => t) = (k.factorial : ℂ) * Mk n k t :=
  (injForm n k t).symm

/-- The sum over injective index maps: `Inj x = ∑ over distinct i_1..i_k of ∏ x_a (i_a)`. -/
noncomputable def Inj (n k : ℕ) (x : Fin k → Fin n → ℂ) : ℂ :=
  ∑ i : Fin k ↪ Fin n, ∏ a, x a (i a)

/-- The rank-one lemma. -/
theorem MkPol_rankOne (n k : ℕ) (u w : Fin k → Fin n → ℂ) :
    MkPol n k (fun a p => u a p.1 * w a p.2) = Inj n k u * Inj n k w := by
  simp only [MkPol, Inj, Finset.prod_mul_distrib, Finset.sum_mul_sum]

/-- `Inj` of `k` copies of one vector is `k!` times the elementary symmetric polynomial. -/
theorem Inj_const (n k : ℕ) (x : Fin n → ℂ) :
    Inj n k (fun _ => x) = (k.factorial : ℂ) * ∑ S : KSub n k, ∏ i ∈ S.1, x i := by
  rw [Inj, sum_emb n k, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have h1 : ∀ σ : Equiv.Perm (Fin k),
      ∏ a, x (emb S σ a) = ∏ i ∈ S.1, x i := by
    intro σ
    have h2 : ∏ a, x (emb S σ a) = ∏ b, x (S.1.orderEmbOfFin S.2 b) :=
      Fintype.prod_equiv σ _ _ (fun _ => rfl)
    rw [h2]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S.1 S.2, Finset.prod_map]
    rfl
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- The single-matrix corollary: `Mk n k (x yᵀ) = k! * e_k(x) * e_k(y)`. -/
theorem Mk_rankOne (n k : ℕ) (x y : Fin n → ℂ) :
    Mk n k (fun p => x p.1 * y p.2)
      = (k.factorial : ℂ) * (∑ S : KSub n k, ∏ i ∈ S.1, x i)
          * (∑ T : KSub n k, ∏ j ∈ T.1, y j) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h := MkPol_rankOne n k (fun _ => x) (fun _ => y)
  rw [MkPol_diag, Inj_const, Inj_const] at h
  apply mul_left_cancel₀ hk
  rw [h]
  ring

end PEqualNP.Gct.Helpers.RankOne
