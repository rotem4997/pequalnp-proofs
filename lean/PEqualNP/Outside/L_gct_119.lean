import Mathlib
import PEqualNP.Defs

open Finset in
theorem PEqualNP.Outside.L_gct_119 : ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (z : ℂ) (t : Fin n × Fin n → ℂ), (∀ k : ℕ, 1 ≤ k → k ≤ n → z ^ k ≠ 1) → (∀ i j : Fin n, t (σ i, τ j) = z * t (i, j)) → MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  intro n σ τ z t hz ht
  classical
  -- `G k` collects the terms of the expansion with exactly `k` factors from `t`.
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℂ, G = fun k => ∑ π : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
      if S.card = k then ∏ c ∈ S, t (π c, c) else 0 := ⟨_, rfl⟩
  -- Expand the permanent of `1 + t` over subsets.
  have heval : MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ π : Equiv.Perm (Fin n), ∑ S : Finset (Fin n), ∏ c ∈ S, t (π c, c) := by
    simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum,
      map_prod, MvPolynomial.eval_X]
    refine sum_congr rfl fun π _ => ?_
    rw [prod_one_add, powerset_univ]
  -- Group the subsets by their size.
  have hsplit : ∑ k ∈ range (n + 1), G k =
      ∑ π : Equiv.Perm (Fin n), ∑ S : Finset (Fin n), ∏ c ∈ S, t (π c, c) := by
    rw [hG]
    rw [sum_comm]
    refine sum_congr rfl fun π _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S _ => ?_
    rw [sum_ite_eq]
    have hS : S.card ∈ range (n + 1) := by
      rw [mem_range]
      have := card_le_univ S
      rw [Fintype.card_fin] at this
      omega
    simp only [hS, ↓reduceIte]
  -- Relabelling by `σ` and `τ` multiplies `G k` by `z ^ k`.
  have hsym : ∀ k, G k = z ^ k * G k := by
    intro k
    rw [hG]
    dsimp only
    let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
      (Equiv.mulLeft σ).trans (Equiv.mulRight τ⁻¹)
    conv_lhs => rw [← Equiv.sum_comp e]
    rw [mul_sum]
    refine sum_congr rfl fun ρ _ => ?_
    rw [← Equiv.sum_comp (Equiv.finsetCongr τ), mul_sum]
    refine sum_congr rfl fun S _ => ?_
    simp only [Equiv.finsetCongr_apply, card_map, mul_ite, mul_zero]
    split_ifs with h
    · rw [prod_map]
      have hterm : ∀ d ∈ S, t ((e ρ) (τ.toEmbedding d), τ.toEmbedding d) = z * t (ρ d, d) := by
        intro d _
        simp only [e, Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight,
          Equiv.Perm.mul_apply, Equiv.coe_toEmbedding]
        simpa using ht (ρ d) d
      rw [prod_congr rfl hterm, prod_mul_distrib, prod_const, h]
    · rfl
  -- Only the term with no factor from `t` survives.
  have hzero : ∀ k ∈ range (n + 1), k ≠ 0 → G k = 0 := by
    intro k hk hk0
    rw [mem_range] at hk
    have hzk : z ^ k ≠ 1 := hz k (by omega) (by omega)
    have hmul : (1 - z ^ k) * G k = 0 := by linear_combination hsym k
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h).symm hzk
    · exact h
  have hG0 : G 0 = (Nat.factorial n : ℂ) := by
    rw [hG]
    simp only [card_eq_zero, sum_ite_eq', mem_univ, ↓reduceIte, prod_empty, sum_const, card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [heval, ← hsplit, sum_eq_single 0 hzero (fun h => absurd (by simp) h), hG0]
