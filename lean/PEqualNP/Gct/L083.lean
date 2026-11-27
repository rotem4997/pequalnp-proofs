import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Extension.Gradient

/-! L-gct-083, the first-order extension bound for level spaces (R2 of the L-gct-037 level-space
study). If `perm_n (J + ·)` is constant `n!` on a subspace `L`, then `dim L + dim W(L) ≤ n^2`,
where `W(L)` is the span of the vectors `G(t) q = perm_n (J + t + e_q) - perm_n (J + t)`,
`t ∈ L`. Since the permanent is affine in each variable, `G(t)` is the gradient at `J + t`
(`Helpers/Extension/Gradient.lean`), and the derivative of `s ↦ perm_n (J + t + s l)` at `0`
vanishes for `l ∈ L`, so `L` lies in the orthogonal of `W(L)` under the dot product. -/

open PEqualNP.Gct.Extension in
theorem PEqualNP.Gct.L083 : ∀ (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ L + Module.finrank ℂ (Submodule.span ℂ (Set.range fun t : L => fun q : Fin n × Fin n => MvPolynomial.eval (fun p => 1 + (t : Fin n × Fin n → ℂ) p + if p = q then 1 else 0) (PEqualNP.Gct.permPoly ℂ n) - MvPolynomial.eval (fun p => 1 + (t : Fin n × Fin n → ℂ) p) (PEqualNP.Gct.permPoly ℂ n))) ≤ n ^ 2 := by
  intro n L hL
  have horth : ∀ t : L, ∀ l ∈ L, ∑ q, (MvPolynomial.eval
      (fun p => 1 + (t : Fin n × Fin n → ℂ) p + if p = q then 1 else 0)
      (PEqualNP.Gct.permPoly ℂ n) - MvPolynomial.eval (fun p => 1 + (t : Fin n × Fin n → ℂ) p)
      (PEqualNP.Gct.permPoly ℂ n)) * l q = 0 := by
    intro t l hl
    have hG : ∀ q, MvPolynomial.eval
        (fun p => 1 + (t : Fin n × Fin n → ℂ) p + if p = q then 1 else 0)
        (PEqualNP.Gct.permPoly ℂ n) - MvPolynomial.eval (fun p => 1 + (t : Fin n × Fin n → ℂ) p)
        (PEqualNP.Gct.permPoly ℂ n) =
        D (fun p => 1 + (t : Fin n × Fin n → ℂ) p) (fun p => if p = q then 1 else 0) := by
      intro q
      rw [eval_perm, eval_perm]
      exact diff_eq_D (fun p => 1 + (t : Fin n × Fin n → ℂ) p) q
    simp only [hG]
    rw [sum_D_single]
    apply D_eq_zero _ _ (Nat.factorial n : ℂ)
    intro s
    have hmem : (t : Fin n × Fin n → ℂ) + s • l ∈ L := L.add_mem t.2 (L.smul_mem s hl)
    rw [← hL _ hmem, eval_perm]
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  set W := Submodule.span ℂ (Set.range fun t : L => fun q : Fin n × Fin n => MvPolynomial.eval
    (fun p => 1 + (t : Fin n × Fin n → ℂ) p + if p = q then 1 else 0) (PEqualNP.Gct.permPoly ℂ n) -
      MvPolynomial.eval (fun p => 1 + (t : Fin n × Fin n → ℂ) p) (PEqualNP.Gct.permPoly ℂ n))
  have hW : W.map (dotProductEquiv ℂ (Fin n × Fin n)).toLinearMap ≤ L.dualAnnihilator := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    intro l hl
    simpa [dotProduct] using horth t l hl
  have h1 := Submodule.finrank_mono hW
  rw [LinearEquiv.finrank_map_eq] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h2
  rw [sq]
  omega
