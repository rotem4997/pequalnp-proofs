import PEqualNP.Gct.Helpers.LS4.TwoTwo
import PEqualNP.Gct.Helpers.LS4.GlueRow

/-! Helper for L-gct-091 (LS(4) <= 5). `no_glue_twoCol_twoRow` for arbitrary distinct columns
`c0, c1`, arbitrary distinct rows `r0, r1`, and arbitrary skew `4 x 4` matrices `K, K2` with
zero row sums, reduced to rows and columns `0, 1` by the symmetry of `Symmetry.lean` (the
matrices are conjugated by the permutations, which keeps them skew with zero row sums). -/

namespace PEqualNP.Gct.LS4

open Finset Matrix

/-- Rows `r0, r1` equal to `w, v`, zero elsewhere. -/
def rowPair (r0 r1 : Fin 4) (w v : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.1 = r0 then w p.2 else if p.1 = r1 then v p.2 else 0

theorem mulVec_perm (K : Matrix (Fin 4) (Fin 4) ℂ) (ρ : Equiv.Perm (Fin 4)) (y : Fin 4 → ℂ)
    (i : Fin 4) : (K *ᵥ (fun j => y (ρ.symm j))) (ρ i) =
      ((fun a b => K (ρ a) (ρ b) : Matrix (Fin 4) (Fin 4) ℂ) *ᵥ y) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp ρ (fun j => K (ρ i) j * y (ρ.symm j))]
  simp

/-- Columns and rows `0, 1`, general skew `K, K2` with zero row sums. -/
theorem no_glue_twoCol_twoRow_K (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (K K2 : Matrix (Fin 4) (Fin 4) ℂ) (hs : ∀ i j, K i j = -K j i) (hr : ∀ i, ∑ j, K i j = 0)
    (hs2 : ∀ i j, K2 i j = -K2 j i) (hr2 : ∀ i, ∑ j, K2 i j = 0)
    (hC : ∀ y : Fin 4 → ℂ, ∑ i, y i = 0 → twoCol y (K *ᵥ y) ∈ L)
    (hR : ∀ w : Fin 4 → ℂ, ∑ j, w j = 0 → twoRow w (K2 *ᵥ w) ∈ L) : False := by
  rw [eq_Kf K hs hr] at hC
  rw [eq_Kf K2 hs2 hr2] at hR
  exact no_glue_twoCol_twoRow L hL _ _ _ _ _ _ hC hR

/-- Gluing at any two distinct columns and any two distinct rows: no level space contains a
skew two-column space on columns `c0, c1` and a skew two-row space on rows `r0, r1`. -/
theorem no_glue_twoCol_twoRow_any (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (c0 c1 r0 r1 : Fin 4) (hc : c0 ≠ c1) (hr01 : r0 ≠ r1)
    (K K2 : Matrix (Fin 4) (Fin 4) ℂ) (hs : ∀ i j, K i j = -K j i) (hr : ∀ i, ∑ j, K i j = 0)
    (hs2 : ∀ i j, K2 i j = -K2 j i) (hr2 : ∀ i, ∑ j, K2 i j = 0)
    (hC : ∀ y : Fin 4 → ℂ, ∑ i, y i = 0 → colPair c0 c1 y (K *ᵥ y) ∈ L)
    (hR : ∀ w : Fin 4 → ℂ, ∑ j, w j = 0 → rowPair r0 r1 w (K2 *ᵥ w) ∈ L) : False := by
  obtain ⟨τ, h0, h1⟩ := exists_perm_pair c0 c1 hc
  obtain ⟨ρ, g0, g1⟩ := exists_perm_pair r0 r1 hr01
  subst h0 h1 g0 g1
  let e : Fin 4 × Fin 4 ≃ Fin 4 × Fin 4 := Equiv.prodCongr ρ τ
  have hf : ((Nat.factorial 4 : ℕ) : ℂ) = 24 := by norm_num [Nat.factorial]
  have hlev := (map_level e (permInvariant_rowCol ρ τ) L
    (fun t ht => by rw [hf]; exact hL t ht)).1
  refine no_glue_twoCol_twoRow_K (L.map (reindex e).toLinearMap)
    (fun t ht => by rw [← hf]; exact hlev t ht)
    (fun a b => K (ρ a) (ρ b)) (fun a b => K2 (τ a) (τ b))
    (fun i j => hs _ _) (fun i => by rw [Equiv.sum_comp ρ (fun j => K (ρ i) j)]; exact hr _)
    (fun i j => hs2 _ _) (fun i => by rw [Equiv.sum_comp τ (fun j => K2 (τ i) j)]; exact hr2 _)
    ?_ ?_
  · intro y hy
    have hy' : ∑ j, y (ρ.symm j) = 0 := by rw [ρ.symm.sum_comp]; exact hy
    have hm := Submodule.mem_map_of_mem (f := (reindex e).toLinearMap) (hC _ hy')
    convert hm using 1
    funext p
    simp only [twoCol, colPair, e, LinearEquiv.funCongrLeft_apply, LinearEquiv.coe_coe,
      LinearMap.funLeft_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      EmbeddingLike.apply_eq_iff_eq, mulVec_perm]
    simp
  · intro w hw
    have hw' : ∑ j, w (τ.symm j) = 0 := by rw [τ.symm.sum_comp]; exact hw
    have hm := Submodule.mem_map_of_mem (f := (reindex e).toLinearMap) (hR _ hw')
    convert hm using 1
    funext p
    simp only [twoRow, rowPair, e, LinearEquiv.funCongrLeft_apply, LinearEquiv.coe_coe,
      LinearMap.funLeft_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      EmbeddingLike.apply_eq_iff_eq, mulVec_perm]
    simp

end PEqualNP.Gct.LS4
