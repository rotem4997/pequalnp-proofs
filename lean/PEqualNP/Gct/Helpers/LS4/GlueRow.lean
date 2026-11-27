import PEqualNP.Gct.Helpers.LS4.OddPart
import PEqualNP.Gct.Helpers.LS4.Symmetry

/-! Helper for L-gct-091 (LS(4) <= 5). `no_glue_oneRow` for an arbitrary row `r` and an
arbitrary pair of distinct columns `c0, c1`: reduced to columns `0, 1` by the column symmetry
of `Symmetry.lean`. -/

namespace PEqualNP.Gct.LS4

open Finset

/-- Columns `c0, c1` equal to `y, z`, zero elsewhere. -/
def colPair (c0 c1 : Fin 4) (y z : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.2 = c0 then y p.1 else if p.2 = c1 then z p.1 else 0

theorem exists_perm_pair (c0 c1 : Fin 4) (h : c0 ≠ c1) :
    ∃ τ : Equiv.Perm (Fin 4), τ 0 = c0 ∧ τ 1 = c1 := by
  set d := Equiv.swap 0 c0 c1 with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply h
    have := congrArg (Equiv.swap 0 c0) h0
    rw [hd, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  refine ⟨Equiv.swap 0 c0 * Equiv.swap 1 d, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd0.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hd, Equiv.swap_apply_self]

/-- Gluing at any row `r` and any two distinct columns `c0, c1`: a level space containing the
whole one-row space at row `r` contains no `colPair c0 c1 y z` (sums zero) with `y r ≠ 0`. -/
theorem no_glue_oneRow_any (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (r c0 c1 : Fin 4) (hc : c0 ≠ c1)
    (hrow : ∀ w : Fin 4 → ℂ, ∑ j, w j = 0 → oneRow r w ∈ L)
    (y z : Fin 4 → ℂ) (hy : ∑ i, y i = 0) (hz : ∑ i, z i = 0) (hA : colPair c0 c1 y z ∈ L) :
    y r = 0 := by
  obtain ⟨τ, h0, h1⟩ := exists_perm_pair c0 c1 hc
  subst h0 h1
  let e : Fin 4 × Fin 4 ≃ Fin 4 × Fin 4 := Equiv.prodCongr (Equiv.refl _) τ
  have hf : ((Nat.factorial 4 : ℕ) : ℂ) = 24 := by norm_num [Nat.factorial]
  have hlev := (map_level e (permInvariant_rowCol 1 τ) L
    (fun t ht => by rw [hf]; exact hL t ht)).1
  refine no_glue_oneRow (L.map (reindex e).toLinearMap)
    (fun t ht => by rw [← hf]; exact hlev t ht) r ?_ y z hy hz ?_
  · intro w hw
    have hw' : ∑ j, w (τ.symm j) = 0 := by rw [τ.symm.sum_comp]; exact hw
    have hm := Submodule.mem_map_of_mem (f := (reindex e).toLinearMap) (hrow _ hw')
    convert hm using 1
    funext p
    simp [oneRow, e, LinearEquiv.funCongrLeft_apply]
  · have hm := Submodule.mem_map_of_mem (f := (reindex e).toLinearMap) hA
    convert hm using 1
    funext p
    simp [twoCol, colPair, e, LinearEquiv.funCongrLeft_apply]

end PEqualNP.Gct.LS4
