import PEqualNP.Gct.Helpers.LS4.OddPart

/-! Helper for L-gct-091 (LS(4) <= 5), the `r <= 1` gluing step for a two-column and a
two-row space. `twoRow w v` has rows `w, v, 0, 0`. With `A = twoCol y z`, `R = twoRow w v`
and all of `y, z, w, v` of sum zero, the four-sign combination of `perm (J ± A ± R)` is
`8 (w 0 * y 0 + w 1 * z 0 + v 0 * y 1 + v 1 * z 1)` (the polar of the quadratic part at `J`;
cubic terms cancel since `R` has two rows). A level space containing `A` and `R` makes that form
vanish. For the skew two-column spaces `{twoCol y (K y)}` (`K = Kf a b e`, the general skew
`4 x 4` matrix with zero row sums) and the transposed two-row spaces `{twoRow w (K' w)}`, the form
cannot vanish identically, so no level space contains both. -/

namespace PEqualNP.Gct.LS4

open Finset Matrix

/-- Rows `w, v, 0, 0`. -/
def twoRow (w v : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.1 = 0 then w p.2 else if p.1 = 1 then v p.2 else 0

theorem fourSign_twoCol_twoRow (y z w v : Fin 4 → ℂ) (hy : ∑ i, y i = 0)
    (hz : ∑ i, z i = 0) (hw : ∑ j, w j = 0) (hv : ∑ j, v j = 0) :
    MvPolynomial.eval (fun p => 1 + (twoCol y z p + twoRow w v p)) (PEqualNP.Gct.permPoly ℂ 4) -
      MvPolynomial.eval (fun p => 1 + (-twoCol y z p + twoRow w v p))
        (PEqualNP.Gct.permPoly ℂ 4) -
      MvPolynomial.eval (fun p => 1 + (twoCol y z p + -twoRow w v p))
        (PEqualNP.Gct.permPoly ℂ 4) +
      MvPolynomial.eval (fun p => 1 + (-twoCol y z p + -twoRow w v p))
        (PEqualNP.Gct.permPoly ℂ 4) =
      8 * (w 0 * y 0 + w 1 * z 0 + v 0 * y 1 + v 1 * z 1) := by
  rw [Fin.sum_univ_four] at hy hz hw hv
  have hy3 : y 3 = -(y 0 + y 1 + y 2) := by linear_combination hy
  have hz3 : z 3 = -(z 0 + z 1 + z 2) := by linear_combination hz
  have hw3 : w 3 = -(w 0 + w 1 + w 2) := by linear_combination hw
  have hv3 : v 3 = -(v 0 + v 1 + v 2) := by linear_combination hv
  rw [eval_perm_four, eval_perm_four, eval_perm_four, eval_perm_four]
  simp [twoCol, twoRow, hy3, hz3, hw3, hv3]
  ring

theorem level_twoCol_twoRow (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (y z w v : Fin 4 → ℂ) (hy : ∑ i, y i = 0) (hz : ∑ i, z i = 0) (hw : ∑ j, w j = 0)
    (hv : ∑ j, v j = 0) (hA : twoCol y z ∈ L) (hR : twoRow w v ∈ L) :
    w 0 * y 0 + w 1 * z 0 + v 0 * y 1 + v 1 * z 1 = 0 := by
  have h1 := hL _ (L.add_mem hA hR)
  have h2 := hL _ (L.add_mem (L.neg_mem hA) hR)
  have h3 := hL _ (L.add_mem hA (L.neg_mem hR))
  have h4 := hL _ (L.add_mem (L.neg_mem hA) (L.neg_mem hR))
  have h := fourSign_twoCol_twoRow y z w v hy hz hw hv
  simp only [Pi.add_apply, Pi.neg_apply] at h1 h2 h3 h4
  rw [h1, h2, h3, h4] at h
  linear_combination -h / 8

/-- The general skew `4 x 4` matrix with zero row sums (three parameters). -/
def Kf (a b e : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, a, b, -a - b; -a, 0, e, a - e; -b, -e, 0, b + e; a + b, -a + e, -b - e, 0]

/-- Every skew matrix with zero row sums is some `Kf a b e`. -/
theorem eq_Kf (K : Matrix (Fin 4) (Fin 4) ℂ) (hs : ∀ i j, K i j = -K j i)
    (hr : ∀ i, ∑ j, K i j = 0) : K = Kf (K 0 1) (K 0 2) (K 1 2) := by
  have hd : ∀ i, K i i = 0 := fun i => by have := hs i i; linear_combination this / 2
  have r0 := hr 0; have r1 := hr 1; have r2 := hr 2; have r3 := hr 3
  simp only [Fin.sum_univ_four] at r0 r1 r2 r3
  have h03 : K 0 3 = -K 0 1 - K 0 2 := by linear_combination r0 - hd 0
  have h13 : K 1 3 = K 0 1 - K 1 2 := by linear_combination r1 - hd 1 - hs 0 1
  have h23 : K 2 3 = K 0 2 + K 1 2 := by linear_combination r2 - hd 2 - hs 0 2 - hs 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kf, hd, h03, h13, h23, hs 1 0, hs 2 0, hs 2 1, hs 3 0, hs 3 1, hs 3 2] <;> ring

theorem sum_Kf_mulVec (a b e : ℂ) (y : Fin 4 → ℂ) : ∑ i, (Kf a b e *ᵥ y) i = 0 := by
  simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- Non-vacuity: each skew two-column space `{twoCol y (Kf a b e *ᵥ y)}` is level. -/
theorem twoCol_Kf_level (a b e : ℂ) (y : Fin 4 → ℂ) (hy : ∑ i, y i = 0) :
    MvPolynomial.eval (fun p => 1 + twoCol y (Kf a b e *ᵥ y) p) (PEqualNP.Gct.permPoly ℂ 4) =
      24 := by
  have h := twoCol_level y (Kf a b e *ᵥ y) hy (sum_Kf_mulVec a b e y)
  have h0 : ∑ i, y i * (Kf a b e *ᵥ y) i = 0 := by
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  rw [h0] at h
  linear_combination h

/-- Gluing: no level space contains a skew two-column space on columns `0, 1` and a skew
two-row space on rows `0, 1`. -/
theorem no_glue_twoCol_twoRow (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (a b e a2 b2 e2 : ℂ)
    (hC : ∀ y : Fin 4 → ℂ, ∑ i, y i = 0 → twoCol y (Kf a b e *ᵥ y) ∈ L)
    (hR : ∀ w : Fin 4 → ℂ, ∑ j, w j = 0 → twoRow w (Kf a2 b2 e2 *ᵥ w) ∈ L) : False := by
  have key : ∀ y w : Fin 4 → ℂ, ∑ i, y i = 0 → ∑ j, w j = 0 →
      w 0 * y 0 + w 1 * (Kf a b e *ᵥ y) 0 + (Kf a2 b2 e2 *ᵥ w) 0 * y 1 +
        (Kf a2 b2 e2 *ᵥ w) 1 * (Kf a b e *ᵥ y) 1 = 0 := fun y w hy hw =>
    level_twoCol_twoRow L hL y _ w _ hy (sum_Kf_mulVec a b e y) hw (sum_Kf_mulVec a2 b2 e2 w)
      (hC y hy) (hR w hw)
  have s0 : ∑ i, (![1, 0, 0, -1] : Fin 4 → ℂ) i = 0 := by simp [Fin.sum_univ_four]
  have s1 : ∑ i, (![0, 1, 0, -1] : Fin 4 → ℂ) i = 0 := by simp [Fin.sum_univ_four]
  have s2 : ∑ i, (![0, 0, 1, -1] : Fin 4 → ℂ) i = 0 := by simp [Fin.sum_univ_four]
  have c00 : 4*a*a2 - 2*a*e2 - 2*a2*e + e*e2 + 1 = 0 := by
    have := key _ _ s0 s0
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c01 : 2*a*a2 - 2*a*e2 + a - a2*e + b + e*e2 = 0 := by
    have := key _ _ s0 s1
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c02 : 2*a*a2 - 4*a*e2 - a2*e + 2*e*e2 = 0 := by
    have := key _ _ s0 s2
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c10 : 2*a*a2 - a*e2 - 2*a2*e + a2 + b2 + e*e2 = 0 := by
    have := key _ _ s1 s0
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c12 : a*a2 - 2*a*e2 - a2*e + a2 + 2*b2 + 2*e*e2 = 0 := by
    have := key _ _ s1 s2
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c20 : 2*a*a2 - a*e2 - 4*a2*e + 2*e*e2 = 0 := by
    have := key _ _ s2 s0
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have c21 : a*a2 - a*e2 + a - 2*a2*e + 2*b + 2*e*e2 = 0 := by
    have := key _ _ s2 s1
    simp [Kf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero] at this
    linear_combination this
  have hY2 : a2 = 2 * e2 := by linear_combination (a2 - 2*e2) * c00 - (2*a2 - e2) * c02
  have hX2 : a = 2 * e := by linear_combination (a - 2*e) * c00 - (2*a - e) * c20
  subst hY2 hX2
  have he : e = 1/3 := by linear_combination c01 - c21 / 2 - c00 / 3
  have he2 : e2 = 1/3 := by linear_combination c10 - c12 / 2 - c00 / 3
  rw [he, he2] at c00
  norm_num at c00

end PEqualNP.Gct.LS4
