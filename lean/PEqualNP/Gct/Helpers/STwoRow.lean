import Mathlib

/-! Helper module, proofs only. Two-row isotropic spaces: a linear space of pairs of rows of
length `q ≥ 2` on which both the total entry sum and the off-diagonal row product
`∑_{j ≠ l} a_j b_l` vanish has dimension at most `q - 1`. The polar form of the off-diagonal
product is a nondegenerate symmetric bilinear form, the space is isotropic for it, and the all
ones vector lies in its orthogonal but not in the space. -/

namespace PEqualNP.Gct.Helpers.STwoRow

open Module

variable {q : ℕ}

/-- The off-diagonal row product. -/
def Q (t : Fin 2 × Fin q → ℂ) : ℂ := ∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)

/-- Row sums and the row dot product. -/
def sa (t : Fin 2 × Fin q → ℂ) : ℂ := ∑ j, t (0, j)
def sb (t : Fin 2 × Fin q → ℂ) : ℂ := ∑ j, t (1, j)

/-- The polar form, written in closed form. -/
def Bfun (t s : Fin 2 × Fin q → ℂ) : ℂ :=
  sa t * sb s + sa s * sb t - ∑ j, t (0, j) * s (1, j) - ∑ j, s (0, j) * t (1, j)

lemma Q_eq (t : Fin 2 × Fin q → ℂ) : Q t = sa t * sb t - ∑ j, t (0, j) * t (1, j) := by
  unfold Q sa sb
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ l, (if j = l then (0 : ℂ) else t (0, j) * t (1, l)) =
      t (0, j) * t (1, l) - if j = l then t (0, j) * t (1, l) else 0 := by
    intro l; split_ifs <;> simp
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma polar (t s : Fin 2 × Fin q → ℂ) : Q (t + s) - Q t - Q s = Bfun t s := by
  simp only [Q_eq, Bfun, sa, sb, Pi.add_apply, Finset.sum_add_distrib]
  have h : ∑ j, (t (0, j) + s (0, j)) * (t (1, j) + s (1, j)) =
      ∑ j, t (0, j) * t (1, j) + ∑ j, t (0, j) * s (1, j) + ∑ j, s (0, j) * t (1, j)
        + ∑ j, s (0, j) * s (1, j) := by
    simp only [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [h]; ring

/-- The polar form as a bilinear form. -/
def B : LinearMap.BilinForm ℂ (Fin 2 × Fin q → ℂ) :=
  LinearMap.mk₂ ℂ Bfun
    (by intro t t' s; simp only [Bfun, sa, sb, Pi.add_apply, Finset.sum_add_distrib, add_mul,
          mul_add]; ring)
    (by intro c t s; simp only [Bfun, sa, sb, Pi.smul_apply, smul_eq_mul, mul_assoc,
          mul_left_comm _ c, ← Finset.mul_sum]; ring)
    (by intro t s s'; simp only [Bfun, sa, sb, Pi.add_apply, Finset.sum_add_distrib, add_mul,
          mul_add]; ring)
    (by intro c t s; simp only [Bfun, sa, sb, Pi.smul_apply, smul_eq_mul, mul_assoc,
          mul_left_comm _ c, ← Finset.mul_sum]; ring)

lemma B_apply (t s : Fin 2 × Fin q → ℂ) : B t s = Bfun t s := rfl

lemma B_single1 (t : Fin 2 × Fin q → ℂ) (l : Fin q) :
    B t (Pi.single (1, l) 1) = sa t - t (0, l) := by
  rw [B_apply]
  simp [Bfun, sa, sb, Pi.single_apply, Prod.ext_iff]

lemma B_single0 (t : Fin 2 × Fin q → ℂ) (j : Fin q) :
    B t (Pi.single (0, j) 1) = sb t - t (1, j) := by
  rw [B_apply]
  simp [Bfun, sa, sb, Pi.single_apply, Prod.ext_iff]

lemma row_zero (hq : 2 ≤ q) (f : Fin q → ℂ) (h : ∀ l, ∑ j, f j - f l = 0) : f = 0 := by
  have hf : ∀ l, f l = ∑ j, f j := fun l => (sub_eq_zero.mp (h l)).symm
  have hs : ∑ j, f j = (q : ℂ) * ∑ j, f j := by
    conv_lhs => rw [Finset.sum_congr rfl fun l _ => hf l]
    simp
  have hq' : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (by omega : q ≠ 1)
  have h0 : ∑ j, f j = 0 := by
    have : ((q : ℂ) - 1) * ∑ j, f j = 0 := by rw [sub_mul, ← hs]; ring
    exact (mul_eq_zero.mp this).resolve_left hq'
  funext l; rw [hf l, h0]; rfl

lemma B_symm (t s : Fin 2 × Fin q → ℂ) : B t s = B s t := by
  rw [B_apply, B_apply]; unfold Bfun; ring

lemma B_sep (hq : 2 ≤ q) (t : Fin 2 × Fin q → ℂ) (ht : ∀ s, B t s = 0) : t = 0 := by
  have ha := row_zero hq (fun j => t (0, j)) fun l => by
    have := ht (Pi.single (1, l) 1); rwa [B_single1] at this
  have hb := row_zero hq (fun j => t (1, j)) fun l => by
    have := ht (Pi.single (0, l) 1); rwa [B_single0] at this
  funext ⟨i, j⟩
  fin_cases i
  · exact congrFun ha j
  · exact congrFun hb j

lemma B_nondeg (hq : 2 ≤ q) : (B (q := q)).Nondegenerate :=
  ⟨fun t ht => B_sep hq t ht, fun s hs => B_sep hq s fun t => by rw [B_symm]; exact hs t⟩

lemma B_ones (t : Fin 2 × Fin q → ℂ) :
    B t (fun _ => 1) = ((q : ℂ) - 1) * ∑ j, (t (0, j) + t (1, j)) := by
  rw [B_apply]
  simp only [Bfun, sa, sb, Finset.sum_add_distrib, mul_one, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem main : ∀ (q : ℕ) (L : Submodule ℂ (Fin 2 × Fin q → ℂ)), 2 ≤ q →
    (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧
      (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) →
    Module.finrank ℂ L + 1 ≤ q := by
  intro q L hq hL
  set v : Fin 2 × Fin q → ℂ := fun _ => 1
  have hQ : ∀ t ∈ L, Q t = 0 := fun t ht => (hL t ht).2
  have hiso : ∀ t ∈ L, ∀ s ∈ L, B t s = 0 := by
    intro t ht s hs
    rw [B_apply, ← polar, hQ _ (L.add_mem ht hs), hQ t ht, hQ s hs]; simp
  have hv : v ∉ L := by
    intro h
    have := (hL v h).1
    simp only [v, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have h2 : (q : ℂ) * (1 + 1) = 0 := this
    norm_num at h2
    omega
  have hle : L ⊔ Submodule.span ℂ {v} ≤ B.orthogonal L := by
    rw [sup_le_iff]
    constructor
    · intro s hs
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro t ht
      exact hiso t ht s hs
    · rw [Submodule.span_le]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro t ht
      show B t v = 0
      rw [B_ones, (hL t ht).1, mul_zero]
  have hlt : L < L ⊔ Submodule.span ℂ {v} := by
    refine lt_of_le_of_ne le_sup_left fun h => hv ?_
    rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (B_nondeg hq), Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h2
  omega

end PEqualNP.Gct.Helpers.STwoRow
