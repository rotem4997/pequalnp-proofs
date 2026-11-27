import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10024_aux
open Finset
open scoped BigOperators

def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def inc (p : Fin 25) (l : Fin 30) : Bool := (rows.getD p.val 0).testBit l.val
def I (p : Fin 25) (l : Fin 30) : ℤ := if inc p l then 1 else 0
def cls (l : Fin 30) : Fin 6 := ⟨l.val / 5, by omega⟩

set_option maxRecDepth 20000 in
theorem row_sum : ∀ p, ∑ l, I p l = 6 := by decide +kernel
set_option maxRecDepth 20000 in
theorem row_pair : ∀ p q, ∑ l, I p l * I q l = if p = q then 6 else 1 := by decide +kernel
set_option maxRecDepth 20000 in
theorem col_sum : ∀ l, ∑ p, I p l = 5 := by decide +kernel
set_option maxRecDepth 20000 in
theorem col_pair : ∀ l m, ∑ p, I p l * I p m = if l = m then 5 else if cls l = cls m then 0 else 1 := by decide +kernel
set_option maxRecDepth 20000 in
theorem cls_sum : ∀ p c, ∑ l with cls l = c, I p l = 1 := by decide +kernel

abbrev E := EuclideanSpace ℝ (Fin 25)
noncomputable def basisVector (j : Fin 25) : E := EuclideanSpace.basisFun (Fin 25) ℝ j
theorem basis_apply (j k : Fin 25) : basisVector j k = if k = j then 1 else 0 := by
  simp [basisVector, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

theorem trace_reflect (K : Submodule ℝ E) :
    ∑ j : Fin 25, (K.reflection (basisVector j)) j = 2 * (Module.finrank ℝ K : ℝ) - 25 := by
  classical
  let P := K.orthogonalProjectionOnto.toLinearMap
  have comp : P.comp K.subtype = LinearMap.id := by
    ext x
    simp [P]
  have fe : K.reflection.toLinearEquiv.toLinearMap = (2:ℝ) • (K.subtype.comp P) - LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (2 : ℕ) • K.starProjection x - x = (2 : ℝ) • (K.orthogonalProjectionOnto x : E) - x
    rw [two_smul, two_smul]
    rfl
  have tr := LinearMap.trace_comp_comm' P K.subtype
  rw [comp, LinearMap.trace_id] at tr
  have diagon : ∀ (f : E →ₗ[ℝ] E), (∑ j : Fin 25, (f (basisVector j)) j) = LinearMap.trace ℝ E f := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 25) ℝ).toBasis]
    simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, basisVector]
  change (∑ j : Fin 25, (K.reflection.toLinearEquiv.toLinearMap (basisVector j)) j) = _
  rw [diagon K.reflection.toLinearEquiv.toLinearMap, fe]
  simp [tr, LinearMap.trace_id]

theorem refl_inner (K : Submodule ℝ E) (x y : E) :
    inner ℝ (K.reflection x) y = inner ℝ x (K.reflection y) := by
  rw [← K.reflection.inner_map_map x (K.reflection y)]
  simp

theorem inner_sum_apply (x y : E) : inner ℝ x y = ∑ j, x j * y j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

noncomputable def q (l : Fin 30) : E := WithLp.toLp 2 (fun p => ((1 - 4 * I p l : ℤ) : ℝ))
theorem q_apply (l : Fin 30) (p : Fin 25) : q l p = ((1 - 4 * I p l : ℤ) : ℝ) := rfl

theorem q_inner (l m : Fin 30) : inner ℝ (q l) (q m) = (((-15 + 16 * (∑ p, I p l * I p m)) : ℤ) : ℝ) := by
  rw [inner_sum_apply]
  simp only [q_apply]
  have h : (∑ p, (1 - 4 * I p l) * (1 - 4 * I p m)) = -15 + 16 * (∑ p, I p l * I p m) := by
    have e : ∀ p, (1 - 4 * I p l) * (1 - 4 * I p m) = 1 - 4 * I p l - 4 * I p m + 16 * (I p l * I p m) := fun p => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, col_sum]
    simp
  rw [← h]; push_cast; rfl

theorem q_self (l : Fin 30) : inner ℝ (q l) (q l) = 65 := by
  rw [q_inner, col_pair]; norm_num
theorem q_cross (l m : Fin 30) (h : l ≠ m) : inner ℝ (q l) (q m) ≤ 1 := by
  rw [q_inner, col_pair, if_neg h]; split <;> norm_num

theorem norm_y (n : Fin 30 → ℕ) :
    ‖∑ l, (n l : ℝ) • q l‖ ^ 2 ≤ 64 * (∑ l, (n l : ℝ) ^ 2) + (∑ l, (n l : ℝ)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  have step : ∀ l, inner ℝ ((n l : ℝ) • q l) (∑ m, (n m : ℝ) • q m) ≤
      (n l : ℝ) * (∑ m, (n m : ℝ)) + 64 * (n l : ℝ) ^ 2 := by
    intro l
    rw [inner_sum]
    have t : ∀ m, inner ℝ ((n l : ℝ) • q l) ((n m : ℝ) • q m) ≤
        (n l : ℝ) * (n m : ℝ) + if l = m then 64 * (n l : ℝ) ^ 2 else 0 := by
      intro m
      rw [real_inner_smul_left, real_inner_smul_right]
      by_cases h : l = m
      · subst h; rw [q_self, if_pos rfl]; nlinarith
      · rw [if_neg h, add_zero]
        have := q_cross l m h
        have h1 : (0:ℝ) ≤ (n l : ℝ) * (n m : ℝ) := by positivity
        nlinarith
    calc _ ≤ ∑ m, ((n l : ℝ) * (n m : ℝ) + if l = m then 64 * (n l : ℝ) ^ 2 else 0) := sum_le_sum fun m _ => t m
      _ = _ := by simp [sum_add_distrib, mul_sum]
  calc _ ≤ ∑ l, ((n l : ℝ) * (∑ m, (n m : ℝ)) + 64 * (n l : ℝ) ^ 2) := sum_le_sum fun l _ => step l
    _ = _ := by rw [sum_add_distrib, ← sum_mul, ← mul_sum]; ring

noncomputable def one (B : Finset (Fin 25)) : E := WithLp.toLp 2 (fun p => if p ∈ B then (1:ℝ) else 0)
theorem one_inner (B : Finset (Fin 25)) (x : E) : inner ℝ x (one B) = ∑ p ∈ B, x p := by
  rw [inner_sum_apply]
  simp [one]

theorem zero_column (j : Fin 25) : ∑ l, ((1 - I j l : ℤ) : ℝ) • q l = (20:ℝ) • basisVector j + (4:ℝ) • one univ := by
  ext k
  have h : (∑ l, (1 - I j l) * (1 - 4 * I k l)) = 20 * (if k = j then 1 else 0) + 4 := by
    have e : ∀ l, (1 - I j l) * (1 - 4 * I k l) = 1 - I j l - 4 * I k l + 4 * (I j l * I k l) := fun l => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, row_sum, row_pair]
    by_cases hk : k = j
    · subst hk; simp
    · have : ¬ j = k := fun h => hk h.symm
      simp [hk, this]
  have h' : (∑ l, ((1 - I j l : ℤ) : ℝ) * ((1 - 4 * I k l : ℤ) : ℝ)) = 20 * (if k = j then 1 else 0) + 4 := by
    exact_mod_cast h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basis_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simpa [one, q_apply] using h'

abbrev Box := Finset (Fin 25) × Finset (Fin 30)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def nn {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ := cov R p l - 1

theorem swap_sum {k : ℕ} (R : Fin k → Box) (f : Fin 25 → Fin 30 → ℝ) :
    ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, f p l = ∑ p, ∑ l, (cov R p l : ℝ) * f p l := by
  have c : ∀ p l, (cov R p l : ℝ) * f p l = ∑ t, if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0 := by
    intro p l
    rw [cov, card_filter]; push_cast; rw [sum_mul]
    exact sum_congr rfl fun t _ => by split <;> simp
  simp only [c]
  have r : ∀ p, ∑ l, ∑ t, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) =
      ∑ t, ∑ l, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) := fun p => sum_comm
  simp only [r]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have z : ∀ l, ∑ p, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) =
      if l ∈ (R t).2 then ∑ p ∈ (R t).1, f p l else 0 := by
    intro l
    by_cases h : l ∈ (R t).2
    · simp [h]
    · simp [h]
  calc _ = ∑ l, (if l ∈ (R t).2 then ∑ p ∈ (R t).1, f p l else 0) := by simp
    _ = ∑ l, ∑ p, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) := by simp only [z]
    _ = _ := sum_comm

theorem cov_split {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (covers : ∀ p l, inc p l = false → 0 < cov R p l) (p : Fin 25) (l : Fin 30) :
    (cov R p l : ℤ) = (nn R p l : ℤ) + (1 - I p l) := by
  unfold nn I
  by_cases h : inc p l = true
  · have : cov R p l = 0 := by
      rw [cov, card_eq_zero, filter_eq_empty_iff]
      rintro t - ⟨h1, h2⟩
      have := good t p h1 l h2
      rw [h] at this; exact absurd this (by simp)
    simp [this, h]
  · have h' : inc p l = false := by simpa using h
    have := covers p l h'
    simp [h']; omega

theorem spectral {k : ℕ} (hk : k ≤ 13) (R : Fin k → Box) (good : ∀ t, Good (R t))
    (covers : ∀ p l, inc p l = false → 0 < cov R p l) :
    ∃ W : Fin 30 → Fin 25 → ℝ,
      480 + ∑ p, ∑ l, (nn R p l : ℝ) ≤ ∑ p, ∑ l, (nn R p l : ℝ) * W l p ∧
      (∀ p, (∑ l, (nn R p l : ℝ) * W l p) ^ 2 ≤
        64 * (∑ l, (nn R p l : ℝ) ^ 2) + (∑ l, (nn R p l : ℝ)) ^ 2) ∧
      (∀ l, (∑ p, (nn R p l : ℝ) * W l p) ^ 2 ≤ 65 * ∑ p, (nn R p l : ℝ) ^ 2) := by
  classical
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range fun t => one (R t).1)
  have dim : Module.finrank ℝ K ≤ 13 := by
    have := finrank_range_le_card (R := ℝ) (fun t => one (R t).1)
    simp only [Fintype.card_fin] at this
    exact le_trans this hk
  let W : Fin 30 → Fin 25 → ℝ := fun l p => (K.reflection (q l)) p
  have Wdef : ∀ l p, W l p = (K.reflection (q l)) p := fun _ _ => rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · have charge : ∀ t, ∀ l ∈ (R t).2, ∑ p ∈ (R t).1, W l p = ((R t).1.card : ℝ) := by
      intro t l hl
      have m : one (R t).1 ∈ K := Submodule.subset_span ⟨t, rfl⟩
      have e := one_inner (R t).1 (K.reflection (q l))
      rw [refl_inner, K.reflection_mem_subspace_eq_self m, one_inner] at e
      simp only [Wdef]
      rw [← e]
      have : ∀ p ∈ (R t).1, q l p = 1 := by
        intro p hp
        have := good t p hp l hl
        simp [q_apply, I, this]
      rw [sum_congr rfl this]; simp
    have tot : ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, W l p = ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, (1:ℝ) := by
      refine sum_congr rfl fun t _ => sum_congr rfl fun l hl => ?_
      rw [charge t l hl]; simp
    rw [swap_sum R (fun p l => W l p), swap_sum R (fun _ _ => 1)] at tot
    have split : ∀ p l, (cov R p l : ℝ) = (nn R p l : ℝ) + ((1 - I p l : ℤ) : ℝ) := by
      intro p l
      have := cov_split R good covers p l
      exact_mod_cast this
    have zero : ∑ p, ∑ l, ((1 - I p l : ℤ) : ℝ) * W l p ≤ 120 := by
      have col : ∀ p, ∑ l, ((1 - I p l : ℤ) : ℝ) * W l p =
          20 * (K.reflection (basisVector p)) p + 4 * (K.reflection (one univ)) p := by
        intro p
        have := congrArg (fun v => (K.reflection v) p) (zero_column p)
        simp only [map_sum, map_smul, map_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          WithLp.ofLp_sum, Finset.sum_apply] at this
        simpa [Wdef] using this
      simp only [col]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, trace_reflect]
      have u : ∑ p, (K.reflection (one univ)) p ≤ 25 := by
        rw [← one_inner univ]
        have n1 : ‖one univ‖ ^ 2 = 25 := by
          rw [← real_inner_self_eq_norm_sq, one_inner]; simp [one]
        have := real_inner_le_norm (K.reflection (one univ)) (one univ)
        rw [LinearIsometryEquiv.norm_map] at this
        nlinarith
      have : (Module.finrank ℝ K : ℝ) ≤ 13 := by exact_mod_cast dim
      linarith
    have area : ∑ p, ∑ l, ((1 - I p l : ℤ) : ℝ) = 600 := by
      have : (∑ p, ∑ l, (1 - I p l)) = 600 := by
        simp only [sum_sub_distrib, row_sum]; simp
      exact_mod_cast this
    simp only [split, add_mul, sum_add_distrib, mul_one] at tot
    linarith
  · intro p
    have e : ∑ l, (nn R p l : ℝ) * W l p = (K.reflection (∑ l, (nn R p l : ℝ) • q l)) p := by
      simp [map_sum, map_smul, Wdef]
    rw [e]
    refine le_trans ?_ (norm_y (fun l => nn R p l))
    have := PiLp.norm_apply_le (K.reflection (∑ l, (nn R p l : ℝ) • q l)) p
    rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  · intro l
    have cs := sum_mul_sq_le_sq_mul_sq univ (fun p => (nn R p l : ℝ)) (fun p => W l p)
    have n : ∑ p, (W l p) ^ 2 = 65 := by
      have h := q_self l
      rw [← K.reflection.inner_map_map, inner_sum_apply] at h
      simpa [Wdef, pow_two] using h
    rw [n] at cs
    linarith

def xx (B : Finset (Fin 25)) (l : Fin 30) : ℤ := ∑ p ∈ B, I p l
def yy (A : Finset (Fin 30)) (p : Fin 25) : ℤ := ∑ l ∈ A, I p l

theorem I_nonneg (p l) : 0 ≤ I p l := by unfold I; split <;> simp
theorem I_le (p l) : I p l ≤ 1 := by unfold I; split <;> simp
theorem xx_nonneg (B l) : 0 ≤ xx B l := sum_nonneg fun p _ => I_nonneg p l

theorem xx_sum (B : Finset (Fin 25)) : ∑ l, xx B l = 6 * (B.card : ℤ) := by
  unfold xx; rw [sum_comm]; simp [row_sum, mul_comm]

theorem xx_through (B : Finset (Fin 25)) (p : Fin 25) :
    ∑ l, I p l * xx B l = (B.card : ℤ) + if p ∈ B then 5 else 0 := by
  unfold xx
  simp only [mul_sum]
  rw [sum_comm]
  simp only [row_pair]
  have : ∀ r ∈ B, (if p = r then (6:ℤ) else 1) = 1 + if p = r then 5 else 0 := by
    intro r _; split <;> simp
  rw [sum_congr rfl this, sum_add_distrib]
  simp

theorem xx_sq (B : Finset (Fin 25)) : ∑ l, xx B l ^ 2 = (B.card : ℤ) ^ 2 + 5 * B.card := by
  have e : ∀ l, xx B l ^ 2 = ∑ p ∈ B, I p l * xx B l := by
    intro l; rw [← sum_mul]; unfold xx; ring
  simp only [e]
  rw [sum_comm]
  have : ∀ p ∈ B, ∑ l, I p l * xx B l = (B.card : ℤ) + 5 := by
    intro p hp; rw [xx_through, if_pos hp]
  rw [sum_congr rfl this]; simp; ring

theorem xx_zero {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) {l} (hl : l ∈ A) : xx B l = 0 :=
  sum_eq_zero fun p hp => by simp [I, g p hp l hl]
theorem yy_zero {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) {p} (hp : p ∈ B) : yy A p = 0 :=
  sum_eq_zero fun l hl => by simp [I, g p hp l hl]

theorem xx_off {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (u v w : ℤ) :
    ∑ l ∈ Aᶜ, (u * xx B l ^ 2 + v * xx B l + w) =
      u * ((B.card : ℤ) ^ 2 + 5 * B.card) + v * (6 * B.card) + w * (30 - A.card) := by
  have s := sum_add_sum_compl A (fun l => u * xx B l ^ 2 + v * xx B l + w)
  have z : ∑ l ∈ A, (u * xx B l ^ 2 + v * xx B l + w) = w * A.card := by
    rw [sum_congr rfl (fun l hl => by rw [xx_zero g hl] : ∀ l ∈ A, _ = u * 0 ^ 2 + v * 0 + w)]
    simp [mul_comm]
  have t : ∑ l, (u * xx B l ^ 2 + v * xx B l + w) =
      u * ((B.card : ℤ) ^ 2 + 5 * B.card) + v * (6 * B.card) + w * 30 := by
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, xx_sq, xx_sum]; simp [mul_comm]
  linarith

theorem consec_nonneg (x c : ℤ) : 0 ≤ (x - c) * (x - c - 1) := by
  rcases le_or_gt x c with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem row_moment {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (c : ℤ) :
    0 ≤ ((B.card : ℤ) ^ 2 + 5 * B.card) - (2 * c + 1) * (6 * B.card) + c * (c + 1) * (30 - A.card) := by
  have h := xx_off g 1 (-(2 * c + 1)) (c * (c + 1))
  have n : 0 ≤ ∑ l ∈ Aᶜ, (1 * xx B l ^ 2 + -(2 * c + 1) * xx B l + c * (c + 1)) :=
    sum_nonneg fun l _ => by have := consec_nonneg (xx B l) c; nlinarith
  rw [h] at n; linarith

theorem yy_sum (A : Finset (Fin 30)) : ∑ p, yy A p = 5 * (A.card : ℤ) := by
  unfold yy; rw [sum_comm]; simp [col_sum, mul_comm]

theorem yy_sq (A : Finset (Fin 30)) : ∑ p, yy A p ^ 2 ≤ (A.card : ℤ) ^ 2 + 4 * A.card := by
  have e : ∀ p, yy A p ^ 2 = ∑ l ∈ A, ∑ m ∈ A, I p l * I p m := by
    intro p; rw [pow_two]; unfold yy; rw [sum_mul_sum]
  simp only [e]
  rw [sum_comm]
  have b : ∀ l ∈ A, ∑ p, ∑ m ∈ A, I p l * I p m ≤ (A.card : ℤ) + 4 := by
    intro l hl
    rw [sum_comm]
    simp only [col_pair]
    have : ∀ m ∈ A, (if l = m then (5:ℤ) else if cls l = cls m then 0 else 1) ≤ 1 + if l = m then 4 else 0 := by
      intro m _; split
      · norm_num
      · split <;> norm_num
    refine (sum_le_sum this).trans ?_
    rw [sum_add_distrib]; simp [hl]
  refine (sum_le_sum b).trans ?_
  simp; nlinarith

theorem col_moment {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (c : ℤ) :
    0 ≤ ((A.card : ℤ) ^ 2 + 4 * A.card) - (2 * c + 1) * (5 * A.card) + c * (c + 1) * (25 - B.card) := by
  have s := sum_add_sum_compl B (fun p => yy A p ^ 2 - (2 * c + 1) * yy A p + c * (c + 1))
  have z : ∑ p ∈ B, (yy A p ^ 2 - (2 * c + 1) * yy A p + c * (c + 1)) = c * (c + 1) * B.card := by
    rw [sum_congr rfl (fun p hp => by rw [yy_zero g hp] : ∀ p ∈ B, _ = (0:ℤ) ^ 2 - (2 * c + 1) * 0 + c * (c + 1))]
    simp [mul_comm]
  have t : ∑ p, (yy A p ^ 2 - (2 * c + 1) * yy A p + c * (c + 1)) ≤
      ((A.card : ℤ) ^ 2 + 4 * A.card) - (2 * c + 1) * (5 * A.card) + c * (c + 1) * 25 := by
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, yy_sum]
    have := yy_sq A; simp; linarith
  have n : 0 ≤ ∑ p ∈ Bᶜ, (yy A p ^ 2 - (2 * c + 1) * yy A p + c * (c + 1)) :=
    sum_nonneg fun p _ => by have := consec_nonneg (yy A p) c; nlinarith
  linarith

def oo (B : Finset (Fin 25)) (l : Fin 30) : ℤ := xx B l % 2
theorem oo_01 (B l) : oo B l = 0 ∨ oo B l = 1 := by unfold oo; omega
theorem oo_nonneg (B l) : 0 ≤ oo B l := by rcases oo_01 B l with h | h <;> rw [h] <;> norm_num
theorem oo_split (B l) : ∃ z, xx B l = oo B l + 2 * z := ⟨xx B l / 2, by unfold oo; omega⟩

theorem cls_xx (B : Finset (Fin 25)) (c : Fin 6) : ∑ l with cls l = c, xx B l = (B.card : ℤ) := by
  unfold xx; rw [sum_comm]; simp [cls_sum]

theorem cls_parity (B : Finset (Fin 25)) (c : Fin 6) :
    ∃ z : ℤ, (B.card : ℤ) = (∑ l with cls l = c, oo B l) + 2 * z := by
  choose z hz using oo_split B
  refine ⟨∑ l with cls l = c, z l, ?_⟩
  rw [← cls_xx B c, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => hz l

theorem pt_parity (B : Finset (Fin 25)) (p : Fin 25) :
    ∃ z : ℤ, (B.card : ℤ) + (if p ∈ B then 5 else 0) = (∑ l, I p l * oo B l) + 2 * z := by
  choose z hz using oo_split B
  refine ⟨∑ l, I p l * z l, ?_⟩
  rw [← xx_through B p, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => by rw [hz l]; ring

theorem sum_by_class (f : Fin 30 → ℤ) : ∑ l, f l = ∑ c : Fin 6, ∑ l with cls l = c, f l :=
  (sum_fiberwise univ cls f).symm

theorem odd_le_sq (x : ℤ) : x % 2 ≤ (x - 2) ^ 2 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · rw [h]; positivity
  · rw [h]
    have h0 : x - 2 ≠ 0 := by intro e; omega
    have := Int.one_le_abs h0
    nlinarith [sq_abs (x - 2)]

theorem odd_off {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (f : Fin 30 → ℤ) :
    ∑ l, oo B l * f l = ∑ l ∈ Aᶜ, oo B l * f l := by
  rw [← sum_add_sum_compl A]
  have : ∑ l ∈ A, oo B l * f l = 0 := sum_eq_zero fun l hl => by simp [oo, xx_zero g hl]
  rw [this, zero_add]

theorem odd_total {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) :
    ∑ l, oo B l ≤ ((B.card : ℤ) ^ 2 + 5 * B.card) - 4 * (6 * B.card) + 4 * (30 - A.card) := by
  have h := xx_off g 1 (-4) 4
  have e := odd_off g (fun _ => 1)
  simp only [mul_one] at e
  rw [e]
  have : ∑ l ∈ Aᶜ, oo B l ≤ ∑ l ∈ Aᶜ, (1 * xx B l ^ 2 + -4 * xx B l + 4) :=
    sum_le_sum fun l _ => by have := odd_le_sq (xx B l); unfold oo; nlinarith
  rw [h] at this; linarith

theorem no_7_8 {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 7) (ha : A.card = 8) : False := by
  have u := odd_total g
  rw [hb, ha, sum_by_class] at u
  have h1 : ∀ c ∈ (univ : Finset (Fin 6)), (1:ℤ) ≤ ∑ l with cls l = c, oo B l := by
    intro c _
    obtain ⟨z, h⟩ := cls_parity B c
    rw [hb] at h
    have : 0 ≤ ∑ l with cls l = c, oo B l := sum_nonneg fun l _ => oo_nonneg B l
    push_cast at h; omega
  have := sum_le_sum h1
  simp at this
  norm_num at u
  linarith

theorem no_9_6 {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 9) (ha : A.card = 6) : False := by
  have h := xx_off g 1 (-5) 6
  rw [hb, ha] at h
  have nn : ∀ l ∈ Aᶜ, 0 ≤ 1 * xx B l ^ 2 + -5 * xx B l + 6 := fun l _ => by
    have := consec_nonneg (xx B l) 2; nlinarith
  have each := (sum_eq_zero_iff_of_nonneg nn).mp (by rw [h]; norm_num)
  have two : ∀ l ∈ Aᶜ, 2 ≤ xx B l := by
    intro l hl
    have e := each l hl
    by_contra hc
    have : xx B l ≤ 1 := by omega
    nlinarith
  have y2 : ∀ p ∈ Bᶜ, 2 ≤ yy A p := by
    intro p hp
    have t := xx_through B p
    rw [if_neg (by simpa using hp), hb, ← sum_add_sum_compl A] at t
    have z : ∑ l ∈ A, I p l * xx B l = 0 := sum_eq_zero fun l hl => by simp [xx_zero g hl]
    rw [z] at t
    have b : ∑ l ∈ Aᶜ, I p l * 2 ≤ ∑ l ∈ Aᶜ, I p l * xx B l :=
      sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (two l hl) (I_nonneg p l)
    rw [← sum_mul] at b
    have r := row_sum p
    rw [← sum_add_sum_compl A] at r
    unfold yy
    push_cast at t
    omega
  have tot := yy_sum A
  rw [← sum_add_sum_compl B, sum_eq_zero (fun p hp => yy_zero g hp), ha] at tot
  have hs := sum_le_sum y2
  rw [sum_const, card_compl, hb] at hs
  simp at hs
  norm_num at tot
  linarith

theorem no_8_7 {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 8) (ha : A.card = 7) : False := by
  have u := odd_total g
  rw [hb, ha] at u; norm_num at u

  have half : ∀ p, 2 * ∑ l, I p l * oo B l ≤ ∑ l, oo B l := by
    intro p
    rw [sum_by_class, sum_by_class (fun l => oo B l), mul_sum]
    refine sum_le_sum fun c _ => ?_
    obtain ⟨z, par⟩ := cls_parity B c
    rw [hb] at par
    have le : ∑ l with cls l = c, I p l * oo B l ≤ ∑ l with cls l = c, oo B l :=
      sum_le_sum fun l _ => by have := I_le p l; have := oo_nonneg B l; nlinarith
    have le1 : ∑ l with cls l = c, I p l * oo B l ≤ 1 := by
      rw [← cls_sum p c]
      exact sum_le_sum fun l _ => by
        have := I_nonneg p l; rcases oo_01 B l with h | h <;> rw [h] <;> linarith
    have ge : 0 ≤ ∑ l with cls l = c, oo B l := sum_nonneg fun l _ => oo_nonneg B l
    push_cast at par
    omega

  have sq := xx_off g 1 (-4) 4
  have sf := xx_off g 0 1 (-2)
  rw [hb, ha] at sq sf; norm_num at sq sf
  have e1 := odd_off g (fun _ => 1)
  simp only [mul_one] at e1
  have quart : ∀ l, ∃ z : ℤ, 0 ≤ z ∧ xx B l ^ 2 + -(4 * xx B l) + 4 = oo B l + 4 * z := by
    intro l
    obtain ⟨w, hw⟩ := oo_split B l
    have hle := odd_le_sq (xx B l)
    rcases oo_01 B l with h | h
    · refine ⟨(w - 1) ^ 2, by positivity, ?_⟩
      rw [hw, h]; ring
    · refine ⟨w ^ 2 - w, ?_, ?_⟩
      · have := consec_nonneg w 0; nlinarith
      · rw [hw, h]; ring
  choose z z0 hz using quart
  have tot : ∑ l ∈ Aᶜ, (xx B l ^ 2 + -(4 * xx B l) + 4) = ∑ l ∈ Aᶜ, oo B l + 4 * ∑ l ∈ Aᶜ, z l := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => hz l
  rw [sq, ← e1] at tot
  have zs : 0 ≤ ∑ l ∈ Aᶜ, z l := sum_nonneg fun l _ => z0 l
  have pos : B.Nonempty := card_pos.mp (by omega)
  obtain ⟨b, hbB⟩ := pos
  have odd : ∀ p ∈ B, ∑ l, I p l * oo B l = 1 := by
    intro p hp
    obtain ⟨w, hw⟩ := pt_parity B p
    rw [if_pos hp, hb] at hw
    have := half p
    have ge : 0 ≤ ∑ l, I p l * oo B l := sum_nonneg fun l _ => mul_nonneg (I_nonneg p l) (oo_nonneg B l)
    push_cast at hw
    omega
  have o4 : ∑ l, oo B l = 4 := by have := half b; have := odd b hbB; omega
  have z4 : ∑ l ∈ Aᶜ, z l = 0 := by omega
  have each := (sum_eq_zero_iff_of_nonneg fun l _ => z0 l).mp z4
  have of : ∑ l ∈ Aᶜ, oo B l * (xx B l - 2) = 2 := by
    refine (sum_congr rfl fun l hl => ?_).trans sf
    have h1 := hz l
    rw [each l hl] at h1
    rcases oo_01 B l with h | h
    · rw [h] at h1 ⊢
      have : (xx B l - 2) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith
    · rw [h]; ring
  have dbl : ∑ p ∈ B, ∑ l, I p l * oo B l = ∑ l, oo B l * xx B l := by
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [← sum_mul]; unfold xx; ring
  rw [sum_congr rfl odd, odd_off g] at dbl
  have : ∑ l ∈ Aᶜ, oo B l * xx B l = ∑ l ∈ Aᶜ, oo B l * (xx B l - 2) + 2 * ∑ l ∈ Aᶜ, oo B l := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [this, of, ← e1, o4] at dbl
  simp [hb] at dbl

def forb : List (ℕ × ℕ) := [(1,25),(2,20),(3,16),(4,13),(5,11),(6,10),(7,8),(8,7),(9,6),(11,5),(12,4),(14,3),(17,2),(21,1)]

theorem no_forb {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) :
    ∀ f ∈ forb, ¬ (f.1 ≤ B.card ∧ f.2 ≤ A.card) := by
  rintro ⟨b, a⟩ hf ⟨h1, h2⟩
  obtain ⟨B1, s1, c1⟩ := exists_subset_card_eq h1
  obtain ⟨A1, s2, c2⟩ := exists_subset_card_eq h2
  have g1 : Good (B1, A1) := fun p hp l hl => g p (s1 hp) l (s2 hl)
  simp only [forb, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 1; rw [c1, c2] at this; norm_num at this
  · exact no_7_8 g1 c1 c2
  · exact no_8_7 g1 c1 c2
  · exact no_9_6 g1 c1 c2
  · have := row_moment g1 2; rw [c1, c2] at this; norm_num at this
  · have := col_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := col_moment g1 1; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 3; rw [c1, c2] at this; norm_num at this
  · have := row_moment g1 4; rw [c1, c2] at this; norm_num at this

def ind (A : Finset (Fin 30)) (l : Fin 30) : ℤ := if l ∈ A then 1 else 0

theorem yy_ind (A : Finset (Fin 30)) (p : Fin 25) : yy A p = ∑ l, I p l * ind A l := by
  unfold yy ind
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter]
  simp

theorem ind_sum (A : Finset (Fin 30)) : ∑ l, ind A l = (A.card : ℤ) := by
  unfold ind; simp

theorem arc {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 6) (ha : A.card = 9) (l : Fin 30) :
    xx B l = 2 - 2 * ind A l - oo B l := by
  by_cases hl : l ∈ A
  · simp [ind, hl, oo, xx_zero g hl]
  · have h := xx_off g 1 (-3) 2
    rw [hb, ha] at h
    have nn : ∀ m ∈ Aᶜ, 0 ≤ 1 * xx B m ^ 2 + -3 * xx B m + 2 := fun m _ => by
      have := consec_nonneg (xx B m) 1; nlinarith
    have each := (sum_eq_zero_iff_of_nonneg nn).mp (by rw [h]; norm_num) l (by simpa using hl)
    have hx : xx B l = 1 ∨ xx B l = 2 := by
      have : (xx B l - 1) * (xx B l - 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with e | e
      · left; linarith
      · right; linarith
    rcases hx with e | e <;> simp [ind, hl, oo, e]

theorem oo_A {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) {l : Fin 30} (hl : l ∈ A) : oo B l = 0 := by
  simp [oo, xx_zero g hl]

theorem tang {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 6) (ha : A.card = 9) (p : Fin 25) :
    ∑ l, I p l * oo B l = 6 - 2 * yy A p - if p ∈ B then 5 else 0 := by
  have t := xx_through B p
  have e : ∀ l, I p l * xx B l = 2 * I p l - 2 * (I p l * ind A l) - I p l * oo B l := by
    intro l; rw [arc g hb ha l]; ring
  simp only [e, sum_sub_distrib, ← mul_sum, row_sum, ← yy_ind, hb] at t
  push_cast at t
  linarith

theorem tang_total {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 6) (ha : A.card = 9) :
    ∑ l, oo B l = 6 := by
  have t := xx_sum B
  simp only [arc g hb ha, sum_sub_distrib, ← mul_sum, ind_sum, ha, hb] at t
  simp at t
  linarith

theorem off_point {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 6) (ha : A.card = 9)
    {p : Fin 25} (hp : p ∉ B) : 2 ≤ yy A p ∧ yy A p ≤ 3 := by
  have tp := tang g hb ha p
  rw [if_neg hp] at tp
  have t0 : 0 ≤ ∑ l, I p l * oo B l := sum_nonneg fun l _ => mul_nonneg (I_nonneg p l) (oo_nonneg B l)
  refine ⟨?_, by omega⟩
  by_contra hc
  have big : 4 ≤ ∑ l, I p l * oo B l := by omega
  obtain ⟨T, -, hT⟩ : ∃ T ∈ (univ : Finset (Fin 30)), I p T * oo B T ≠ 0 := by
    by_contra hn
    push Not at hn
    rw [sum_eq_zero hn] at big; norm_num at big
  have hI : I p T = 1 := by
    have h1 : I p T ≠ 0 := left_ne_zero_of_mul hT
    have := I_nonneg p T; have := I_le p T; omega
  have hO : oo B T = 1 := (oo_01 B T).resolve_left (right_ne_zero_of_mul hT)
  have hx : xx B T = 1 := by
    have h := arc g hb ha T
    have : ind A T = 0 := by
      unfold ind; split
      · rename_i hm; rw [oo_A g hm] at hO; norm_num at hO
      · rfl
    rw [this, hO] at h; linarith
  have up : ∑ r, I r T * ∑ l, I r l * oo B l ≤ 10 := by
    have e : ∑ r, I r T * ∑ l, I r l * oo B l = ∑ l, oo B l * ∑ r, I r T * I r l := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun l _ => sum_congr rfl fun r _ => by ring
    rw [e]
    have b : ∀ l ∈ (univ : Finset (Fin 30)), oo B l * ∑ r, I r T * I r l ≤ oo B l + if T = l then 4 else 0 := by
      intro l _
      rw [col_pair]
      have := oo_01 B l
      by_cases h : T = l
      · simp [h]; rcases this with h | h <;> rw [h] <;> norm_num
      · simp only [h, if_false]
        split <;> rcases this with h | h <;> rw [h] <;> norm_num
    refine (sum_le_sum b).trans ?_
    rw [sum_add_distrib, tang_total g hb ha]
    simp
  have lo : ∀ r ∈ (univ : Finset (Fin 25)),
      I r T * (2 - (if r ∈ B then 1 else 0) + 2 * (if r = p then 1 else 0)) ≤ I r T * ∑ l, I r l * oo B l := by
    intro r _
    rcases (show I r T = 0 ∨ I r T = 1 by have := I_nonneg r T; have := I_le r T; omega) with h0 | h1
    · simp [h0]
    · rw [h1, one_mul, one_mul]
      have tr := tang g hb ha r
      by_cases hr : r ∈ B
      · have hne : r ≠ p := fun e => hp (e ▸ hr)
        rw [if_pos hr, yy_zero g hr] at tr
        rw [tr]; simp [hr, hne]
      · rw [if_neg hr] at tr
        have ge : I r T * oo B T ≤ ∑ l, I r l * oo B l :=
          single_le_sum (f := fun l => I r l * oo B l) (fun l _ => mul_nonneg (I_nonneg r l) (oo_nonneg B l)) (mem_univ T)
        rw [h1, hO] at ge
        by_cases he : r = p
        · subst he; simp [hr]; linarith
        · simp only [hr, he, if_false]; omega
  have lo2 : ∑ r, I r T * (2 - (if r ∈ B then 1 else 0) + 2 * (if r = p then 1 else 0)) = 11 := by
    have e : ∀ r, I r T * (2 - (if r ∈ B then (1:ℤ) else 0) + 2 * (if r = p then 1 else 0)) =
        2 * I r T - (if r ∈ B then I r T else 0) + 2 * (if r = p then I r T else 0) := by
      intro r; split <;> split <;> ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, col_sum]
    have : ∑ r, (if r ∈ B then I r T else 0) = xx B T := by
      rw [← sum_filter]; unfold xx; simp
    rw [this, hx]
    simp [hI]
  have := sum_le_sum lo
  rw [lo2] at this
  linarith

theorem cls_size : ∀ c : Fin 6, ∑ l with cls l = c, (1:ℤ) = 5 := by decide +kernel

theorem zeros_in_class {B : Finset (Fin 25)} {A : Finset (Fin 30)} (g : Good (B, A)) (hb : B.card = 6) (ha : A.card = 9) (c : Fin 6) :
    ∑ l with cls l = c, ind A l ≤ 2 := by
  have t := cls_xx B c
  rw [hb] at t
  have b : ∑ l with cls l = c, xx B l ≤ ∑ l with cls l = c, (2 * (1:ℤ) - 2 * ind A l) :=
    sum_le_sum fun l _ => by rw [arc g hb ha l]; have := oo_nonneg B l; linarith
  rw [t, sum_sub_distrib, ← mul_sum, ← mul_sum, cls_size] at b
  push_cast at b
  omega

theorem triple (B : Fin 3 → Finset (Fin 25)) (A : Fin 3 → Finset (Fin 30)) (g : ∀ r, Good (B r, A r))
    (hb : ∀ r, (B r).card = 6) (ha : ∀ r, (A r).card = 9) (j : Fin 25) (hj : ∀ r, j ∈ B r)
    (hc : ∀ l, inc j l = false → ∃ r, l ∈ A r) (s : Fin 30) (hs : ∀ r, s ∈ A r) : False := by
  have Ij : ∀ l, I j l = 0 ∨ I j l = 1 := fun l => by have := I_nonneg j l; have := I_le j l; omega
  have miss : ∀ r, ∀ l ∈ A r, I j l = 0 := fun r l hl => by simp [I, g r j (hj r) l hl]
  let f : Fin 30 → ℤ := fun l => ∑ r, ind (A r) l
  have fdef : ∀ l, f l = ∑ r, ind (A r) l := fun _ => rfl
  let h : Fin 30 → ℤ := fun l => f l - (1 - I j l) - 2 * (if l = s then 1 else 0)
  have hdef : ∀ l, h l = f l - (1 - I j l) - 2 * (if l = s then 1 else 0) := fun _ => rfl
  have ind0 : ∀ r l, 0 ≤ ind (A r) l := fun r l => by unfold ind; split <;> norm_num
  have ind1 : ∀ r l, ind (A r) l ≤ 1 := fun r l => by unfold ind; split <;> norm_num
  have h0 : ∀ l, 0 ≤ h l := by
    intro l
    rw [hdef]
    by_cases e : l = s
    · subst e
      have : f l = 3 := by rw [fdef]; simp [ind, hs]
      rw [this, miss 0 l (hs 0)]; norm_num
    · rw [if_neg e]
      rcases Ij l with hz | hz
      · have hf : inc j l = false := by
          unfold I at hz; by_contra hne; simp [hne] at hz
        obtain ⟨r, hr⟩ := hc l hf
        have : ind (A r) l ≤ f l := single_le_sum (f := fun r => ind (A r) l) (fun r _ => ind0 r l) (mem_univ r)
        have : ind (A r) l = 1 := by simp [ind, hr]
        rw [hz]; linarith
      · have : 0 ≤ f l := sum_nonneg fun r _ => ind0 r l
        rw [hz]; linarith
  have htot : ∑ l, h l = 1 := by
    have fs : ∑ l, f l = 27 := by
      simp only [fdef]; rw [sum_comm]; simp [ind_sum, ha]
    simp only [hdef, sum_sub_distrib, ← mul_sum, fs, row_sum]
    simp
  obtain ⟨m, -, hm0⟩ : ∃ m ∈ (univ : Finset (Fin 30)), h m ≠ 0 := by
    by_contra hn
    push Not at hn
    rw [sum_eq_zero hn] at htot; norm_num at htot
  have hm1 : h m = 1 ∧ ∀ l, l ≠ m → h l = 0 := by
    have hsplit := add_sum_erase univ h (mem_univ m)
    have er : 0 ≤ ∑ l ∈ univ.erase m, h l := sum_nonneg fun l _ => h0 l
    have := h0 m
    have hmm : h m = 1 := by omega
    have erz : ∑ l ∈ univ.erase m, h l = 0 := by omega
    exact ⟨hmm, fun l hl => (sum_eq_zero_iff_of_nonneg fun l _ => h0 l).mp erz l (by simp [hl])⟩
  have hind : ∀ l, h l = if l = m then 1 else 0 := by
    intro l; split
    · rename_i e; rw [e]; exact hm1.1
    · rename_i e; exact hm1.2 l e
  have fval : ∀ l, f l = (1 - I j l) + 2 * (if l = s then 1 else 0) + (if l = m then 1 else 0) := by
    intro l; have h1 := hdef l; have h2 := hind l; linarith
  have hsm : s ≠ m := by
    intro e
    have h1 := fval s
    have : f s = 3 := by rw [fdef]; simp [ind, hs]
    rw [this, miss 0 s (hs 0)] at h1
    simp [e] at h1
  have Ijs : I j s = 0 := miss 0 s (hs 0)
  have fle : ∀ l, f l ≤ 3 := fun l => by
    rw [fdef]; refine (sum_le_sum fun r _ => ind1 r l).trans ?_; simp
  have Ijm : I j m = 0 := by
    rcases Ij m with hz | hz
    · exact hz
    · exfalso
      have h1 := fval m
      have hf : f m = 0 := by
        rw [fdef]; refine sum_eq_zero fun r _ => ?_
        unfold ind; split
        · rename_i hl; rw [miss r m hl] at hz; norm_num at hz
        · rfl
      rw [hf, hz] at h1
      simp [Ne.symm hsm] at h1
  have fm : f m = 2 := by rw [fval m, Ijm]; simp [Ne.symm hsm]

  have npar : cls s ≠ cls m := by
    intro e
    have up : ∑ l with cls l = cls m, f l ≤ 6 := by
      simp only [fdef]; rw [sum_comm]
      refine (sum_le_sum fun r _ => zeros_in_class (g r) (hb r) (ha r) (cls m)).trans ?_
      simp
    have lo : ∑ l with cls l = cls m, f l = 7 := by
      simp only [fval, sum_add_distrib, sum_sub_distrib, ← mul_sum, cls_size, cls_sum]
      simp [sum_filter, e]
    omega
  have cross : ∑ p, I p s * I p m = 1 := by rw [col_pair, if_neg hsm, if_neg npar]

  let k : Fin 25 → ℤ := fun p => ∑ r, if p ∈ B r then 1 else 0
  have kdef : ∀ p, k p = ∑ r, if p ∈ B r then (1:ℤ) else 0 := fun _ => rfl
  have F : ∀ p, p ≠ j → ∑ r, yy (A r) p = 5 + 2 * I p s + I p m := by
    intro p hp
    simp only [yy_ind]
    rw [sum_comm]
    have e : ∀ l, ∑ r, I p l * ind (A r) l = I p l - I p l * I j l + 2 * (if l = s then I p l else 0) + (if l = m then I p l else 0) := by
      intro l
      rw [← mul_sum, ← fdef, fval l]
      split <;> split <;> ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, row_sum, row_pair, if_neg hp]
    simp
  have kb : ∀ p, p ≠ j → 6 - 2 * k p ≤ 5 + 2 * I p s + I p m ∧ 5 + 2 * I p s + I p m ≤ 9 - 3 * k p := by
    intro p hp
    rw [← F p hp, kdef]
    have b : ∀ r, 2 - 2 * (if p ∈ B r then (1:ℤ) else 0) ≤ yy (A r) p ∧ yy (A r) p ≤ 3 - 3 * (if p ∈ B r then (1:ℤ) else 0) := by
      intro r
      by_cases hr : p ∈ B r
      · rw [yy_zero (g r) hr]; simp [hr]
      · have := off_point (g r) (hb r) (ha r) hr; simp [hr]; exact this
    constructor
    · have := sum_le_sum fun r (_ : r ∈ (univ : Finset (Fin 3))) => (b r).1
      rw [sum_sub_distrib, ← mul_sum] at this; simp at this ⊢; linarith
    · have := sum_le_sum fun r (_ : r ∈ (univ : Finset (Fin 3))) => (b r).2
      rw [sum_sub_distrib, ← mul_sum] at this; simp at this ⊢; linarith
  have Ip : ∀ p l, I p l = 0 ∨ I p l = 1 := fun p l => by have := I_nonneg p l; have := I_le p l; omega
  have klow : ∀ p, p ≠ j → 0 ≤ k p - (1 - I p s - I p m + I p s * I p m) := by
    intro p hp
    obtain ⟨h1, h2⟩ := kb p hp
    have k0 : 0 ≤ k p := sum_nonneg fun r _ => by split <;> norm_num
    rcases Ip p s with a | a <;> rcases Ip p m with b | b <;> rw [a, b] at h1 h2 ⊢ <;> omega
  have ktot : ∑ p, k p = 18 := by
    simp only [kdef]; rw [sum_comm]; simp [hb]
  have kj : k j = 3 := by rw [kdef]; simp [hj]
  have slack : ∑ p ∈ univ.erase j, (k p - (1 - I p s - I p m + I p s * I p m)) = 0 := by
    have e := add_sum_erase univ (fun p => k p - (1 - I p s - I p m + I p s * I p m)) (mem_univ j)
    have t : ∑ p, (k p - (1 - I p s - I p m + I p s * I p m)) = 2 := by
      simp only [sum_sub_distrib, sum_add_distrib, ktot, col_sum, cross]; simp
    rw [t, kj, Ijs, Ijm] at e
    linarith
  have each := (sum_eq_zero_iff_of_nonneg fun p hp => klow p (ne_of_mem_erase hp)).mp slack

  have noB : ∀ r, ∀ p ∈ B r, I p m = 0 := by
    intro r p hp
    rcases Ip p m with hz | hz
    · exact hz
    · exfalso
      have hpj : p ≠ j := by intro e; rw [e, Ijm] at hz; norm_num at hz
      have e := each p (by simp [hpj])
      rw [hz] at e
      have k1 : (1:ℤ) ≤ k p := by
        rw [kdef]
        refine le_trans (le_of_eq ?_) (single_le_sum (f := fun r => if p ∈ B r then (1:ℤ) else 0)
          (fun r _ => by split <;> norm_num) (mem_univ r))
        simp [hp]
      rcases Ip p s with a | a <;> rw [a] at e <;> omega
  have allA : ∀ r, ind (A r) m = 1 := by
    intro r
    have x0 : xx (B r) m = 0 := sum_eq_zero fun p hp => noB r p hp
    have e := arc (g r) (hb r) (ha r) m
    have := oo_01 (B r) m
    have := ind1 r m
    have := ind0 r m
    have : oo (B r) m = 0 := by unfold oo; rw [x0]; norm_num
    omega
  have : f m = 3 := by rw [fdef]; simp [allA]
  omega

def pcL : List ℕ := [0, 940, 1413, 1984, 2690, 2733, 3439, 4010, 4763, 5508, 5231, 6799, 6509, 9733, 9457, 7828, 15568, 15292, 9050, 14738, 10327, 10570, 14656, 13505, 12353]
def pRL : List ℕ := [0, 2939, 1413, 2119, 2969, 3532, 3642, 4348, 5310, 5761, 6467, 6639, 7284, 12086, 8696, 9403, 9637, 10219, 10926, 11632, 12338]
def dcL : List (List ℕ) := [[0, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999],
  [99999, 940, 1413, 1984, 2690, 2733, 3439, 4010, 4763, 4525, 5231, 6799, 6509, 9733, 9457, 7828, 15568, 15292, 9050, 14738, 10327, 10570, 14656, 13505, 12353, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999],
  [99999, 99999, 1880, 2353, 2826, 3397, 3673, 4146, 4717, 5423, 5465, 5938, 6509, 7215, 7258, 7964, 8535, 9241, 9050, 9756, 10462, 11034, 11510, 11783, 12353, 13059, 13303, 13575, 14281, 14852, 15095, 15801, 16836, 16878, 17584],
  [99999, 99999, 99999, 2820, 3293, 3766, 4239, 4613, 5086, 5559, 6130, 6405, 6878, 7351, 7922, 8198, 8671, 9242, 9948, 9990, 10463, 11034, 11740, 11783, 12489, 13060, 13766, 13575, 14281, 14987, 15559, 16035, 16308, 16878, 17584],
  [99999, 99999, 99999, 99999, 3760, 4233, 4706, 5179, 5553, 6026, 6499, 6972, 7345, 7818, 8291, 8764, 9138, 9611, 10084, 10655, 10930, 11403, 11876, 12447, 12723, 13196, 13767, 14473, 14515, 14988, 15559, 16265, 16308, 17014, 17585],
  [99999, 99999, 99999, 99999, 99999, 4700, 5173, 5646, 6119, 6493, 6966, 7439, 7912, 8285, 8758, 9231, 9704, 10078, 10551, 11024, 11497, 11870, 12343, 12816, 13289, 13663, 14136, 14609, 15180, 15455, 15928, 16401, 16972, 17248, 17721],
  [99999, 99999, 99999, 99999, 99999, 99999, 5640, 6113, 6586, 7059, 7433, 7906, 8379, 8852, 9225, 9698, 10171, 10644, 11018, 11491, 11964, 12437, 12810, 13283, 13756, 14229, 14603, 15076, 15549, 16022, 16395, 16868, 17341, 17814, 18188],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 6580, 7053, 7526, 7999, 8373, 8846, 9319, 9792, 10165, 10638, 11111, 11584, 11958, 12431, 12904, 13377, 13750, 14223, 14696, 15169, 15543, 16016, 16489, 16962, 17335, 17808, 18281, 18754],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 7520, 7993, 8466, 8939, 9313, 9786, 10259, 10732, 11105, 11578, 12051, 12524, 12898, 13371, 13844, 14317, 14690, 15163, 15636, 16109, 16483, 16956, 17429, 17902, 18275, 18748, 19221],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 8460, 8933, 9406, 9879, 10253, 10726, 11199, 11672, 12045, 12518, 12991, 13464, 13838, 14311, 14784, 15257, 15630, 16103, 16576, 17049, 17423, 17896, 18369, 18842, 19215, 19688],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 9400, 9873, 10346, 10819, 11193, 11666, 12139, 12612, 12985, 13458, 13931, 14404, 14778, 15251, 15724, 16197, 16570, 17043, 17516, 17989, 18363, 18836, 19309, 19782, 20155],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 10340, 10813, 11286, 11759, 12133, 12606, 13079, 13552, 13925, 14398, 14871, 15344, 15718, 16191, 16664, 17137, 17510, 17983, 18456, 18929, 19303, 19776, 20249, 20722],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 11280, 11753, 12226, 12699, 13073, 13546, 14019, 14492, 14865, 15338, 15811, 16284, 16658, 17131, 17604, 18077, 18450, 18923, 19396, 19869, 20243, 20716, 21189],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 12220, 12693, 13166, 13639, 14013, 14486, 14959, 15432, 15805, 16278, 16751, 17224, 17598, 18071, 18544, 19017, 19390, 19863, 20336, 20809, 21183, 21656]]
def drL : List (List ℕ) := [[0, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999],
  [99999, 2939, 1413, 2119, 2969, 3532, 3642, 4348, 5310, 5761, 6467, 6639, 7284, 12086, 8696, 9403, 9637, 10219, 10926, 11632, 12338, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999],
  [99999, 99999, 5878, 4352, 2826, 3532, 4238, 4945, 5055, 5761, 6467, 7174, 7284, 7990, 8696, 9403, 10109, 10281, 10926, 11632, 12338, 13044, 13278, 13861, 14567, 15274, 15980, 16276, 16858, 17503, 18210],
  [99999, 99999, 99999, 8817, 7291, 5765, 4239, 4945, 5651, 6357, 6468, 7174, 7880, 8586, 8697, 9403, 10109, 10815, 10926, 11632, 12338, 13044, 13751, 13923, 14568, 15274, 15980, 16686, 16920, 17503, 18209],
  [99999, 99999, 99999, 99999, 11756, 10230, 8704, 7178, 5652, 6358, 7064, 7770, 7881, 8587, 9293, 9999, 10110, 10816, 11522, 12228, 12339, 13045, 13751, 14457, 14568, 15274, 15980, 16686, 17392, 17565, 18210],
  [99999, 99999, 99999, 99999, 99999, 14695, 13169, 11643, 10117, 8591, 7065, 7771, 8477, 9183, 9294, 10000, 10706, 11412, 11523, 12229, 12935, 13641, 13752, 14458, 15164, 15870, 15981, 16687, 17393, 18099, 18210],
  [99999, 99999, 99999, 99999, 99999, 99999, 17634, 16108, 14582, 13056, 11530, 10004, 8478, 9184, 9890, 10596, 10707, 11413, 12119, 12825, 12936, 13642, 14348, 15054, 15165, 15871, 16577, 17283, 17394, 18100, 18806],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 20573, 19047, 17521, 15995, 14469, 12943, 11417, 9891, 10597, 11303, 12009, 12120, 12826, 13532, 14238, 14349, 15055, 15761, 16467, 16578, 17284, 17990, 18696, 18807],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 23512, 21986, 20460, 18934, 17408, 15882, 14356, 12830, 11304, 12010, 12716, 13422, 13533, 14239, 14945, 15651, 15762, 16468, 17174, 17880, 17991, 18697, 19403],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 26451, 24925, 23399, 21873, 20347, 18821, 17295, 15769, 14243, 12717, 13423, 14129, 14835, 14946, 15652, 16358, 17064, 17175, 17881, 18587, 19293, 19404],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 29390, 27864, 26338, 24812, 23286, 21760, 20234, 18708, 17182, 15656, 14130, 14836, 15542, 16248, 16359, 17065, 17771, 18477, 18588, 19294, 20000],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 32329, 30803, 29277, 27751, 26225, 24699, 23173, 21647, 20121, 18595, 17069, 15543, 16249, 16955, 17661, 17772, 18478, 19184, 19890, 20001],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 35268, 33742, 32216, 30690, 29164, 27638, 26112, 24586, 23060, 21534, 20008, 18482, 16956, 17662, 18368, 19074, 19185, 19891, 20597],
  [99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 99999, 38207, 36681, 35155, 33629, 32103, 30577, 29051, 27525, 25999, 24473, 22947, 21421, 19895, 18369, 19075, 19781, 20487, 20598]]
def pc (a b : ℕ) : ℕ := if a = 9 ∧ b = 6 then 4525 else pcL.getD a 0
def pm (a : ℕ) : ℕ := if a = 9 then 4525 else pcL.getD a 0
def pr (b : ℕ) : ℕ := pRL.getD b 0
def dc (t s : ℕ) : ℕ := (dcL.getD t []).getD s 0
def dr (t s : ℕ) : ℕ := (drL.getD t []).getD s 0
def qm (c s : ℕ) : ℕ := c ^ 2 * (s / c) + (s % c) ^ 2

set_option maxRecDepth 20000 in
theorem dc_step : ∀ t < 13, ∀ s < 35, ∀ a < 25, 1 ≤ a → s + a ≤ 34 → dc (t + 1) (s + a) ≤ dc t s + pm a := by decide +kernel
set_option maxRecDepth 20000 in
theorem dr_step : ∀ t < 13, ∀ s < 31, ∀ a < 21, 1 ≤ a → s + a ≤ 30 → dr (t + 1) (s + a) ≤ dr t s + pr a := by decide +kernel
set_option maxRecDepth 20000 in
theorem dc_check : ∀ c < 13, ∀ s < 11, c ≠ 2 → (c = 0 → s = 0) →
    12352 ≤ 100 * s + dc (c + 1) (24 + s) ∧ 10000 * (64 * qm c s + s ^ 2) ≤ (100 * s + dc (c + 1) (24 + s) - 12352) ^ 2 := by decide +kernel
set_option maxRecDepth 20000 in
theorem dc3_check : ∀ a < 25, 1 ≤ a → ∀ s < 11, a ≤ 24 + s →
    12352 ≤ 100 * s + (pcL.getD a 0 + dc 2 (24 + s - a)) ∧
    10000 * (64 * qm 2 s + s ^ 2) ≤ (100 * s + (pcL.getD a 0 + dc 2 (24 + s - a)) - 12352) ^ 2 := by decide +kernel
set_option maxRecDepth 20000 in
theorem dr_check : ∀ c < 13, ∀ s < 11, (c = 0 → s = 0) →
    12337 ≤ 100 * s + dr (c + 1) (20 + s) ∧ 650000 * qm c s ≤ (100 * s + dr (c + 1) (20 + s) - 12337) ^ 2 := by decide +kernel
theorem pm_line : ∀ a < 25, 1 ≤ a → 450 * a + 475 ≤ pm a := by decide +kernel
theorem pr_line : ∀ b < 21, 1 ≤ b → 500 * b + 413 ≤ pr b := by decide +kernel
theorem pm_le : ∀ a < 25, ∀ b < 26, pm a ≤ pc a b := by decide +kernel
def okb (a b : ℕ) : Bool := forb.all fun f => !(decide (f.1 ≤ b) && decide (f.2 ≤ a))
set_option maxRecDepth 20000 in
theorem shape_check : ∀ a < 31, ∀ b < 26, (1 ≤ a ∧ 1 ≤ b ∧ okb a b = true) →
    (a ≤ 24 ∧ b ≤ 20 ∧ 23 * (b * pc a b) + 9 * (a * pr b) ≤ 919621) := by decide +kernel

theorem shape {R : Box} (g : Good R) (h1 : R.1.Nonempty) (h2 : R.2.Nonempty) :
    R.2.card ≤ 24 ∧ R.1.card ≤ 20 ∧ 23 * (R.1.card * pc R.2.card R.1.card) + 9 * (R.2.card * pr R.1.card) ≤ 919621 := by
  have ok : okb R.2.card R.1.card = true := by
    unfold okb
    rw [List.all_eq_true]
    intro f hf
    have := no_forb (B := R.1) (A := R.2) g f hf
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  exact shape_check _ (by have := card_le_univ R.2; simp at this; omega) _ (by have := card_le_univ R.1; simp at this; omega)
    ⟨card_pos.mpr h2, card_pos.mpr h1, ok⟩

theorem qm_add (c s n : ℕ) (h : n ≤ c) : qm c s + n ^ 2 ≤ qm c (s + n) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have : n = 0 := by omega
    subst this; simp
  · have hs := Nat.div_add_mod s c
    have hr := Nat.mod_lt s hc
    unfold qm
    generalize s / c = u at hs
    generalize s % c = r at hs hr
    by_cases hn : r + n < c
    · have e := (Nat.div_mod_unique (a := s + n) (d := u) (c := r + n) hc).mpr ⟨by linarith, hn⟩
      rw [e.1, e.2]; nlinarith
    · have e := (Nat.div_mod_unique (a := s + n) (d := u + 1) (c := r + n - c) hc).mpr ⟨by rw [mul_add]; omega, by omega⟩
      rw [e.1, e.2]
      obtain ⟨z, hz⟩ : ∃ z, r + n = c + z := ⟨r + n - c, by omega⟩
      have : r + n - c = z := by omega
      rw [this]
      obtain ⟨x, hx⟩ : ∃ x, c = r + x := ⟨c - r, by omega⟩
      have hn2 : n = x + z := by omega
      obtain ⟨y, hy⟩ : ∃ y, r = z + y := ⟨r - z, by omega⟩
      subst hx; subst hn2; rw [hy]
      nlinarith [Nat.zero_le (x * y)]

theorem qm_sum {ι : Type} (U : Finset ι) (n : ι → ℕ) (c : ℕ) (h : ∀ i ∈ U, n i ≤ c) :
    ∑ i ∈ U, n i ^ 2 ≤ qm c (∑ i ∈ U, n i) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    rw [sum_insert hi, sum_insert hi, add_comm, add_comm (n i)]
    exact (Nat.add_le_add_right (ih fun j hj => h j (mem_insert_of_mem hj)) _).trans
      (qm_add c _ _ (h i (mem_insert_self i U)))

theorem qm_lin {ι : Type} (U : Finset ι) (n : ι → ℕ) (c : ℕ) (h : ∀ i ∈ U, n i ≤ c) :
    ∑ i ∈ U, n i ^ 2 ≤ c * ∑ i ∈ U, n i := by
  rw [mul_sum]
  exact sum_le_sum fun i hi => by rw [pow_two]; exact Nat.mul_le_mul_right _ (h i hi)

theorem dp {ι : Type} (T : Finset ι) (a : ι → ℕ) (D : ℕ → ℕ → ℕ) (price : ℕ → ℕ) (M Amax : ℕ)
    (D0 : D 0 0 = 0)
    (step : ∀ t < 13, ∀ s < M + 1, ∀ x < Amax, 1 ≤ x → s + x ≤ M → D (t + 1) (s + x) ≤ D t s + price x)
    (ha : ∀ i ∈ T, 1 ≤ a i ∧ a i < Amax) (hc : T.card ≤ 13) (hM : ∑ i ∈ T, a i ≤ M) :
    D T.card (∑ i ∈ T, a i) ≤ ∑ i ∈ T, price (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [D0]
  | insert i T hi ih =>
    rw [card_insert_of_notMem hi] at hc ⊢
    rw [sum_insert hi] at hM
    rw [sum_insert hi, sum_insert hi, add_comm (a i), add_comm (price (a i))]
    have hi2 := ha i (mem_insert_self i T)
    exact (step T.card (by omega) _ (by omega) (a i) hi2.2 hi2.1 (by omega)).trans
      (Nat.add_le_add_right (ih (fun j hj => ha j (mem_insert_of_mem hj)) (by omega) (by omega)) _)

theorem col_cert {ι : Type} [DecidableEq ι] (T : Finset ι) (a b : ι → ℕ) (n : Fin 30 → ℕ) (s : ℕ)
    (ha : ∀ i ∈ T, 1 ≤ a i ∧ a i < 25) (hb : ∀ i ∈ T, b i < 26) (hc : T.card ≤ 13)
    (hs : ∑ i ∈ T, a i = 24 + s) (hn : ∑ l, n l = s) (hcap : ∀ l, n l ≤ T.card - 1)
    (star : T.card = 3 → (∀ i ∈ T, a i = 9 ∧ b i = 6) → ∀ l, n l ≤ 1) :
    12352 ≤ 100 * s + ∑ i ∈ T, pc (a i) (b i) ∧
    10000 * (64 * ∑ l, n l ^ 2 + s ^ 2) ≤ (100 * s + ∑ i ∈ T, pc (a i) (b i) - 12352) ^ 2 := by
  have tpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h | h
    · rw [card_eq_zero] at h; subst h; simp at hs; omega
    · exact h
  have pmle : ∑ i ∈ T, pm (a i) ≤ ∑ i ∈ T, pc (a i) (b i) :=
    sum_le_sum fun i hi => pm_le _ (ha i hi).2 _ (hb i hi)
  have Q := qm_sum univ n (T.card - 1) fun l _ => hcap l
  have Ql := qm_lin univ n (T.card - 1) fun l _ => hcap l
  rw [hn] at Q Ql
  have key : ∀ P q : ℕ, P ≤ ∑ i ∈ T, pc (a i) (b i) → ∑ l, n l ^ 2 ≤ q →
      12352 ≤ 100 * s + P ∧ 10000 * (64 * q + s ^ 2) ≤ (100 * s + P - 12352) ^ 2 →
      12352 ≤ 100 * s + ∑ i ∈ T, pc (a i) (b i) ∧
      10000 * (64 * ∑ l, n l ^ 2 + s ^ 2) ≤ (100 * s + ∑ i ∈ T, pc (a i) (b i) - 12352) ^ 2 := by
    rintro P q hP hq ⟨h1, h2⟩
    refine ⟨by omega, le_trans ?_ (h2.trans (Nat.pow_le_pow_left (by omega) 2))⟩
    omega
  by_cases small : s < 11
  · have dpT := dp T a dc pm 34 25 (by decide +kernel) dc_step ha hc (by omega)
    rw [hs] at dpT
    have z0 : T.card - 1 = 0 → s = 0 := by
      intro h0
      rw [← hn]; exact sum_eq_zero fun l _ => by have := hcap l; omega
    by_cases h3 : T.card = 3
    · by_cases st : ∀ i ∈ T, a i = 9 ∧ b i = 6
      · have n1 := star h3 st
        have s3 : s = 3 := by
          rw [sum_congr rfl fun i hi => (st i hi).1] at hs
          simp [h3] at hs; omega
        have Q1 : ∑ l, n l ^ 2 ≤ 3 := by
          have := qm_lin univ n 1 fun l _ => n1 l
          rw [hn, s3] at this; simpa using this
        have P : ∑ i ∈ T, pc (a i) (b i) = 13575 := by
          rw [sum_congr rfl fun i hi => by rw [(st i hi).1, (st i hi).2]]
          simp [h3, pc]
        refine key 13575 3 (by rw [P]) Q1 ?_
        rw [s3]; norm_num
      · push Not at st
        obtain ⟨i, hi, hne⟩ := st
        have pci : pc (a i) (b i) = pcL.getD (a i) 0 := by
          unfold pc; rw [if_neg]; rintro ⟨e1, e2⟩; exact hne e1 e2
        have e1 := add_sum_erase T (fun i => pc (a i) (b i)) hi
        have e2 := add_sum_erase T a hi
        have hle : ∑ j ∈ T.erase i, a j = 24 + s - a i := by omega
        have dpE := dp (T.erase i) a dc pm 34 25 (by decide +kernel) dc_step
          (fun j hj => ha j (mem_of_mem_erase hj)) (by rw [card_erase_of_mem hi]; omega) (by omega)
        rw [card_erase_of_mem hi, h3, hle] at dpE
        have pmE : ∑ j ∈ T.erase i, pm (a j) ≤ ∑ j ∈ T.erase i, pc (a j) (b j) :=
          sum_le_sum fun j hj => pm_le _ (ha j (mem_of_mem_erase hj)).2 _ (hb j (mem_of_mem_erase hj))
        refine key (pcL.getD (a i) 0 + dc 2 (24 + s - a i)) (qm 2 s) ?_ ?_
          (dc3_check _ (ha i hi).2 (ha i hi).1 s small (by omega))
        · rw [← e1]; simp only [pci]; exact Nat.add_le_add_left (dpE.trans pmE) _
        · rw [h3] at Q; exact Q
    · refine key (dc (T.card - 1 + 1) (24 + s)) (qm (T.card - 1) s) ?_ Q
        (dc_check (T.card - 1) (by omega) s small (by omega) z0)
      rw [Nat.sub_add_cancel tpos]; exact dpT.trans pmle
  · have line : 450 * (24 + s) + 475 * T.card ≤ ∑ i ∈ T, pm (a i) := by
      rw [← hs, mul_sum]
      have : 475 * T.card = ∑ _i ∈ T, 475 := by simp [mul_comm]
      rw [this, ← sum_add_distrib]
      exact sum_le_sum fun i hi => pm_line _ (ha i hi).2 (ha i hi).1
    refine key (450 * (24 + s) + 475 * T.card) ((T.card - 1) * s) (line.trans pmle) Ql ?_
    obtain ⟨x, rfl⟩ : ∃ x, s = 11 + x := ⟨s - 11, by omega⟩
    generalize T.card = t at *
    refine ⟨by omega, ?_⟩
    obtain ⟨u, hu⟩ : ∃ u, 100 * (11 + x) + (450 * (24 + (11 + x)) + 475 * t) = 12352 + u :=
      ⟨100 * (11 + x) + (450 * (24 + (11 + x)) + 475 * t) - 12352, by omega⟩
    rw [hu, Nat.add_sub_cancel_left]
    have hu2 : u = 4498 + 550 * x + 475 * t := by omega
    rw [hu2]
    interval_cases t <;> norm_num <;> nlinarith [Nat.zero_le x]

theorem row_cert {ι : Type} [DecidableEq ι] (T : Finset ι) (b : ι → ℕ) (n : Fin 25 → ℕ) (s : ℕ)
    (hb : ∀ i ∈ T, 1 ≤ b i ∧ b i < 21) (hc : T.card ≤ 13)
    (hs : ∑ i ∈ T, b i = 20 + s) (hn : ∑ p, n p = s) (hcap : ∀ p, n p ≤ T.card - 1) :
    12337 ≤ 100 * s + ∑ i ∈ T, pr (b i) ∧
    650000 * ∑ p, n p ^ 2 ≤ (100 * s + ∑ i ∈ T, pr (b i) - 12337) ^ 2 := by
  have tpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h | h
    · rw [card_eq_zero] at h; subst h; simp at hs; omega
    · exact h
  have Q := qm_sum univ n (T.card - 1) fun l _ => hcap l
  have Ql := qm_lin univ n (T.card - 1) fun l _ => hcap l
  rw [hn] at Q Ql
  have key : ∀ P q : ℕ, P ≤ ∑ i ∈ T, pr (b i) → ∑ p, n p ^ 2 ≤ q →
      12337 ≤ 100 * s + P ∧ 650000 * q ≤ (100 * s + P - 12337) ^ 2 →
      12337 ≤ 100 * s + ∑ i ∈ T, pr (b i) ∧
      650000 * ∑ p, n p ^ 2 ≤ (100 * s + ∑ i ∈ T, pr (b i) - 12337) ^ 2 := by
    rintro P q hP hq ⟨h1, h2⟩
    refine ⟨by omega, le_trans ?_ (h2.trans (Nat.pow_le_pow_left (by omega) 2))⟩
    omega
  by_cases small : s < 11
  · have dpT := dp T b dr pr 30 21 (by decide +kernel) dr_step hb hc (by omega)
    rw [hs] at dpT
    have z0 : T.card - 1 = 0 → s = 0 := by
      intro h0
      rw [← hn]; exact sum_eq_zero fun l _ => by have := hcap l; omega
    refine key (dr (T.card - 1 + 1) (20 + s)) (qm (T.card - 1) s) ?_ Q
        (dr_check (T.card - 1) (by omega) s small z0)
    rw [Nat.sub_add_cancel tpos]; exact dpT
  · have line : 500 * (20 + s) + 413 * T.card ≤ ∑ i ∈ T, pr (b i) := by
      rw [← hs, mul_sum]
      have : 413 * T.card = ∑ _i ∈ T, 413 := by simp [mul_comm]
      rw [this, ← sum_add_distrib]
      exact sum_le_sum fun i hi => pr_line _ (hb i hi).2 (hb i hi).1
    refine key (500 * (20 + s) + 413 * T.card) ((T.card - 1) * s) line Ql ?_
    obtain ⟨x, rfl⟩ : ∃ x, s = 11 + x := ⟨s - 11, by omega⟩
    generalize T.card = t at *
    refine ⟨by omega, ?_⟩
    obtain ⟨u, hu⟩ : ∃ u, 100 * (11 + x) + (500 * (20 + (11 + x)) + 413 * t) = 12337 + u :=
      ⟨100 * (11 + x) + (500 * (20 + (11 + x)) + 413 * t) - 12337, by omega⟩
    rw [hu, Nat.add_sub_cancel_left]
    have hu2 : u = 4263 + 600 * x + 413 * t := by omega
    rw [hu2]
    interval_cases t <;> norm_num <;> nlinarith [Nat.zero_le x]

def tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : Finset (Fin k) := univ.filter fun t => p ∈ (R t).1
def tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : Finset (Fin k) := univ.filter fun t => l ∈ (R t).2

theorem cov_tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : ∑ l, cov R p l = ∑ t ∈ tp R p, (R t).2.card := by
  have e : ∀ l, cov R p l = ∑ t ∈ tp R p, if l ∈ (R t).2 then 1 else 0 := by
    intro l; unfold cov tp; rw [← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : ∑ p, cov R p l = ∑ t ∈ tl R l, (R t).1.card := by
  have e : ∀ p, cov R p l = ∑ t ∈ tl R l, if p ∈ (R t).1 then 1 else 0 := by
    intro p; unfold cov tl
    rw [filter_congr (fun t _ => and_comm), ← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_le_tp {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tp R p).card :=
  card_le_card fun t ht => by simp [tp] at ht ⊢; exact ht.1
theorem cov_le_tl {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tl R l).card :=
  card_le_card fun t ht => by simp [tl] at ht ⊢; exact ht.2

theorem swap_tp {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ p, ∑ t ∈ tp R p, f t = ∑ t, (R t).1.card * f t := by
  unfold tp; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp
theorem swap_tl {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ l, ∑ t ∈ tl R l, f t = ∑ t, (R t).2.card * f t := by
  unfold tl; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp

theorem sq_bound (C X : ℝ) (a b : ℕ) (h1 : b ≤ a) (hX : C ^ 2 ≤ X) (h2 : 10000 * X ≤ ((a - b : ℕ) : ℝ) ^ 2) :
    100 * C ≤ (a : ℝ) - b := by
  rw [← Nat.cast_sub h1]
  by_contra h
  push Not at h
  have h0 : (0:ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _
  have := pow_lt_pow_left₀ h h0 (two_ne_zero)
  nlinarith

theorem main {k : ℕ} (hk : k ≤ 13) (R : Fin k → Box) (good : ∀ t, Good (R t))
    (n1 : ∀ t, (R t).1.Nonempty) (n2 : ∀ t, (R t).2.Nonempty)
    (covers : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2) : False := by
  classical
  have cpos : ∀ p l, inc p l = false → 0 < cov R p l := by
    intro p l h
    obtain ⟨t, ht⟩ := covers p l h
    exact card_pos.mpr ⟨t, by simpa using ht⟩
  obtain ⟨W, tot, colB, rowB⟩ := spectral hk R good cpos
  have sh : ∀ t, (R t).2.card ≤ 24 ∧ (R t).1.card ≤ 20 ∧
      23 * ((R t).1.card * pc (R t).2.card (R t).1.card) + 9 * ((R t).2.card * pr (R t).1.card) ≤ 919621 :=
    fun t => shape (good t) (n1 t) (n2 t)
  have cardT : ∀ T : Finset (Fin k), T.card ≤ 13 := fun T => by
    have := card_le_univ T; simp at this; omega
  have sp : ∀ p, ∑ t ∈ tp R p, (R t).2.card = 24 + ∑ l, nn R p l := by
    intro p
    rw [← cov_tp]
    have : (∑ l, (cov R p l : ℤ)) = 24 + ∑ l, (nn R p l : ℤ) := by
      simp only [cov_split R good cpos, sum_add_distrib, sum_sub_distrib, row_sum]
      simp; ring
    exact_mod_cast this
  have sl : ∀ l, ∑ t ∈ tl R l, (R t).1.card = 20 + ∑ p, nn R p l := by
    intro l
    rw [← cov_tl]
    have : (∑ p, (cov R p l : ℤ)) = 20 + ∑ p, (nn R p l : ℤ) := by
      simp only [cov_split R good cpos, sum_add_distrib, sum_sub_distrib, col_sum]
      simp; ring
    exact_mod_cast this
  have star : ∀ p, (tp R p).card = 3 → (∀ t ∈ tp R p, (R t).2.card = 9 ∧ (R t).1.card = 6) → ∀ l, nn R p l ≤ 1 := by
    intro p h3 hst l
    by_contra hc
    have c3 : 3 ≤ cov R p l := by unfold nn at hc; omega
    have sub : (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2) ⊆ tp R p :=
      fun t ht => by simp [tp] at ht ⊢; exact ht.1
    have eq := eq_of_subset_of_card_le sub (by rw [h3]; exact c3)
    let e := (tp R p).equivFinOfCardEq h3
    have mem : ∀ r, ((e.symm r : tp R p) : Fin k) ∈ tp R p := fun r => (e.symm r).2
    refine triple (fun r => (R (e.symm r)).1) (fun r => (R (e.symm r)).2) (fun r => good _)
      (fun r => (hst _ (mem r)).2) (fun r => (hst _ (mem r)).1) p (fun r => ?_) (fun m hm => ?_) l (fun r => ?_)
    · have := mem r; simp only [tp, mem_filter] at this; exact this.2
    · obtain ⟨t, ht1, ht2⟩ := covers p m hm
      have htm : t ∈ tp R p := by simp [tp, ht1]
      exact ⟨e ⟨t, htm⟩, by simpa using ht2⟩
    · have := eq.ge (mem r); simp only [mem_filter] at this; exact this.2.2
  have colC : ∀ p, 100 * (∑ l, (nn R p l : ℝ) * W l p) ≤
      100 * (∑ l, (nn R p l : ℝ)) + ((∑ t ∈ tp R p, pc (R t).2.card (R t).1.card : ℕ) : ℝ) - 12352 := by
    intro p
    have c := col_cert (tp R p) (fun t => (R t).2.card) (fun t => (R t).1.card) (nn R p) (∑ l, nn R p l)
      (fun t _ => ⟨card_pos.mpr (n2 t), by have := (sh t).1; omega⟩)
      (fun t _ => by have := (sh t).2.1; omega) (cardT _) (sp p) rfl
      (fun l => by have := cov_le_tp R p l; unfold nn; omega) (star p)
    have := sq_bound _ _ _ _ c.1 (colB p) (by exact_mod_cast c.2)
    push_cast at this ⊢
    linarith
  have rowC : ∀ l, 100 * (∑ p, (nn R p l : ℝ) * W l p) ≤
      100 * (∑ p, (nn R p l : ℝ)) + ((∑ t ∈ tl R l, pr (R t).1.card : ℕ) : ℝ) - 12337 := by
    intro l
    have c := row_cert (tl R l) (fun t => (R t).1.card) (fun p => nn R p l) (∑ p, nn R p l)
      (fun t _ => ⟨card_pos.mpr (n1 t), by have := (sh t).2.1; omega⟩) (cardT _) (sl l) rfl
      (fun p => by have := cov_le_tl R p l; unfold nn; omega)
    have h2 : (10000:ℝ) * (65 * ∑ p, (nn R p l : ℝ) ^ 2) ≤
        ((100 * ∑ p, nn R p l + ∑ t ∈ tl R l, pr (R t).1.card - 12337 : ℕ) : ℝ) ^ 2 := by
      have := c.2
      have h : ((650000 * ∑ p, nn R p l ^ 2 : ℕ) : ℝ) ≤
        (((100 * ∑ p, nn R p l + ∑ t ∈ tl R l, pr (R t).1.card - 12337) ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h ⊢
      linarith
    have := sq_bound _ _ _ _ c.1 (rowB l) h2
    push_cast at this ⊢
    linarith
  have colS : (356800 : ℝ) ≤ ((∑ t, (R t).1.card * pc (R t).2.card (R t).1.card : ℕ) : ℝ) := by
    have h := sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin 25))) => colC p
    rw [← mul_sum, sum_sub_distrib, sum_add_distrib, ← mul_sum] at h
    rw [← swap_tp R (fun t => pc (R t).2.card (R t).1.card)]
    push_cast at h ⊢
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    push_cast at h
    linarith
  have rowS : (418110 : ℝ) ≤ ((∑ t, (R t).2.card * pr (R t).1.card : ℕ) : ℝ) := by
    have h := sum_le_sum fun l (_ : l ∈ (univ : Finset (Fin 30))) => rowC l
    rw [← mul_sum, sum_sub_distrib, sum_add_distrib, ← mul_sum] at h
    rw [sum_comm, sum_comm (f := fun p l => (nn R p l : ℝ) * W l p)] at tot
    rw [← swap_tl R (fun t => pr (R t).1.card)]
    push_cast at h ⊢
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    push_cast at h
    linarith
  have colN : 356800 ≤ ∑ t, (R t).1.card * pc (R t).2.card (R t).1.card := by exact_mod_cast colS
  have rowN : 418110 ≤ ∑ t, (R t).2.card * pr (R t).1.card := by exact_mod_cast rowS
  have up : 23 * (∑ t, (R t).1.card * pc (R t).2.card (R t).1.card) + 9 * (∑ t, (R t).2.card * pr (R t).1.card) ≤ k * 919621 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine (sum_le_sum fun t _ => (sh t).2.2).trans ?_
    simp
  have : k * 919621 ≤ 13 * 919621 := Nat.mul_le_mul_right _ hk
  omega

theorem final (L : List Box) (size : L.length ≤ 13) (good : ∀ r ∈ L, Good r)
    (covers : ∀ p l, inc p l = false → ∃ r ∈ L, p ∈ r.1 ∧ l ∈ r.2) : False := by
  classical
  let N := L.filter fun r => decide (r.1.Nonempty ∧ r.2.Nonempty)
  have memN : ∀ r, r ∈ N ↔ r ∈ L ∧ r.1.Nonempty ∧ r.2.Nonempty := fun r => by simp [N]
  refine main (k := N.length) ((List.length_filter_le _ L).trans size) (fun t => N.get t)
    (fun t => good _ ((memN _).mp (N.get_mem t)).1) (fun t => ((memN _).mp (N.get_mem t)).2.1)
    (fun t => ((memN _).mp (N.get_mem t)).2.2) ?_
  intro p l h
  obtain ⟨r, hr, hp, hl⟩ := covers p l h
  obtain ⟨t, ht⟩ := List.mem_iff_get.mp ((memN r).mpr ⟨hr, ⟨p, hp⟩, ⟨l, hl⟩⟩)
  exact ⟨t, by rw [ht]; exact ⟨hp, hl⟩⟩

end PEqualNP.Outside.L_meta_10024_aux

theorem PEqualNP.Outside.L_meta_10024 : (¬ (∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 13 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2)) := by
  rintro ⟨L, size, good, cover⟩
  exact PEqualNP.Outside.L_meta_10024_aux.final L size good cover
