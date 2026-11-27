import Mathlib
import PEqualNP.CircuitLowerBounds.Helpers.Lindsey

/-!
Helpers for L-clb-019: the discriminator method for inner product modulo two.

A depth-two circuit whose top gate is a weighted threshold of total weight `C` and whose
bottom gates each have small correlation with the inner product sign matrix cannot compute
inner product modulo two.  The bottom gates considered here are comparisons
`t ≤ a x + b y`; when `a` takes at most `V` values such a gate splits into at most `V`
rectangles, and Lindsey's lemma bounds the correlation of each rectangle.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

/-- The total sum of the inner product sign matrix is `2 ^ n`. -/
theorem ipSign_total (n : ℕ) :
    ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, ipSign n x y = (2 : ℤ) ^ n := by
  have h1 : ∀ x : Fin n → Bool, ipSign n x (fun _ => false) = 1 := by
    intro x
    simp [ipSign]
  rw [Finset.sum_comm]
  have h2 : ∀ y : Fin n → Bool, ∑ x : Fin n → Bool, ipSign n x y =
      if y = (fun _ => false) then (2 : ℤ) ^ n else 0 := by
    intro y
    rw [← ipSign_orth n y (fun _ => false)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [h1, mul_one]
  simp_rw [h2]
  simp

/-- A weighted sum of zero-one values is bounded by the total weight. -/
theorem abs_weighted_le {m : ℕ} (c : Fin m → ℤ) (g : Fin m → ℤ)
    (hg : ∀ j, g j = 0 ∨ g j = 1) : |∑ j, c j * g j| ≤ ∑ j, |c j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rcases hg j with h | h <;> simp [h]

/-- Integer form of the discriminator inequality. -/
theorem discriminator_int (n m : ℕ) (c : Fin m → ℤ) (t0 : ℤ)
    (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ) (hn : 0 < n)
    (hip : ∀ x y : Fin n → Bool,
      (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔
        (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) :
    (2 : ℤ) ^ n * 2 ^ n ≤
      2 * (∑ j, |c j| *
        |∑ x, ∑ y, (if t j ≤ a j x + b j y then ipSign n x y else 0)|) +
      2 * (∑ j, |c j|) * 2 ^ n := by
  set C : ℤ := ∑ j, |c j| with hC
  set F : (Fin n → Bool) → (Fin n → Bool) → ℤ :=
    fun x y => ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0) with hF
  have hFabs : ∀ x y, |F x y| ≤ C := by
    intro x y
    refine abs_weighted_le c _ fun j => ?_
    by_cases h : t j ≤ a j x + b j y <;> simp [h]
  -- bounds on the top threshold
  have ht0_lo : -C + 1 ≤ t0 := by
    have h := hip (fun _ => false) (fun _ => false)
    have h' : ¬ t0 ≤ F (fun _ => false) (fun _ => false) := by
      rw [hF]; rw [h]; simp
    have := (abs_le.mp (hFabs (fun _ => false) (fun _ => false))).1
    omega
  have ht0_hi : t0 ≤ C := by
    let e : Fin n → Bool := fun i => decide (i = ⟨0, hn⟩)
    have h := hip e e
    have hcard : (Finset.univ.filter (fun i : Fin n => e i = true ∧ e i = true)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨⟨0, hn⟩, ?_⟩
      ext i
      simp [e]
    have h' : t0 ≤ F e e := by
      rw [hF]; rw [h, hcard]
    have := (abs_le.mp (hFabs e e)).2
    omega
  -- pointwise inequality
  have hpt : ∀ x y : Fin n → Bool, ipSign n x y * (2 * F x y - 2 * t0 + 1) ≤ -1 := by
    intro x y
    have h := hip x y
    by_cases hodd : (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1
    · have hs : ipSign n x y = -1 := by
        unfold ipSign
        exact Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
      have : t0 ≤ F x y := h.mpr hodd
      rw [hs]; linarith
    · have hs : ipSign n x y = 1 := by
        unfold ipSign
        exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
      have : ¬ t0 ≤ F x y := fun hh => hodd (h.mp hh)
      rw [hs]; omega
  have hsum : ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      ipSign n x y * (2 * F x y - 2 * t0 + 1) ≤ -((2 : ℤ) ^ n * 2 ^ n) := by
    have h1 : ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
        ipSign n x y * (2 * F x y - 2 * t0 + 1) ≤
        ∑ _x : Fin n → Bool, ∑ _y : Fin n → Bool, (-1 : ℤ) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
    refine h1.trans (le_of_eq ?_)
    simp
  -- expand the sum
  have hexp : ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      ipSign n x y * (2 * F x y - 2 * t0 + 1) =
      2 * (∑ j, c j * ∑ x, ∑ y, (if t j ≤ a j x + b j y then ipSign n x y else 0)) -
        (2 * t0 - 1) * 2 ^ n := by
    rw [← ipSign_total n]
    have h1 : ∀ x y : Fin n → Bool, ipSign n x y * (2 * F x y - 2 * t0 + 1) =
        2 * (∑ j, c j * (if t j ≤ a j x + b j y then ipSign n x y else 0)) -
          (2 * t0 - 1) * ipSign n x y := by
      intro x y
      have : ipSign n x y * F x y =
          ∑ j, c j * (if t j ≤ a j x + b j y then ipSign n x y else 0) := by
        rw [hF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : t j ≤ a j x + b j y <;> simp [h, mul_comm]
      rw [← this]; ring
    have hsw : ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
        ∑ j, c j * (if t j ≤ a j x + b j y then ipSign n x y else 0) =
        ∑ j, c j * ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
          (if t j ≤ a j x + b j y then ipSign n x y else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [← hsw]
    simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp] at hsum
  have h2 : -(∑ j, c j * ∑ x, ∑ y, (if t j ≤ a j x + b j y then ipSign n x y else 0)) ≤
      ∑ j, |c j| * |∑ x, ∑ y, (if t j ≤ a j x + b j y then ipSign n x y else 0)| := by
    refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
  have hN : (0 : ℤ) < 2 ^ n := by positivity
  have h3 : (2 * t0 - 1) * 2 ^ n ≤ 2 * C * 2 ^ n :=
    mul_le_mul_of_nonneg_right (by linarith) hN.le
  linarith

/-- The discriminator inequality: if every bottom gate has correlation at most `K` with the
inner product sign matrix, then `2 ^ n * 2 ^ n ≤ 2 C K + 2 C 2 ^ n` where `C` is the total
weight of the top gate. -/
theorem discriminator (n m : ℕ) (c : Fin m → ℤ) (t0 : ℤ)
    (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ) (hn : 0 < n)
    (hip : ∀ x y : Fin n → Bool,
      (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔
        (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1)
    (K : ℝ)
    (hK : ∀ j : Fin m, |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t j ≤ a j x + b j y then ipSign n x y else 0) : ℤ) : ℝ)| ≤ K) :
    (2 : ℝ) ^ n * 2 ^ n ≤
      2 * (∑ j : Fin m, |(c j : ℝ)|) * K + 2 * (∑ j : Fin m, |(c j : ℝ)|) * 2 ^ n := by
  have h := discriminator_int n m c t0 a b t hn hip
  have h' : ((2 : ℝ)) ^ n * 2 ^ n ≤
      2 * (∑ j, |(c j : ℝ)| *
        |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
          (if t j ≤ a j x + b j y then ipSign n x y else 0) : ℤ) : ℝ)|) +
      2 * (∑ j, |(c j : ℝ)|) * 2 ^ n := by
    have := (Int.cast_le (R := ℝ)).mpr h
    push_cast at this
    push_cast
    exact this
  have h2 : (∑ j, |(c j : ℝ)| *
        |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
          (if t j ≤ a j x + b j y then ipSign n x y else 0) : ℤ) : ℝ)|) ≤
      (∑ j, |(c j : ℝ)|) * K := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hK j) (abs_nonneg _)
  linarith

/-- A rectangle sum of the inner product sign matrix is at most `sqrt (2 ^ n) ^ 3`. -/
theorem rect_abs_le (n : ℕ) (A B : Finset (Fin n → Bool)) :
    |((∑ x ∈ A, ∑ y ∈ B, ipSign n x y : ℤ) : ℝ)| ≤ (Real.sqrt (2 ^ n)) ^ 3 := by
  have hA : (A.card : ℤ) ≤ 2 ^ n := by
    have := Finset.card_le_univ A
    simp at this
    exact_mod_cast this
  have hB : (B.card : ℤ) ≤ 2 ^ n := by
    have := Finset.card_le_univ B
    simp at this
    exact_mod_cast this
  have h1 : (∑ x ∈ A, ∑ y ∈ B, ipSign n x y) ^ 2 ≤ (2 : ℤ) ^ n * 2 ^ n * 2 ^ n := by
    refine (lindsey n A B).trans ?_
    have hN : (0 : ℤ) ≤ 2 ^ n := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hA hB (by positivity) hN) hN
  have h2 : ((∑ x ∈ A, ∑ y ∈ B, ipSign n x y : ℤ) : ℝ) ^ 2 ≤ (2 : ℝ) ^ n * 2 ^ n * 2 ^ n := by
    exact_mod_cast h1
  have hr : (Real.sqrt (2 ^ n)) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc ((∑ x ∈ A, ∑ y ∈ B, ipSign n x y : ℤ) : ℝ) ^ 2 ≤ (2 : ℝ) ^ n * 2 ^ n * 2 ^ n := h2
    _ = ((Real.sqrt (2 ^ n)) ^ 3) ^ 2 := by
        rw [show ((Real.sqrt (2 ^ n)) ^ 3) ^ 2 = ((Real.sqrt (2 ^ n)) ^ 2) ^ 3 by ring, hr]
        ring

/-- A comparison gate `t ≤ a x + b y` in which `a` takes at most `V` values has correlation
at most `V * sqrt (2 ^ n) ^ 3` with the inner product sign matrix. -/
theorem gate_rect_bound (n V : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ)
    (hV : (Finset.univ.image a).card ≤ V) :
    |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t ≤ a x + b y then ipSign n x y else 0) : ℤ) : ℝ)| ≤
      (V : ℝ) * (Real.sqrt (2 ^ n)) ^ 3 := by
  have hsplit : ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t ≤ a x + b y then ipSign n x y else 0) =
      ∑ v ∈ Finset.univ.image a, ∑ x ∈ Finset.univ.filter (fun x => a x = v),
        ∑ y ∈ Finset.univ.filter (fun y => t - v ≤ b y), ipSign n x y := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image a)
      (g := a) (fun x _ => Finset.mem_image_of_mem a (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun x hx => ?_
    have hxv : a x = v := (Finset.mem_filter.mp hx).2
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : (t ≤ a x + b y) ↔ (t - v ≤ b y) := by rw [hxv]; constructor <;> intro h <;> linarith
    simp only [this]
  rw [hsplit, Int.cast_sum]
  have hr : (0 : ℝ) ≤ (Real.sqrt (2 ^ n)) ^ 3 := by positivity
  calc |∑ v ∈ Finset.univ.image a, ((∑ x ∈ Finset.univ.filter (fun x => a x = v),
        ∑ y ∈ Finset.univ.filter (fun y => t - v ≤ b y), ipSign n x y : ℤ) : ℝ)|
      ≤ ∑ v ∈ Finset.univ.image a, |((∑ x ∈ Finset.univ.filter (fun x => a x = v),
        ∑ y ∈ Finset.univ.filter (fun y => t - v ≤ b y), ipSign n x y : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ Finset.univ.image a, (Real.sqrt (2 ^ n)) ^ 3 :=
        Finset.sum_le_sum fun v _ => rect_abs_le n _ _
    _ = ((Finset.univ.image a).card : ℝ) * (Real.sqrt (2 ^ n)) ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (V : ℝ) * (Real.sqrt (2 ^ n)) ^ 3 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hV) hr

/-- If every bottom gate has correlation at most `M * sqrt (2 ^ n) ^ 3` with the inner product
sign matrix, the total weight `C` of the top gate satisfies `2 ^ n ≤ (2 C (M + 1)) ^ 2`. -/
theorem ip_bound_of_gate_bound (n m M : ℕ) (c : Fin m → ℤ) (t0 : ℤ)
    (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ) (hn : 0 < n)
    (hip : ∀ x y : Fin n → Bool,
      (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔
        (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1)
    (hM : ∀ j : Fin m, |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t j ≤ a j x + b j y then ipSign n x y else 0) : ℤ) : ℝ)| ≤
        (M : ℝ) * (Real.sqrt (2 ^ n)) ^ 3) :
    (2 : ℤ) ^ n ≤ (2 * (∑ j : Fin m, |c j|) * ((M : ℤ) + 1)) ^ 2 := by
  have h := discriminator n m c t0 a b t hn hip _ hM
  set r : ℝ := Real.sqrt (2 ^ n) with hr
  set C : ℝ := ∑ j : Fin m, |(c j : ℝ)| with hC
  have hr2 : r ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hr1 : 1 ≤ r := by
    rw [hr, Real.one_le_sqrt]
    exact one_le_pow₀ (by norm_num)
  have hr0 : 0 < r := by linarith
  rw [← hr2] at h
  have h3 : r ^ 2 ≤ r ^ 3 := by
    have : r ^ 2 * 1 ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr1 (by positivity)
    calc r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r := this
      _ = r ^ 3 := by ring
  have h4 : r * r ^ 3 ≤ (2 * C * ((M : ℝ) + 1)) * r ^ 3 := by
    have : 2 * C * r ^ 2 ≤ 2 * C * r ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc r * r ^ 3 = r ^ 2 * r ^ 2 := by ring
      _ ≤ 2 * C * ((M : ℝ) * r ^ 3) + 2 * C * r ^ 2 := h
      _ ≤ 2 * C * ((M : ℝ) * r ^ 3) + 2 * C * r ^ 3 := by linarith
      _ = (2 * C * ((M : ℝ) + 1)) * r ^ 3 := by ring
  have h5 : r ≤ 2 * C * ((M : ℝ) + 1) := le_of_mul_le_mul_right h4 (by positivity)
  have h6 : (2 : ℝ) ^ n ≤ (2 * C * ((M : ℝ) + 1)) ^ 2 := by
    rw [← hr2]
    exact pow_le_pow_left₀ hr0.le h5 2
  have h7 : (((2 : ℤ) ^ n : ℤ) : ℝ) ≤
      (((2 * (∑ j : Fin m, |c j|) * ((M : ℤ) + 1)) ^ 2 : ℤ) : ℝ) := by
    push_cast
    exact h6
  exact_mod_cast h7

/-- STATEMENT of L-clb-019: a threshold of `m` comparison gates `t j ≤ a j x + b j y`, each
with `a j` taking at most `V` values, that computes inner product modulo two on `n + n` bits
has top weight `C` with `2 ^ n ≤ (2 C (V + 1)) ^ 2`. -/
theorem ip_rect_bound : ∀ (n m V : ℕ) (c : Fin m → ℤ) (t0 : ℤ)
    (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ), 0 < n →
    (∀ j : Fin m, (Finset.univ.image (a j)).card ≤ V) →
    (∀ x y : Fin n → Bool,
      (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔
        (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) →
    (2 : ℤ) ^ n ≤ (2 * (∑ j : Fin m, |c j|) * ((V : ℤ) + 1)) ^ 2 := by
  intro n m V c t0 a b t hn hV hip
  exact ip_bound_of_gate_bound n m V c t0 a b t hn hip
    (fun j => gate_rect_bound n V (a j) (b j) (t j) (hV j))

end PEqualNP.CircuitLowerBounds.Helpers
