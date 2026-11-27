import Mathlib
import PEqualNP.CircuitLowerBounds.Helpers.Lindsey

/-!
Helpers for L-clb-020: one linear threshold gate whose inputs are split in two halves has small
correlation with inner product modulo two. The accepting region of the gate is a "staircase"
(the accepted columns of the rows are nested), and a staircase with at most `2 ^ k` rows splits
into `k + 1` families of rectangles, each of which is controlled by Lindsey's lemma.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

/-- A finset has, for every `m` up to its size, a subset of `m` elements lying below the rest
with respect to an integer valued function. -/
theorem exists_lower_subset {α : Type*} [DecidableEq α] (f : α → ℤ) (S : Finset α) :
    ∀ m : ℕ, m ≤ S.card → ∃ S1 : Finset α, S1 ⊆ S ∧ S1.card = m ∧
      ∀ x1 ∈ S1, ∀ x2 ∈ S \ S1, f x1 ≤ f x2 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨∅, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨S1, hsub, hcard, hle⟩ := ih (by omega)
    have hne : (S \ S1).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
    obtain ⟨z, hz, hzmin⟩ := Finset.exists_min_image (S \ S1) f hne
    have hz' := Finset.mem_sdiff.mp hz
    refine ⟨insert z S1, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hz'.1 hsub
    · rw [Finset.card_insert_of_notMem hz'.2, hcard]
    · intro x1 hx1 x2 hx2
      have hx2' := Finset.mem_sdiff.mp hx2
      have hx2S : x2 ∈ S \ S1 :=
        Finset.mem_sdiff.mpr ⟨hx2'.1, fun h => hx2'.2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hx1 with rfl | h
      · exact hzmin x2 hx2S
      · exact hle x1 h x2 hx2S

/-- Cauchy-Schwarz for two square roots of products. -/
theorem sqrt_mul_add_sqrt_mul_le (p q r u : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hu : 0 ≤ u) :
    Real.sqrt (p * q) + Real.sqrt (r * u) ≤ Real.sqrt ((p + r) * (q + u)) := by
  apply Real.le_sqrt_of_sq_le
  have h1 : Real.sqrt (p * q) * Real.sqrt (r * u) = Real.sqrt (p * u) * Real.sqrt (r * q) := by
    rw [← Real.sqrt_mul (mul_nonneg hp hq), ← Real.sqrt_mul (mul_nonneg hp hu)]
    congr 1; ring
  have h2 := Real.sq_sqrt (mul_nonneg hp hq)
  have h3 := Real.sq_sqrt (mul_nonneg hr hu)
  have h4 := Real.sq_sqrt (mul_nonneg hp hu)
  have h5 := Real.sq_sqrt (mul_nonneg hr hq)
  nlinarith [sq_nonneg (Real.sqrt (p * u) - Real.sqrt (r * q))]

/-- Lindsey's lemma with a real square root. -/
theorem rect_bound (n : ℕ) (A B : Finset (Fin n → Bool)) :
    |((∑ x ∈ A, ∑ y ∈ B, ipSign n x y : ℤ) : ℝ)| ≤
      Real.sqrt ((2 : ℝ) ^ n * A.card * B.card) := by
  apply Real.abs_le_sqrt
  have h := lindsey n A B
  have h' : (((∑ x ∈ A, ∑ y ∈ B, ipSign n x y) ^ 2 : ℤ) : ℝ) ≤
      (((A.card : ℤ) * (B.card : ℤ) * 2 ^ n : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h' ⊢
  linarith

/-- The sum of the inner product sign over the part of `S × D` accepted by the gate
`t ≤ a x + b y`. -/
def stairSum (n : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ) (S D : Finset (Fin n → Bool)) : ℤ :=
  ∑ x ∈ S, ∑ y ∈ D, if t ≤ a x + b y then ipSign n x y else 0

open Classical in
/-- The staircase bound: with at most `2 ^ k` rows the sum is at most
`(k + 1) * sqrt (2 ^ n |S| |D|)`. -/
theorem stairSum_bound (n : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ) :
    ∀ k : ℕ, ∀ S D : Finset (Fin n → Bool), S.card ≤ 2 ^ k →
      |((stairSum n a b t S D : ℤ) : ℝ)| ≤
        ((k : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ n * S.card * D.card) := by
  intro k
  induction k with
  | zero =>
    intro S D hS
    have h1 : stairSum n a b t S D =
        ∑ x ∈ S, ∑ y ∈ D.filter (fun y => t ≤ a x + b y), ipSign n x y := by
      unfold stairSum
      exact Finset.sum_congr rfl (fun x _ => (Finset.sum_filter _ _).symm)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using hS) with h0 | h1'
    · rw [Finset.card_eq_zero.mp h0]
      simp [stairSum]
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1'
      rw [h1]
      have h2 := rect_bound n {x} (D.filter (fun y => t ≤ a x + b y))
      have h3 : Real.sqrt ((2 : ℝ) ^ n * (({x} : Finset (Fin n → Bool)).card : ℝ) *
            ((D.filter (fun y => t ≤ a x + b y)).card : ℝ)) ≤
          Real.sqrt ((2 : ℝ) ^ n * (({x} : Finset (Fin n → Bool)).card : ℝ) * (D.card : ℝ)) := by
        apply Real.sqrt_le_sqrt
        have : ((D.filter (fun y => t ≤ a x + b y)).card : ℝ) ≤ (D.card : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have h4 := h2.trans h3
      simpa using h4
  | succ k ih =>
    intro S D hS
    obtain ⟨S1, hsub, hcard, hle⟩ := exists_lower_subset a S (S.card / 2) (Nat.div_le_self _ _)
    have hc2 : (S \ S1).card = S.card - S.card / 2 := by
      rw [Finset.card_sdiff_of_subset hsub, hcard]
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    have hS1k : S1.card ≤ 2 ^ k := by omega
    have hS2k : (S \ S1).card ≤ 2 ^ k := by omega
    have hs : (S.card : ℝ) = (S1.card : ℝ) + ((S \ S1).card : ℝ) := by
      have : S.card = S1.card + (S \ S1).card := by omega
      exact_mod_cast this
    obtain ⟨E, hEdef⟩ : ∃ E : (Fin n → Bool) → Prop,
        ∀ y, E y ↔ ∀ x ∈ S \ S1, t ≤ a x + b y := ⟨_, fun _ => Iff.rfl⟩
    have hd : (D.card : ℝ) = ((D.filter E).card : ℝ) + ((D.filter (fun y => ¬ E y)).card : ℝ) := by
      have := Finset.card_filter_add_card_filter_not (s := D) E
      exact_mod_cast this.symm
    have hlow : stairSum n a b t S1 D = stairSum n a b t S1 (D.filter E) := by
      unfold stairSum
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hE : E y
      · simp [hE]
      · have : ¬ t ≤ a x + b y := by
          intro hxy
          apply hE
          rw [hEdef]
          intro x2 hx2
          have := hle x hx x2 hx2
          linarith
        simp [hE, this]
    have hupp : stairSum n a b t (S \ S1) D =
        stairSum n a b t (S \ S1) (D.filter (fun y => ¬ E y)) +
          ∑ x ∈ S \ S1, ∑ y ∈ D.filter E, ipSign n x y := by
      unfold stairSum
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hE : E y
      · have : t ≤ a x + b y := (hEdef y).mp hE x hx
        simp [hE, this]
      · simp [hE]
    have hsplit : stairSum n a b t S D = stairSum n a b t (S \ S1) D + stairSum n a b t S1 D := by
      unfold stairSum
      exact (Finset.sum_sdiff hsub).symm
    have b1 := ih S1 (D.filter E) hS1k
    have b2 := ih (S \ S1) (D.filter (fun y => ¬ E y)) hS2k
    have b3 := rect_bound n (S \ S1) (D.filter E)
    set N : ℝ := (2 : ℝ) ^ n with hN
    have hNpos : 0 ≤ N := by positivity
    set s1 : ℝ := (S1.card : ℝ) with hs1
    set s2 : ℝ := ((S \ S1).card : ℝ) with hs2
    set d1 : ℝ := ((D.filter E).card : ℝ) with hd1
    set d2 : ℝ := ((D.filter (fun y => ¬ E y)).card : ℝ) with hd2
    have hs1n : 0 ≤ s1 := by positivity
    have hs2n : 0 ≤ s2 := by positivity
    have hd1n : 0 ≤ d1 := by positivity
    have hd2n : 0 ≤ d2 := by positivity
    have hQ : Real.sqrt (N * s1 * d1) + Real.sqrt (N * s2 * d2) ≤
        Real.sqrt (N * (s1 + s2) * (d1 + d2)) := by
      have := sqrt_mul_add_sqrt_mul_le (N * s1) d1 (N * s2) d2 (by positivity) hd1n
        (by positivity) hd2n
      have e : (N * s1 + N * s2) * (d1 + d2) = N * (s1 + s2) * (d1 + d2) := by ring
      rwa [e] at this
    have hR : Real.sqrt (N * s2 * d1) ≤ Real.sqrt (N * (s1 + s2) * (d1 + d2)) := by
      apply Real.sqrt_le_sqrt
      have h1 : N * s2 * d1 ≤ N * (s1 + s2) * d1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hNpos) hd1n
      have h2 : N * (s1 + s2) * d1 ≤ N * (s1 + s2) * (d1 + d2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact h1.trans h2
    rw [hsplit, hupp, hlow, hs, hd]
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have tri := abs_add_three
      ((stairSum n a b t (S \ S1) (D.filter (fun y => ¬ E y)) : ℤ) : ℝ)
      ((∑ x ∈ S \ S1, ∑ y ∈ D.filter E, ipSign n x y : ℤ) : ℝ)
      ((stairSum n a b t S1 (D.filter E) : ℤ) : ℝ)
    push_cast at tri b3
    have hmul := mul_le_mul_of_nonneg_left hQ hk
    calc _ ≤ _ := tri
      _ ≤ ((k : ℝ) + 1) * Real.sqrt (N * s2 * d2) + Real.sqrt (N * s2 * d1) +
            ((k : ℝ) + 1) * Real.sqrt (N * s1 * d1) := by linarith
      _ ≤ ((k : ℝ) + 1 + 1) * Real.sqrt (N * (s1 + s2) * (d1 + d2)) := by linarith

/-- One linear threshold gate on split inputs against inner product modulo two. -/
theorem threshold_ip_bound (n : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ) :
    (∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t ≤ a x + b y then
        (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card
      else 0)) ^ 2 ≤ ((n : ℤ) + 1) ^ 2 * 2 ^ (3 * n) := by
  have h := stairSum_bound n a b t n univ univ (by simp)
  have hcard : ((univ : Finset (Fin n → Bool)).card : ℝ) = (2 : ℝ) ^ n := by simp
  rw [hcard] at h
  have hsq : Real.sqrt ((2 : ℝ) ^ n * 2 ^ n * 2 ^ n) ^ 2 = (2 : ℝ) ^ (3 * n) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have h2 : ((stairSum n a b t univ univ : ℤ) : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * 2 ^ (3 * n) := by
    rw [← hsq, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 : (stairSum n a b t univ univ) ^ 2 ≤ ((n : ℤ) + 1) ^ 2 * 2 ^ (3 * n) := by
    exact_mod_cast h2
  exact h3

end PEqualNP.CircuitLowerBounds.Helpers
