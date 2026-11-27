import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10006

-- The area bound is adapted from the checked proof of L_meta_10002.
namespace Area

namespace Moments

open scoped BigOperators

abbrev Vertex := Fin 31

def rowDegree (I : Vertex → Vertex → Bool) : Prop :=
  ∀ p, (Finset.univ.filter fun l => I p l = true).card = 6

def uniqueJoin (I : Vertex → Vertex → Bool) : Prop :=
  ∀ p q, p ≠ q → (Finset.univ.filter fun l => I p l = true ∧ I q l = true).card = 1

def EmptyRectangle (I : Vertex → Vertex → Bool) (A B : Finset Vertex) : Prop :=
  ∀ p ∈ A, ∀ l ∈ B, I p l = false

def occupancy (I : Vertex → Vertex → Bool) (A : Finset Vertex) (l : Vertex) : ℕ :=
  (A.filter fun p => I p l = true).card

theorem first_moment (I : Vertex → Vertex → Bool) (A : Finset Vertex)
    (row : rowDegree I) : ∑ l : Vertex, occupancy I A l = 6*A.card := by
  unfold rowDegree at row
  simp only [occupancy, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ A, ∑ l : Vertex, if I p l = true then 1 else 0) =
      ∑ p ∈ A, (Finset.univ.filter fun l => I p l = true).card := by
        simp only [Finset.card_filter]
    _ = 6*A.card := by simp [row, Nat.mul_comm]

private theorem occupancy_square (I : Vertex → Vertex → Bool) (A : Finset Vertex) (l : Vertex) :
    (occupancy I A l)^2 =
      ∑ p ∈ A, ∑ q ∈ A, if I p l = true ∧ I q l = true then 1 else 0 := by
  simp only [occupancy, Finset.card_filter, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases e : I p l = true <;> by_cases f : I q l = true <;> simp [e,f]

theorem second_moment (I : Vertex → Vertex → Bool) (A : Finset Vertex)
    (row : rowDegree I) (joint : uniqueJoin I) :
    ∑ l : Vertex, (occupancy I A l)^2 = A.card*(A.card+5) := by
  have count (p q : Vertex) :
      (Finset.univ.filter fun l => I p l = true ∧ I q l = true).card =
        (if p = q then 6 else 1) := by
    by_cases e : p = q
    · subst q
      simpa using row p
    · simpa [e] using joint p q e
  have totals (p : Vertex) (hp : p ∈ A) :
      (∑ q ∈ A, if p = q then 6 else 1) = A.card+5 := by
    have summand (q : Vertex) : (if p = q then 6 else 1) = (if p = q then 5 else 0) + 1 := by
      split <;> rfl
    simp [summand, Finset.sum_add_distrib, hp, Nat.add_comm]
  simp only [occupancy_square]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ A, ∑ l : Vertex, ∑ q ∈ A, if I p l = true ∧ I q l = true then 1 else 0) =
      ∑ p ∈ A, ∑ q ∈ A, (if p = q then 6 else 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
        simp only [← Finset.card_filter, count]
    _ = ∑ _p ∈ A, (A.card+5) := Finset.sum_congr rfl totals
    _ = A.card*(A.card+5) := by simp

theorem occupancy_zero (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (rect : EmptyRectangle I A B) (l : Vertex) (hl : l ∈ B) : occupancy I A l = 0 := by
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_notMem.2
  intro p hp
  obtain ⟨hA,on⟩ := Finset.mem_filter.1 hp
  exact Bool.false_ne_true ((rect p hA l hl).symm.trans on)

theorem first_moment_off (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (row : rowDegree I) (rect : EmptyRectangle I A B) :
    ∑ l ∈ Finset.univ \ B, occupancy I A l = 6*A.card := by
  have zero : ∑ l ∈ B, occupancy I A l = 0 :=
    Finset.sum_eq_zero fun l hl => occupancy_zero I A B rect l hl
  have split := Finset.sum_sdiff (f := occupancy I A) (Finset.subset_univ B)
  rw [zero,add_zero] at split
  exact split.trans (first_moment I A row)

theorem second_moment_off (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (row : rowDegree I) (joint : uniqueJoin I) (rect : EmptyRectangle I A B) :
    ∑ l ∈ Finset.univ \ B, (occupancy I A l)^2 = A.card*(A.card+5) := by
  have zero : ∑ l ∈ B, (occupancy I A l)^2 = 0 :=
    Finset.sum_eq_zero fun l hl => by simp [occupancy_zero I A B rect l hl]
  have split := Finset.sum_sdiff (f := fun l => (occupancy I A l)^2) (Finset.subset_univ B)
  rw [zero,add_zero] at split
  exact split.trans (second_moment I A row joint)

private theorem discrete_square (r k : ℕ) : (2*k+1)*r ≤ r^2+k*(k+1) := by
  have z : 0 ≤ ((r : ℤ)-k)*((r : ℤ)-k-1) := by
    by_cases h : r ≤ k
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  exact_mod_cast (show (2*(k : ℤ)+1)*(r : ℤ) ≤ (r : ℤ)^2+k*(k+1) by nlinarith)

theorem convex_bound (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (row : rowDegree I) (joint : uniqueJoin I) (rect : EmptyRectangle I A B) (k : ℕ) :
    (2*k+1)*6*A.card ≤ A.card*(A.card+5)+k*(k+1)*(31-B.card) := by
  have lo : (∑ l ∈ Finset.univ \ B, (2*k+1)*occupancy I A l) ≤
      (∑ l ∈ Finset.univ \ B, ((occupancy I A l)^2+k*(k+1))) :=
    Finset.sum_le_sum fun l _ => discrete_square (occupancy I A l) k
  rw [← Finset.mul_sum, first_moment_off I A B row rect, Finset.sum_add_distrib,
    second_moment_off I A B row joint rect, Finset.sum_const, nsmul_eq_mul,
    Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin] at lo
  simpa only [Nat.cast_id, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lo

theorem cap_small (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (row : rowDegree I) (joint : uniqueJoin I) (rect : EmptyRectangle I A B) :
    (A.card = 1 → B.card ≤ 25) ∧
    (A.card = 2 → B.card ≤ 20) ∧
    (A.card = 3 → B.card ≤ 16) ∧
    (A.card = 4 → B.card ≤ 13) ∧
    (A.card = 5 → B.card ≤ 11) ∧
    (A.card = 6 → B.card ≤ 10) := by
  have bnd := convex_bound I A B row joint rect 1
  have cb : B.card ≤ 31 := by simpa using Finset.card_le_univ B
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> intro h <;> rw [h] at bnd <;> norm_num at bnd <;> omega

theorem no_nine_by_nine (I : Vertex → Vertex → Bool) (A B : Finset Vertex)
    (row : rowDegree I) (joint : uniqueJoin I) (rect : EmptyRectangle I A B) :
    A.card < 9 ∨ B.card < 9 := by
  by_contra! large
  obtain ⟨A',ha,ha'⟩ := Finset.exists_subset_card_eq large.1
  obtain ⟨B',hb,hb'⟩ := Finset.exists_subset_card_eq large.2
  have newRect : EmptyRectangle I A' B' := fun p hp l hl => rect p (ha hp) l (hb hl)
  have bound := convex_bound I A' B' row joint newRect 2
  rw [ha',hb'] at bound
  norm_num at bound

end Moments

namespace Large

open Finset
open scoped BigOperators

abbrev Place := Fin 31

def hit (I : Place → Place → Bool) (R : Finset Place) (l : Place) : ℕ :=
  (R.filter fun p => I p l = true).card

def tally (k : Place → ℕ) (j : ℕ) : ℕ := (univ.filter fun l => k l = j).card

private theorem sum_tally (k : Place → ℕ) (cap : ∀ l, k l ≤ 6) (f : ℕ → ℕ) :
    (∑ l, f (k l)) = ∑ j ∈ range 7, tally k j * f j := by
  have maps : (↑(univ : Finset Place) : Set Place).MapsTo k (↑(range 7) : Set ℕ) := by
    intro l _
    simpa using (show k l < 7 by have := cap l; omega)
  rw [← Finset.sum_fiberwise_of_maps_to maps]
  apply Finset.sum_congr rfl
  intro j hj
  unfold tally
  apply Finset.sum_const_nat
  intro l hl
  rw [(Finset.mem_filter.mp hl).2]

private theorem tally_constraints (k : Place → ℕ) (cap : ∀ l, k l ≤ 6) :
    tally k 0 + tally k 1 + tally k 2 + tally k 3 + tally k 4 + tally k 5 + tally k 6 = 31 ∧
    tally k 1 + 2 * tally k 2 + 3 * tally k 3 + 4 * tally k 4 + 5 * tally k 5 + 6 * tally k 6 = (∑ l, k l) ∧
    tally k 1 + 4 * tally k 2 + 9 * tally k 3 + 16 * tally k 4 + 25 * tally k 5 + 36 * tally k 6 = (∑ l, (k l)^2) := by
  have count := sum_tally k cap (fun _ => 1)
  have first := sum_tally k cap id
  have second := sum_tally k cap (fun j => j^2)
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one, id_eq,
    Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at count first second
  norm_num at count first second
  constructor
  · omega
  constructor <;> omega

private theorem seven_profile (k : Place → ℕ) (cap : ∀ l, k l ≤ 6)
    (first : ∑ l, k l = 42) (second : ∑ l, (k l)^2 = 84) (empty : 9 ≤ tally k 0) :
    tally k 5 = 0 ∧
    ((tally k 1 = 0 ∧ tally k 3 = 0) ∨ (tally k 1 = 3 ∧ tally k 3 = 1)) := by
  obtain ⟨a, b, c⟩ := tally_constraints k cap
  have t4 : tally k 4 = 0 := by omega
  have t5 : tally k 5 = 0 := by omega
  have t6 : tally k 6 = 0 := by omega
  have t3 : tally k 3 ≤ 1 := by omega
  by_cases zero : tally k 3 = 0 <;> omega

private theorem eight_profile (k : Place → ℕ) (cap : ∀ l, k l ≤ 6)
    (first : ∑ l, k l = 48) (second : ∑ l, (k l)^2 = 104) (empty : 8 ≤ tally k 0) :
    ((tally k 1 = 1 ∧ tally k 3 = 3 ∧ tally k 5 = 0) ∨
      (tally k 1 = 0 ∧ tally k 3 = 0 ∧ tally k 4 = 1 ∧ tally k 5 = 0 ∧ tally k 6 = 0)) := by
  obtain ⟨a, b, c⟩ := tally_constraints k cap
  have t5 : tally k 5 = 0 := by omega
  have t6 : tally k 6 = 0 := by omega
  have t4 : tally k 4 ≤ 1 := by omega
  by_cases zero : tally k 4 = 0 <;> omega

private theorem hit_swap (I : Place → Place → Bool) (A B : Finset Place) :
    (∑ l ∈ B, hit I A l) = ∑ p ∈ A, (B.filter fun l => I p l = true).card := by
  unfold hit
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

private theorem hit_through (I : Place → Place → Bool) (R : Finset Place) (p : Place)
    (rowDeg : ∀ q, (univ.filter fun l => I q l = true).card = 6)
    (commonLine : ∀ q q' : Place, q ≠ q' → (univ.filter fun l => I q l = true ∧ I q' l = true).card = 1) :
    (∑ l ∈ univ.filter (fun l => I p l = true), hit I R l) = R.card + if p ∈ R then 5 else 0 := by
  rw [hit_swap]
  have factor (q : Place) :
      (((univ.filter fun l => I p l = true).filter fun l => I q l = true).card) = 1 + if q = p then 5 else 0 := by
    by_cases h : q = p
    · subst q
      simpa [Finset.filter_filter, and_self] using rowDeg p
    · simpa [Finset.filter_filter, h] using commonLine p q (Ne.symm h)
  simp_rw [factor]
  rw [Finset.sum_add_distrib]
  simp

private theorem hit_cap (I : Place → Place → Bool) (R : Finset Place)
    (colDeg : ∀ q, (univ.filter fun p => I p q = true).card = 6) (l : Place) : hit I R l ≤ 6 := by
  rw [← colDeg l]
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.subset_univ R)

def oddLines (k : Place → ℕ) : Finset Place := univ.filter fun l => k l % 2 = 1

private theorem sum_mod_eq_odd_card (k : Place → ℕ) : (∑ l, k l % 2) = (oddLines k).card := by
  unfold oddLines
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  split <;> omega

private theorem odd_count (k : Place → ℕ) (cap : ∀ l, k l ≤ 6) :
    (oddLines k).card = tally k 1 + tally k 3 + tally k 5 := by
  have t := sum_tally k cap (fun n => n % 2)
  rw [← sum_mod_eq_odd_card, t]
  norm_num [Finset.sum_range_succ]

private theorem parity_through (I : Place → Place → Bool) (R : Finset Place) (p : Place)
    (rowDeg : ∀ q, (univ.filter fun l => I q l = true).card = 6)
    (commonLine : ∀ q q' : Place, q ≠ q' → (univ.filter fun l => I q l = true ∧ I q' l = true).card = 1) :
    ((oddLines (hit I R)).filter fun l => I p l = true).card % 2 =
      (R.card + if p ∈ R then 5 else 0) % 2 := by
  have total := hit_through I R p rowDeg commonLine
  rw [← total, Finset.sum_nat_mod]
  congr 1
  unfold oddLines
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases v : I p l = true
  · simp only [v, and_true, ite_true]
    split <;> omega
  · simp [v]

abbrev transpose (I : Place → Place → Bool) : Place → Place → Bool := fun r c => I c r

private theorem odd_transpose_eq (I : Place → Place → Bool) (R : Finset Place)
    (rowDeg : ∀ q, (univ.filter fun l => I q l = true).card = 6)
    (commonLine : ∀ q q' : Place, q ≠ q' → (univ.filter fun l => I q l = true ∧ I q' l = true).card = 1) :
    oddLines (hit (transpose I) (oddLines (hit I R))) = if R.card % 2 = 1 then Rᶜ else R := by
  ext p
  have h := parity_through I R p rowDeg commonLine
  change hit (transpose I) (oddLines (hit I R)) p % 2 = (R.card + if p ∈ R then 5 else 0) % 2 at h
  rw [oddLines, Finset.mem_filter, and_iff_right (Finset.mem_univ p), h]
  by_cases hp : p ∈ R <;> by_cases hr : R.card % 2 = 1 <;> simp [hp, hr] <;> omega

private theorem odd_lt_of_four (k : Place → ℕ) (first : ∑ p, k p = 24) (second : ∑ p, (k p)^2 = 36) :
    (oddLines k).card < 24 := by
  have each (p : Place) : k p % 2 ≤ k p := Nat.mod_le _ _
  have dom : (oddLines k).card ≤ 24 := by
    rw [← sum_mod_eq_odd_card, ← first]
    exact Finset.sum_le_sum (fun p _ => each p)
  by_contra fail
  have equal : (∑ p, k p % 2) = ∑ p, k p := by rw [sum_mod_eq_odd_card, first]; omega
  have equalEach := (Finset.sum_eq_sum_iff_of_le (fun p _ => each p)).mp equal
  have sq (p : Place) : (k p)^2 = k p := by
    have e := equalEach p (Finset.mem_univ _)
    have h : k p = 0 ∨ k p = 1 := by omega
    rcases h with zero | one
    · simp [zero]
    · simp [one]
  simp_rw [sq] at second
  omega

private theorem odd_ge_of_four (k : Place → ℕ) (first : ∑ p, k p = 24) (second : ∑ p, (k p)^2 = 36) :
    12 ≤ (oddLines k).card := by
  have each (p : Place) : 2 * k p ≤ (k p)^2 + k p % 2 := by
    by_cases h : 2 ≤ k p
    · rw [pow_two]
      exact Nat.le_add_right_of_le (Nat.mul_le_mul_right (k p) h)
    · have small : k p = 0 ∨ k p = 1 := by omega
      rcases small with zero | one
      · simp [zero]
      · simp [one]
  have all := Finset.sum_le_sum (s := (Finset.univ : Finset Place)) (fun p _ => each p)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, first, second, sum_mod_eq_odd_card] at all
  omega

abbrev transposeMoments (I : Place → Place → Bool) : Prop :=
  ∀ L : Finset Place, (∑ p, hit (transpose I) L p) = 6 * L.card ∧
    (∑ p, (hit (transpose I) L p)^2) = L.card * (L.card + 5)

-- Seven selected points in the order-five plane avoid at most eight lines.
theorem empty_le_eight_of_seven (I : Place → Place → Bool) (R : Finset Place)
    (rowDeg : ∀ q, (univ.filter fun l => I q l = true).card = 6)
    (colDeg : ∀ q, (univ.filter fun p => I p q = true).card = 6)
    (commonLine : ∀ q q' : Place, q ≠ q' → (univ.filter fun l => I q l = true ∧ I q' l = true).card = 1)
    (hr : R.card = 7) (first : (∑ l, hit I R l) = 6 * R.card)
    (second : (∑ l, (hit I R l)^2) = R.card * (R.card + 5))
    (tm : transposeMoments I) : tally (hit I R) 0 ≤ 8 := by
  by_contra tooMany
  have missing : 9 ≤ tally (hit I R) 0 := by omega
  have cap := hit_cap I R colDeg
  let L := oddLines (hit I R)
  have hL : L.card = 0 ∨ L.card = 4 := by
    rw [show L.card = tally (hit I R) 1 + tally (hit I R) 3 + tally (hit I R) 5 from odd_count _ cap]
    obtain ⟨five, profile⟩ := seven_profile _ cap (by simpa [hr] using first)
      (by simpa [hr] using second) missing
    rcases profile with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b, five]
  have transposeCard : (oddLines (hit (transpose I) L)).card = 24 := by
    have h := congrArg Finset.card (odd_transpose_eq I R rowDeg commonLine)
    norm_num [hr] at h
    simpa [L, Finset.card_compl, hr] using h
  rcases hL with zero | four
  · have Lempty : L = ∅ := Finset.card_eq_zero.mp zero
    simp [Lempty, oddLines, hit] at transposeCard
  · obtain ⟨a, b⟩ := tm L
    rw [four] at a b
    have below := odd_lt_of_four _ a b
    omega

-- Eight selected points in the order-five plane avoid at most seven lines.
theorem empty_le_seven_of_eight (I : Place → Place → Bool) (R : Finset Place)
    (rowDeg : ∀ q, (univ.filter fun l => I q l = true).card = 6)
    (colDeg : ∀ q, (univ.filter fun p => I p q = true).card = 6)
    (commonLine : ∀ q q' : Place, q ≠ q' → (univ.filter fun l => I q l = true ∧ I q' l = true).card = 1)
    (hr : R.card = 8) (first : (∑ l, hit I R l) = 6 * R.card)
    (second : (∑ l, (hit I R l)^2) = R.card * (R.card + 5))
    (tm : transposeMoments I) : tally (hit I R) 0 ≤ 7 := by
  by_contra tooMany
  have missing : 8 ≤ tally (hit I R) 0 := by omega
  have cap := hit_cap I R colDeg
  let L := oddLines (hit I R)
  have hL : L.card = 0 ∨ L.card = 4 := by
    rw [show L.card = tally (hit I R) 1 + tally (hit I R) 3 + tally (hit I R) 5 from odd_count _ cap]
    obtain ⟨a, b, c⟩ | ⟨a, b, _, c, _⟩ := eight_profile _ cap (by simpa [hr] using first)
      (by simpa [hr] using second) missing <;> simp [a, b, c]
  have transposeCard : (oddLines (hit (transpose I) L)).card = 8 := by
    have h := congrArg Finset.card (odd_transpose_eq I R rowDeg commonLine)
    norm_num [hr] at h
    simpa [L] using h
  rcases hL with zero | four
  · have Lempty : L = ∅ := Finset.card_eq_zero.mp zero
    simp [Lempty, oddLines, hit] at transposeCard
  · obtain ⟨a, b⟩ := tm L
    rw [four] at a b
    have above := odd_ge_of_four _ a b
    omega

end Large

def matrix : Fin 31 → Fin 31 → Bool := fun i j =>
  (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210,
    134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584,
    6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504,
    1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868,
    570949736] : List ℕ).getD i.val 0).testBit j.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem matrix_row_degree : ∀ p : Fin 31,
    (Finset.univ.filter fun l => matrix p l = true).card = 6 := by
  intro p
  fin_cases p <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem matrix_col_degree : ∀ l : Fin 31,
    (Finset.univ.filter fun p => matrix p l = true).card = 6 := by
  intro l
  fin_cases l <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem matrix_row_join : ∀ p q : Fin 31, p ≠ q →
    (Finset.univ.filter fun l => matrix p l = true ∧ matrix q l = true).card = 1 := by
  intro p
  fin_cases p <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem matrix_col_join : ∀ l m : Fin 31, l ≠ m →
    (Finset.univ.filter fun p => matrix p l = true ∧ matrix p m = true).card = 1 := by
  intro l
  fin_cases l <;> decide

-- Number of possible columns when the number of chosen rows is small.
def RowCaps (r c : ℕ) : Prop :=
  (r = 1 → c ≤ 25) ∧ (r = 2 → c ≤ 20) ∧ (r = 3 → c ≤ 16) ∧
  (r = 4 → c ≤ 13) ∧ (r = 5 → c ≤ 11) ∧ (r = 6 → c ≤ 10) ∧
  (r = 7 → c ≤ 8) ∧ (r = 8 → c ≤ 7)

private theorem small_side {r c : ℕ} (small : r ≤ 8) (caps : RowCaps r c) :
    r*c ≤ 60 ∧ (56 < r*c → r = 6 ∧ c = 10) := by
  rcases caps with ⟨c1,c2,c3,c4,c5,c6,c7,c8⟩
  interval_cases r
  · simp
  · have := c1 rfl; omega
  · have := c2 rfl; omega
  · have := c3 rfl; omega
  · have := c4 rfl; omega
  · have := c5 rfl; omega
  · have := c6 rfl; omega
  · have := c7 rfl; omega
  · have := c8 rfl; omega

-- Exchanging rows and columns preserves area. Only the two orientations of
-- the 6 by 10 shape can have area greater than 56.
theorem area_and_large_shapes {r c : ℕ} (minSide : r ≤ 8 ∨ c ≤ 8)
    (rows : RowCaps r c) (cols : RowCaps c r) :
    r*c ≤ 60 ∧ (56 < r*c → (r = 6 ∧ c = 10) ∨ (r = 10 ∧ c = 6)) := by
  rcases minSide with row | col
  · obtain ⟨bound,shape⟩ := small_side row rows
    exact ⟨bound,fun h => .inl (shape h)⟩
  · obtain ⟨bound,shape⟩ := small_side col cols
    rw [Nat.mul_comm] at bound shape
    exact ⟨bound,fun h => .inr (shape h).symm⟩

theorem area_le_60 {r c : ℕ} (minSide : r ≤ 8 ∨ c ≤ 8)
    (rows : RowCaps r c) (cols : RowCaps c r) : r*c ≤ 60 :=
  (area_and_large_shapes minSide rows cols).1

theorem area_le_56_of_odd_width {r c : ℕ} (minSide : r ≤ 8 ∨ c ≤ 8)
    (rows : RowCaps r c) (cols : RowCaps c r) (oddWidth : c % 2 = 1) :
    r*c ≤ 56 := by
  by_contra! large
  rcases (area_and_large_shapes minSide rows cols).2 large with ⟨_,h⟩ | ⟨_,h⟩ <;>
    rw [h] at oddWidth <;> contradiction

open scoped BigOperators
open PEqualNP.Outside.L_meta_10006.Area.Moments
open PEqualNP.Outside.L_meta_10006.Area.Large (hit tally transpose empty_le_eight_of_seven empty_le_seven_of_eight)

private theorem abstract_row_caps (I : Fin 31 → Fin 31 → Bool) (A B : Finset (Fin 31))
    (row : rowDegree I) (col : rowDegree (transpose I))
    (joint : uniqueJoin I) (jointCol : uniqueJoin (transpose I))
    (rect : EmptyRectangle I A B) : RowCaps A.card B.card := by
  obtain ⟨s1,s2,s3,s4,s5,s6⟩ := cap_small I A B row joint rect
  have zeros : B.card ≤ tally (hit I A) 0 := by
    apply Finset.card_le_card
    intro l lm
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ l,occupancy_zero I A B rect l lm⟩
  have first : ∑ l : Fin 31, hit I A l = 6*A.card := first_moment I A row
  have second : ∑ l : Fin 31, (hit I A l)^2 = A.card*(A.card+5) := second_moment I A row joint
  have transposed (L : Finset (Fin 31)) :
      (∑ p : Fin 31, hit (transpose I) L p = 6*L.card) ∧
      (∑ p : Fin 31, (hit (transpose I) L p)^2 = L.card*(L.card+5)) :=
    ⟨first_moment (transpose I) L col,second_moment (transpose I) L col jointCol⟩
  refine ⟨s1,s2,s3,s4,s5,s6,?_,?_⟩
  · intro h
    exact zeros.trans (empty_le_eight_of_seven I A row col joint h first second transposed)
  · intro h
    exact zeros.trans (empty_le_seven_of_eight I A row col joint h first second transposed)

private theorem matrix_caps (A B : Finset (Fin 31)) (rect : EmptyRectangle matrix A B) :
    (A.card ≤ 8 ∨ B.card ≤ 8) ∧ RowCaps A.card B.card ∧ RowCaps B.card A.card := by
  have reverse : EmptyRectangle (transpose matrix) B A :=
    fun l lm p pm => rect p pm l lm
  have minSide := no_nine_by_nine matrix A B matrix_row_degree matrix_row_join rect
  refine ⟨minSide.imp (fun h => by omega) (fun h => by omega),?_,?_⟩
  · exact abstract_row_caps matrix A B matrix_row_degree matrix_col_degree matrix_row_join matrix_col_join rect
  · exact abstract_row_caps (transpose matrix) B A matrix_col_degree matrix_row_degree matrix_col_join matrix_row_join reverse

theorem matrix_area_le_60 (A B : Finset (Fin 31))
    (rect : ∀ p ∈ A, ∀ l ∈ B, matrix p l = false) : A.card * B.card ≤ 60 := by
  obtain ⟨small,rs,cs⟩ := matrix_caps A B rect
  exact area_le_60 small rs cs
end Area

-- Reflection in the span of the rectangle row vectors fixes their total weight.
abbrev V := Fin 31
abbrev E := EuclideanSpace ℝ V
abbrev Box := Finset V × Finset V
noncomputable def basisVector (j : V) : E := EuclideanSpace.basisFun V ℝ j
theorem basis_apply (j k : V) : basisVector j k = if k=j then 1 else 0 := by
  simp [basisVector,EuclideanSpace.basisFun_apply,PiLp.single_apply,eq_comm]
theorem trace_reflect (K : Submodule ℝ E) :
    ∑ j : V, (K.reflection (basisVector j)) j = 2*(Module.finrank ℝ K : ℝ)-31 := by
  classical
  let P := K.orthogonalProjectionOnto.toLinearMap
  have comp : P.comp K.subtype = LinearMap.id := by
    ext x
    simp [P]
  have fe : K.reflection.toLinearEquiv.toLinearMap = (2:ℝ) • (K.subtype.comp P) - LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (2 : ℕ) • K.starProjection x - x = (2 : ℝ) • (K.orthogonalProjectionOnto x : E) - x
    rw [two_smul,two_smul]
    rfl
  have tr := LinearMap.trace_comp_comm' P K.subtype
  rw [comp,LinearMap.trace_id] at tr
  have diagon : ∀ (f : E →ₗ[ℝ] E), (∑ j : V, (f (basisVector j)) j) = LinearMap.trace ℝ E f := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun V ℝ).toBasis]
    simp [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,basisVector]
  change (∑ j : V, (K.reflection.toLinearEquiv.toLinearMap (basisVector j)) j) = _
  rw [diagon K.reflection.toLinearEquiv.toLinearMap,fe]
  simp [tr,LinearMap.trace_id]
-- The incidence vectors have norm eleven, and their column sums are the scaled basis.
open scoped BigOperators
abbrev matrix := Area.matrix
def zeros (j : V) := Finset.univ.filter (fun i => matrix i j = false)
def code (i j : V) : ℤ := if matrix i j then -4 else 1
noncomputable def q (i : V) : E := WithLp.toLp 2 (fun j => (code i j : ℝ))
theorem q_apply (i j : V) : q i j = (code i j : ℝ) := rfl
theorem norm_table : ∀ i : V, (∑ j : V, (code i j)^2) = 121 := by decide +kernel
set_option maxRecDepth 20000 in
theorem column_table : ∀ j k : V, ∑ i ∈ zeros j, code i k = if k=j then 25 else 0 := by decide +kernel
theorem count_table : ∀ j : V, (zeros j).card=25 := by decide +kernel
theorem norm_q (i : V) : ‖q i‖=11 := by
  rw [EuclideanSpace.norm_eq]
  have n : (∑ j : V, (q i j)^2) = (121:ℝ) := by
    simp only [q_apply]; exact_mod_cast norm_table i
  simp only [Real.norm_eq_abs,sq_abs]
  rw [n]; norm_num

noncomputable def ev (j : V) : E →ₗ[ℝ] ℝ := (EuclideanSpace.basisFun V ℝ).toBasis.coord j
theorem ev_apply (j : V) (v : E) : ev j v = v j := rfl
theorem column_sum (j : V) : ∑ i ∈ zeros j, q i = (25:ℝ) • basisVector j := by
  ext k
  change ev k (∑ i ∈ zeros j, q i) = ev k ((25:ℝ) • basisVector j)
  rw [map_sum,map_smul]
  simp only [ev_apply,q_apply,basis_apply,smul_eq_mul]
  split_ifs with eq
  · have t := column_table j k
    rw [if_pos eq] at t
    simp; exact_mod_cast t
  · have t := column_table j k
    rw [if_neg eq] at t
    simp; exact_mod_cast t

noncomputable def w (K : Submodule ℝ E) (i j : V) : ℝ := 11 - (K.reflection (q i)) j
theorem w_ge (K : Submodule ℝ E) (i j : V) : 0 ≤ w K i j := by
  have lt := PiLp.norm_apply_le (K.reflection (q i)) j
  rw [LinearIsometryEquiv.norm_map,norm_q,Real.norm_eq_abs] at lt
  exact sub_nonneg.mpr ((le_abs_self _).trans lt)

theorem w_column (K : Submodule ℝ E) (j : V) :
    ∑ i ∈ zeros j, w K i j = 275-25*(K.reflection (basisVector j)) j := by
  let linear := (ev j).comp K.reflection.toLinearEquiv.toLinearMap
  have col := congrArg linear (column_sum j)
  rw [map_sum,map_smul] at col
  change (∑ i ∈ zeros j, (K.reflection (q i)) j) = (25:ℝ) * (K.reflection (basisVector j)) j at col
  simp [w,Finset.sum_sub_distrib,count_table,col] <;> norm_num
theorem w_total (K : Submodule ℝ E) :
    ∑ j : V, ∑ i ∈ zeros j, w K i j = 9300-50*(Module.finrank ℝ K : ℝ) := by
  simp_rw [w_column]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,trace_reflect]
  simp; ring
-- Each rectangle pays ten times its area. Covering all zero entries pays at least
-- 9300 minus fifty times the dimension of the span.
open scoped BigOperators
noncomputable def rowVector (R : Box) := ∑ i ∈ R.1, q i
noncomputable def boxCharge (K : Submodule ℝ E) (R : Box) : ℝ :=
  ∑ j ∈ R.2, ∑ i ∈ R.1, w K i j
def plain (R : Box) := ∀ i∈R.1, ∀ j∈R.2, matrix i j=false

theorem charge_eq (K : Submodule ℝ E) (R : Box) (hr : rowVector R∈K) (good : plain R) :
    boxCharge K R = 10*(R.1.card:ℝ)*(R.2.card:ℝ) := by
  classical
  have part (j : V) (hj : j∈R.2) : ∑ i ∈ R.1, w K i j = 10*(R.1.card:ℝ) := by
    have hx := congrArg (ev j) (K.reflection_mem_subspace_eq_self hr)
    simp only [rowVector,map_sum] at hx
    change ∑ i ∈ R.1, (K.reflection (q i)) j = ∑ i ∈ R.1, q i j at hx
    have units : ∑ i ∈ R.1, q i j = R.1.card := by
      calc
        _ = ∑ _i ∈ R.1, (1:ℝ) := Finset.sum_congr rfl (fun i hi => by simp [q_apply,code,good i hi j hj])
        _ = _ := by simp
    unfold w; rw [Finset.sum_sub_distrib,hx,units]; simp; ring
  unfold boxCharge
  rw [Finset.sum_congr rfl part]
  simp; ring

noncomputable def cellCharge (K : Submodule ℝ E) (R : Box) (i j : V) : ℝ :=
  if i∈R.1 ∧ j∈R.2 then w K i j else 0

theorem cc_nonneg (K : Submodule ℝ E) (R : Box) (i j : V) : 0≤cellCharge K R i j := by
  unfold cellCharge; split <;> simp [w_ge]
theorem cc_total (K : Submodule ℝ E) (R : Box) :
    ∑ j : V, ∑ i : V, cellCharge K R i j = boxCharge K R := by
  classical
  have col (j : V) : (∑ i : V, cellCharge K R i j) =
      if j∈R.2 then ∑ i ∈ R.1, w K i j else 0 := by
    by_cases hj : j∈R.2
    · simp [cellCharge,hj,← Finset.sum_filter]
    · simp [cellCharge,hj]
  simp only [col,← Finset.sum_filter]
  simp [boxCharge]

theorem cover_charge {k : ℕ} (K : Submodule ℝ E) (R : Fin k → Box)
    (covers : ∀ i j, matrix i j=false → ∃ t, i∈(R t).1 ∧ j∈(R t).2) :
    (∑ j : V, ∑ i ∈ zeros j, w K i j) ≤ ∑ t, boxCharge K (R t) := by
  classical
  have single (i j : V) (h : i∈zeros j) : w K i j ≤ ∑ t, cellCharge K (R t) i j := by
    obtain ⟨t, ht⟩ := covers i j (Finset.mem_filter.mp h).2
    have le := Finset.single_le_sum (f:=fun s : Fin k => cellCharge K (R s) i j)
      (fun s _ => cc_nonneg K (R s) i j) (Finset.mem_univ t)
    simpa [cellCharge,ht] using le
  have byCol (j : V) : ∑ i ∈ zeros j, w K i j ≤ ∑ t, ∑ i : V, cellCharge K (R t) i j := by
    calc
      _ ≤ ∑ i ∈ zeros j, ∑ t, cellCharge K (R t) i j := Finset.sum_le_sum (fun i hi => single i j hi)
      _ = ∑ t, ∑ i ∈ zeros j, cellCharge K (R t) i j := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum (fun t _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => cc_nonneg K (R t) i j))
  calc
    _ ≤ ∑ j : V, ∑ t, ∑ i : V, cellCharge K (R t) i j := Finset.sum_le_sum (fun j _ => byCol j)
    _ = ∑ t, ∑ j : V, ∑ i : V, cellCharge K (R t) i j := Finset.sum_comm
    _ = _ := by simp only [cc_total]

theorem area_lower {k : ℕ} (R : Fin k → Box) (allgood : ∀ t, plain (R t))
    (covers : ∀ i j, matrix i j=false → ∃ t, i∈(R t).1 ∧ j∈(R t).2) :
    930 ≤ 5*k + ∑ t, (R t).1.card * (R t).2.card := by
  classical
  let K := Submodule.span ℝ (Set.range (fun t => rowVector (R t)))
  have dim : Module.finrank ℝ K ≤ k := by
    simpa [K, Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t => rowVector (R t)))
  have ch (t : Fin k) := charge_eq K (R t) (Submodule.subset_span (Set.mem_range_self t)) (allgood t)
  have cover := cover_charge K R covers
  simp only [w_total,ch,mul_assoc,← Finset.mul_sum] at cover
  have dk : (Module.finrank ℝ K:ℝ) ≤ k := by exact_mod_cast dim
  have res : (930:ℝ) ≤ 5 * (k:ℝ) + ∑ t, ((R t).1.card:ℝ) * (R t).2.card := by linarith
  exact_mod_cast res

theorem at_least_fifteen {k : ℕ} (R : Fin k → Box) (allgood : ∀ t, plain (R t))
    (covers : ∀ i j, matrix i j=false → ∃ t, i∈(R t).1 ∧ j∈(R t).2) : 15 ≤ k := by
  have low := area_lower R allgood covers
  have high : ∑ t, (R t).1.card * (R t).2.card ≤ ∑ _t : Fin k, 60 :=
    Finset.sum_le_sum (fun t _ => Area.matrix_area_le_60 _ _ (allgood t))
  simp at high; omega

open scoped RealInnerProductSpace

def zeroEntry (M : V → V → Bool) (i j : V) : ℕ := if M i j then 0 else 1

def multiplicity {k : ℕ} (R : Fin k → Box) (i j : V) : ℕ :=
  (Finset.univ.filter fun t => i ∈ (R t).1 ∧ j ∈ (R t).2).card

def extra (M : V → V → Bool) {k : ℕ} (R : Fin k → Box) (i j : V) : ℕ :=
  multiplicity R i j - zeroEntry M i j

def load (M : V → V → Bool) {k : ℕ} (R : Fin k → Box) (j : V) : ℕ :=
  ∑ i, extra M R i j

def squares (M : V → V → Bool) {k : ℕ} (R : Fin k → Box) (j : V) : ℕ :=
  ∑ i, (extra M R i j)^2

noncomputable def signedRow (c : V → V → ℤ) (i : V) : E :=
  WithLp.toLp 2 (fun j => (c i j : ℝ))

theorem signedRow_apply (c : V → V → ℤ) (i j : V) : signedRow c i j = c i j := rfl

theorem basis_inner (j : V) (x : E) : ⟪basisVector j, x⟫ = x j := by
  simp [basisVector, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem trace_projection (K : Submodule ℝ E) :
    ∑ j : V, (K.starProjection (basisVector j)) j = Module.finrank ℝ K := by
  classical
  have h := trace_reflect K
  have entry (j : V) : (K.reflection (basisVector j)) j =
      2 * (K.starProjection (basisVector j)) j - 1 := by
    rw [K.reflection_apply]
    simp [PiLp.sub_apply, PiLp.smul_apply, basis_apply, nsmul_eq_mul]
  simp_rw [entry] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  norm_num at h
  linarith

theorem coord_sq_le (K : Submodule ℝ E) (j : V) {x : E} (hx : x ∈ K) :
    (x j)^2 ≤ (K.starProjection (basisVector j)) j * ‖x‖^2 := by
  let b := basisVector j
  have eq : x j = ⟪K.starProjection b, x⟫ := by
    have h := K.starProjection_inner_eq_zero b x hx
    rwa [inner_sub_left, sub_eq_zero, show ⟪b, x⟫ = x j from basis_inner j x] at h
  have diag : ‖K.starProjection b‖^2 = (K.starProjection b) j := by
    have h := K.starProjection_inner_eq_zero b (K.starProjection b) (K.starProjection_apply_mem b)
    rw [inner_sub_left, sub_eq_zero, real_inner_self_eq_norm_sq,
        show ⟪b, K.starProjection b⟫ = (K.starProjection b) j from basis_inner j _] at h
    exact h.symm
  calc
    (x j)^2 = |⟪K.starProjection b, x⟫|^2 := by rw [sq_abs, ← eq]
    _ ≤ (‖K.starProjection b‖ * ‖x‖)^2 := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = _ := by rw [mul_pow, diag]

theorem signed_inner (c : V → V → ℤ)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 121 else -4) (i i' : V) :
    ⟪signedRow c i, signedRow c i'⟫ = if i = i' then 121 else -4 := by
  simp only [PiLp.inner_apply, Real.inner_apply, signedRow_apply]
  by_cases equal : i = i' <;> simp only [equal, ↓reduceIte] <;>
    exact_mod_cast (by simpa [equal] using gram i i')

theorem signed_sum_sq (c : V → V → ℤ)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 121 else -4) (f : V → ℝ) :
    ‖∑ i, f i • signedRow c i‖ ^ 2 = 125 * ∑ i, (f i)^2 - 4 * (∑ i, f i)^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, signed_inner c gram]
  have term (i i' : V) :
      f i * (f i' * (if i = i' then 121 else -4)) =
        (if i = i' then 125 * (f i)^2 else 0) - 4 * (f i * f i') := by
    by_cases e : i = i'
    · subst i'; simp; ring
    · simp [e]; ring
  simp_rw [term, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  have eq : (∑ i : V, ∑ j : V, 4 * (f i * f j)) = 4 * (∑ i, f i)^2 := by
    calc
      _ = ∑ i : V, 4 * (f i * ∑ j : V, f j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [eq]

theorem multiplicity_eq {k : ℕ} (M : V → V → Bool) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) (i j : V) :
    multiplicity R i j = zeroEntry M i j + extra M R i j := by
  by_cases z : M i j = false
  · obtain ⟨t, hi, hj⟩ := covers i j z
    have p : 0 < multiplicity R i j := by
      apply Finset.card_pos.mpr
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hi, hj⟩⟩
    have h : zeroEntry M i j = 1 := by simp [zeroEntry,z]
    unfold extra
    omega
  · have m : M i j = true := Bool.eq_true_of_ne_false z
    simp [zeroEntry,m,extra]

theorem extra_eq_zero_of_incident {k : ℕ} (M : V → V → Bool) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    {i j : V} (h : M i j = true) : extra M R i j = 0 := by
  have em : (Finset.univ.filter fun t => i ∈ (R t).1 ∧ j ∈ (R t).2) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨_, hi, hj⟩ := Finset.mem_filter.mp ht
    exact Bool.false_ne_true ((good t i hi j hj).symm.trans h)
  simp [extra, multiplicity, em]

noncomputable def columnWitness {k : ℕ} (c : V → V → ℤ) (R : Fin k → Box) (j : V) : E :=
  ∑ i, (multiplicity R i j : ℝ) • signedRow c i

theorem columnWitness_mem {k : ℕ} (c : V → V → ℤ) (R : Fin k → Box) (j : V) :
    columnWitness c R j ∈
      Submodule.span ℝ (Set.range fun t => ∑ i ∈ (R t).1, signedRow c i) := by
  classical
  let K := Submodule.span ℝ (Set.range fun t => ∑ i ∈ (R t).1, signedRow c i)
  have repr : columnWitness c R j = ∑ t : Fin k, if j ∈ (R t).2 then
      ∑ i ∈ (R t).1, signedRow c i else 0 := by
    unfold columnWitness
    simp only [multiplicity, Finset.card_filter, Nat.cast_sum, Finset.sum_smul, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : j ∈ (R t).2
    · simp [h, Finset.sum_filter]
    · simp [h]
  rw [repr]
  change (∑ t : Fin k, if j ∈ (R t).2 then ∑ i ∈ (R t).1, signedRow c i else 0) ∈ K
  apply Submodule.sum_mem
  intro t ht
  split
  · exact Submodule.subset_span (Set.mem_range_self t)
  · exact K.zero_mem

theorem zeroEntry_sum_sq (M : V → V → Bool)
    (count : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25) (j : V) :
    (∑ i, zeroEntry M i j) = 25 ∧ (∑ i, (zeroEntry M i j)^2) = 25 := by
  have val (i : V) : zeroEntry M i j = if M i j = false then 1 else 0 := by
    cases h : M i j <;> simp [zeroEntry,h]
  constructor
  · simpa only [val, ← Finset.card_filter] using count j
  · calc
      (∑ i, (zeroEntry M i j)^2) = ∑ i, zeroEntry M i j := by
        apply Finset.sum_congr rfl
        intro i _
        cases h : M i j <;> simp [zeroEntry,h]
      _ = 25 := by simpa only [val, ← Finset.card_filter] using count j

theorem column_stats {k : ℕ} (M : V → V → Bool) (c : V → V → ℤ) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (count : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25)
    (ones : ∀ i j, M i j = false → c i j = 1)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 121 else -4)
    (j : V) :
    columnWitness c R j j = 25 + load M R j ∧
      ‖columnWitness c R j‖^2 = (25 + (load M R j : ℝ))^2 +
        125 * squares M R j - 5 * (load M R j : ℝ)^2 := by
  obtain ⟨zsum, zsq⟩ := zeroEntry_sum_sq M count j
  have sumM : (∑ i, (multiplicity R i j : ℝ)) = 25 + load M R j := by
    unfold load
    simp_rw [multiplicity_eq M R good covers, Nat.cast_add, Finset.sum_add_distrib]
    exact_mod_cast congrArg (· + ∑ i, extra M R i j) zsum
  have incidents (i : V) (h : M i j = true) : multiplicity R i j = 0 := by
    rw [multiplicity_eq M R good covers, extra_eq_zero_of_incident M R good h]
    simp [zeroEntry,h]
  constructor
  · unfold columnWitness
    change ev j (∑ i, (multiplicity R i j : ℝ) • signedRow c i) = _
    rw [map_sum, ← sumM]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, ev_apply, signedRow_apply]
    cases h : M i j
    · simp [ones i j h]
    · simp [incidents i h]
  · unfold columnWitness
    rw [signed_sum_sq c gram, sumM]
    have squaresM : (∑ i, (multiplicity R i j : ℝ)^2) =
        25 + 2 * load M R j + squares M R j := by
      have val (i : V) : (multiplicity R i j : ℝ)^2 =
          (zeroEntry M i j : ℝ)^2 + 2 * extra M R i j + (extra M R i j : ℝ)^2 := by
        rw [multiplicity_eq M R good covers, Nat.cast_add]
        cases h : M i j
        · simp [zeroEntry,h]; ring
        · simp [zeroEntry,h, extra_eq_zero_of_incident M R good h]
      simp_rw [val, Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold load squares
      push_cast
      have f : (∑ i, (zeroEntry M i j : ℝ)^2) = 25 := by exact_mod_cast zsq
      rw [f]
    rw [squaresM]
    ring

noncomputable def projectionLoss (d u : ℕ) : ℝ :=
  1 - (25 + (d : ℝ))^2 / ((25 + (d : ℝ))^2 + 125 * u - 5 * (d : ℝ)^2)

theorem sum_loss_ge {k : ℕ} (M : V → V → Bool) (c : V → V → ℤ) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (count : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25)
    (ones : ∀ i j, M i j = false → c i j = 1)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 121 else -4) :
    (31 : ℝ) - k ≤ ∑ j : V, projectionLoss (load M R j) (squares M R j) := by
  classical
  let K := Submodule.span ℝ (Set.range fun t => ∑ i ∈ (R t).1, signedRow c i)
  have dim : Module.finrank ℝ K ≤ k := by
    simpa [K,Set.finrank] using
      (finrank_range_le_card (R:=ℝ) (fun t : Fin k => ∑ i ∈ (R t).1, signedRow c i))
  have diag (j : V) : 1 - (K.starProjection (basisVector j)) j ≤
      projectionLoss (load M R j) (squares M R j) := by
    obtain ⟨coord, normsq⟩ := column_stats M c R good covers count ones gram j
    have nonzero : columnWitness c R j ≠ 0 := by
      intro eq
      rw [eq] at coord
      change (0 : ℝ) = 25 + load M R j at coord
      have le : (0 : ℝ) ≤ load M R j := Nat.cast_nonneg _
      linarith
    have p : 0 < ‖columnWitness c R j‖^2 := by positivity
    have h := coord_sq_le K j (columnWitness_mem c R j)
    have z := (div_le_iff₀ p).2 h
    rw [coord, normsq] at z
    unfold projectionLoss
    linarith
  have sum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => diag j)
  rw [Finset.sum_sub_distrib, trace_projection] at sum
  norm_num at sum
  have dc : (Module.finrank ℝ K : ℝ) ≤ k := by exact_mod_cast dim
  linarith


def transposeMatrix (M : V → V → Bool) (j i : V) : Bool := M i j
def transposeBox (R : Box) : Box := (R.2, R.1)

def lineNeighbors (M : V → V → Bool) (i : V) : Finset V :=
  Finset.univ.filter fun j => M i j = true

def rectClosed (M : V → V → Bool) (R : Box) : Prop :=
  (∀ i, i ∈ R.1 ↔ ∀ j ∈ R.2, M i j = false) ∧
  (∀ j, j ∈ R.2 ↔ ∀ i ∈ R.1, M i j = false)

def closeBox (M : V → V → Bool) (R : Box) : Box :=
  let A := Finset.univ.filter fun i => ∀ j ∈ R.2, M i j = false
  let B := Finset.univ.filter fun j => ∀ i ∈ A, M i j = false
  (A, B)

theorem closeBox_right (M : V → V → Bool) (R : Box) : R.2 ⊆ (closeBox M R).2 := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ j, fun i hi => ?_⟩
  exact (Finset.mem_filter.mp hi).2 j hj

theorem closeBox_left (M : V → V → Bool) (R : Box)
    (h : Area.Moments.EmptyRectangle M R.1 R.2) : R.1 ⊆ (closeBox M R).1 := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j hj => h i hi j hj⟩

theorem closeBox_closed (M : V → V → Bool) (R : Box) : rectClosed M (closeBox M R) := by
  constructor
  · intro i
    constructor
    · intro hi j hj
      exact (Finset.mem_filter.mp hj).2 i hi
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j hj => h j (closeBox_right M R hj)⟩
  · intro j
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩⟩

theorem unique_neighbor {M : V → V → Bool} (join : Area.Moments.uniqueJoin M)
    {p q : V} (neq : p ≠ q) :
    ∃ l, ∀ j, (M p j = true ∧ M q j = true) ↔ j = l := by
  obtain ⟨l, eq⟩ := Finset.card_eq_one.mp (join p q neq)
  refine ⟨l, fun j => ?_⟩
  have h := congrArg (fun s : Finset V => j ∈ s) eq
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using iff_of_eq h

theorem line_union_card {M : V → V → Bool} (deg : Area.Moments.rowDegree M)
    (join : Area.Moments.uniqueJoin M) (A : Finset V) (nonempty : A.Nonempty)
    (l : V) (onLine : ∀ p ∈ A, M p l = true) :
    ((A.biUnion (lineNeighbors M))).card = 1 + 5 * A.card := by
  classical
  let pencil (p : V) := (lineNeighbors M p).erase l
  have disj : (A : Set V).PairwiseDisjoint pencil := by
    intro i hi j hj neq
    apply Finset.disjoint_left.mpr
    intro m hmi hmj
    have hmi' := Finset.mem_erase.mp hmi
    have hmj' := Finset.mem_erase.mp hmj
    have yesI : M i m = true := (Finset.mem_filter.mp hmi'.2).2
    have yesJ : M j m = true := (Finset.mem_filter.mp hmj'.2).2
    obtain ⟨w, hw⟩ := unique_neighbor join neq
    exact hmi'.1 ((hw m).mp ⟨yesI,yesJ⟩ |>.trans ((hw l).mp ⟨onLine i hi,onLine j hj⟩).symm)
  have eq : (A.biUnion (lineNeighbors M)) = insert l (A.biUnion pencil) := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
      by_cases e : j = l
      · simp [e]
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_erase.mpr ⟨e,hj⟩⟩)
    · intro hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · obtain ⟨p,hp⟩ := nonempty
        exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,onLine p hp⟩⟩
      · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
        exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_of_mem_erase hj⟩
  have no : l ∉ A.biUnion pencil := by
    intro h
    obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_erase.mp hm).1 rfl
  rw [eq,Finset.card_insert_of_notMem no, Finset.card_biUnion disj]
  have f (p : V) (hp : p ∈ A) : (pencil p).card = 5 := by
    have lm : l ∈ lineNeighbors M p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ l,onLine p hp⟩
    simp only [pencil,Finset.card_erase_of_mem lm]
    exact congrArg (· - 1) (deg p)
  rw [Finset.sum_congr rfl f]
  simp [Nat.mul_comm,Nat.add_comm]

theorem collinear_closed_width {M : V → V → Bool} (deg : Area.Moments.rowDegree M)
    (join : Area.Moments.uniqueJoin M) (R : Box) (closed : rectClosed M R)
    (nonempty : R.1.Nonempty) (l : V) (onLine : ∀ p ∈ R.1, M p l = true) :
    R.2.card = 30 - 5 * R.1.card := by
  let incident := R.1.biUnion (lineNeighbors M)
  have equal : R.2 = Finset.univ \ incident := by
    ext j
    rw [closed.2 j]
    constructor
    · intro h
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ j, fun hj => ?_⟩
      obtain ⟨i,hi,ij⟩ := Finset.mem_biUnion.mp hj
      exact Bool.false_ne_true ((h i hi).symm.trans (Finset.mem_filter.mp ij).2)
    · intro h i hi
      apply Bool.eq_false_of_ne_true
      intro ij
      exact (Finset.mem_sdiff.mp h).2
        (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ j,ij⟩⟩)
  rw [equal, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,Fintype.card_fin]
  change 31 - ((R.1.biUnion (lineNeighbors M))).card = _
  rw [line_union_card deg join _ nonempty l onLine]
  omega

def rowSupport {k : ℕ} (R : Fin k → Box) (p : V) : Finset (Fin k) :=
  Finset.univ.filter fun t => p ∈ (R t).1

def colSupport {k : ℕ} (R : Fin k → Box) (j : V) : Finset (Fin k) :=
  Finset.univ.filter fun t => j ∈ (R t).2

theorem support_inter_card {k : ℕ} (R : Fin k → Box) (p j : V) :
    ((rowSupport R p) ∩ (colSupport R j)).card = multiplicity R p j := by
  unfold multiplicity rowSupport colSupport
  congr 1
  ext t
  simp

def badShape (a b : ℕ) : Prop := 1 ≤ a ∧ a ≤ 5 ∧ b = 30 - 5*a

def badVertex {k : ℕ} (R : Fin k → Box) (p : V) : Prop :=
  ∃ t ∈ rowSupport R p, badShape (R t).1.card (R t).2.card

theorem directed_diff {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (deg : Area.Moments.rowDegree M) (coldeg : Area.Moments.rowDegree (transposeMatrix M))
    (join : Area.Moments.uniqueJoin M) (closed : ∀ t, rectClosed M (R t))
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    {p q : V} (neq : p ≠ q) :
    1 ≤ (rowSupport R p \ rowSupport R q).card ∧
      (¬ badVertex R p → 2 ≤ (rowSupport R p \ rowSupport R q).card) := by
  classical
  obtain ⟨l, hl⟩ := unique_neighbor join neq
  have ql : M q l = true := ((hl l).mpr rfl).2
  let T := (lineNeighbors M q).erase l
  have size : T.card = 5 := by
    have lm : l ∈ lineNeighbors M q := Finset.mem_filter.mpr ⟨Finset.mem_univ l,ql⟩
    simp only [T,Finset.card_erase_of_mem lm]
    exact congrArg (· - 1) (deg q)
  have avoid (j : V) (hj : j ∈ T) : M p j = false ∧ M q j = true := by
    obtain ⟨noteq,hq⟩ := Finset.mem_erase.mp hj
    have qj : M q j = true := (Finset.mem_filter.mp hq).2
    refine ⟨Bool.eq_false_of_ne_true (fun hp => noteq ((hl j).mp ⟨hp,qj⟩)),qj⟩
  let S := rowSupport R p \ rowSupport R q
  have coverT (j : V) (hj : j ∈ T) : ∃ t ∈ S, j ∈ (R t).2 := by
    obtain ⟨pj,qj⟩ := avoid j hj
    obtain ⟨t,pt,jt⟩ := covers p j pj
    have qt : q ∉ (R t).1 := fun z => Bool.false_ne_true (((closed t).1 q |>.mp z j jt).symm.trans qj)
    exact ⟨t, by simp [S,rowSupport,pt,qt],jt⟩
  have neT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j,hj⟩ := neT
  obtain ⟨t,ht,jt⟩ := coverT j hj
  have spos : 1 ≤ S.card := Finset.card_pos.mpr ⟨t,ht⟩
  refine ⟨spos, fun notbad => ?_⟩
  by_contra n
  change ¬ 2 ≤ S.card at n
  have one : S.card = 1 := by omega
  obtain ⟨u,single⟩ := Finset.card_eq_one.mp one
  have U := Finset.mem_sdiff.mp (show u ∈ S by simp [single])
  have pout : p ∈ (R u).1 := (Finset.mem_filter.mp U.1).2
  have qout : q ∉ (R u).1 := fun x => U.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ u,x⟩)
  have contained : T ⊆ (R u).2 := by
    intro j hj
    obtain ⟨v,hv,hj'⟩ := coverT j hj
    rw [single,Finset.mem_singleton] at hv
    simpa [hv] using hj'
  have allLine : ∀ i ∈ (R u).1, M i l = true := by
    intro i hi
    have ne : i ≠ q := fun h => qout (h ▸ hi)
    obtain ⟨m,hm⟩ := unique_neighbor join ne
    have both := (hm m).mpr rfl
    by_cases e : m = l
    · simpa [e] using both.1
    · have hT : m ∈ T := Finset.mem_erase.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ m,both.2⟩⟩
      exact False.elim (Bool.false_ne_true (((closed u).1 i |>.mp hi m (contained hT)).symm.trans both.1))
  have sub : (R u).1 ⊆ (lineNeighbors (transposeMatrix M) l).erase q := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨fun h => qout (h ▸ hi),
      Finset.mem_filter.mpr ⟨Finset.mem_univ i,allLine i hi⟩⟩
  have a : (R u).1.card ≤ 5 := by
    have le := Finset.card_le_card sub
    have hq : q ∈ lineNeighbors (transposeMatrix M) l :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q,ql⟩
    have cs : (lineNeighbors (transposeMatrix M) l).card = 6 := coldeg l
    rw [Finset.card_erase_of_mem hq,cs] at le
    exact le
  have nonempty : (R u).1.Nonempty := ⟨p,pout⟩
  exact notbad ⟨u,U.1,Finset.card_pos.mpr nonempty,a,
    collinear_closed_width deg join _ (closed u) nonempty l allLine⟩

theorem inter_two_bound {α : Type*} [DecidableEq α] (S T U : Finset α) :
    (T \ U).card + (S ∩ T).card + (S ∩ U).card ≤ S.card + T.card := by
  have sub : T \ U ⊆ (T \ S) ∪ (S \ U) := by
    intro t ht
    obtain ⟨ht,hu⟩ := Finset.mem_sdiff.mp ht
    by_cases hs : t ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hs,hu⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht,hs⟩)
  have card := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have lhs := Finset.card_sdiff_add_card_inter T S
  have rhs := Finset.card_sdiff_add_card_inter S U
  rw [Finset.inter_comm T S] at lhs
  omega


theorem closed_columns_complement {M : V → V → Bool} (R : Box) (cl : rectClosed M R) :
    R.2 = Finset.univ \ (R.1.biUnion (lineNeighbors M)) := by
  classical
  ext j
  rw [cl.2 j]
  constructor
  · intro h
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hj => ?_⟩
    obtain ⟨i,hi,ij⟩ := Finset.mem_biUnion.mp hj
    exact Bool.false_ne_true ((h i hi).symm.trans (Finset.mem_filter.mp ij).2)
  · intro h i hi
    apply Bool.eq_false_of_ne_true
    intro ij
    exact (Finset.mem_sdiff.mp h).2
      (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ j,ij⟩⟩)

theorem closed_transpose (M : V → V → Bool) (R : Box) (h : rectClosed M R) :
    rectClosed (transposeMatrix M) (transposeBox R) := ⟨h.2,h.1⟩

theorem five_not_six {M : V → V → Bool} (deg : Area.Moments.rowDegree M)
    (join : Area.Moments.uniqueJoin M) (R : Box) (closed : rectClosed M R)
    (size : R.1.card = 5) : R.2.card ≠ 6 := by
  classical
  let I := lineNeighbors M
  have deg' (i : V) : (I i).card = 6 := deg i
  have mem (i j : V) : j ∈ I i ↔ M i j = true := by simp [I,lineNeighbors]
  obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp (by omega : 1 < R.1.card)
  obtain ⟨l,hl⟩ := unique_neighbor join pq
  have pl : l ∈ I p := (mem p l).mpr ((hl l).mpr rfl).1
  have ql : l ∈ I q := (mem q l).mpr ((hl l).mpr rfl).2
  by_cases allLine : ∀ i ∈ R.1, M i l = true
  · rw [collinear_closed_width deg join R closed ⟨p,hp⟩ l allLine,size]
    decide
  push_neg at allLine
  obtain ⟨r,hr,notl⟩ := allLine
  have rp : r ≠ p := fun e => notl (e ▸ (mem p l).mp pl)
  have rq : r ≠ q := fun e => notl (e ▸ (mem q l).mp ql)
  let U12 := I p ∪ I q
  let U := U12 ∪ I r
  have ul : l ∈ U12 := Finset.mem_union_left _ pl
  have u12 : U12.card ≤ 11 := by
    have e := Finset.card_union_add_card_inter (I p) (I q)
    have m : 0 < (I p ∩ I q).card := Finset.card_pos.mpr ⟨l,Finset.mem_inter.mpr ⟨pl,ql⟩⟩
    change U12.card + (I p ∩ I q).card = (I p).card + (I q).card at e
    rw [deg' p,deg' q] at e
    omega
  have double (i : V) (ip : i ≠ p) (iq : i ≠ q) (no : M i l ≠ true) :
      2 ≤ (I i ∩ U12).card := by
    obtain ⟨u,hu⟩ := unique_neighbor join ip
    obtain ⟨v,hv⟩ := unique_neighbor join iq
    have uon := (hu u).mpr rfl
    have von := (hv v).mpr rfl
    have ne : u ≠ v := by
      intro e
      have w := (hl u).mp ⟨uon.2,e.symm ▸ von.2⟩
      exact no (w ▸ uon.1)
    have sub : ({u,v} : Finset V) ⊆ I i ∩ U12 := by
      intro j hj
      rcases Finset.mem_insert.mp hj with e | hj
      · rw [e]
        exact Finset.mem_inter.mpr ⟨(mem i u).mpr uon.1,
          Finset.mem_union_left _ ((mem p u).mpr uon.2)⟩
      · have eq : j = v := Finset.mem_singleton.mp hj
        subst j
        exact Finset.mem_inter.mpr ⟨(mem i v).mpr von.1,
          Finset.mem_union_right _ ((mem q v).mpr von.2)⟩
    simpa [ne] using Finset.card_le_card sub
  have ucap : U.card ≤ 15 := by
    have m := double r rp rq notl
    have e := Finset.card_union_add_card_inter U12 (I r)
    change U.card + (U12 ∩ I r).card = U12.card + (I r).card at e
    rw [Finset.inter_comm U12,deg' r] at e
    omega
  have extra (i : V) (ip : i ≠ p) (iq : i ≠ q) (ir : i ≠ r) :
      (I i \ U).card ≤ 4 := by
    have h : 2 ≤ (I i ∩ U).card := by
      by_cases yes : M i l = true
      · obtain ⟨m,hm⟩ := unique_neighbor join ir
        have both := (hm m).mpr rfl
        have ne : l ≠ m := fun e => notl (e.symm ▸ both.2)
        have sub : ({l,m} : Finset V) ⊆ I i ∩ U := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Finset.mem_inter.mpr ⟨(mem i _).mpr yes,Finset.mem_union_left _ ul⟩
          · have eq : j = m := Finset.mem_singleton.mp hj
            subst j
            exact Finset.mem_inter.mpr ⟨(mem i _).mpr both.1,
              Finset.mem_union_right _ ((mem r _).mpr both.2)⟩
        simpa [ne] using Finset.card_le_card sub
      · apply (double i ip iq yes).trans
        apply Finset.card_le_card
        intro j hj
        obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hj
        exact Finset.mem_inter.mpr ⟨h1,Finset.mem_union_left _ h2⟩
    have e := Finset.card_sdiff_add_card_inter (I i) U
    rw [deg' i] at e
    omega
  let first : Finset V := {p,q,r}
  let rest := R.1 \ first
  have subFirst : first ⊆ R.1 := by
    intro i hi
    simp only [first,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have restCard : rest.card = 2 := by
    have e := Finset.card_sdiff_add_card_eq_card subFirst
    have three : first.card = 3 := by simp [first,pq,rp.symm,rq.symm]
    change rest.card + first.card = R.1.card at e
    omega
  have cover : R.1.biUnion I ⊆ U ∪ rest.biUnion (fun i => I i \ U) := by
    intro j hj
    by_cases ju : j ∈ U
    · exact Finset.mem_union_left _ ju
    · obtain ⟨i,hi,ij⟩ := Finset.mem_biUnion.mp hj
      have ir : i ∈ rest := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hi,fun h => ju ?_⟩
        simp only [first,Finset.mem_insert,Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ ij)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ ij)
        · exact Finset.mem_union_right _ ij
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i,ir,Finset.mem_sdiff.mpr ⟨ij,ju⟩⟩)
  have boundExtra : (rest.biUnion (fun i => I i \ U)).card ≤ 8 := by
    apply Finset.card_biUnion_le.trans
    have h (i : V) (hi : i ∈ rest) : (I i \ U).card ≤ 4 := by
      have h := (Finset.mem_sdiff.mp hi).2
      simp only [first, Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact extra i h.1 h.2.1 h.2.2
    have le := Finset.sum_le_sum h
    simpa [restCard] using le
  have w := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have lim : (R.1.biUnion I).card ≤ 23 := by omega
  rw [closed_columns_complement R closed,Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,Fintype.card_fin]
  change 31 - (R.1.biUnion I).card ≠ 6
  omega


def sideCap (a : ℕ) : ℕ := ([0,25,20,16,13,11,10,8,7] : List ℕ).getD a 0

theorem width_cap {a b : ℕ} (caps : Area.RowCaps a b) (lo : 1 ≤ a) (hi : a ≤ 8) :
    b ≤ sideCap a := by
  rcases caps with ⟨c1,c2,c3,c4,c5,c6,c7,c8⟩
  interval_cases a
  · exact c1 rfl
  · exact c2 rfl
  · exact c3 rfl
  · exact c4 rfl
  · exact c5 rfl
  · exact c6 rfl
  · exact c7 rfl
  · exact c8 rfl

def shapeOkay (a b : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ 25 ∧ 1 ≤ b ∧ b ≤ 25 ∧ 15 ≤ a*b ∧ a*b ≤ 60 ∧
    (a ≤ 8 ∨ b ≤ 8) ∧ (a ≤ 8 → b ≤ sideCap a) ∧ (b ≤ 8 → a ≤ sideCap b) ∧ ¬ (a=5 ∧ b=6) ∧ ¬ (a=6 ∧ b=5)

def boxSize (R : Box) : ℕ × ℕ := (R.1.card,R.2.card)

def generatedDims : List (ℕ × ℕ) :=
  (List.range 26).flatMap fun a =>
    ((List.range 26).filter (fun b => @decide (shapeOkay a b) (by unfold shapeOkay; infer_instance))).map fun b => (a,b)

def dims : List (ℕ × ℕ) := [
  (1,15),(1,16),(1,17),(1,18),(1,19),(1,20),(1,21),(1,22),(1,23),(1,24),
  (1,25),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),
  (2,17),(2,18),(2,19),(2,20),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),
  (3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(4,4),(4,5),(4,6),(4,7),
  (4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(5,3),(5,4),(5,5),(5,7),
  (5,8),(5,9),(5,10),(5,11),(6,3),(6,4),(6,6),(6,7),(6,8),(6,9),
  (6,10),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(8,2),(8,3),(8,4),
  (8,5),(8,6),(8,7),(9,2),(9,3),(9,4),(9,5),(9,6),(10,2),(10,3),
  (10,4),(10,5),(10,6),(11,2),(11,3),(11,4),(11,5),(12,2),(12,3),(12,4),
  (13,2),(13,3),(13,4),(14,2),(14,3),(15,1),(15,2),(15,3),(16,1),(16,2),
  (16,3),(17,1),(17,2),(18,1),(18,2),(19,1),(19,2),(20,1),(20,2),(21,1),
  (22,1),(23,1),(24,1),(25,1)]

set_option maxRecDepth 8192 in
theorem dims_eq : dims = generatedDims := by decide +kernel

theorem mem_dims {a b : ℕ} : (a,b) ∈ dims ↔ shapeOkay a b := by
  rw [dims_eq]
  unfold generatedDims
  simp only [List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, ⟨hy,ok⟩, rfl, rfl⟩
    exact ok
  · intro ok
    have ⟨_,ha,_,hb,_⟩ := ok
    exact ⟨a, by omega, b, ⟨by omega,ok⟩, rfl, rfl⟩

def deficit (x : ℕ × ℕ) : ℕ := 60 - x.1 * x.2

theorem actual_shape (R : Box) (good : plain R) (closed : rectClosed matrix R) (large : 15 ≤ R.1.card * R.2.card) :
    boxSize R ∈ dims := by
  obtain ⟨small,row,col⟩ := Area.matrix_caps R.1 R.2 good
  have p1 : 1 ≤ R.1.card := by
    by_contra! h
    have z : R.1.card = 0 := by omega
    simp [z] at large
  have p2 : 1 ≤ R.2.card := by
    by_contra! h
    have z : R.2.card = 0 := by omega
    simp [z] at large
  have rowBound : R.1.card ≤ 25 := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp p2
    have inc : R.1 ⊆ zeros j := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,good i hi j hj⟩
    simpa only [count_table] using Finset.card_le_card inc
  have colBound : R.2.card ≤ 25 := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp p1
    have rel : R.2 ⊆ Finset.univ \ lineNeighbors matrix i := by
      intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j,fun h => Bool.false_ne_true
        ((good i hi j hj).symm.trans (Finset.mem_filter.mp h).2)⟩
    have le := Finset.card_le_card rel
    have deg : (lineNeighbors matrix i).card = 6 := Area.matrix_row_degree i
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,Fintype.card_fin,deg] at le
  apply mem_dims.mpr
  refine ⟨p1,rowBound,p2,colBound,large,Area.matrix_area_le_60 _ _ good,small,
    width_cap row p1,width_cap col p2,?_,?_⟩
  · rintro ⟨a,b⟩
    exact five_not_six Area.matrix_row_degree Area.matrix_row_join R closed a b
  · rintro ⟨a,b⟩
    exact five_not_six Area.matrix_col_degree Area.matrix_col_join (transposeBox R)
      (closed_transpose matrix R closed) b a

theorem swap_shape {a b : ℕ} (h : (a,b) ∈ dims) : (b,a) ∈ dims := by
  obtain ⟨ha,ha',hb,hb',lo,hi,small,r,c,ex,exT⟩ := mem_dims.mp h
  exact mem_dims.mpr ⟨hb,hb',ha,ha',by simpa [Nat.mul_comm] using lo,
    by simpa [Nat.mul_comm] using hi,small.symm,c,r,fun x => exT x.symm,fun x => ex x.symm⟩

theorem total_deficit {k : ℕ} (R : Fin k → Box) (good : ∀ t, plain (R t)) :
    (∑ t : Fin k, deficit (boxSize (R t))) + ∑ t : Fin k, (R t).1.card * (R t).2.card = 60*k := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _t : Fin k, (60 : ℕ) := by
      apply Finset.sum_congr rfl
      intro t _
      have h := Area.matrix_area_le_60 _ _ (good t)
      change 60 - (R t).1.card * (R t).2.card + (R t).1.card * (R t).2.card = 60
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem cert_size {k : ℕ} (R : Fin k → Box) (bound : k ≤ 15) (good : ∀ t, plain (R t))
    (closed : ∀ t, rectClosed matrix (R t))
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    k = 15 ∧ (∑ t, deficit (boxSize (R t))) ≤ 45 ∧ ∀ t, boxSize (R t) ∈ dims := by
  have lower := area_lower R good covers
  have fifteen := at_least_fifteen R good covers
  have k15 : k = 15 := by omega
  have total := total_deficit R good
  rw [show 60*k = 900 by omega] at total
  have small : (∑ t, deficit (boxSize (R t))) ≤ 45 := by omega
  refine ⟨k15,small,fun t => actual_shape (R t) (good t) (closed t) ?_⟩
  have hit := Finset.single_le_sum (f := fun s => deficit (boxSize (R s)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  change 60 - (R t).1.card * (R t).2.card ≤ _ at hit
  omega

theorem column_load {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (counts : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25) (j : V) :
    (∑ t ∈ colSupport R j, (R t).1.card) = 25 + load M R j := by
  have h : (∑ i, multiplicity R i j) = 25 + load M R j := by
    simp_rw [multiplicity_eq M R good covers,Finset.sum_add_distrib,load]
    rw [(zeroEntry_sum_sq M counts j).1]
  rw [← h]
  unfold multiplicity
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  unfold colSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases yes : j ∈ (R t).2
  · simp [colSupport,yes,← Finset.card_filter]
  · simp [colSupport,yes]

theorem transpose_multiplicity {k : ℕ} (R : Fin k → Box) (i j : V) :
    multiplicity (fun t => transposeBox (R t)) j i = multiplicity R i j := by
  unfold multiplicity
  congr 1
  ext t
  simp [transposeBox,and_comm]

theorem transpose_extra {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i j : V) :
    extra (transposeMatrix M) (fun t => transposeBox (R t)) j i = extra M R i j := by
  change multiplicity (fun t => transposeBox (R t)) j i - zeroEntry M i j = _
  rw [transpose_multiplicity]
  rfl

theorem total_load {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (counts : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25) :
    775 + ∑ j, load M R j = ∑ t : Fin k, (R t).1.card * (R t).2.card := by
  let W (t : Fin k) (j : V) := if j ∈ (R t).2 then (R t).1.card else 0
  have bycol (j : V) : (∑ t, W t j) = 25 + load M R j := by
    simpa only [W,colSupport,Finset.sum_filter] using column_load R good covers counts j
  have bybox (t : Fin k) : (∑ j, W t j) = (R t).1.card * (R t).2.card := by
    simp [W, ← Finset.sum_filter, Nat.mul_comm]
  have e : (∑ j, (25 + load M R j)) = ∑ t : Fin k, (R t).1.card * (R t).2.card := by
    simp_rw [← bycol]
    rw [Finset.sum_comm]
    simp_rw [bybox]
  simpa [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.mul_comm] using e


abbrev ChargeParameter := ℕ × ℤ × ℕ × ℕ × ℕ
abbrev Parameters := ℤ × ℕ × ℕ × ℕ × ℕ × List ChargeParameter


def gapData : List ℕ := [
  1412077055586107420947814264421393090361036937628924431858763789589067532330736098682714726851684421998003935344503144101646491100905608075865001013498222882038757084088442826297787555962198537174012338916209972579686492574558761326968046325698212367786657870020844231930870461824853670045052682269254376526952522181532848832484157142665624785592472097829461817030353818045119597291209013612227149999326217327783170991244327600478189396983747528456770013829728583363786859035023635087074706961614824535542172589387592806469745180588015433893464983661207153140929207166943579469281786677866710524736243496910848,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974076173395993917490017545364378994909980885464566877684017078391659021396189712244325020373524994276175166258365671090578588075575915291502001266717672426627705154262772906388064539597617790211438914402757881794577237606400,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092976887323064072439325261296322612304147265719786776120431840439060008359163591113184103824073273577551681662420061229420399206959226296682012093077456513292911971991552,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092977869885840461004980141446940874631409753057630215125893571292695472200861148216703467453211108106279686181043702498754739038655584981156473685195559847182151040696320,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092977870125723950440584167327268416154509957641893362254101235674533518535957039666348567527747403667678168483241687812713459362034012546175116167661121409621395726467072,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092978849089365643040117066900447688624162447687986304751160598399557569188706964256616363711149951278600767461489941359831324388139404188261672069560162255596606912004096,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092978849089365643040117066900447688624162447687986304751160638471565537047098381561442884852489981653842443563511395393008921438155604764483280137879750354468867608215552,
  1412077055586107420947814264421393090361036937628929580254860211980661225541721321372139301856966635294075800416492939494350876242964711446173000281261356143158453498550990585520945946702376414421297566085114492135554106220515923006660165869736613058580048527960642546451604203892257642957948378690612801911242911943262866422070278540197970192889065146924400903151658746454369148133370974100177514642937338741612789537734246819371972817616092978849089365643040117066900447688624162447687986304751160638481348742080931030353157792734012946260677791095432344567812529337336003525246459271745822562510031989833728]

def widthData : List ℕ := [
  240045884396056727512981681163180474816781379890740076921548533274961983231811227993282401457112171385358349769230355173411601074909181525499880435962288213390813778642766320949222750855832187494523303154609024,
  240045884396056727512981681163180474816781379890740076921539531450770453054950346067343914475731963363070642229736316354684582700704199364057189038324366581726180655769896926951616366537506236502122833539844334,
  240045884396056727512981681163174332365404912483651024138820892013018531769223123279732602164194149698208119939154743399418588322300774572436326101699236391241153520817222185615054376109043136800507382160092078,
  240045884386406726715867421255979424289041832832724459827566913653348904506103464465582891078733907654889608037037298456139710975797655075615591059518073219807388122516360697285154312343987298183301436920228782,
  192676479353864635102003042372007372359810454875007827437790934059899681755237120496713449518116901689119890756174399357832841249660109299015939103970276108833989442819286420814879946878580850031533651031419822,
  124908930403353379125009104043626176060521422135734566814557738082559695035569290591831157502770675253531718225299463400212725326970127888808318577152827902740461317534380007992655081172458799297062463673658286,
  78682243251955506952537100102934976446236846371775687484406466759914029725901641969144733579086784767077681565008255430235460685844435884490892814814096823748765879003972388622705244484683228956388241614498734,
  99144390171879233546246091635148911697461759688934676223975030115631822427836135825855036482118467075299048510082429125626626199533114617161799180587285289991721805547838417722532145756705347706218714433776558,
  78687360442213028369637748223877334056669515297413494412535696161428625403508390881510581885293828582811731697333268481558971771798766735796778284462817110363469532469842632452262894524126337824095009616096174,
  130709507177642900008216247480719883510720812029715701008032540065395892020634408389871759033645769641231531255194272431618572206639128547894419389239083993260935517609494589673330265244300872565278162894384046,
  224635329996989227003486593615680097866926868749656559755049663441752806998518999022246269026611423969653989240223076436005919360466809247695816528612840996279909113795070825646782385211341020891658304500722606,
  240045884396056727512981681163180474816781379890740076921548533274961983231811227993282401457112171385358259335161888295000575969432099120326908543818998502629417318731273695032517853458910588118706107971201966]

def allowData : List ℕ := [
  339442399026646437824236258292121203117628376108931629444536788385452801784181039249814102737689874170080395264,
  23577524976930532220087552659768504285669155040784415650385233983589927671125377494559813800631161990078791680]

def budgetMask : ℕ := 70368744177521

def parameterData : List ℕ := [
  134439079612719707112894093173341230165492946402719286917060320986705042928549802415373521998829282418,
  2000000,
  2000000,
  2000000,
  2083177665772872588154688887803953714405617633532745281654423050978695805413667596859377973403406611531057205277435726765,
  8510373968115442726953681317153986486661409056740706096950734530654331937189104557,
  640724043812366283972783220932116748534533446704796852012520022306991115436761013216890393157401002287778859949,
  2000000,
  142402702573591839795696380746944032971581097306490967062818772219360431511136774601874631105034927013,
  142402702573591839795696380746944032971581097306490967062818772219360431511136774601874631105034927013,
  2293021636444979674072467062897543819767761928070970095442536278129346150089561170495199168872876468408811218467018719402253259497,
  142402702573591839795696380746944032971581097306490967062818772219360431511136774601874631105034927013,
  11282261989124988019234704300366057533159496400130181137868758458706466063452439393478652760523300689674251171532721065872045718437,
  3185377257535536372692551084976163203710020168430349541353535563656807364040603496190377728461016894252069590427974669033,
  1408428121870647213713881858525502024258289672266899582010590058869672933135667447103767549419192910467955321667611431657,
  2359956981524912540887246430380614291788467688545573375182547050203796045928527997524788463702959458146639016256864424681,
  2478774251641670065171880683162316393031984860716592455587193188833096928253429876079584398646807694387758403351634438918429114232,
  2478774252642224870808542386444799524576486259714522242882684285845975601477618555171037080313870293280648927128066255648400244600,
  2478774252642224870808542386444799524576486259714522242882684285845975601477618555171037080313870293280648927128066255648400244600,
  2478774251641670065171880683154850853429912148656752596845751556207374830947555365841179080833531097571432312526350250047371902840,
  6711901678102395659054084253503834309568237287959333248583710237804880224542579760910545904553316454343317236508168935750555035496,
  1562736387854068460654021295625410978752498603986740513559462264746772846544490684193373520652732225840611041305642035048,
  123812732475257821537553947901919313067480660282551728191039480450290357034446454014219424325323548214272746003609943763851018322578939832871493461864,
  1364406389573728142400821653854272729931582699603543460106549985103602697167346564504625199286217047792077526203898155967,
  47684502058647141707403118890480665684642456209779415157788772869629023999199901809925800204915621245012765277973868977484115539647214526706,
  204803376867934147637173954415713114834880420675004895037041840162458188460141382823024818592219893617455080845124309790208469949565971284673832296690,
  204803376867933966637296364351082739423270623162872382981795146659775595554325073517834021106147625354334869407813506948328629224268988967457080353010,
  11102413305950523653003443520790751884957993120224732780942656619945045498047361498050389015778609714169736649193291492177611989234,
  571295281840446435580898801436051707869820629644092074203192087731354912981412108342779743362125723978896117655,
  45262675429482109661952934435894154854806836645584631988637790786578457533344381600692474288827600748166930152226637953058537183081016725399,
  23633466900450540912618757599390948236567895832635642327388473320635833590673754871665115841,
  23633466900450540912618757599390948236567895832635642327388473320635833590673754871665115841,
  5502566362182013333533179063810194453474973248978784417923595224245994500734960321,
  5502566362182013333533179063810194453474973248978784417923595224245994500734960321,
  23633342569641438353882732090390223007760775014873691343651675930377393029495168376586224321,
  5502566362182013333533179069940176616938528682079865527578602990494999224399282881,
  68136940983499334168161713507389257607428951850985374365843252565825641,
  68130227324905457517527556342321297478020632629130885435549165123852393,
  68130200996832540378230881862814376560412552905357035298271351546108009,
  68130200996833318885965641734354422600702345262422313617745420816013417,
  68130227324905457517527556342321297478020632629130885435549165123852393,
  68130227324905457517527556342321297478020632629130885435549165123852393,
  68130200996832540378230881862814376560412552905357035298271351546108009,
  764946613177,
  764946613177,
  764946613177]

def qMult (q : ChargeParameter) : ℕ := q.1
def qThreshold (q : ChargeParameter) : ℤ := q.2.1
def qAllowance (q : ChargeParameter) : ℕ := q.2.2.1
def qExtra (q : ChargeParameter) : ℕ := q.2.2.2.1
def qWeight (q : ChargeParameter) : ℕ := q.2.2.2.2
def baseWeight (p : Parameters) : ℤ := p.1
def slopeWeight (p : Parameters) : ℕ := p.2.1
def parityWeight (p : Parameters) : ℕ := p.2.2.1
def badWeight (p : Parameters) : ℕ := p.2.2.2.1
def tailWeight (p : Parameters) : ℕ := p.2.2.2.2.1
def terms (p : Parameters) : List ChargeParameter := p.2.2.2.2.2

def loadFromPacked (word bits idx : ℕ) : ℕ :=
  (word >>> (bits * idx)) &&& ((1 <<< bits) - 1)

def parameterAt (δ : ℕ) : Parameters :=
  let word := parameterData.getD δ 0
  let field (i : ℕ) := loadFromPacked word 22 i
  let count := (word >>> 110) &&& 31
  let charges := (List.range count).map fun j =>
    let q := loadFromPacked (word >>> 115) 32 j
    (q &&& 7, (((q >>> 3) &&& 31 : ℕ) : ℤ) - 32, (q >>> 8) &&& 3,
      (q >>> 10) &&& 3, q >>> 12)
  ((field 0 : ℤ) - 2000000, field 1, field 2, field 3, field 4, charges)

def gapUpper (common extra δ : ℕ) : ℕ :=
  loadFromPacked (gapData.getD common 0) 4 (46*extra+δ)

def widthLower (degree width : ℕ) (bad : Bool) : ℕ :=
  loadFromPacked (widthData.getD degree 0) 6 ((if bad then 58 else 0)+width)

def allowanceUpper (which δ : ℕ) : ℕ :=
  loadFromPacked (allowData.getD which 0) 8 δ

def possibleBudget (δ : ℕ) : Bool := budgetMask.testBit δ

def badBit (x : ℕ × ℕ) : Bool := @decide (badShape x.1 x.2) (by unfold badShape; infer_instance)
def oddSlots (x : ℕ × ℕ) : ℕ := x.1 * (x.2 % 2) + x.2 * (x.1 % 2)
def badSlots (x : ℕ × ℕ) : ℕ :=
  (if badBit x then x.1 else 0) + (if badBit x.swap then x.2 else 0)

def commonGap (x : ℕ × ℕ) : ℕ := 16 - (x.1 + x.2)
def extraGap (x : ℕ × ℕ) : ℕ := 6 - min x.1 x.2

def gapCheck (m n : ℕ) : Bool :=
  (List.range 46).all fun δ =>
    (if m = 0 ∧ n = 0 then decide (gapUpper m n δ = 0) else
      dims.all fun p =>
        if deficit p ≤ δ then
          if m > 0 then
            decide (commonGap p + gapUpper (m-1) n (δ-deficit p) ≤ gapUpper m n δ)
          else
            decide (extraGap p + gapUpper 0 (n-1) (δ-deficit p) ≤ gapUpper 0 n δ)
        else true) &&
    (if n > 0 then decide (gapUpper m (n-1) δ ≤ gapUpper m n δ) else true)

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
theorem gapChecks : ∀ (m : Fin 8) (n : Fin 11), gapCheck m.val n.val = true := by
  intro m
  fin_cases m <;> (intro n; fin_cases n <;> decide +kernel)

theorem gap_common_step {m n δ : ℕ} {p : ℕ × ℕ} (hm : 0 < m) (mb : m ≤ 7)
    (nb : n ≤ 10) (db : δ ≤ 45) (pd : deficit p ≤ δ) (ps : p ∈ dims) :
    commonGap p + gapUpper (m-1) n (δ-deficit p) ≤ gapUpper m n δ := by
  have h := gapChecks ⟨m,by omega⟩ ⟨n,by omega⟩
  unfold gapCheck at h
  have f := List.all_eq_true.mp h δ (List.mem_range.mpr (by omega))
  have f' := (Bool.and_eq_true_iff.mp f).1
  have c := List.all_eq_true.mp (by simpa [hm.ne',hm,pd] using f' :
    dims.all (fun p => if deficit p ≤ δ then
      decide (commonGap p + gapUpper (m-1) n (δ-deficit p) ≤ gapUpper m n δ) else true) = true) p ps
  simpa [pd] using c

theorem gap_extra_step {n δ : ℕ} {p : ℕ × ℕ} (hn : 0 < n)
    (nb : n ≤ 10) (db : δ ≤ 45) (pd : deficit p ≤ δ) (ps : p ∈ dims) :
    extraGap p + gapUpper 0 (n-1) (δ-deficit p) ≤ gapUpper 0 n δ := by
  have h := gapChecks ⟨0,by decide⟩ ⟨n,by omega⟩
  unfold gapCheck at h
  have f := List.all_eq_true.mp h δ (List.mem_range.mpr (by omega))
  have f' := (Bool.and_eq_true_iff.mp f).1
  have c := List.all_eq_true.mp (by simpa [hn.ne'] using f' :
    dims.all (fun p => if deficit p ≤ δ then
      decide (extraGap p + gapUpper 0 (n-1) (δ-deficit p) ≤ gapUpper 0 n δ) else true) = true) p ps
  simpa [pd] using c

theorem gap_mono_extra {m n n' δ : ℕ} (h : n ≤ n') (mb : m ≤ 7) (nb : n' ≤ 10)
    (db : δ ≤ 45) : gapUpper m n δ ≤ gapUpper m n' δ := by
  induction n' with
  | zero =>
    have e : n = 0 := by omega
    rw [e]
  | succ z ih =>
    by_cases e : n = z+1
    · simp [e]
    · have le := ih (by omega) (by omega)
      have hn := gapChecks ⟨m,by omega⟩ ⟨z+1,by omega⟩
      unfold gapCheck at hn
      have f := List.all_eq_true.mp hn δ (List.mem_range.mpr (by omega))
      have step : gapUpper m z δ ≤ gapUpper m (z+1) δ := by
        simpa using (Bool.and_eq_true_iff.mp f).2
      exact le.trans step

theorem gap_extras {δ : ℕ} (extra : List (ℕ × ℕ)) (nc : extra.length ≤ 10)
    (db : δ ≤ 45) (es : ∀ p ∈ extra, p ∈ dims) (cost : (extra.map deficit).sum ≤ δ) :
    (extra.map extraGap).sum ≤ gapUpper 0 extra.length δ := by
  induction extra generalizing δ with
  | nil => exact Nat.zero_le _
  | cons p ps ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons] at *
    have step := gap_extra_step (n:=ps.length+1) (δ:=δ) (p:=p) (by omega) nc db
      (by omega) (es p (List.mem_cons_self ..))
    have rest := ih (δ:=δ-deficit p) (by omega) (by omega)
      (fun t ht => es t (List.mem_cons_of_mem _ ht)) (by omega)
    rw [show ps.length+1-1 = ps.length by omega] at step
    omega

theorem gap_bound {δ : ℕ} (common extra : List (ℕ × ℕ))
    (mc : common.length ≤ 7) (nc : extra.length ≤ 10) (db : δ ≤ 45)
    (cs : ∀ p ∈ common, p ∈ dims) (es : ∀ p ∈ extra, p ∈ dims)
    (cost : (common.map deficit).sum + (extra.map deficit).sum ≤ δ) :
    (common.map commonGap).sum + (extra.map extraGap).sum ≤
      gapUpper common.length extra.length δ := by
  induction common generalizing δ with
  | nil => simpa using gap_extras extra nc db es (by simpa using cost)
  | cons p ps ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons] at *
    have step := gap_common_step (m:=ps.length+1) (n:=extra.length) (δ:=δ)
      (p:=p) (by omega) mc nc db (by omega) (cs p (List.mem_cons_self ..))
    have rest := ih (δ:=δ-deficit p) (by omega) (by omega)
      (fun s hs => cs s (List.mem_cons_of_mem _ hs)) (by omega)
    rw [show ps.length+1-1 = ps.length by omega] at step
    omega

def widthCheck (d w : ℕ) (v : Bool) : Bool :=
  if d = 0 then
    decide (widthLower 0 0 false = 0)
  else dims.all fun p =>
    if p.2 ≤ w then
      [false,true].all fun u =>
        if (u || badBit p) == v then
          decide (widthLower d w v ≤ deficit p + widthLower (d-1) (w-p.2) u)
        else true
    else true

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
theorem widthChecks : ∀ (d : Fin 12) (w : Fin 58) (b : Bool),
    widthCheck d.val w.val b = true := by
  intro d
  fin_cases d <;> (intro w; fin_cases w <;> decide +kernel)

theorem width_step {d w : ℕ} {p : ℕ × ℕ} {b : Bool} (d0 : 0 < d) (db : d ≤ 11) (wb : w ≤ 57)
    (pw : p.2 ≤ w) (ps : p ∈ dims) :
    widthLower d w (b || badBit p) ≤ deficit p + widthLower (d-1) (w-p.2) b := by
  have h := widthChecks ⟨d,by omega⟩ ⟨w,by omega⟩ (b || badBit p)
  unfold widthCheck at h
  rw [if_neg d0.ne'] at h
  have f := List.all_eq_true.mp h p ps
  rw [if_pos pw] at f
  have g := List.all_eq_true.mp f b (by cases b <;> simp)
  simpa using g

theorem width_bound (shapes : List (ℕ × ℕ)) (d : shapes.length ≤ 11)
    (w : (shapes.map Prod.snd).sum ≤ 57) (ok : ∀ p ∈ shapes, p ∈ dims) :
    widthLower shapes.length (shapes.map Prod.snd).sum (shapes.any badBit) ≤ (shapes.map deficit).sum := by
  induction shapes with
  | nil => decide +kernel
  | cons p ps ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons,List.any_cons] at *
    have h := width_step (d:=ps.length+1) (w:=p.2+(ps.map Prod.snd).sum) (p:=p)
      (b:=ps.any badBit) (by omega) d w (by omega) (ok p (List.mem_cons_self ..))
    have rest := ih (by omega) (by omega) (fun s hs => ok s (List.mem_cons_of_mem _ hs))
    rw [show p.2 + (ps.map Prod.snd).sum - p.2 = (ps.map Prod.snd).sum by omega] at h
    simpa only [Bool.or_comm] using h.trans (Nat.add_le_add_left rest _)

def budgetCheck (δ : ℕ) : Bool :=
  if possibleBudget δ then
    dims.all fun p =>
      if δ + deficit p ≤ 45 then
        possibleBudget (δ+deficit p) &&
          decide (oddSlots p + allowanceUpper 0 δ ≤ allowanceUpper 0 (δ+deficit p)) &&
          decide (badSlots p + allowanceUpper 1 δ ≤ allowanceUpper 1 (δ+deficit p))
      else true
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetChecks : ∀ δ : Fin 46, budgetCheck δ.val = true := by decide +kernel

theorem budget_bound (shapes : List (ℕ × ℕ)) (total : (shapes.map deficit).sum ≤ 45)
    (ok : ∀ p ∈ shapes, p ∈ dims) :
    possibleBudget (shapes.map deficit).sum = true ∧
    (shapes.map oddSlots).sum ≤ allowanceUpper 0 (shapes.map deficit).sum ∧
    (shapes.map badSlots).sum ≤ allowanceUpper 1 (shapes.map deficit).sum := by
  induction shapes with
  | nil => decide +kernel
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons] at *
    obtain ⟨yes,od,bd⟩ := ih (by omega) (fun s hs => ok s (List.mem_cons_of_mem _ hs))
    let d := (ps.map deficit).sum
    have h := budgetChecks ⟨d,by dsimp [d]; omega⟩
    unfold budgetCheck at h
    have cond : possibleBudget d = true := yes
    simp only [Fin.val_mk,cond,↓reduceIte] at h
    have s := List.all_eq_true.mp h p (ok p (List.mem_cons_self ..))
    have avail : d + deficit p ≤ 45 := by dsimp [d]; omega
    rw [if_pos avail] at s
    simp only [Bool.and_eq_true_iff,decide_eq_true_eq] at s
    have ⟨⟨mark,odd⟩,bad⟩ := s
    refine ⟨by simpa [d,Nat.add_comm] using mark, ?_, ?_⟩
    · have b := (Nat.add_le_add_left od (oddSlots p)).trans odd
      simpa [d,Nat.add_comm] using b
    · have b := (Nat.add_le_add_left bd (badSlots p)).trans bad
      simpa [d,Nat.add_comm] using b

def lowTag (q : ChargeParameter) (n d : ℕ) (bad : Bool) : Bool :=
  decide (n - qMult q ≤ qExtra q ∧
    n - qMult q + (if bad then 1 else 0) ≤ qAllowance q ∧
    (d : ℤ) - 6*n ≤ qThreshold q)

def highTag (q : ChargeParameter) (δ n d second : ℕ) : Bool :=
  if 32 < d then true else
  decide (n - (second+1) ≥ 2 - qAllowance q ∧
    (d : ℤ) - 6*n ≥ 4*(qMult q : ℤ)-50 -
       gapUpper (qMult q) (qExtra q+n-qMult q) δ - qThreshold q)

def tagValue (p : Bool) : ℤ := if p then 1 else 0

def fee (param : Parameters) (δ n d second : ℕ) (bad : Bool) (e : ℕ) : ℤ :=
  ((terms param).map fun q =>
    if qMult q = e+1 then
      (qWeight q : ℤ) * (tagValue (lowTag q n d bad) - tagValue (highTag q δ n d second))
    else 0).sum

def profileBase (p : Parameters) (d : ℕ) (bad : Bool) : ℤ :=
  baseWeight p + (slopeWeight p : ℤ)*d + (if d % 2 = 0 then (parityWeight p : ℤ) else 0) +
    (if bad then (badWeight p : ℤ) else 0)

def profileCost (p : Parameters) (δ n d : ℕ) (bad : Bool) (parts : List ℕ) : ℤ :=
  profileBase p d bad + (parts.map (fee p δ n d (parts.getD 1 0) bad)).sum

def rationalNumer (d u : ℕ) : ℤ := 125*(u : ℤ)-5*(d : ℤ)^2
def rationalDenom (d u : ℕ) : ℤ := (25+(d : ℤ))^2 + rationalNumer d u

def checkOne (p : Parameters) (δ n d : ℕ) (bad : Bool) (parts : List ℕ) : Bool :=
  let u := (parts.map fun e => e*e).sum
  decide (1000000*rationalNumer d u ≤ profileCost p δ n d bad parts * rationalDenom d u)

def checkParameters (δ : ℕ) : Bool :=
  if possibleBudget δ then
    let p := parameterAt δ
    (terms p).all (fun q => decide (3 ≤ qMult q ∧ qMult q ≤ 7 ∧
      qExtra q ≤ qAllowance q ∧ qAllowance q ≤ 2)) &&
    (List.range 8).all (fun m =>
      decide ((((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤ (m-1)*tailWeight p)) &&
    decide (tailWeight p ≤ slopeWeight p ∧
      1000000 ≤ baseWeight p + ((slopeWeight p : ℤ) - tailWeight p)*33 ∧
      62*baseWeight p + 2*(125-(δ : ℤ))*slopeWeight p +
        ((min 62 (allowanceUpper 0 δ) : ℕ) : ℤ)*parityWeight p +
        (allowanceUpper 1 δ : ℤ)*badWeight p < 32000000)
  else true

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
theorem parameterChecks : ∀ δ : Fin 46, checkParameters δ.val = true := by decide +kernel



def flip {k : ℕ} (R : Fin k → Box) (t : Fin k) : Box := transposeBox (R t)

theorem flip_flip {k : ℕ} (R : Fin k → Box) : flip (flip R) = R := by
  funext t
  exact Prod.eta _

theorem flip_matrix (M : V → V → Bool) : transposeMatrix (transposeMatrix M) = M := rfl

def degree {k : ℕ} (R : Fin k → Box) (i : V) : ℕ := (rowSupport R i).card

def rowLoad {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) : ℕ :=
  ∑ j, extra M R i j

theorem row_load {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (counts : ∀ i, (Finset.univ.filter fun j => M i j = false).card = 25) (i : V) :
    (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i := by
  have g (t : Fin k) : Area.Moments.EmptyRectangle (transposeMatrix M) (flip R t).1 (flip R t).2 :=
    fun j hj i hi => good t i hi j hj
  have c (j i : V) (h : transposeMatrix M j i = false) :
      ∃ t, j ∈ (flip R t).1 ∧ i ∈ (flip R t).2 := by
    obtain ⟨t,hi,hj⟩ := covers i j h
    exact ⟨t,hj,hi⟩
  rw [show rowLoad M R i = load (transposeMatrix M) (flip R) i by
    unfold rowLoad load
    apply Finset.sum_congr rfl
    intro j _
    exact (transpose_extra M R i j).symm]
  exact column_load (flip R) g c counts i

noncomputable def shapesAt {k : ℕ} (R : Fin k → Box) (i : V) : List (ℕ × ℕ) :=
  (rowSupport R i).toList.map fun t => boxSize (R t)

noncomputable def isBad {k : ℕ} (R : Fin k → Box) (i : V) : Bool := (shapesAt R i).any badBit

theorem isBad_eq {k : ℕ} (R : Fin k → Box) (i : V) :
    isBad R i = true ↔ badVertex R i := by
  simp only [isBad, shapesAt, List.any_map, List.any_eq_true, Function.comp_apply,
    Finset.mem_toList, badBit, decide_eq_true_eq, badVertex, boxSize]

theorem shapesAt_width {k : ℕ} (R : Fin k → Box) (i : V) :
    ((shapesAt R i).map Prod.snd).sum = ∑ t ∈ rowSupport R i, (R t).2.card := by
  simp only [shapesAt,List.map_map,Finset.sum_map_toList,Function.comp_apply,boxSize]

theorem shapesAt_degree {k : ℕ} (R : Fin k → Box) (i : V) :
    (shapesAt R i).length = degree R i := by
  simp only [shapesAt, List.length_map,Finset.length_toList,degree]

theorem shapesAt_deficit {k : ℕ} (R : Fin k → Box) (i : V) :
    ((shapesAt R i).map deficit).sum ≤ ∑ t, deficit (boxSize (R t)) := by
  simp only [shapesAt,List.map_map,Finset.sum_map_toList,Function.comp_apply]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem shape_width_cost : dims.all (fun x => decide (24 ≤ deficit x + 4*x.2)) = true := by
  decide +kernel

theorem degree_small {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (width : ∀ i, (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i)
    (ok : ∀ t, boxSize (R t) ∈ dims)
    (db : (∑ t, deficit (boxSize (R t))) ≤ 45) (i : V)
    (small : rowLoad M R i ≤ 32) : 0 < degree R i ∧ degree R i ≤ 11 := by
  have b (t : Fin k) : 24 ≤ deficit (boxSize (R t)) + 4*(R t).2.card :=
    of_decide_eq_true (List.all_eq_true.mp shape_width_cost _ (ok t))
  have total := Finset.sum_le_sum (s := rowSupport R i) (fun t _ => b t)
  rw [Finset.sum_const,nsmul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,width] at total
  have budget := (shapesAt_deficit R i).trans db
  simp only [shapesAt,List.map_map,Finset.sum_map_toList,Function.comp_apply] at budget
  change degree R i * 24 ≤ _ at total
  have pos : 0 < degree R i := by
    by_contra! h
    have e : rowSupport R i = ∅ := Finset.card_eq_zero.mp (by simpa [degree] using h)
    have w := width i
    rw [e,Finset.sum_empty] at w
    omega
  omega

def positiveCells {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) : Finset V :=
  Finset.univ.filter fun j => 0 < extra M R i j

noncomputable def cellOrder {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) : List V :=
  (positiveCells M R i).toList.mergeSort fun a b => decide (extra M R i b ≤ extra M R i a)

noncomputable def vertexParts {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) : List ℕ :=
  (cellOrder M R i).map (extra M R i)

theorem cellOrder_perm {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) :
    (cellOrder M R i).Perm (positiveCells M R i).toList := List.mergeSort_perm _ _

theorem cellOrder_pos {k : ℕ} {M : V → V → Bool} {R : Fin k → Box} {i j : V}
    (h : j ∈ cellOrder M R i) : 0 < extra M R i j :=
  (Finset.mem_filter.mp (Finset.mem_toList.mp ((cellOrder_perm M R i).mem_iff.mp h))).2

theorem vertexParts_sorted {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i : V) :
    (vertexParts M R i).Pairwise (· ≥ ·) := by
  rw [vertexParts,List.pairwise_map]
  have h := List.pairwise_mergeSort
    (le := fun a b : V => decide (extra M R i b ≤ extra M R i a))
    (fun a b c ab bc => decide_eq_true (le_trans (of_decide_eq_true bc) (of_decide_eq_true ab)))
    (fun a b => by simpa using le_total (extra M R i b) (extra M R i a))
    (positiveCells M R i).toList
  simpa only [cellOrder,decide_eq_true_eq] using h

theorem vertexParts_sum {α : Type*} [AddCommMonoid α] {k : ℕ} (M : V → V → Bool)
    (R : Fin k → Box) (i : V) (f : ℕ → α) (h : f 0 = 0) :
    ((vertexParts M R i).map f).sum = ∑ j, f (extra M R i j) := by
  simp only [vertexParts,List.map_map]
  rw [((cellOrder_perm M R i).map (f ∘ extra M R i)).sum_eq,Finset.sum_map_toList]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj no
  have e : extra M R i j = 0 := by simpa [positiveCells] using no
  change f (extra M R i j) = 0
  rw [e,h]

theorem extra_le_degree {k : ℕ} (M : V → V → Bool) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2) (i j : V) :
    extra M R i j ≤ degree R i - 1 := by
  cases h : M i j
  · have b := Finset.card_le_card (Finset.inter_subset_left :
      rowSupport R i ∩ colSupport R j ⊆ rowSupport R i)
    rw [support_inter_card] at b
    simpa only [extra,zeroEntry,h,Bool.false_eq_true,↓reduceIte,degree] using Nat.sub_le_sub_right b 1
  · rw [extra_eq_zero_of_incident M R good h]
    exact Nat.zero_le _

theorem second_bound {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (i j : V) (z : ℕ)
    (hz : 1 ≤ z) (bound : ∀ j', j' ≠ j → extra M R i j' + 1 ≤ z) :
    (vertexParts M R i).getD 1 0 + 1 ≤ z := by
  have nodup := (cellOrder_perm M R i).nodup_iff.mpr (positiveCells M R i).nodup_toList
  have sorted := vertexParts_sorted M R i
  unfold vertexParts at sorted ⊢
  cases eq : cellOrder M R i with
  | nil => simpa using hz
  | cons a rest =>
    cases rest with
    | nil => simpa using hz
    | cons b bs =>
      rw [eq] at nodup sorted
      simp only [List.map_cons,List.getD_cons_succ,List.getD_cons_zero]
      simp only [List.map_cons] at sorted
      have ba : extra M R i b ≤ extra M R i a :=
        (List.pairwise_cons.mp sorted).1 _ (List.mem_cons_self ..)
      by_cases h : b = j
      · have ab : a ≠ j := by
          subst j
          exact fun e => (List.nodup_cons.mp nodup).1 (by simp [e])
        exact (Nat.add_le_add_right ba 1).trans (bound a ab)
      · exact bound b h

theorem perimeter_bound {k : ℕ} (R : Fin k → Box) (S T : Finset (Fin k))
    (δ r : ℕ) (db : δ ≤ 45) (mlo : 0 < (S ∩ T).card) (mhi : (S ∩ T).card ≤ 7)
    (ex : (S \ T).card ≤ r) (nb : r + T.card - (S ∩ T).card ≤ 10)
    (budget : (∑ t, deficit (boxSize (R t))) ≤ δ)
    (okay : ∀ t, boxSize (R t) ∈ dims) :
    16*(S ∩ T).card + 6*(S \ T).card + 6*(T \ S).card ≤
      (∑ t ∈ S, (R t).2.card) + (∑ t ∈ T, (R t).1.card) +
        gapUpper (S ∩ T).card (r + T.card - (S ∩ T).card) δ := by
  let C := S ∩ T
  let A := S \ T
  let B := T \ S
  have AB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro t ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have CAB : Disjoint C (A ∪ B) := by
    apply Finset.disjoint_left.mpr
    intro t hc hu
    obtain ⟨l,r⟩ := Finset.mem_inter.mp hc
    rcases Finset.mem_union.mp hu with ha | hb
    · exact (Finset.mem_sdiff.mp ha).2 r
    · exact (Finset.mem_sdiff.mp hb).2 l
  have ca : C ∪ A = S := by
    ext t; simp [C,A] <;> tauto
  have cb : C ∪ B = T := by
    ext t; simp [C,B] <;> tauto
  have dca : Disjoint C A := CAB.mono_right Finset.subset_union_left
  have dcb : Disjoint C B := CAB.mono_right Finset.subset_union_right
  have toShapesSum (F : Finset (Fin k)) (f : (ℕ × ℕ) → ℕ) :
      ((F.toList.map fun t => boxSize (R t)).map f).sum = ∑ t ∈ F, f (boxSize (R t)) := by
    simp only [List.map_map,Finset.sum_map_toList,Function.comp_apply]
  have lengths (F : Finset (Fin k)) : (F.toList.map fun t => boxSize (R t)).length = F.card := by
    simp
  have ok (F : Finset (Fin k)) (p : ℕ × ℕ) (h : p ∈ F.toList.map fun t => boxSize (R t)) :
      p ∈ dims := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp h
    exact okay t
  have cost : (∑ t ∈ C, deficit (boxSize (R t))) +
      (∑ t ∈ A ∪ B, deficit (boxSize (R t))) ≤ δ := by
    rw [← Finset.sum_union CAB]
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans budget
  have bc : B.card + C.card = T.card := by
    simpa only [B,C,Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S
  have nmax : (A ∪ B).card ≤ r + T.card - C.card := by
    rw [Finset.card_union_of_disjoint AB]
    change A.card ≤ r at ex
    omega
  have nsmall : (A ∪ B).card ≤ 10 := nmax.trans nb
  have gap := gap_bound (δ := δ)
    (C.toList.map fun t => boxSize (R t)) ((A ∪ B).toList.map fun t => boxSize (R t))
    (by rwa [lengths]) (by rwa [lengths]) db (ok C) (ok (A ∪ B))
    (by simpa only [toShapesSum] using cost)
  rw [lengths,lengths,toShapesSum,toShapesSum,Finset.sum_union AB] at gap
  have gap' := gap.trans (gap_mono_extra nmax mhi nb db)
  have estC : 16*C.card ≤ (∑ t ∈ C, (R t).2.card) +
      (∑ t ∈ C, (R t).1.card) + (∑ t ∈ C, commonGap (boxSize (R t))) := by
    have h := Finset.sum_le_sum (s := C) (fun t _ =>
      show 16 ≤ (R t).2.card + (R t).1.card + commonGap (boxSize (R t)) by
        unfold commonGap boxSize; omega)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at h
    omega
  have estA : 6*A.card ≤ (∑ t ∈ A, (R t).2.card) + ∑ t ∈ A, extraGap (boxSize (R t)) := by
    have h := Finset.sum_le_sum (s := A) (fun t _ =>
      show 6 ≤ (R t).2.card + extraGap (boxSize (R t)) by
        have v := Nat.min_le_right (R t).1.card (R t).2.card
        unfold extraGap boxSize; omega)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at h
    omega
  have estB : 6*B.card ≤ (∑ t ∈ B, (R t).1.card) + ∑ t ∈ B, extraGap (boxSize (R t)) := by
    have h := Finset.sum_le_sum (s := B) (fun t _ =>
      show 6 ≤ (R t).1.card + extraGap (boxSize (R t)) by
        have v := Nat.min_le_left (R t).1.card (R t).2.card
        unfold extraGap boxSize; omega)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at h
    omega
  change 16*C.card + 6*A.card + 6*B.card ≤ _ + _ + gapUpper C.card (r+T.card-C.card) δ
  have eqA : (∑ t ∈ S, (R t).2.card) =
      (∑ t ∈ C, (R t).2.card) + ∑ t ∈ A, (R t).2.card := by rw [← ca,Finset.sum_union dca]
  have eqB : (∑ t ∈ T, (R t).1.card) =
      (∑ t ∈ C, (R t).1.card) + ∑ t ∈ B, (R t).1.card := by rw [← cb,Finset.sum_union dcb]
  rw [eqA,eqB]
  omega

theorem cell_multiplicity_of_extra {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2) {i j : V}
    (positive : 0 < extra M R i j) :
    multiplicity R i j = extra M R i j + 1 := by
  have h : M i j = false := by
    by_contra! e
    rw [extra_eq_zero_of_incident M R good (by simpa using e)] at positive
    omega
  simp only [extra, zeroEntry, h, Bool.false_eq_true, ↓reduceIte] at positive ⊢
  omega

theorem transfer_threshold {d e n m count g : ℕ} {x : ℤ}
    (a : count ≤ n) (b : count ≤ m)
    (bound : 16*count + 6*(n-count) + 6*(m-count) ≤ 25+d+(25+e)+g)
    (low : (d : ℤ)-6*n ≤ x) :
    (e : ℤ)-6*m ≥ 4*(count : ℤ)-50-g-x := by omega

theorem tagged_transfer {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (deg : Area.Moments.rowDegree M) (coldeg : Area.Moments.rowDegree (transposeMatrix M))
    (join : Area.Moments.uniqueJoin M)
    (closed : ∀ t, rectClosed M (R t))
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (width : ∀ i, (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i)
    (widthT : ∀ j, (∑ t ∈ rowSupport (flip R) j, (flip R t).2.card) =
      25 + rowLoad (transposeMatrix M) (flip R) j)
    (δ : ℕ) (db : δ ≤ 45)
    (budget : (∑ t, deficit (boxSize (R t))) ≤ δ)
    (ok : ∀ t, boxSize (R t) ∈ dims)
    (okT : ∀ t, boxSize (flip R t) ∈ dims)
    (budgetT : (∑ t, deficit (boxSize (flip R t))) ≤ δ)
    (q : ChargeParameter) (qr : 3 ≤ qMult q ∧ qMult q ≤ 7 ∧
      qExtra q ≤ qAllowance q ∧ qAllowance q ≤ 2)
    (i j : V) (mult : qMult q = extra M R i j + 1)
    (low : lowTag q (degree R i) (rowLoad M R i) (isBad R i) = true) :
    highTag q δ (degree (flip R) j) (rowLoad (transposeMatrix M) (flip R) j)
      ((vertexParts (transposeMatrix M) (flip R) j).getD 1 0) = true := by
  unfold highTag
  split
  · rfl
  rename_i notTail
  have good (t : Fin k) : Area.Moments.EmptyRectangle M (R t).1 (R t).2 :=
    fun a ha => ((closed t).1 a).mp ha
  let S := rowSupport R i
  let T := rowSupport (flip R) j
  let C := S ∩ T
  have tm : T = colSupport R j := rfl
  have cm : C.card = qMult q := by
    rw [show C = rowSupport R i ∩ colSupport R j by rw [← tm],support_inter_card,
      cell_multiplicity_of_extra R good (by omega),mult]
  have right : degree (flip R) j = T.card := rfl
  have left : degree R i = S.card := rfl
  have Cleft := Finset.card_le_card (Finset.inter_subset_left : C ⊆ S)
  have Cright := Finset.card_le_card (Finset.inter_subset_right : C ⊆ T)
  have sa : (S \ T).card + C.card = S.card := Finset.card_sdiff_add_card_inter S T
  have sb : (T \ S).card + C.card = T.card := by
    simpa only [C,Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S
  unfold lowTag at low
  have low' := of_decide_eq_true low
  obtain ⟨lr,lb,lx⟩ := low'
  obtain ⟨qmLo,qmHi,qrLe,qhLe⟩ := qr
  rw [left] at lr lb lx
  have small := (degree_small (flip R) widthT okT (budgetT.trans db) j (by omega)).2
  rw [right] at small
  have cm' : (S ∩ T).card = qMult q := cm
  have sq : (S \ T).card = S.card - qMult q := by omega
  have gap := perimeter_bound R S T δ (qExtra q) db (by rw [cm']; omega) (by rwa [cm'])
    (by rwa [sq]) (by rw [cm']; omega) budget ok
  have ws := width i
  have wt : (∑ t ∈ T, (R t).1.card) = 25 + rowLoad (transposeMatrix M) (flip R) j :=
    widthT j
  have p (a : V) (ae : a ≠ i) :
      extra (transposeMatrix M) (flip R) j a + 1 ≤ T.card - (2-qAllowance q) := by
    have dd := directed_diff R deg coldeg join closed covers (Ne.symm ae)
    have bad : (if isBad R i then 1 else 0) + (S \ rowSupport R a).card ≥ 2 := by
      cases eb : isBad R i
      · have nb : ¬ badVertex R i := fun yes => by
          have := (isBad_eq R i).2 yes
          simp [eb] at this
        simpa [eb,S] using dd.2 nb
      · have := dd.1
        simp only [eb, Bool.true_eq, ↓reduceIte]
        change 1 ≤ (S \ rowSupport R a).card at this
        omega
    have tw := inter_two_bound T S (rowSupport R a)
    have ti : (T ∩ S).card = qMult q := by rw [Finset.inter_comm]; exact cm
    have ta : (T ∩ rowSupport R a).card = multiplicity R a j := by
      rw [Finset.inter_comm,tm,support_inter_card]
    rw [ti,ta] at tw
    rw [show extra (transposeMatrix M) (flip R) j a = extra M R a j by exact transpose_extra M R a j]
    by_cases ea : extra M R a j = 0
    · rw [ea]; omega
    · have eq := cell_multiplicity_of_extra R good (i:=a) (j:=j) (by omega)
      omega
  have second := second_bound (transposeMatrix M) (flip R) j i (T.card - (2-qAllowance q))
    (by omega) p
  apply decide_eq_true
  rw [right]
  constructor
  · omega
  · have per :
        16 * C.card + 6 * (S \ T).card + 6 * (T \ S).card ≤
          25 + rowLoad M R i + (25 + rowLoad (transposeMatrix M) (flip R) j) +
            gapUpper C.card (qExtra q + T.card - C.card) δ := by
      rw [← ws, ← wt]
      exact gap
    have tq : (T \ S).card = T.card - qMult q := by omega
    rw [cm,sq,tq] at per
    have qc₁ : qMult q ≤ S.card := by omega
    have qc₂ : qMult q ≤ T.card := by omega
    exact transfer_threshold qc₁ qc₂ per lx


theorem sum_map_mono {α β : Type*} [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    (xs : List α) {f g : α → β} (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    exact add_le_add (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

set_option maxHeartbeats 2000000 in
theorem parameter_spec {δ : ℕ} (db : δ ≤ 45) (yes : possibleBudget δ = true) :
    let p := parameterAt δ
    (∀ q ∈ terms p, 3 ≤ qMult q ∧ qMult q ≤ 7 ∧
       qExtra q ≤ qAllowance q ∧ qAllowance q ≤ 2) ∧
    (∀ m < 8, (((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤
      (m-1)*tailWeight p) ∧
    tailWeight p ≤ slopeWeight p ∧
    1000000 ≤ baseWeight p + ((slopeWeight p : ℤ) - tailWeight p)*33 ∧
    62*baseWeight p + 2*(125-(δ : ℤ))*slopeWeight p +
      ((min 62 (allowanceUpper 0 δ) : ℕ) : ℤ)*parityWeight p +
      (allowanceUpper 1 δ : ℤ)*badWeight p < 32000000 := by
  have h := parameterChecks ⟨δ, by omega⟩
  change checkParameters δ = true at h
  unfold checkParameters at h
  rw [if_pos yes] at h
  dsimp only at h ⊢
  generalize parameterAt δ = p at h ⊢
  have ⟨hw,ineq⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨valid,weights⟩ := Bool.and_eq_true_iff.mp hw
  obtain ⟨tail,incr,obj⟩ := of_decide_eq_true ineq
  refine ⟨?_,?_,tail,incr,obj⟩
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp valid q hq)
  · intro m hm
    exact of_decide_eq_true (List.all_eq_true.mp weights m (List.mem_range.mpr hm))

theorem tagValue_ge (p : Bool) : 0 ≤ tagValue p := by cases p <;> decide
theorem tagValue_le (p : Bool) : tagValue p ≤ 1 := by cases p <;> decide

theorem charge_mono (L₁ H₁ L₂ H₂ : Bool)
    (t₁ : L₁ = true → H₂ = true) (t₂ : L₂ = true → H₁ = true) :
    tagValue L₁ - tagValue H₁ + (tagValue L₂ - tagValue H₂) ≤ 0 := by
  cases L₁ <;> cases H₁ <;> cases L₂ <;> cases H₂ <;> simp_all [tagValue]

theorem fee_pair_nonpos (p : Parameters) (δ n d s n' d' s' e : ℕ) (b b' : Bool)
    (t₁ : ∀ q ∈ terms p, qMult q = e+1 → lowTag q n d b = true →
      highTag q δ n' d' s' = true)
    (t₂ : ∀ q ∈ terms p, qMult q = e+1 → lowTag q n' d' b' = true →
      highTag q δ n d s = true) :
    fee p δ n d s b e + fee p δ n' d' s' b' e ≤ 0 := by
  unfold fee
  rw [← List.sum_map_add]
  have z := sum_map_mono (terms p)
    (f := fun q =>
      (if qMult q = e+1 then (qWeight q : ℤ) *
        (tagValue (lowTag q n d b) - tagValue (highTag q δ n d s)) else 0) +
      (if qMult q = e+1 then (qWeight q : ℤ) *
        (tagValue (lowTag q n' d' b') - tagValue (highTag q δ n' d' s')) else 0))
    (g := fun _ => (0 : ℤ)) (fun q hq => by
    by_cases eq : qMult q = e+1
    · simp only [if_pos eq]
      rw [← mul_add]
      exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (charge_mono _ _ _ _
        (t₁ q hq eq) (t₂ q hq eq))
    · simp [eq])
  simpa using z

theorem fee_lower (p : Parameters) (δ n d s e : ℕ) (b : Bool)
    (valid : ∀ q ∈ terms p, qMult q ≤ 7)
    (weights : ∀ m < 8, (((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤
      (m-1)*tailWeight p) :
    -((tailWeight p : ℤ)*e) ≤ fee p δ n d s b e := by
  let xs := (terms p).filter (fun q => qMult q == e+1)
  let f := fun q : ChargeParameter =>
    (qWeight q : ℤ) * (tagValue (lowTag q n d b) - tagValue (highTag q δ n d s))
  have eq : fee p δ n d s b e = (xs.map f).sum := by
    unfold fee xs
    induction terms p with
    | nil => rfl
    | cons q qs ih =>
      by_cases h : qMult q = e+1 <;> simp [h,f,ih]
  have w : (xs.map qWeight).sum ≤ e*tailWeight p := by
    by_cases h : e+1 < 8
    · simpa only [Nat.add_sub_cancel] using weights (e+1) h
    · have em : xs = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro q hq
        obtain ⟨hq',eq'⟩ := List.mem_filter.mp hq
        have := valid q hq'
        have : qMult q = e+1 := beq_iff_eq.mp eq'
        omega
      simp [em]
  have lb := sum_map_mono xs (f := fun q => -(qWeight q : ℤ)) (g := f) (fun q _ => by
    have h : -1 ≤ tagValue (lowTag q n d b) - tagValue (highTag q δ n d s) :=
      by have a := tagValue_ge (lowTag q n d b); have b := tagValue_le (highTag q δ n d s); omega
    have hh := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg (qWeight q))
    simpa only [f,mul_neg,mul_one] using hh)
  rw [eq]
  have hw : ((xs.map qWeight).sum : ℤ) ≤ (e : ℤ)*tailWeight p := by exact_mod_cast w
  have lh : ((xs.map fun q => -(qWeight q : ℤ)).sum) = -((xs.map qWeight).sum : ℤ) := by
    induction xs with
    | nil => simp
    | cons q qs ih => simp [ih,neg_add,add_comm]
  rw [lh] at lb
  rw [mul_comm]
  omega

noncomputable def vertexCost {k : ℕ} (p : Parameters) (δ : ℕ) (M : V → V → Bool) (R : Fin k → Box)
    (i : V) : ℤ :=
  profileCost p δ (degree R i) (rowLoad M R i) (isBad R i) (vertexParts M R i)

theorem vertexCost_split {k : ℕ} (p : Parameters) (δ : ℕ) (M : V → V → Bool) (R : Fin k → Box)
    (i : V) (valid : ∀ q ∈ terms p, 3 ≤ qMult q) :
    vertexCost p δ M R i =
      profileBase p (rowLoad M R i) (isBad R i) +
      ∑ j, fee p δ (degree R i) (rowLoad M R i) ((vertexParts M R i).getD 1 0)
        (isBad R i) (extra M R i j) := by
  unfold vertexCost profileCost
  congr 1
  apply vertexParts_sum
  unfold fee
  have f (q : ChargeParameter) (hq : q ∈ terms p) : ¬qMult q = 0+1 := by
    have := valid q hq
    omega
  have e : ((terms p).map (fun q => if qMult q = 0+1 then
      (qWeight q : ℤ) * (tagValue (lowTag q (degree R i) (rowLoad M R i) (isBad R i)) -
        tagValue (highTag q δ (degree R i) (rowLoad M R i) ((vertexParts M R i).getD 1 0))) else
      0)) = (terms p).map (fun _ => (0 : ℤ)) := by
    apply List.map_congr_left
    intro q hq
    exact if_neg (f q hq)
  rw [e]
  simp

theorem sum_nat_map_cast (xs : List ℕ) :
    (xs.map (Nat.cast : ℕ → ℤ)).sum = (xs.sum : ℤ) := by
  exact (Nat.cast_list_sum (R := ℤ) xs).symm

theorem rationalDenom_real (d u : ℕ) :
    (rationalDenom d u : ℝ) = (25+(d : ℝ))^2 + 125*(u : ℝ) - 5*(d : ℝ)^2 := by
  unfold rationalDenom rationalNumer
  push_cast
  ring

theorem loss_of_numeric_bound (d u : ℕ) (cost : ℤ)
    (h : 1000000*rationalNumer d u ≤ cost*rationalDenom d u)
    (den : 0 < (25+(d : ℝ))^2 + 125*(u : ℝ) - 5*(d : ℝ)^2) :
    1000000*projectionLoss d u ≤ (cost : ℝ) := by
  have hr : (1000000 : ℝ) * (rationalNumer d u : ℝ) ≤
      (cost : ℝ) * (rationalDenom d u : ℝ) := by exact_mod_cast h
  rw [rationalDenom_real] at hr
  unfold projectionLoss
  rw [one_sub_div den.ne', ← mul_div_assoc]
  apply (div_le_iff₀ den).2
  convert hr using 1
  unfold rationalNumer
  push_cast
  ring

theorem loss_of_large_cost (d u : ℕ) (cost : ℤ) (h : 1000000 ≤ cost)
    (den : 0 < (25+(d : ℝ))^2 + 125*(u : ℝ) - 5*(d : ℝ)^2) :
    1000000*projectionLoss d u ≤ (cost : ℝ) := by
  have h' : (1000000 : ℝ) ≤ cost := by exact_mod_cast h
  unfold projectionLoss
  have q := div_nonneg (sq_nonneg (25+(d : ℝ))) den.le
  linarith only [h',q]

theorem profile_large_cost (p : Parameters) (δ n d : ℕ) (b : Bool) (parts : List ℕ)
    (loads : parts.sum = d) (large : 33 ≤ d)
    (valid : ∀ q ∈ terms p, qMult q ≤ 7)
    (weights : ∀ m < 8, (((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤
      (m-1)*tailWeight p)
    (tail : tailWeight p ≤ slopeWeight p)
    (incr : 1000000 ≤ baseWeight p + ((slopeWeight p : ℤ) - tailWeight p)*33) :
    1000000 ≤ profileCost p δ n d b parts := by
  let f := fee p δ n d (parts.getD 1 0) b
  have lb := sum_map_mono parts (f := fun e => -(tailWeight p : ℤ)*(e : ℤ)) (g := f)
    (fun e _ => by simpa only [neg_mul] using fee_lower p δ n d (parts.getD 1 0) e b valid weights)
  rw [List.sum_map_mul_left,sum_nat_map_cast,loads] at lb
  have even : 0 ≤ if d % 2 = 0 then (parityWeight p : ℤ) else 0 := by split <;> positivity
  have bad : 0 ≤ if b then (badWeight p : ℤ) else 0 := by split <;> positivity
  have a : 0 ≤ (slopeWeight p : ℤ) - tailWeight p := sub_nonneg.mpr (by exact_mod_cast tail)
  have z : (33 : ℤ) ≤ d := by exact_mod_cast large
  have inc := mul_le_mul_of_nonneg_left z a
  unfold profileCost profileBase
  change 1000000 ≤ _ + (parts.map f).sum
  nlinarith only [incr,inc,even,bad,lb]

set_option maxHeartbeats 3000000 in
theorem row_loss_mul_le {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (p : Parameters) (δ : ℕ) (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (width : ∀ i, (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i)
    (ok : ∀ t, boxSize (R t) ∈ dims)
    (db : δ ≤ 45) (budget : (∑ t, deficit (boxSize (R t))) ≤ δ)
    (yes : possibleBudget δ = true)
    (valid : ∀ q ∈ terms p, qMult q ≤ 7)
    (weights : ∀ m < 8, (((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤
      (m-1)*tailWeight p)
    (tail : tailWeight p ≤ slopeWeight p)
    (incr : 1000000 ≤ baseWeight p + ((slopeWeight p : ℤ) - tailWeight p)*33)
    (profiles : ∀ n d b parts, 0 < n → n ≤ 11 → d ≤ 32 →
      widthLower n (25+d) b ≤ δ → parts.sum = d →
      (∀ e ∈ parts, 0 < e) → (∀ e ∈ parts, e ≤ n-1) → parts.Pairwise (· ≥ ·) →
      0 ≤ rationalDenom d (parts.map fun e => e*e).sum → checkOne p δ n d b parts = true)
    (i : V) (den : 0 < (25 + (rowLoad M R i : ℝ))^2 + 125 *
      (∑ j, (extra M R i j)^2 : ℕ) - 5 * (rowLoad M R i : ℝ)^2) :
    1000000 * projectionLoss (rowLoad M R i) (∑ j, (extra M R i j)^2) ≤ vertexCost p δ M R i := by
  let parts := vertexParts M R i
  let d := rowLoad M R i
  let n := degree R i
  let b := isBad R i
  let u := ∑ j, (extra M R i j)^2
  have loads : parts.sum = d := by
    simpa only [parts,d,rowLoad,List.map_id,id_eq] using vertexParts_sum M R i id rfl
  have squares' : (parts.map fun e => e*e).sum = u := by
    simpa only [u,parts,pow_two] using vertexParts_sum M R i (fun e => e*e) rfl
  change 0 < (25 + (d : ℝ))^2 + 125 * (u : ℝ) - 5 * (d : ℝ)^2 at den
  change 1000000 * projectionLoss d u ≤ (profileCost p δ n d b parts : ℝ)
  by_cases small : d ≤ 32
  · obtain ⟨npos,nb⟩ := degree_small R width ok (budget.trans db) i small
    have w := width_bound (shapesAt R i)
      (by simpa [shapesAt_degree] using nb)
      (by rw [shapesAt_width,width]; omega)
      (fun x hx => by
        obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
        exact ok t)
    rw [shapesAt_degree,shapesAt_width,width] at w
    have w' : widthLower n (25+d) b ≤ δ := w.trans ((shapesAt_deficit R i).trans budget)
    have pos (e : ℕ) (he : e ∈ parts) : 0 < e := by
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
      exact cellOrder_pos hj
    have cap (e : ℕ) (he : e ∈ parts) : e ≤ n-1 := by
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      exact extra_le_degree M R good i j
    have denZ : 0 ≤ rationalDenom d (parts.map fun e => e*e).sum := by
      rw [squares']
      have h : 0 ≤ (rationalDenom d u : ℝ) := by rw [rationalDenom_real]; exact den.le
      exact_mod_cast h
    have check := profiles n d b parts npos nb small w' loads pos cap
      (vertexParts_sorted M R i) denZ
    have cle : 1000000*rationalNumer d (parts.map fun e => e*e).sum ≤
        profileCost p δ n d b parts * rationalDenom d (parts.map fun e => e*e).sum :=
      of_decide_eq_true check
    rw [squares'] at cle
    exact loss_of_numeric_bound d u _ cle den
  · exact loss_of_large_cost d u _
      (profile_large_cost p δ n d b parts loads (by omega) valid weights tail incr) den


def evenCount {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) : ℕ :=
  ∑ i : V, if rowLoad M R i % 2 = 0 then 1 else 0

noncomputable def badCount {k : ℕ} (R : Fin k → Box) : ℕ :=
  ∑ i : V, if isBad R i then 1 else 0

theorem sum_support {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) :
    (∑ i : V, ∑ t ∈ rowSupport R i, f t) = ∑ t, (R t).1.card * f t := by
  simp only [rowSupport,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

theorem even_count_le {k : ℕ} (M : V → V → Bool) (R : Fin k → Box)
    (width : ∀ i, (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i) :
    evenCount M R ≤ ∑ t, (R t).1.card * ((R t).2.card % 2) := by
  unfold evenCount
  rw [← sum_support R]
  apply Finset.sum_le_sum
  intro i _
  split
  rename_i even
  · by_contra! bad
    have each (t : Fin k) (ht : t ∈ rowSupport R i) : Even (R t).2.card := by
      have learn := Finset.single_le_sum (f := fun z => (R z).2.card % 2)
        (fun _ _ => Nat.zero_le _) ht
      exact Nat.even_iff.mpr (by omega)
    have t := Finset.even_sum _ each
    rw [width] at t
    have f := Nat.even_iff.mp t
    omega
  · exact Nat.zero_le _

theorem bad_count_le {k : ℕ} (R : Fin k → Box) :
    badCount R ≤ ∑ t, if badBit (boxSize (R t)) then (R t).1.card else 0 := by
  have eq : (∑ t, (R t).1.card * if badBit (boxSize (R t)) then 1 else 0) =
      ∑ t, if badBit (boxSize (R t)) then (R t).1.card else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    split <;> simp
  unfold badCount
  rw [← eq, ← sum_support R]
  apply Finset.sum_le_sum
  intro i _
  split
  rename_i yes
  · obtain ⟨t,ht,bt⟩ := (isBad_eq R i).mp yes
    have h := Finset.single_le_sum (f := fun z => if badBit (boxSize (R z)) then 1 else 0)
      (fun _ _ => Nat.zero_le _) ht
    have e : badBit (boxSize (R t)) = true := by
      unfold badBit badShape
      exact decide_eq_true bt
    simpa only [e, ↓reduceIte] using h
  · exact Nat.zero_le _

theorem flip_deficit {k : ℕ} (R : Fin k → Box) (t : Fin k) :
    deficit (boxSize (flip R t)) = deficit (boxSize (R t)) := by
  simp [deficit,boxSize,flip,transposeBox,Nat.mul_comm]

theorem combined_counts {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (width : ∀ i, (∑ t ∈ rowSupport R i, (R t).2.card) = 25 + rowLoad M R i)
    (widthT : ∀ j, (∑ t ∈ rowSupport (flip R) j, (flip R t).2.card) =
      25 + rowLoad (transposeMatrix M) (flip R) j)
    (δ : ℕ) (delta : (∑ t, deficit (boxSize (R t))) = δ)
    (db : δ ≤ 45) (ok : ∀ t, boxSize (R t) ∈ dims) :
    possibleBudget δ = true ∧
      evenCount M R + evenCount (transposeMatrix M) (flip R) ≤ min 62 (allowanceUpper 0 δ) ∧
      badCount R + badCount (flip R) ≤ allowanceUpper 1 δ := by
  let shapes := (Finset.univ : Finset (Fin k)).toList.map fun t => boxSize (R t)
  have h (f : (ℕ × ℕ) → ℕ) : (shapes.map f).sum = ∑ t, f (boxSize (R t)) := by
    simp only [shapes,List.map_map,Finset.sum_map_toList,Function.comp_apply]
  obtain ⟨yes,o,b⟩ := budget_bound shapes (by rw [h,delta]; exact db)
    (fun x hx => by
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
      exact ok t)
  simp only [h,delta] at yes o b
  refine ⟨yes,le_min ?_ ?_,?_⟩
  · have z (I : V → V → Bool) (B : Fin k → Box) : evenCount I B ≤ 31 := by
      calc
        _ ≤ ∑ i : V, (1 : ℕ) := Finset.sum_le_sum (fun i _ => by split <;> omega)
        _ = 31 := by simp
    have a := z M R
    have a' := z (transposeMatrix M) (flip R)
    omega
  · have a := Nat.add_le_add (even_count_le M R width)
      (even_count_le (transposeMatrix M) (flip R) widthT)
    apply a.trans
    rw [← Finset.sum_add_distrib]
    exact o
  · have a := Nat.add_le_add (bad_count_le R) (bad_count_le (flip R))
    apply a.trans
    rw [← Finset.sum_add_distrib]
    exact b

theorem sum_profileBase {k : ℕ} (M : V → V → Bool) (R : Fin k → Box) (p : Parameters) :
    (∑ i : V, profileBase p (rowLoad M R i) (isBad R i)) =
      31*baseWeight p + (∑ i : V, rowLoad M R i : ℕ) * (slopeWeight p : ℤ) +
        (evenCount M R : ℤ)*parityWeight p + (badCount R : ℤ)*badWeight p := by
  have ep (i : V) : (if rowLoad M R i % 2 = 0 then (parityWeight p : ℤ) else 0) =
      (parityWeight p : ℤ) * (if rowLoad M R i % 2 = 0 then 1 else 0) := by split <;> simp
  have bp (i : V) : (if isBad R i then (badWeight p : ℤ) else 0) =
      (badWeight p : ℤ) * (if isBad R i then 1 else 0) := by split <;> simp
  simp only [profileBase, ep,bp,Finset.sum_add_distrib,Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ,Fintype.card_fin, ← Finset.mul_sum]
  unfold evenCount badCount
  push_cast
  ring

theorem row_total_load {k : ℕ} {M : V → V → Bool} (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (counts : ∀ i, (Finset.univ.filter fun j => M i j = false).card = 25) :
    775 + ∑ i, rowLoad M R i = ∑ t : Fin k, (R t).1.card * (R t).2.card := by
  have eq : (∑ i, rowLoad M R i) = ∑ i, load (transposeMatrix M) (flip R) i := by
    unfold rowLoad load
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (transpose_extra M R i j).symm
  rw [eq]
  have g (t : Fin k) : Area.Moments.EmptyRectangle (transposeMatrix M) (flip R t).1 (flip R t).2 :=
    fun j hj i hi => good t i hi j hj
  have c (j i : V) (h : transposeMatrix M j i = false) :
      ∃ t, j ∈ (flip R t).1 ∧ i ∈ (flip R t).2 := by
    obtain ⟨t,hi,hj⟩ := covers i j h
    exact ⟨t,hj,hi⟩
  simpa only [flip,transposeBox,Nat.mul_comm] using total_load (flip R) g c counts

theorem incidence_gram (M : V → V → Bool) (deg : Area.Moments.rowDegree M)
    (join : Area.Moments.uniqueJoin M) (i i' : V) :
    (∑ j, (if M i j then (-4 : ℤ) else 1) * (if M i' j then -4 else 1)) =
      if i = i' then 121 else -4 := by
  let b (a j : V) : ℤ := if M a j = true then 1 else 0
  have row (a : V) : (∑ j, b a j) = 6 := by
    unfold b
    rw [← Finset.sum_filter]
    norm_num [Finset.sum_const,nsmul_eq_mul,deg a]
  have both : (∑ j, b i j * b i' j) = if i = i' then 6 else 1 := by
    by_cases eq : i = i'
    · subst i'
      rw [if_pos rfl, ← row i]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : M i j = true <;> simp [b,h]
    · have pair (j : V) : b i j * b i' j = if M i j = true ∧ M i' j = true then 1 else 0 := by
        by_cases h : M i j = true <;> by_cases h' : M i' j = true <;> simp [b,h,h']
      simp_rw [pair]
      rw [← Finset.sum_filter]
      norm_num [Finset.sum_const,nsmul_eq_mul,join i i' eq,eq]
  have term (j : V) : (if M i j then (-4 : ℤ) else 1) * (if M i' j then -4 else 1) =
      1 - 5*b i j - 5*b i' j + 25*(b i j*b i' j) := by
    by_cases h : M i j = true <;> by_cases h' : M i' j = true <;> norm_num [b,h,h']
  simp_rw [term,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,row,both]
  by_cases eq : i = i' <;> norm_num [eq]

theorem signedData_original :
    ∀ i i' : V, ∑ j, code i j * code i' j = if i = i' then 121 else -4 :=
  incidence_gram matrix Area.matrix_row_degree Area.matrix_row_join

theorem signedData_transpose :
    ∀ i i' : V, ∑ j, code j i * code j i' = if i = i' then 121 else -4 :=
  incidence_gram (transposeMatrix matrix) Area.matrix_col_degree Area.matrix_col_join

theorem row_counts : ∀ i : V, (Finset.univ.filter fun j => matrix i j = false).card = 25 := by
  intro i
  fin_cases i <;> decide +kernel

theorem row_loss_data {k : ℕ} {M : V → V → Bool} (R : Fin k → Box) (c : V → V → ℤ)
    (good : ∀ t, Area.Moments.EmptyRectangle (transposeMatrix M) (flip R t).1 (flip R t).2)
    (covers : ∀ i j, transposeMatrix M i j = false → ∃ t, i ∈ (flip R t).1 ∧ j ∈ (flip R t).2)
    (counts : ∀ i, (Finset.univ.filter fun j => M i j = false).card = 25)
    (ones : ∀ i j, transposeMatrix M i j = false → c i j = 1)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 121 else -4) :
    (∀ i, 0 < (25 + (rowLoad M R i : ℝ))^2 + 125 *
        (∑ j, (extra M R i j)^2 : ℕ) - 5 * (rowLoad M R i : ℝ)^2) ∧
      (31 : ℝ) - k ≤ ∑ i : V, projectionLoss (rowLoad M R i) (∑ j, (extra M R i j)^2) := by
  have l (i : V) : load (transposeMatrix M) (flip R) i = rowLoad M R i := by
    unfold load rowLoad
    apply Finset.sum_congr rfl
    intro j _
    exact transpose_extra M R i j
  have sq (i : V) : squares (transposeMatrix M) (flip R) i = ∑ j, (extra M R i j)^2 := by
    unfold squares
    apply Finset.sum_congr rfl
    intro j _
    rw [show extra (transposeMatrix M) (flip R) j i = extra M R i j from transpose_extra M R i j]
  refine ⟨fun i => ?_,?_⟩
  · obtain ⟨coord, normsq⟩ := column_stats (transposeMatrix M) c (flip R) good covers counts ones gram i
    rw [l,sq] at normsq
    have ne : columnWitness c (flip R) i ≠ 0 := by
      intro e
      rw [e] at coord
      change (0 : ℝ) = 25 + load (transposeMatrix M) (flip R) i at coord
      have h := Nat.cast_nonneg (α := ℝ) (load (transposeMatrix M) (flip R) i)
      linarith
    rw [← normsq]
    positivity
  · simpa only [l,sq] using sum_loss_ge (transposeMatrix M) c (flip R) good covers counts ones gram



def fits (d u : ℕ) (cost : ℤ) : Bool :=
  if 1000000 ≤ cost then true else
    decide ((1000000-cost)*rationalNumer d u ≤ cost*(25+(d : ℤ))^2)

theorem fits_sound {d u umax : ℕ} {L cost : ℤ}
    (verified : fits d umax L = true) (bound : u ≤ umax) (lb : L ≤ cost)
    (pos : 0 ≤ rationalDenom d u) :
    1000000*rationalNumer d u ≤ cost*rationalDenom d u := by
  unfold fits at verified
  have prod := mul_le_mul_of_nonneg_right lb pos
  apply le_trans _ prod
  unfold rationalDenom
  split at verified
  · rename_i g
    have pp := mul_le_mul_of_nonneg_right g pos
    have z := sq_nonneg ((25 : ℤ) + d)
    unfold rationalDenom at pp
    linarith
  · rename_i g
    have vu : rationalNumer d u ≤ rationalNumer d umax := by
      unfold rationalNumer
      have c : (u : ℤ) ≤ umax := by exact_mod_cast bound
      linarith
    have g' : 0 ≤ 1000000-L := by omega
    have h := (mul_le_mul_of_nonneg_left vu g').trans (of_decide_eq_true verified)
    linarith

def scanTail (d : ℕ) (f : ℕ → ℤ) (rate : ℤ) : ℕ → ℕ → ℕ → ℕ → ℤ → Bool
  | 0, cap, rem, u, cost => fits d (u+cap*rem) (cost + rate * rem)
  | fuel+1, cap, rem, u, cost =>
    if fits d (u+cap*rem) (cost + rate * rem) then true else
      if rem = 0 then false else
        (List.range (min cap rem)).all fun a =>
          let e := a+1
          scanTail d f rate fuel e (rem-e) (u+e*e) (cost+f e)

theorem squares_le (xs : List ℕ) (cap : ℕ) (vals : ∀ e ∈ xs, e ≤ cap) :
    (xs.map fun e => e*e).sum ≤ cap*xs.sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right a (vals a (List.mem_cons_self ..)))
      (ih fun e he => vals e (List.mem_cons_of_mem _ he))

theorem scanTail_sound (d : ℕ) (f : ℕ → ℤ) (rate : ℤ)
    (charge : ∀ e : ℕ, rate * (e : ℤ) ≤ f e) (xs : List ℕ)
    (uf : ∀ e ∈ xs, 0 < e) (ord : xs.Pairwise (· ≥ ·))
    {fuel cap rem u : ℕ} {cost : ℤ} (length : xs.length ≤ fuel) (s : xs.sum = rem)
    (vals : ∀ e ∈ xs, e ≤ cap)
    (pos : 0 ≤ rationalDenom d (u+(xs.map fun e => e*e).sum))
    (verified : scanTail d f rate fuel cap rem u cost = true) :
    1000000*rationalNumer d (u+(xs.map fun e => e*e).sum) ≤
      (cost+(xs.map f).sum)*rationalDenom d (u+(xs.map fun e => e*e).sum) := by
  have close (h : fits d (u+cap*rem) (cost+rate * rem) = true) :
      1000000*rationalNumer d (u+(xs.map fun e => e*e).sum) ≤
        (cost+(xs.map f).sum)*rationalDenom d (u+(xs.map fun e => e*e).sum) := by
    have sq := squares_le xs cap vals
    rw [s] at sq
    have low := sum_map_mono xs (f := fun e => rate * (e : ℤ)) (g := f) (fun e _ => charge e)
    rw [List.sum_map_mul_left,sum_nat_map_cast,s] at low
    exact fits_sound h (Nat.add_le_add_left sq _) (add_le_add (le_refl cost) low) pos
  cases fuel with
  | zero => exact close verified
  | succ fuel =>
    by_cases h : fits d (u+cap*rem) (cost + rate * rem) = true
    · exact close h
    · rw [scanTail, if_neg h] at verified
      have ne : rem ≠ 0 := by
        intro e
        rw [if_pos e] at verified
        cases verified
      rw [if_neg ne] at verified
      cases xs with
      | nil => exact (ne s.symm).elim
      | cons a as =>
        have pp := uf a (List.mem_cons_self ..)
        have vc := vals a (List.mem_cons_self ..)
        have sum : a+as.sum = rem := s
        have v := List.all_eq_true.mp verified (a-1) (List.mem_range.mpr (by omega))
        rw [show a-1+1 = a by omega] at v
        have h' := scanTail_sound d f rate charge as
          (fun e he => uf e (List.mem_cons_of_mem _ he)) (List.pairwise_cons.mp ord).2
          (by simpa only [List.length_cons,Nat.add_le_add_iff_right] using length)
          (by omega) ((List.pairwise_cons.mp ord).1)
          (by simpa only [List.map_cons,List.sum_cons,add_assoc] using pos) v
        simpa only [List.map_cons,List.sum_cons,add_assoc] using h'
termination_by fuel

def checkProfile (p : Parameters) (δ n d : ℕ) (b : Bool) : Bool :=
  let base := profileBase p d b
  if fits d ((n-1)*d) (base - (tailWeight p : ℤ)*d) then true else
    if d = 0 then fits d 0 base else
      (List.range (min (n-1) d)).all fun a =>
        let first := a+1
        if first = d then fits d (first*first) (base + fee p δ n d 0 b first) else
          (List.range (min first (d-first))).all fun v =>
            let second := v+1
            let f := fee p δ n d second b
            let rem := d-first-second
            scanTail d f (-(tailWeight p : ℤ)) rem second rem (first*first+second*second)
              (base + f first + f second)

theorem checkProfile_sound (p : Parameters) (δ n d : ℕ) (b : Bool) (parts : List ℕ)
    (valid : ∀ q ∈ terms p, qMult q ≤ 7)
    (weights : ∀ m < 8, (((terms p).filter (fun q => qMult q == m)).map qWeight).sum ≤
      (m-1)*tailWeight p)
    (load : parts.sum = d) (uf : ∀ e ∈ parts, 0 < e) (vc : ∀ e ∈ parts, e ≤ n-1)
    (ord : parts.Pairwise (· ≥ ·))
    (pos : 0 ≤ rationalDenom d (parts.map fun e => e*e).sum)
    (checked : checkProfile p δ n d b = true) : checkOne p δ n d b parts = true := by
  unfold checkOne
  apply decide_eq_true
  unfold checkProfile at checked
  dsimp only at checked
  split at checked
  · rename_i fast
    have sq := squares_le parts (n-1) vc
    rw [load] at sq
    have feeBound := sum_map_mono parts
      (f := fun e => -(tailWeight p : ℤ) * (e : ℤ))
      (g := fee p δ n d (parts.getD 1 0) b)
      (fun e _ => by
        simpa only [neg_mul] using (fee_lower p δ n d (parts.getD 1 0) e b valid weights))
    rw [List.sum_map_mul_left,sum_nat_map_cast,load] at feeBound
    have low : profileBase p d b - (tailWeight p : ℤ)*d ≤ profileCost p δ n d b parts := by
      unfold profileCost
      linarith
    exact fits_sound fast sq low pos
  · cases parts with
    | nil =>
      have eq : d = 0 := load.symm
      simp only [eq, ↓reduceIte] at checked
      have z := fits_sound checked (le_refl 0) (le_refl (profileBase p 0 b))
        (by simpa only [eq,List.map_nil,List.sum_nil] using pos)
      simpa [eq,profileCost] using z
    | cons a rest =>
      have pa := uf a (List.mem_cons_self ..)
      have ca := vc a (List.mem_cons_self ..)
      have s : a+rest.sum = d := load
      have nd : d ≠ 0 := by omega
      rw [if_neg nd] at checked
      have h := List.all_eq_true.mp checked (a-1) (List.mem_range.mpr (by omega))
      rw [show a-1+1 = a by omega] at h
      cases rest with
      | nil =>
        have eq : a = d := by simpa using s
        rw [if_pos eq] at h
        have z := fits_sound h (le_refl _) (le_refl _) (by simpa using pos)
        simpa [profileCost] using z
      | cons c cs =>
        have pc := uf c (by simp)
        have cap : c ≤ a := (List.pairwise_cons.mp ord).1 c (List.mem_cons_self ..)
        have s' : a+c+cs.sum = d := by simpa [add_assoc] using s
        have aq : a ≠ d := by omega
        rw [if_neg aq] at h
        have tr := List.all_eq_true.mp h (c-1) (List.mem_range.mpr (by omega))
        rw [show c-1+1 = c by omega] at tr
        let f := fee p δ n d c b
        have ls : cs.length ≤ cs.sum := by
          have w := sum_map_mono cs (f := fun _ => 1) (g := id) (fun e he => uf e (by simp [he]))
          simpa using w
        have cfee (e : ℕ) : -(tailWeight p : ℤ)*(e : ℤ) ≤ f e := by
          simpa only [neg_mul] using fee_lower p δ n d c e b valid weights
        have w := scanTail_sound d f (-(tailWeight p : ℤ)) cfee cs (fun e he => uf e (by simp [he]))
          (List.pairwise_cons.mp (List.pairwise_cons.mp ord).2).2
          (show cs.length ≤ d-a-c by omega) (show cs.sum = d-a-c by omega)
          (List.pairwise_cons.mp (List.pairwise_cons.mp ord).2).1
          (by simpa only [List.map_cons,List.sum_cons,add_assoc] using pos) tr
        simpa only [profileCost,List.getD_cons_succ,List.getD_cons_zero,List.map_cons,
          List.sum_cons,add_assoc,f] using w

def checksAt (δ n : ℕ) : Bool :=
  if possibleBudget δ then
    (List.range 33).all fun d => [false,true].all fun b =>
      if 0 < n ∧ widthLower n (25+d) b ≤ δ then
        checkProfile (parameterAt δ) δ n d b
      else true
  else true

theorem profiles_spec {δ : ℕ} (yes : possibleBudget δ = true) (db : δ ≤ 45)
    (checks : ∀ n ≤ 11, checksAt δ n = true)
    (n d : ℕ) (b : Bool) (parts : List ℕ) (npos : 0 < n) (nb : n ≤ 11) (ds : d ≤ 32)
    (w : widthLower n (25+d) b ≤ δ) (load : parts.sum = d)
    (uf : ∀ e ∈ parts, 0 < e) (vc : ∀ e ∈ parts, e ≤ n-1)
    (ord : parts.Pairwise (· ≥ ·)) (pos : 0 ≤ rationalDenom d (parts.map fun e => e*e).sum) :
    checkOne (parameterAt δ) δ n d b parts = true := by
  have ch := checks n nb
  unfold checksAt at ch
  rw [if_pos yes] at ch
  have e := List.all_eq_true.mp ch d (List.mem_range.mpr (by omega))
  have l := List.all_eq_true.mp e b (by cases b <;> simp)
  rw [if_pos ⟨npos,w⟩] at l
  obtain ⟨valid,weights,_,_,_⟩ := parameter_spec db yes
  exact checkProfile_sound (parameterAt δ) δ n d b parts
    (fun q hq => (valid q hq).2.1) weights load uf vc ord pos l

set_option maxHeartbeats 3000000 in
theorem exclude_cover (verify : ∀ (δ : Fin 46) (n : Fin 12), checksAt δ.val n.val = true)
    {k : ℕ} (R : Fin k → Box) (bound : k ≤ 15) (closed : ∀ t, rectClosed matrix (R t))
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) : False := by
  have good (t : Fin k) : Area.Moments.EmptyRectangle matrix (R t).1 (R t).2 :=
    fun i hi => ((closed t).1 i).mp hi
  obtain ⟨k15,db,ok⟩ := cert_size R bound good closed covers
  subst k
  let M := transposeMatrix matrix
  let T := flip R
  have closedT (t : Fin 15) : rectClosed M (T t) := closed_transpose matrix (R t) (closed t)
  have goodT (t : Fin 15) : Area.Moments.EmptyRectangle M (T t).1 (T t).2 :=
    fun j hj => ((closedT t).1 j).mp hj
  have coverT (j i : V) (h : M j i = false) : ∃ t, j ∈ (T t).1 ∧ i ∈ (T t).2 := by
    obtain ⟨t,hi,hj⟩ := covers i j h
    exact ⟨t,hj,hi⟩
  have width := row_load R good covers row_counts
  have widthT := row_load T goodT coverT count_table
  have okT (t : Fin 15) : boxSize (T t) ∈ dims := swap_shape (ok t)
  let δ := ∑ t, deficit (boxSize (R t))
  have budgetT : (∑ t, deficit (boxSize (T t))) ≤ δ := by simp only [T,flip_deficit,δ,le_refl]
  obtain ⟨yes,eBudget,bBudget⟩ := combined_counts R width widthT δ rfl db ok
  let p := parameterAt δ
  obtain ⟨valid,weights,tail,incr,obj⟩ := parameter_spec db yes
  have checks := profiles_spec yes db (fun n hn => verify ⟨δ,by omega⟩ ⟨n,by omega⟩)
  have ones (i j : V) (h : matrix i j = false) : code i j = 1 := by simp [code,h]
  have onesT (i j : V) (h : M i j = false) : code j i = 1 := ones j i h
  have goodTT (t : Fin 15) : Area.Moments.EmptyRectangle (transposeMatrix M) (flip T t).1 (flip T t).2 := by
    simpa only [M,T,flip_flip,flip_matrix] using good t
  have coverTT (i j : V) (h : transposeMatrix M i j = false) :
      ∃ t, i ∈ (flip T t).1 ∧ j ∈ (flip T t).2 := by
    simpa only [T,flip_flip] using covers i j h
  obtain ⟨denR,projR⟩ := row_loss_data R (fun i j => code j i) goodT coverT row_counts onesT signedData_transpose
  obtain ⟨denT,projT⟩ := row_loss_data T code goodTT coverTT count_table ones signedData_original
  have loR (i : V) := row_loss_mul_le R p δ good width ok db (le_refl δ) yes
    (fun q hq => (valid q hq).2.1) weights tail incr checks i (denR i)
  have loT (j : V) := row_loss_mul_le T p δ goodT widthT okT db budgetT yes
    (fun q hq => (valid q hq).2.1) weights tail incr checks j (denT j)
  have lowerR : (16000000 : ℤ) ≤ ∑ i : V, vertexCost p δ matrix R i := by
    have u := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => loR i)
    rw [← Finset.mul_sum] at u
    have e : (16000000 : ℝ) ≤ ∑ i : V, (vertexCost p δ matrix R i : ℝ) := by
      norm_num at projR
      linarith
    exact_mod_cast e
  have lowerT : (16000000 : ℤ) ≤ ∑ j : V, vertexCost p δ M T j := by
    have u := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => loT j)
    rw [← Finset.mul_sum] at u
    have e : (16000000 : ℝ) ≤ ∑ j : V, (vertexCost p δ M T j : ℝ) := by
      norm_num at projT
      linarith
    exact_mod_cast e
  let f (i j : V) := fee p δ (degree R i) (rowLoad matrix R i)
    ((vertexParts matrix R i).getD 1 0) (isBad R i) (extra matrix R i j)
  let g (j i : V) := fee p δ (degree T j) (rowLoad M T j)
    ((vertexParts M T j).getD 1 0) (isBad T j) (extra M T j i)
  have closedTT (t : Fin 15) : rectClosed (transposeMatrix M) (flip T t) := by
    simpa only [M,T,flip_flip,flip_matrix] using closed t
  have widthTT : ∀ i, (∑ t ∈ rowSupport (flip T) i, (flip T t).2.card) =
      25 + rowLoad (transposeMatrix M) (flip T) i := by
    simpa only [M,T,flip_flip,flip_matrix] using width
  have pairs (i j : V) : f i j + g j i ≤ 0 := by
    have extraT : extra M T j i = extra matrix R i j := transpose_extra matrix R i j
    dsimp only [f,g]
    rw [extraT]
    apply fee_pair_nonpos
    · intro q hq e low
      exact tagged_transfer R Area.matrix_row_degree Area.matrix_col_degree Area.matrix_row_join
        closed covers width widthT δ db (le_refl δ) ok okT budgetT q (valid q hq) i j e low
    · intro q hq e low
      have h :=
        tagged_transfer (M := M) T Area.matrix_col_degree Area.matrix_row_degree Area.matrix_col_join
          closedT coverT widthT widthTT δ db budgetT okT
          (by simpa only [T,flip_flip] using ok)
          (by simp only [T,flip_flip,δ,le_refl]) q (valid q hq) j i (by rw [extraT]; exact e) low
      simpa only [M,T,flip_flip,flip_matrix] using h
  have fees : (∑ i, ∑ j, f i j) + (∑ j, ∑ i, g j i) ≤ 0 := by
    rw [show (∑ j, ∑ i, g j i) = ∑ i, ∑ j, g j i by exact Finset.sum_comm,
      ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_nonpos (fun i _ => Finset.sum_nonpos (fun j _ => pairs i j))
  have sumD := total_deficit R good
  have dR := row_total_load R good covers row_counts
  have dT := row_total_load T goodT coverT count_table
  have arT : (∑ t, (T t).1.card * (T t).2.card) = ∑ t, (R t).1.card * (R t).2.card := by
    simp only [T,flip,transposeBox,Nat.mul_comm]
  rw [arT] at dT
  have loadZ : ((∑ i, rowLoad matrix R i : ℕ) : ℤ) = 125 - (δ : ℤ) := by omega
  have loadZT : ((∑ j, rowLoad M T j : ℕ) : ℤ) = 125 - (δ : ℤ) := by omega
  have ee : (evenCount matrix R : ℤ) + (evenCount M T : ℤ) ≤ min 62 (allowanceUpper 0 δ) := by
    exact_mod_cast eBudget
  have bb : (badCount R : ℤ) + (badCount T : ℤ) ≤ (allowanceUpper 1 δ : ℤ) := by
    exact_mod_cast bBudget
  have ee' := mul_le_mul_of_nonneg_right ee (Int.natCast_nonneg (parityWeight p))
  have bb' := mul_le_mul_of_nonneg_right bb (Int.natCast_nonneg (badWeight p))
  have aR (i : V) : vertexCost p δ matrix R i =
      profileBase p (rowLoad matrix R i) (isBad R i) + ∑ j, f i j :=
    vertexCost_split p δ matrix R i (fun q hq => (valid q hq).1)
  have aT (j : V) : vertexCost p δ M T j =
      profileBase p (rowLoad M T j) (isBad T j) + ∑ i, g j i :=
    vertexCost_split p δ M T j (fun q hq => (valid q hq).1)
  simp_rw [aR,Finset.sum_add_distrib,sum_profileBase,loadZ] at lowerR
  simp_rw [aT,Finset.sum_add_distrib,sum_profileBase,loadZT] at lowerT
  change 62*baseWeight p + 2*(125-(δ : ℤ))*slopeWeight p +
    ((min 62 (allowanceUpper 0 δ) : ℕ) : ℤ)*parityWeight p +
    (allowanceUpper 1 δ : ℤ)*badWeight p < 32000000 at obj
  linarith only [lowerR,lowerT,fees,ee',bb',obj]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
theorem profileChecks : ∀ (δ : Fin 46) (n : Fin 12), checksAt δ.val n.val = true := by
  intro δ
  fin_cases δ <;> decide +kernel

end PEqualNP.Outside.L_meta_10006

open PEqualNP.Outside.L_meta_10006

theorem PEqualNP.Outside.L_meta_10006 : ¬ (∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 15 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,bound,good,covers⟩
  let R (t : Fin L.length) : Box := closeBox matrix (L.get t)
  apply exclude_cover profileChecks R bound (fun t => closeBox_closed matrix (L.get t))
  intro i j h
  obtain ⟨r,mem,ri,rj⟩ := covers i j h
  obtain ⟨t,rfl⟩ := List.mem_iff_get.mp mem
  have g : Area.Moments.EmptyRectangle matrix (L.get t).1 (L.get t).2 :=
    good _ (List.mem_iff_get.mpr ⟨t,rfl⟩)
  exact ⟨t,closeBox_left matrix (L.get t) g ri,closeBox_right matrix (L.get t) rj⟩
