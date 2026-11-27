import PEqualNP.Defs

-- Count incidences and ordered pairs in each selected set of rows.
-- Seven and eight rows require the parity of the incidence counts in both directions.
-- The resulting bounds cap every empty rectangle's area at 60, or 56 if its width is odd.
-- A cover of 13 rectangles has room for at most one odd-width rectangle.
-- Each of the six incident rows of one of its columns must then cover an even number of cells.

namespace PEqualNP.Outside.L_meta_10002_aux

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
open PEqualNP.Outside.L_meta_10002_aux.Moments
open PEqualNP.Outside.L_meta_10002_aux.Large (hit tally transpose empty_le_eight_of_seven empty_le_seven_of_eight)

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

theorem matrix_area_le_56_of_odd_width (A B : Finset (Fin 31))
    (rect : ∀ p ∈ A, ∀ l ∈ B, matrix p l = false) (oddWidth : B.card % 2 = 1) :
    A.card * B.card ≤ 56 := by
  obtain ⟨small,rs,cs⟩ := matrix_caps A B rect
  exact area_le_56_of_odd_width small rs cs oddWidth

namespace Cover

abbrev Vertex := Fin 31
abbrev Rectangle := Finset Vertex × Finset Vertex

def zeroRectangle (I : Vertex → Vertex → Bool) (R : Rectangle) : Prop :=
  ∀ i ∈ R.1, ∀ j ∈ R.2, I i j = false

def coversZeros (I : Vertex → Vertex → Bool) (L : List Rectangle) : Prop :=
  ∀ i j : Vertex, I i j = false → ∃ R ∈ L, i ∈ R.1 ∧ j ∈ R.2

def area (R : Rectangle) : ℕ := R.1.card * R.2.card
def totalArea (L : List Rectangle) : ℕ := (L.map area).sum

def oddWidth (R : Rectangle) : Bool := decide (R.2.card % 2 = 1)

def contribution (i : Vertex) (R : Rectangle) : ℕ :=
  if i ∈ R.1 then R.2.card else 0

def rowLoad (L : List Rectangle) (i : Vertex) : ℕ :=
  (L.map (contribution i)).sum

def rowUnion (i : Vertex) : List Rectangle → Finset Vertex
  | [] => ∅
  | R :: rest => if i ∈ R.1 then R.2 ∪ rowUnion i rest else rowUnion i rest

theorem rowUnion_contains {i j : Vertex} {L : List Rectangle} {R : Rectangle}
    (member : R ∈ L) (row : i ∈ R.1) (col : j ∈ R.2) : j ∈ rowUnion i L := by
  induction L with
  | nil => simp at member
  | cons Q rest ih =>
    rw [List.mem_cons] at member
    rcases member with rfl | later
    · simp [rowUnion, row, col]
    · by_cases active : i ∈ Q.1
      · have covered := ih later
        simp [rowUnion, active, covered]
      · simpa [rowUnion, active] using ih later

theorem rowUnion_card_le (i : Vertex) (L : List Rectangle) :
    (rowUnion i L).card ≤ rowLoad L i := by
  induction L with
  | nil => simp [rowUnion, rowLoad]
  | cons R rest ih =>
    by_cases active : i ∈ R.1
    · simpa [rowUnion, rowLoad, contribution, active] using
        (Finset.card_union_le R.2 (rowUnion i rest)).trans (Nat.add_le_add_left ih R.2.card)
    · simpa [rowUnion, rowLoad, contribution, active] using ih

theorem row_zeros {I : Vertex → Vertex → Bool}
    (degree : ∀ i, (Finset.univ.filter fun j => I i j = true).card = 6) (i : Vertex) :
    (Finset.univ.filter fun j => I i j = false).card = 25 := by
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Vertex)) (fun j => I i j = true)
  have edge := degree i
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at split
  omega

theorem coverage_cost {I : Vertex → Vertex → Bool} {L : List Rectangle}
    (degree : ∀ i, (Finset.univ.filter fun j => I i j = true).card = 6)
    (cover : coversZeros I L) (i : Vertex) : 25 ≤ rowLoad L i := by
  have subset : (Finset.univ.filter fun j => I i j = false) ⊆ rowUnion i L := by
    intro j absent
    obtain ⟨R, mem, row, col⟩ := cover i j (Finset.mem_filter.mp absent).2
    exact rowUnion_contains mem row col
  rw [← row_zeros degree i]
  exact (Finset.card_le_card subset).trans (rowUnion_card_le i L)

theorem sum_contribution (R : Rectangle) : (∑ i, contribution i R) = area R := by
  unfold contribution area
  rw [← Finset.sum_filter]
  simp

theorem sum_row_loads (L : List Rectangle) : (∑ i, rowLoad L i) = totalArea L := by
  induction L with
  | nil => simp [rowLoad, totalArea]
  | cons R rest ih =>
    have weights (i : Vertex) : rowLoad (R :: rest) i = contribution i R + rowLoad rest i := rfl
    simp only [weights, Finset.sum_add_distrib, sum_contribution, ih, totalArea, List.map_cons, List.sum_cons]

theorem area_with_penalty (L : List Rectangle)
    (cap : ∀ R ∈ L, area R ≤ 60)
    (oddCap : ∀ R ∈ L, oddWidth R = true → area R ≤ 56) :
    totalArea L + 4 * (L.filter oddWidth).length ≤ 60 * L.length := by
  induction L with
  | nil => simp [totalArea]
  | cons R rest ih =>
    have capR := cap R (by simp)
    have bound := ih (fun Q h => cap Q (by simp [h])) (fun Q h => oddCap Q (by simp [h]))
    cases odd : oddWidth R
    · simp only [totalArea, List.map_cons, List.sum_cons, List.filter_cons, odd,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] at bound ⊢
      omega
    · have small := oddCap R (by simp) odd
      simp only [totalArea, List.map_cons, List.sum_cons, List.filter_cons, odd,
        ↓reduceIte, List.length_cons] at bound ⊢
      omega

theorem only_one_odd {L : List Rectangle} (one : (L.filter oddWidth).length ≤ 1)
    {R S : Rectangle} (memR : R ∈ L) (oddR : oddWidth R = true)
    (memS : S ∈ L) (oddS : oddWidth S = true) : R = S := by
  have left : R ∈ L.filter oddWidth := List.mem_filter.mpr ⟨memR, oddR⟩
  have right : S ∈ L.filter oddWidth := List.mem_filter.mpr ⟨memS, oddS⟩
  generalize L.filter oddWidth = F at left right one
  cases F with
  | nil => simp at left
  | cons T rest =>
    have empty : rest = [] := List.length_eq_zero_iff.mp (by
      change rest.length + 1 ≤ 1 at one
      omega)
    subst rest
    simp_all

theorem row_load_even (L : List Rectangle) (i : Vertex)
    (even : ∀ R ∈ L, i ∈ R.1 → R.2.card % 2 = 0) : rowLoad L i % 2 = 0 := by
  induction L with
  | nil => simp [rowLoad]
  | cons R rest ih =>
    have tail := ih (fun Q h => even Q (by simp [h]))
    change (contribution i R + rowLoad rest i) % 2 = 0
    by_cases member : i ∈ R.1
    · have first := even R (by simp) member
      simp only [contribution, member, ↓reduceIte]
      rw [Nat.add_mod, first, tail]
    · simpa [contribution, member] using tail

theorem no_thirteen_of_area_bounds (I : Vertex → Vertex → Bool)
    (rows : ∀ i, (Finset.univ.filter fun j => I i j = true).card = 6)
    (cols : ∀ j, (Finset.univ.filter fun i => I i j = true).card = 6)
    (areaBound : ∀ R, zeroRectangle I R → area R ≤ 60)
    (oddBound : ∀ R, zeroRectangle I R → oddWidth R = true → area R ≤ 56)
    (L : List Rectangle) (size : L.length ≤ 13)
    (valid : ∀ R ∈ L, zeroRectangle I R) (cover : coversZeros I L) : False := by
  have cost := coverage_cost rows cover
  have start : 775 ≤ totalArea L := by
    rw [← sum_row_loads]
    simpa using (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => cost i :
      (∑ _i : Vertex, (25 : ℕ)) ≤ ∑ i, rowLoad L i)
  have upper := area_with_penalty L (fun R h => areaBound R (valid R h))
    (fun R h => oddBound R (valid R h))
  have one : (L.filter oddWidth).length ≤ 1 := by omega
  have column : ∃ j : Vertex, ∀ i, I i j = true → rowLoad L i % 2 = 0 := by
    by_cases existsOdd : ∃ R ∈ L, oddWidth R = true
    · obtain ⟨R, memR, oddR⟩ := existsOdd
      have oddCount : R.2.card % 2 = 1 := of_decide_eq_true oddR
      have positive : R.2.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, selected⟩ := positive
      refine ⟨j, fun i incident => row_load_even L i ?_⟩
      intro S memS inside
      by_contra! notEven
      have oddS : oddWidth S = true := decide_eq_true (by omega)
      have same := only_one_odd one memS oddS memR oddR
      subst S
      exact Bool.noConfusion ((valid R memR i inside j selected).symm.trans incident)
    · refine ⟨0, fun i _ => row_load_even L i ?_⟩
      intro R memR _
      by_contra! notEven
      exact existsOdd ⟨R, memR, decide_eq_true (by omega)⟩
  obtain ⟨j, even⟩ := column
  have adjusted (i : Vertex) : (25 : ℕ) + (if I i j = true then 1 else 0) ≤ rowLoad L i := by
    by_cases supported : I i j = true
    · have := even i supported
      simp only [supported, ↓reduceIte]
      have := cost i
      omega
    · simp [supported, cost i]
  have sumAdjusted := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => adjusted i
  simp only [Finset.sum_add_distrib, sum_row_loads] at sumAdjusted
  have columnSum : (∑ i : Vertex, (if I i j = true then (1 : ℕ) else 0)) = 6 := by
    rw [← Finset.sum_filter]
    simpa using cols j
  rw [columnSum] at sumAdjusted
  have total : (∑ _i : Vertex, (25 : ℕ)) = 775 := by decide
  rw [total] at sumAdjusted
  omega

end Cover

end PEqualNP.Outside.L_meta_10002_aux

theorem PEqualNP.Outside.L_meta_10002 :
    ¬ (∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 13 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2,
    (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840,
    536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344,
    109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717,
    142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j :
    Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420,
    268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672,
    54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182,
    71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i
    ∈ r.1 ∧ j ∈ r.2) := by
  intro ⟨L, size, valid, cover⟩
  apply PEqualNP.Outside.L_meta_10002_aux.Cover.no_thirteen_of_area_bounds
    PEqualNP.Outside.L_meta_10002_aux.matrix
    PEqualNP.Outside.L_meta_10002_aux.matrix_row_degree
    PEqualNP.Outside.L_meta_10002_aux.matrix_col_degree _ _ L size valid cover
  · intro R empty
    exact PEqualNP.Outside.L_meta_10002_aux.matrix_area_le_60 R.1 R.2 empty
  · intro R empty odd
    exact PEqualNP.Outside.L_meta_10002_aux.matrix_area_le_56_of_odd_width
      R.1 R.2 empty (of_decide_eq_true odd)
