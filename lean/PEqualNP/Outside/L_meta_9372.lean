import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9372

private abbrev Point := Fin 16
private abbrev Rectangle := Finset Point × Finset Point

abbrev zeroAt (i j : Point) : Prop :=
  (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270,
    4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false

def points : Finset Point := Finset.univ.erase 0

def neighbors (i : Point) : Finset Point := points.filter (zeroAt i)

def active (S : Finset Point) : Finset Point := S ∩ points

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem neighbors_card : ∀ i : Point, i ≠ 0 → (neighbors i).card = 7 := by
  unfold neighbors zeroAt
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem symmetric : ∀ i j : Point, zeroAt i j → zeroAt j i := by
  unfold zeroAt
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem two_neighbors : ∀ i j : Point, i ≠ 0 → j ≠ 0 → i ≠ j →
    (neighbors i ∩ neighbors j).card ≤ 3 := by
  unfold neighbors zeroAt
  decide

def correct (r : Rectangle) : Prop := ∀ i ∈ r.1, ∀ j ∈ r.2, zeroAt i j

def charge (c : ℕ) : ℕ := if c = 0 then 0 else if 3 < c then 3 else 1

theorem active_nonzero {S : Finset Point} {i : Point} (hi : i ∈ active S) : i ≠ 0 := by
  have nz := (Finset.mem_inter.mp hi).2
  simpa [points] using nz

theorem oneBound {r : Rectangle} (ok : correct r) {i : Point}
    (hi : i ∈ active r.1) : (active r.2).card ≤ 7 := by
  have sub : active r.2 ⊆ neighbors i := by
    intro j hj
    obtain ⟨jr,jz⟩ := Finset.mem_inter.mp hj
    exact Finset.mem_filter.mpr ⟨jz,ok i (Finset.mem_inter.mp hi).1 j jr⟩
  exact (Finset.card_le_card sub).trans (le_of_eq (neighbors_card _ (active_nonzero hi)))

theorem twoBound {r : Rectangle} (ok : correct r) {i j : Point}
    (hi : i ∈ active r.1) (hj : j ∈ active r.1) (diff : i ≠ j) :
    (active r.2).card ≤ 3 := by
  have sub : active r.2 ⊆ neighbors i ∩ neighbors j := by
    intro p hp
    obtain ⟨pr,pz⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨pz,ok i (Finset.mem_inter.mp hi).1 p pr⟩,
       Finset.mem_filter.mpr ⟨pz,ok j (Finset.mem_inter.mp hj).1 p pr⟩⟩
  exact (Finset.card_le_card sub).trans
    (two_neighbors i j (active_nonzero hi) (active_nonzero hj) diff)

theorem swapCorrect {r : Rectangle} (ok : correct r) : correct (r.2,r.1) := by
  intro j hj i hi
  exact symmetric _ _ (ok i hi j hj)

theorem weightCap {r : Rectangle} (ok : correct r) :
    (active r.1).card * (2 * (active r.2).card + charge (active r.2).card) ≤ 21 := by
  let c := (active r.2).card
  change (active r.1).card * (2*c + charge c) ≤ 21
  by_cases h0 : c = 0
  · simp [h0, charge]
  · have nonempty : (active r.2).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j,hj⟩ := nonempty
    have row7 := oneBound (swapCorrect ok) hj
    change (active r.1).card ≤ 7 at row7
    by_cases h1 : c = 1
    · simpa [h1, charge, Nat.mul_comm] using (Nat.mul_le_mul_right 3 row7)
    · have two : 1 < (active r.2).card := by omega
      obtain ⟨i,hi,k,hk,ik⟩ := Finset.one_lt_card.mp two
      have row3 := twoBound (swapCorrect ok) hi hk ik
      change (active r.1).card ≤ 3 at row3
      by_cases small : c ≤ 3
      · have w : 2*c + charge c ≤ 7 := by
          rw [charge,ite_eq_right h0,ite_eq_right (by omega)]
          omega
        exact Nat.mul_le_mul row3 w
      · by_cases empty : (active r.1).card = 0
        · simp [empty]
        · obtain ⟨a,ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero empty)
          have c7 : c ≤ 7 := oneBound ok ha
          have row1 : (active r.1).card ≤ 1 := by
            by_contra h
            obtain ⟨b,hb,d,hd,bd⟩ := Finset.one_lt_card.mp (by omega : 1 < (active r.1).card)
            exact small (twoBound ok hb hd bd)
          have w : 2*c + charge c ≤ 17 := by
            rw [charge,ite_eq_right h0,ite_eq_left (by omega)]
            omega
          exact (Nat.mul_le_mul row1 w).trans (by decide)

theorem columnCharge {r : Rectangle} (ok : correct r) {i : Point}
    (hi : i ∈ active r.1) : (active r.2).card ≤ 3 * charge (active r.2).card := by
  have c7 := oneBound ok hi
  simp only [charge]
  split_ifs <;> omega

theorem coverImpossible (L : List Rectangle) (len : L.length ≤ 12)
    (ok : ∀ r ∈ L, correct r)
    (covers : ∀ i j : Point, zeroAt i j → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  classical
  let rects := L.toFinset
  let c (r : Rectangle) := (active r.2).card
  let w (r : Rectangle) := 2*c r + charge (c r)
  have budget : rects.card ≤ 12 := (List.toFinset_card_le L).trans len
  have good (r : Rectangle) (hr : r ∈ rects) : correct r := ok r (List.mem_toFinset.mp hr)
  have rowBound (i : Point) (hi : i ∈ points) :
      17 ≤ ∑ r ∈ rects, (if i ∈ r.1 then w r else 0) := by
    let used := rects.filter fun r => i ∈ r.1
    have sub : neighbors i ⊆ used.biUnion (fun r => active r.2) := by
      intro j hj
      obtain ⟨jz,zero⟩ := Finset.mem_filter.mp hj
      obtain ⟨r,hr,il,jr⟩ := covers i j zero
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,il⟩,
        Finset.mem_inter.mpr ⟨jr,jz⟩⟩
    have nz : i ≠ 0 := by simpa [points] using hi
    have area : 7 ≤ ∑ r ∈ used, c r := by
      rw [← neighbors_card _ nz]
      exact (Finset.card_le_card sub).trans Finset.card_biUnion_le
    have charges : (∑ r ∈ used, c r) ≤ 3 * ∑ r ∈ used, charge (c r) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (by
        intro r hr
        obtain ⟨valid,ir⟩ := Finset.mem_filter.mp hr
        exact columnCharge (good r valid) (Finset.mem_inter.mpr ⟨ir,hi⟩))
    rw [← Finset.sum_filter]
    change 17 ≤ ∑ r ∈ used, (2*c r + charge (c r))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  have rectBound (r : Rectangle) (hr : r ∈ rects) :
      (∑ i ∈ points, (if i ∈ r.1 then w r else 0)) ≤ 21 := by
    have eq : points.filter (fun i => i ∈ r.1) = active r.1 := by
      ext i
      simp [active, and_comm]
    rw [← Finset.sum_filter,eq,Finset.sum_const,nsmul_eq_mul]
    exact weightCap (good r hr)
  have cardPoints : points.card = 15 := by decide
  have low : 255 ≤ ∑ i ∈ points, ∑ r ∈ rects, (if i ∈ r.1 then w r else 0) := by
    calc
      255 = ∑ _i ∈ points, 17 := by simp [cardPoints]
      _ ≤ _ := Finset.sum_le_sum rowBound
  have up : (∑ i ∈ points, ∑ r ∈ rects, (if i ∈ r.1 then w r else 0)) ≤ 252 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _r ∈ rects, 21 := Finset.sum_le_sum rectBound
      _ = rects.card * 21 := by simp
      _ ≤ 252 := by omega
  omega

end PEqualNP.Outside.L_meta_9372

theorem PEqualNP.Outside.L_meta_9372 :
    ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 16)), L.length ≤ 12 ∧
      (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2,
        (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270,
          4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false) ∧
      ∀ (i : Fin 16) (j : Fin 16),
        (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270,
          4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false →
        ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, len, valid, covers⟩
  exact PEqualNP.Outside.L_meta_9372.coverImpossible L len valid covers
