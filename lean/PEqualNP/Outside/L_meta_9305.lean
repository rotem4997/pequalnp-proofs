import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9305

open scoped BigOperators

abbrev I := Fin 13
abbrev Rect := Finset I × Finset I

def rows : List ℕ :=
  [5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664]

def bit (i j : I) : Bool := (rows.getD i.val 0).testBit j.val

def cell (i j : I) : ℕ := if bit i j then 0 else 1

def coeff (i j : I) : ℤ := if bit j i then -2 else 1

def allowed (s : Finset I) : Finset I :=
  Finset.univ.filter fun j => ∀ i ∈ s, bit i j = false

def areaCheck : List I → ℕ → List I → Bool
  | [], n, c => decide (n * c.length ≤ 12)
  | i :: rs, n, c => decide ((n + rs.length + 1) * c.length ≤ 12) ||
      (areaCheck rs n c && areaCheck rs (n + 1) (c.filter fun j => !(bit i j)))

theorem areaCheck_sound (todo : List I) (n : ℕ) (c : List I) (s q : Finset I)
    (pass : areaCheck todo n c = true) (hs : s ⊆ todo.toFinset) (hq : q ⊆ c.toFinset)
    (clean : ∀ i ∈ s, ∀ j ∈ q, bit i j = false) :
    (n + s.card) * q.card ≤ 12 := by
  induction todo generalizing n c s q with
  | nil =>
    have hs0 : s = ∅ := by simpa using hs
    subst s
    have limit : n * c.length ≤ 12 := of_decide_eq_true pass
    have bound := (Finset.card_le_card hq).trans (List.toFinset_card_le c)
    simpa using (Nat.mul_le_mul_left n bound).trans limit
  | cons i rs ih =>
    simp only [areaCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at pass
    rcases pass with limit | ⟨skip, take⟩
    · have hcard := (Finset.card_le_card hs).trans (List.toFinset_card_le (i :: rs))
      have hcol := (Finset.card_le_card hq).trans (List.toFinset_card_le c)
      simp only [List.length_cons] at hcard
      exact (Nat.mul_le_mul (by omega) hcol).trans limit
    · by_cases his : i ∈ s
      · have hs' : s.erase i ⊆ rs.toFinset := by
          intro a ha
          obtain ⟨hne, has⟩ := Finset.mem_erase.mp ha
          simpa [hne] using hs has
        have hq' : q ⊆ (c.filter (fun j => !(bit i j))).toFinset := by
          intro j hj
          apply List.mem_toFinset.mpr
          exact List.mem_filter.mpr ⟨List.mem_toFinset.mp (hq hj), by simp [clean i his j hj]⟩
        have done := ih (n + 1) _ (s.erase i) q take hs' hq'
          fun a ha => clean a (Finset.mem_of_mem_erase ha)
        have eq : n + s.card = n + 1 + (s.erase i).card := by
          have h := Finset.card_erase_add_one his
          omega
        rwa [eq]
      · have hs' : s ⊆ rs.toFinset := by
          intro a ha
          have hne : a ≠ i := fun h => his (h ▸ ha)
          simpa [hne] using hs ha
        exact ih n c s q skip hs' hq clean

theorem areaCheck_join (i : I) (rs : List I) (n : ℕ) (c : List I)
    (skip : areaCheck rs n c = true)
    (take : areaCheck rs (n + 1) (c.filter fun j => !(bit i j)) = true) :
    areaCheck (i :: rs) n c = true := by
  simp [areaCheck, skip, take]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_0 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_1 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 4, 5, 6, 8, 9, 10, 11, 12] = true := by decide +kernel

theorem areaNode3_0 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] areaNode4_0 areaNode4_1

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_2 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [0, 3, 4, 5, 7, 8, 9, 10, 11] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_3 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [4, 5, 8, 9, 10, 11] = true := by decide +kernel

theorem areaNode3_1 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [0, 3, 4, 5, 7, 8, 9, 10, 11] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [0, 3, 4, 5, 7, 8, 9, 10, 11] areaNode4_2 areaNode4_3

theorem areaNode2_0 : areaCheck [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true :=
  areaCheck_join 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] areaNode3_0 areaNode3_1

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_4 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [2, 3, 4, 6, 7, 8, 9, 10, 12] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_5 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [4, 6, 8, 9, 10, 12] = true := by decide +kernel

theorem areaNode3_2 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [2, 3, 4, 6, 7, 8, 9, 10, 12] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [2, 3, 4, 6, 7, 8, 9, 10, 12] areaNode4_4 areaNode4_5

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_6 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 4, 7, 8, 9, 10] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_7 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [4, 8, 9, 10] = true := by decide +kernel

theorem areaNode3_3 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 4, 7, 8, 9, 10] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 4, 7, 8, 9, 10] areaNode4_6 areaNode4_7

theorem areaNode2_1 : areaCheck [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [2, 3, 4, 6, 7, 8, 9, 10, 12] = true :=
  areaCheck_join 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [2, 3, 4, 6, 7, 8, 9, 10, 12] areaNode3_2 areaNode3_3

theorem areaNode1_0 : areaCheck [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true :=
  areaCheck_join 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] areaNode2_0 areaNode2_1

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_8 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_9 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [1, 5, 6, 8, 9, 11] = true := by decide +kernel

theorem areaNode3_4 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] areaNode4_8 areaNode4_9

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_10 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 5, 7, 8, 9, 11] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_11 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [5, 8, 9, 11] = true := by decide +kernel

theorem areaNode3_5 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 5, 7, 8, 9, 11] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [3, 5, 7, 8, 9, 11] areaNode4_10 areaNode4_11

theorem areaNode2_2 : areaCheck [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] = true :=
  areaCheck_join 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] areaNode3_4 areaNode3_5

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_12 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [2, 3, 6, 7, 8, 9] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_13 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [6, 8, 9] = true := by decide +kernel

theorem areaNode3_6 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [2, 3, 6, 7, 8, 9] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [2, 3, 6, 7, 8, 9] areaNode4_12 areaNode4_13

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_14 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [3, 7, 8, 9] = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 600000 in
theorem areaNode4_15 : areaCheck [4, 5, 6, 7, 8, 9, 10, 11, 12] 4 [8, 9] = true := by decide +kernel

theorem areaNode3_7 : areaCheck [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [3, 7, 8, 9] = true :=
  areaCheck_join 3 [4, 5, 6, 7, 8, 9, 10, 11, 12] 3 [3, 7, 8, 9] areaNode4_14 areaNode4_15

theorem areaNode2_3 : areaCheck [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [2, 3, 6, 7, 8, 9] = true :=
  areaCheck_join 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 2 [2, 3, 6, 7, 8, 9] areaNode3_6 areaNode3_7

theorem areaNode1_1 : areaCheck [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] = true :=
  areaCheck_join 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 [1, 2, 3, 5, 6, 7, 8, 9, 11] areaNode2_2 areaNode2_3

theorem areaNode0_0 : areaCheck [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true :=
  areaCheck_join 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] areaNode1_0 areaNode1_1

theorem maxArea (s : Finset I) : s.card * (allowed s).card ≤ 12 := by
  have h := areaCheck_sound (List.finRange 13) 0 (List.finRange 13) s (allowed s)
    areaNode0_0 (by simp) (by simp) fun i hi j hj =>
      (Finset.mem_filter.mp hj).2 i hi
  simpa using h

theorem totalCells : ∑ i : I, ∑ j : I, cell i j = 117 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem leftInverse : ∀ i j : I,
    ∑ t : I, coeff i t * (cell t j : ℤ) = if i = j then 9 else 0 := by
  decide +kernel

theorem leftInverseQ (i j : I) :
    ∑ t : I, (coeff i t : ℚ) * (cell t j : ℚ) = if i = j then 9 else 0 := by
  by_cases h : i = j
  · subst j
    have z := leftInverse i i
    simp only [if_pos rfl] at z ⊢
    exact_mod_cast z
  · have z := leftInverse i j
    rw [if_neg h] at z ⊢
    exact_mod_cast z

theorem coeffBound (i j : I) : |(coeff i j : ℚ)| ≤ 2 := by
  unfold coeff
  split <;> norm_num

def ind (s : Finset I) (i : I) : ℕ := if i ∈ s then 1 else 0

theorem sumInd (s : Finset I) : ∑ i : I, ind s i = s.card := by
  classical
  have hf : Finset.univ.filter (fun i : I => i ∈ s) = s := by ext; simp
  simp only [ind, ← Finset.sum_filter]
  simp [hf]

def tally {k : ℕ} (r : Fin k → Rect) (i j : I) : ℕ :=
  ∑ t, ind (r t).1 i * ind (r t).2 j

theorem assocSum {α β R : Type*} [Fintype α] [Fintype β] [Semiring R]
    (a : α → R) (b : α → β → R) (x : β → R) :
    ∑ j, (∑ i, a i * b i j) * x j = ∑ i, a i * ∑ j, b i j * x j := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem tallyMass {k : ℕ} (r : Fin k → Rect) :
    ∑ i, ∑ j, tally r i j = ∑ t, (r t).1.card * (r t).2.card := by
  unfold tally
  calc
    _ = ∑ i, ∑ t, ∑ j, ind (r t).1 i * ind (r t).2 j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, ind (r t).1 i * ind (r t).2 j := Finset.sum_comm
    _ = _ := by simp only [← Finset.mul_sum, sumInd, ← Finset.sum_mul]

def rowMap {k : ℕ} (r : Fin k → Rect) : (I → ℚ) →ₗ[ℚ] (Fin k → ℚ) where
  toFun x t := ∑ j : I, (ind (r t).2 j : ℚ) * x j
  map_add' x y := by
    funext t
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem tallyKernel {k : ℕ} (r : Fin k → Rect) (x : I → ℚ)
    (hx : rowMap r x = 0) (i : I) :
    ∑ j : I, (tally r i j : ℚ) * x j = 0 := by
  have h (t : Fin k) : ∑ j : I, (ind (r t).2 j : ℚ) * x j = 0 := congrFun hx t
  unfold tally
  push_cast
  rw [assocSum]
  simp [h]

theorem recover (p : I) (x : I → ℚ) :
    ∑ i : I, (coeff p i : ℚ) * (∑ j : I, (cell i j : ℚ) * x j) = 9 * x p := by
  rw [← assocSum]
  simp [leftInverseQ, ite_mul]

theorem excessKernel (e : I → I → ℕ) (x : I → ℚ)
    (hMass : ∑ i, ∑ j, e i j ≤ 3)
    (hx : ∀ i, ∑ j : I, (cell i j : ℚ) * x j = -(∑ j : I, (e i j : ℚ) * x j)) :
    x = 0 := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset I)
    (fun j => |x j|) Finset.univ_nonempty
  have top (j : I) : |x j| ≤ |x p| := hp j (Finset.mem_univ j)
  have rowAbs (i : I) : |∑ j, (e i j : ℚ) * x j| ≤
      (∑ j, (e i j : ℚ)) * |x p| := by
    calc
      _ ≤ ∑ j, |(e i j : ℚ) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (e i j : ℚ) * |x p| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ e i j)]
        exact mul_le_mul_of_nonneg_left (top j) (by positivity)
      _ = _ := (Finset.sum_mul ..).symm
  have eqn : 9 * x p = -(∑ i, (coeff p i : ℚ) * ∑ j, (e i j : ℚ) * x j) := by
    rw [← recover p x]
    simp only [hx, mul_neg, Finset.sum_neg_distrib]
  have hMassQ : (∑ i, ∑ j, (e i j : ℚ)) ≤ 3 := by exact_mod_cast hMass
  have bound : 9 * |x p| ≤ 6 * |x p| := calc
    9 * |x p| = |9 * x p| := by rw [abs_mul]; norm_num
    _ = |∑ i, (coeff p i : ℚ) * ∑ j, (e i j : ℚ) * x j| := by rw [eqn, abs_neg]
    _ ≤ ∑ i, |(coeff p i : ℚ) * ∑ j, (e i j : ℚ) * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ((∑ j, (e i j : ℚ)) * |x p|) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (coeffBound p i) (rowAbs i) (abs_nonneg _) (by norm_num)
    _ = 2 * (∑ i, ∑ j, (e i j : ℚ)) * |x p| := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ 6 * |x p| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith
  funext j
  exact abs_eq_zero.mp (le_antisymm (by linarith [top j]) (abs_nonneg _))

theorem impossible (L : List Rect) (hk : L.length ≤ 10)
    (clean : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, bit i j = false)
    (cover : ∀ i j : I, bit i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  classical
  let r : Fin L.length → Rect := L.get
  have memR (t : Fin L.length) : r t ∈ L := List.get_mem L t
  have area (t : Fin L.length) : (r t).1.card * (r t).2.card ≤ 12 := by
    have sub : (r t).2 ⊆ allowed (r t).1 := by
      intro j hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun i hi => clean _ (memR t) _ hi _ hj⟩
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card sub)).trans (maxArea _)
  have mass : ∑ i, ∑ j, tally r i j ≤ 120 := calc
    _ = _ := tallyMass r
    _ ≤ ∑ _t : Fin L.length, 12 := Finset.sum_le_sum fun t _ => area t
    _ ≤ 120 := by simp; omega
  have dominates (i j : I) : cell i j ≤ tally r i j := by
    cases hb : bit i j with
    | true => simp [cell, hb]
    | false =>
      obtain ⟨q, hq, hi, hj⟩ := cover i j hb
      obtain ⟨t, rfl⟩ := List.mem_iff_get.mp hq
      have hone : ind (r t).1 i * ind (r t).2 j = 1 := by
        change i ∈ (r t).1 at hi
        change j ∈ (r t).2 at hj
        simp only [ind, if_pos hi, if_pos hj, Nat.mul_one]
      rw [cell, if_neg (by simp [hb]), ← hone]
      exact Finset.single_le_sum (f := fun u => ind (r u).1 i * ind (r u).2 j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  let e (i j : I) := tally r i j - cell i j
  have counts (i j : I) : cell i j + e i j = tally r i j := by
    dsimp [e]
    have lower := dominates i j
    omega
  have hmassE : ∑ i, ∑ j, e i j ≤ 3 := by
    have heq : (∑ i, ∑ j, cell i j) + (∑ i, ∑ j, e i j) = ∑ i, ∑ j, tally r i j := by
      simp only [← Finset.sum_add_distrib, counts]
    rw [totalCells] at heq
    omega
  have inj : Function.Injective (rowMap r) := by
    intro x y hxy
    have zero : rowMap r (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    apply sub_eq_zero.mp
    apply excessKernel e _ hmassE
    intro i
    have s := tallyKernel r (x - y) zero i
    have c (j : I) :
        (tally r i j : ℚ) = (cell i j : ℚ) + (e i j : ℚ) := by exact_mod_cast (counts i j).symm
    simp only [c, add_mul, Finset.sum_add_distrib] at s
    linarith
  have dim := LinearMap.finrank_le_finrank_of_injective (f := rowMap r) inj
  have hdim : 13 ≤ L.length := by simpa [Module.finrank_pi, I] using dim
  omega

end PEqualNP.Outside.L_meta_9305

theorem PEqualNP.Outside.L_meta_9305 :
  ¬ (∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hk, clean, cover⟩
  exact PEqualNP.Outside.L_meta_9305.impossible L hk clean cover
