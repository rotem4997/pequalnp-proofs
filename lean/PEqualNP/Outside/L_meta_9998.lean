import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9998

def M : List ℕ := [1020, 2040, 2033, 2019, 1991, 1935, 1823, 1599, 1151, 255, 510]
def Cl : List ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 12, 14, 15, 16, 17, 24, 28, 30, 31, 32, 33, 34, 35, 48, 49, 56, 60, 62, 63, 64, 65, 66, 67, 68, 70, 71, 96, 97, 98, 99, 112, 113, 120, 124, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 140, 142, 143, 192, 193, 194, 195, 196, 198, 199, 224, 225, 226, 227, 240, 241, 248, 252, 254, 255, 256, 258, 260, 262, 264, 268, 270, 272, 280, 284, 286, 384, 386, 388, 390, 392, 396, 398, 448, 450, 452, 454, 480, 482, 496, 504, 508, 510, 512, 516, 520, 524, 528, 536, 540, 544, 560, 568, 572, 768, 772, 776, 780, 784, 792, 796, 896, 900, 904, 908, 960, 964, 992, 1008, 1016, 1020, 1024, 1025, 1027, 1031, 1032, 1039, 1040, 1041, 1048, 1055, 1056, 1057, 1059, 1072, 1073, 1080, 1087, 1088, 1089, 1091, 1095, 1120, 1121, 1123, 1136, 1137, 1144, 1151, 1536, 1537, 1539, 1543, 1544, 1551, 1552, 1553, 1560, 1567, 1568, 1569, 1571, 1584, 1585, 1592, 1599, 1792, 1793, 1795, 1799, 1800, 1807, 1808, 1809, 1816, 1823, 1920, 1921, 1923, 1927, 1928, 1935, 1984, 1985, 1987, 1991, 2016, 2017, 2019, 2032, 2033, 2040, 2047]
def z (i j : ℕ) : Bool := (M.getD i 0).testBit j == true
def zm (i : ℕ) : ℕ := M.getD i 0
def wm : List ℕ := [0, 0, 7, 1, 0, 2, 2, 0, 1, 7, 0, 0, 0, 0, 7, 1, 0, 2, 2, 0, 1, 7, 7, 0, 0, 0, 7, 1, 0, 2, 2, 0, 1, 1, 7, 0, 0, 0, 7, 1, 0, 2, 2, 0, 0, 1, 7, 0, 0, 0, 7, 1, 0, 2, 2, 2, 0, 1, 7, 0, 0, 0, 7, 1, 0, 2, 2, 2, 0, 1, 7, 0, 0, 0, 7, 1, 0, 0, 2, 2, 0, 1, 7, 0, 0, 0, 7, 1, 1, 0, 2, 2, 0, 1, 7, 0, 0, 0, 7, 7, 1, 0, 2, 2, 0, 1, 7, 0, 0, 0, 0, 7, 1, 0, 2, 2, 0, 1, 7, 0, 0]
def w (i j : ℕ) : ℕ := wm.getD (i * 11 + j) 0
/-- The weight of the largest rectangle with column set `c`. -/
def val (c : ℕ) : ℕ := ∑ i : Fin 11, if c &&& zm i.val = c then ∑ j : Fin 11, (if c.testBit j.val = true then w i.val j.val else 0) else 0

theorem cl1 : (2047 : ℕ) ∈ Cl := by decide +kernel
theorem cl2 : ∀ c ∈ Cl, ∀ i : Fin 11, Cl.contains (c &&& zm i.val) = true := by decide +kernel
theorem cl3 : ∀ c ∈ Cl, val c ≤ 34 := by decide +kernel
theorem zmz : ∀ i j : Fin 11, (M.getD i.val 0).testBit j.val = true ↔ (zm i.val).testBit j.val = true := by decide +kernel
theorem wz : ∀ i j : Fin 11, w i.val j.val ≠ 0 → (M.getD i.val 0).testBit j.val = true := by decide +kernel
theorem tot : ∑ i : Fin 11, ∑ j : Fin 11, w i.val j.val = 220 := by decide +kernel

theorem land_sub {a b : ℕ} (h : a &&& b = a) (j : ℕ) (hj : a.testBit j = true) : b.testBit j = true := by
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hj
  exact hj.2

/-- The common columns of a row set. -/
theorem common (A : Finset (Fin 11)) : ∃ c ∈ Cl, (∀ i ∈ A, c &&& zm i.val = c) ∧ ∀ j : Fin 11, (∀ i ∈ A, (zm i.val).testBit j.val = true) → c.testBit j.val = true := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨2047, cl1, by simp, fun j _ => ?_⟩
    revert j; decide +kernel
  | insert a A _ ih =>
    obtain ⟨c, hc, h1, h2⟩ := ih
    refine ⟨c &&& zm a.val, List.contains_iff_mem.1 (cl2 c hc a), ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [Nat.and_assoc, Nat.and_self]
      · rw [Nat.and_assoc, Nat.and_comm (zm a.val), ← Nat.and_assoc, h1 i hi]
    · intro j hj
      rw [Nat.testBit_and, h2 j fun i hi => hj i (Finset.mem_insert_of_mem hi), hj a (Finset.mem_insert_self _ _)]
      rfl

theorem rect (A B : Finset (Fin 11)) (h : ∀ i ∈ A, ∀ j ∈ B, (M.getD i.val 0).testBit j.val = true) :
    ∑ i ∈ A, ∑ j ∈ B, w i.val j.val ≤ 34 := by
  obtain ⟨c, hc, h1, h2⟩ := common A
  refine le_trans ?_ (cl3 c hc)
  have hB : ∀ j ∈ B, c.testBit j.val = true := fun j hj => h2 j fun i hi => (zmz i j).1 (h i hi j hj)
  unfold val
  calc ∑ i ∈ A, ∑ j ∈ B, w i.val j.val ≤ ∑ i ∈ A, (if c &&& zm i.val = c then ∑ j : Fin 11, (if c.testBit j.val = true then w i.val j.val else 0) else 0) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [if_pos (h1 i hi)]
        calc ∑ j ∈ B, w i.val j.val = ∑ j ∈ B, (if c.testBit j.val = true then w i.val j.val else 0) :=
              Finset.sum_congr rfl fun j hj => by rw [if_pos (hB j hj)]
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem cover (L : List (Finset (Fin 11) × Finset (Fin 11))) (h : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (M.getD i.val 0).testBit j.val = true) :
    ∑ i : Fin 11, ∑ j : Fin 11, (if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) ≤ 34 * L.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have h1 := rect r.1 r.2 (h r (by simp))
    have h2 : ∑ i ∈ r.1, ∑ j ∈ r.2, w i.val j.val = ∑ i : Fin 11, ∑ j : Fin 11, (if i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ r.1)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_subset (Finset.subset_univ r.2)]
        · exact Finset.sum_congr rfl fun j hj => by rw [if_pos ⟨hi, hj⟩]
        · intro j _ hj; rw [if_neg fun h => hj h.2]
      · intro i _ hi
        exact Finset.sum_eq_zero fun j _ => by rw [if_neg fun h => hi h.1]
    rw [h2] at h1
    rw [List.length_cons, Nat.mul_succ]
    calc _ ≤ ∑ i : Fin 11, ∑ j : Fin 11, ((if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) + (if i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0)) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases h3 : ∃ r' ∈ r :: L, i ∈ r'.1 ∧ j ∈ r'.2
          · rw [if_pos h3]
            obtain ⟨r', hr', h4⟩ := h3
            rcases List.mem_cons.1 hr' with rfl | hr'
            · rw [if_pos h4]; omega
            · rw [if_pos ⟨r', hr', h4⟩]; omega
          · rw [if_neg h3]; omega
      _ ≤ _ := by
          simp only [Finset.sum_add_distrib]
          omega

end PEqualNP.Outside.L_meta_9998

theorem PEqualNP.Outside.L_meta_9998 : ¬ (∃ L : List (Finset (Fin 11) × Finset (Fin 11)), L.length ≤ 6 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1020, 2040, 2033, 2019, 1991, 1935, 1823, 1599, 1151, 255, 510] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 11) (j : Fin 11), (([1020, 2040, 2033, 2019, 1991, 1935, 1823, 1599, 1151, 255, 510] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hL, h1, h2⟩
  have hc := PEqualNP.Outside.L_meta_9998.cover L h1
  have ht := PEqualNP.Outside.L_meta_9998.tot
  have he : ∑ i : Fin 11, ∑ j : Fin 11, (if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then PEqualNP.Outside.L_meta_9998.w i.val j.val else 0) = ∑ i : Fin 11, ∑ j : Fin 11, PEqualNP.Outside.L_meta_9998.w i.val j.val := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : PEqualNP.Outside.L_meta_9998.w i.val j.val = 0
    · rw [h0]; split_ifs <;> rfl
    · rw [if_pos (h2 i j (PEqualNP.Outside.L_meta_9998.wz i j h0))]
  rw [he, ht] at hc
  omega
