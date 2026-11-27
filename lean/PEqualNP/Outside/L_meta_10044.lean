import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10044

def M : List ℕ := [5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829]
def Cl : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 48, 56, 64, 65, 66, 68, 72, 73, 80, 96, 112, 128, 129, 130, 132, 133, 136, 144, 146, 160, 161, 165, 192, 224, 256, 257, 258, 260, 261, 264, 266, 272, 273, 288, 292, 320, 321, 322, 323, 325, 330, 384, 389, 448, 512, 513, 514, 516, 520, 522, 528, 529, 532, 544, 545, 546, 576, 584, 640, 642, 644, 645, 646, 650, 660, 768, 778, 896, 1024, 1025, 1026, 1028, 1032, 1033, 1040, 1044, 1056, 1058, 1064, 1088, 1090, 1092, 1152, 1153, 1168, 1280, 1284, 1285, 1288, 1290, 1292, 1300, 1320, 1359, 1536, 1556, 1792, 1941, 2048, 2049, 2050, 2052, 2056, 2064, 2066, 2080, 2081, 2088, 2089, 2112, 2113, 2116, 2128, 2129, 2145, 2176, 2180, 2184, 2209, 2304, 2306, 2336, 2369, 2533, 2560, 2568, 2570, 2576, 2580, 2584, 2600, 2640, 2681, 2718, 3072, 3112, 3584, 3882, 4096, 4097, 4098, 4099, 4100, 4104, 4112, 4128, 4132, 4160, 4162, 4176, 4178, 4224, 4226, 4232, 4256, 4257, 4258, 4290, 4352, 4360, 4368, 4418, 4608, 4612, 4672, 4738, 4775, 5066, 5120, 5136, 5140, 5152, 5160, 5168, 5200, 5280, 5362, 5436, 6144, 6145, 6224, 6483, 7168, 7337, 7764, 8191]
def z (i j : ℕ) : Bool := (M.getD i 0).testBit j == false
def zm (i : ℕ) : ℕ := 8191 ^^^ M.getD i 0
def wm : List ℕ := [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0]
def w (i j : ℕ) : ℕ := wm.getD (i * 13 + j) 0
/-- The weight of the largest rectangle with column set `c`. -/
def val (c : ℕ) : ℕ := ∑ i : Fin 13, if c &&& zm i.val = c then ∑ j : Fin 13, (if c.testBit j.val = true then w i.val j.val else 0) else 0

theorem cl1 : (8191 : ℕ) ∈ Cl := by decide +kernel
theorem cl2 : ∀ c ∈ Cl, ∀ i : Fin 13, Cl.contains (c &&& zm i.val) = true := by decide +kernel
theorem cl3 : ∀ c ∈ Cl, val c ≤ 6 := by decide +kernel
theorem zmz : ∀ i j : Fin 13, (M.getD i.val 0).testBit j.val = false ↔ (zm i.val).testBit j.val = true := by decide +kernel
theorem wz : ∀ i j : Fin 13, w i.val j.val ≠ 0 → (M.getD i.val 0).testBit j.val = false := by decide +kernel
theorem tot : ∑ i : Fin 13, ∑ j : Fin 13, w i.val j.val = 78 := by decide +kernel

theorem land_sub {a b : ℕ} (h : a &&& b = a) (j : ℕ) (hj : a.testBit j = true) : b.testBit j = true := by
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hj
  exact hj.2

/-- The common columns of a row set. -/
theorem common (A : Finset (Fin 13)) : ∃ c ∈ Cl, (∀ i ∈ A, c &&& zm i.val = c) ∧ ∀ j : Fin 13, (∀ i ∈ A, (zm i.val).testBit j.val = true) → c.testBit j.val = true := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨8191, cl1, by simp, fun j _ => ?_⟩
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

theorem rect (A B : Finset (Fin 13)) (h : ∀ i ∈ A, ∀ j ∈ B, (M.getD i.val 0).testBit j.val = false) :
    ∑ i ∈ A, ∑ j ∈ B, w i.val j.val ≤ 6 := by
  obtain ⟨c, hc, h1, h2⟩ := common A
  refine le_trans ?_ (cl3 c hc)
  have hB : ∀ j ∈ B, c.testBit j.val = true := fun j hj => h2 j fun i hi => (zmz i j).1 (h i hi j hj)
  unfold val
  calc ∑ i ∈ A, ∑ j ∈ B, w i.val j.val ≤ ∑ i ∈ A, (if c &&& zm i.val = c then ∑ j : Fin 13, (if c.testBit j.val = true then w i.val j.val else 0) else 0) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [if_pos (h1 i hi)]
        calc ∑ j ∈ B, w i.val j.val = ∑ j ∈ B, (if c.testBit j.val = true then w i.val j.val else 0) :=
              Finset.sum_congr rfl fun j hj => by rw [if_pos (hB j hj)]
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem cover (L : List (Finset (Fin 13) × Finset (Fin 13))) (h : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (M.getD i.val 0).testBit j.val = false) :
    ∑ i : Fin 13, ∑ j : Fin 13, (if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) ≤ 6 * L.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have h1 := rect r.1 r.2 (h r (by simp))
    have h2 : ∑ i ∈ r.1, ∑ j ∈ r.2, w i.val j.val = ∑ i : Fin 13, ∑ j : Fin 13, (if i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ r.1)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_subset (Finset.subset_univ r.2)]
        · exact Finset.sum_congr rfl fun j hj => by rw [if_pos ⟨hi, hj⟩]
        · intro j _ hj; rw [if_neg fun h => hj h.2]
      · intro i _ hi
        exact Finset.sum_eq_zero fun j _ => by rw [if_neg fun h => hi h.1]
    rw [h2] at h1
    rw [List.length_cons, Nat.mul_succ]
    calc _ ≤ ∑ i : Fin 13, ∑ j : Fin 13, ((if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0) + (if i ∈ r.1 ∧ j ∈ r.2 then w i.val j.val else 0)) := by
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

end PEqualNP.Outside.L_meta_10044

theorem PEqualNP.Outside.L_meta_10044 : ¬ (∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hL, h1, h2⟩
  have hc := PEqualNP.Outside.L_meta_10044.cover L h1
  have ht := PEqualNP.Outside.L_meta_10044.tot
  have he : ∑ i : Fin 13, ∑ j : Fin 13, (if ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 then PEqualNP.Outside.L_meta_10044.w i.val j.val else 0) = ∑ i : Fin 13, ∑ j : Fin 13, PEqualNP.Outside.L_meta_10044.w i.val j.val := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : PEqualNP.Outside.L_meta_10044.w i.val j.val = 0
    · rw [h0]; split_ifs <;> rfl
    · rw [if_pos (h2 i j (PEqualNP.Outside.L_meta_10044.wz i j h0))]
  rw [he, ht] at hc
  omega
