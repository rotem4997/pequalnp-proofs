import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7288

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def LL : List ℕ := [523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]

def Q : List ℕ := [39, 71, 135, 2055, 83, 275, 2067, 4115, 1059, 2083, 4131, 195, 4163, 387, 1155, 1283, 2307, 5123, 29, 77, 141, 1037, 85, 533, 2069, 101, 549, 1061, 1157, 2181, 1541, 2565, 281, 1049, 2073, 105, 297, 1065, 4137, 201, 329, 2185, 4233, 2313, 5129, 6153, 337, 593, 1297, 1553, 4625, 5137, 6161, 609, 4193, 801, 1313, 2337, 2593, 6177, 449, 4289, 833, 4673, 897, 2433, 1665, 2689, 4737, 5249, 1793, 6657, 78, 142, 270, 4110, 166, 550, 4134, 2118, 4166, 390, 774, 2310, 2566, 4614, 58, 154, 282, 2074, 170, 1066, 4138, 202, 1098, 2122, 2314, 4362, 3082, 5130, 562, 2098, 4146, 210, 594, 2130, 402, 658, 4370, 4626, 674, 1186, 2594, 3106, 1218, 1602, 2626, 4674, 5186, 898, 1666, 1794, 4866, 3330, 5378, 3586, 156, 284, 540, 332, 1100, 4236, 780, 1548, 4620, 5132, 116, 308, 564, 4148, 340, 2132, 404, 2196, 4244, 4628, 6164, 1124, 4196, 420, 1188, 4260, 804, 1316, 1348, 2372, 5188, 6212, 2436, 3204, 5252, 1796, 3332, 3588, 6660, 7172, 312, 568, 1080, 664, 2200, 1560, 3096, 232, 616, 1128, 680, 4264, 808, 4392, 2248, 840, 2376, 1608, 2632, 2696, 4744, 4872, 6408, 3592, 6664, 7176, 624, 1136, 2160, 1328, 4400, 3120, 6192, 464, 1232, 2256, 1360, 1616, 4496, 1680, 4752, 3216, 5264, 5392, 7184, 1248, 2272, 4320, 2656, 6240, 928, 2464, 4512, 2720, 3232, 3360, 6432, 2496, 4544, 5312, 1856, 4928, 5440, 6464, 6720, 4992, 3712, 7424]

theorem bit : ∀ l p : Fin 13, (LL.getD l 0).testBit p = decide (p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by decide +kernel

theorem good : ∀ m ∈ Q, (Finset.univ.filter fun p : Fin 13 => m.testBit p = true).card = 4 ∧
    ∀ l : Fin 13, ((Finset.univ.filter fun p : Fin 13 => m.testBit p = true).filter fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))).card ≤ 2 := by decide +kernel

def has (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

theorem has_iff (m i : ℕ) : has m i = m.testBit i := by
  rw [Bool.eq_iff_iff, has, Nat.beq_eq, Nat.testBit_eq_decide_div_mod_eq]
  have : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    show (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [this]; simp

def R : List ℕ := List.range 13

theorem chk : (R.all fun c => R.all fun d => (fun L : List ℕ => R.all fun a => R.all fun b =>
    has (LL.getD c 0) a || has (LL.getD d 0) a || has (LL.getD c 0) b || has (LL.getD d 0) b ||
      L.any fun m => has m a && has m b) (Q.filter fun m => Nat.beq (Nat.land m (LL.getD c 0)) 0 && Nat.beq (Nat.land m (LL.getD d 0)) 0)) = true := by
  decide +kernel

theorem main (a b c d : Fin 13) (h1 : a - c ∉ ({0, 1, 3, 9} : Finset (Fin 13))) (h2 : a - d ∉ ({0, 1, 3, 9} : Finset (Fin 13)))
    (h3 : b - c ∉ ({0, 1, 3, 9} : Finset (Fin 13))) (h4 : b - d ∉ ({0, 1, 3, 9} : Finset (Fin 13))) :
    ∃ m ∈ Q, m.testBit a = true ∧ m.testBit b = true ∧ Nat.beq (Nat.land m (LL.getD c 0)) 0 = true ∧ Nat.beq (Nat.land m (LL.getD d 0)) 0 = true := by
  have h := chk
  rw [List.all_eq_true] at h
  have h := h c (List.mem_range.2 c.isLt)
  rw [List.all_eq_true] at h
  have h := h d (List.mem_range.2 d.isLt)
  simp only at h
  rw [List.all_eq_true] at h
  have h := h a (List.mem_range.2 a.isLt)
  rw [List.all_eq_true] at h
  have h := h b (List.mem_range.2 b.isLt)
  simp only [has_iff, bit, decide_eq_false h1, decide_eq_false h2, decide_eq_false h3, decide_eq_false h4, Bool.false_or] at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hab⟩ := h
  rw [List.mem_filter, Bool.and_eq_true] at hm
  rw [Bool.and_eq_true] at hab
  exact ⟨m, hm.1, hab.1, hab.2, hm.2.1, hm.2.2⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7288

theorem PEqualNP.Outside.L_meta_7288 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 - x4 ∉ x1 → x2 - x5 ∉ x1 → x3 - x4 ∉ x1 → x3 - x5 ∉ x1 → ∃ (x10 : Finset (Fin (13 : ℕ))), (x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x1}.card ≤ (2 : ℕ)) ∧ x2 ∈ x10 ∧ x3 ∈ x10 ∧ (∀ x11 ∈ x10, x11 - x4 ∉ x1) ∧ ∀ x11 ∈ x10, x11 - x5 ∉ x1 := by
  intro D a b c d h1 h2 h3 h4
  obtain ⟨m, hm, k1, k2, k3, k4⟩ := PEqualNP.Outside.L_meta_7288.main a b c d h1 h2 h3 h4
  obtain ⟨g1, g2⟩ := PEqualNP.Outside.L_meta_7288.good m hm
  have key : ∀ l : Fin 13, Nat.beq (Nat.land m (PEqualNP.Outside.L_meta_7288.LL.getD l 0)) 0 = true → ∀ p : Fin 13, m.testBit p = true → p - l ∉ D := by
    intro l hl p hp hD
    rw [Nat.beq_eq] at hl
    have e : (Nat.land m (PEqualNP.Outside.L_meta_7288.LL.getD l 0)).testBit p = (m.testBit p && (PEqualNP.Outside.L_meta_7288.LL.getD l 0).testBit p) := Nat.testBit_and _ _ _
    rw [hl, Nat.zero_testBit, hp, PEqualNP.Outside.L_meta_7288.bit, Bool.true_and] at e
    rw [decide_eq_true hD] at e
    cases e
  refine ⟨Finset.univ.filter fun p : Fin 13 => m.testBit p = true, ⟨g1, g2⟩, by simpa using k1, by simpa using k2, ?_, ?_⟩
  · intro p hp
    exact key c k3 p (by simpa using hp)
  · intro p hp
    exact key d k4 p (by simpa using hp)
