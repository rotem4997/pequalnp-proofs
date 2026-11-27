import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

-- The two premises start after a representative first AND or OR gate.
-- Each key pairs two columns in the original 17-entry bank, using base 17.
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4387_238
    (hand : let bank := ([0, 288230376151711743, 95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat).map (BitVec.ofNat 58)
      ∀ k ∈ ([0, 43, 44, 169, 78, 82, 94, 98, 109, 91, 56, 75, 58, 84, 77, 79, 81, 21, 37, 61, 186, 64, 20, 101, 95, 22, 237, 33, 164, 217, 199, 182, 166, 27, 26, 235, 30, 18] : List Nat),
        let start := bank ++ [bank[k / 17]! &&& bank[k % 17]!]
        ∀ tail : List (BitVec 58), tail.length ≤ 24 →
          (∀ j : Fin tail.length, let pool := start ++ tail.take j.val
            ∃ u ∈ pool, ∃ v ∈ pool, tail.get j = u &&& v ∨ tail.get j = u ||| v) →
          (2097151 : BitVec 58) ∉ start ++ tail)
    (hor : let bank := ([0, 288230376151711743, 95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat).map (BitVec.ofNat 58)
      ∀ k ∈ ([0, 4, 74, 3, 55, 5, 73, 56, 75, 16, 84, 101, 10, 78, 112, 61, 95, 9, 77, 60, 163, 182, 94, 62, 181, 13, 81, 115, 64, 183, 98, 203, 237, 166, 235, 169, 1] : List Nat),
        let start := bank ++ [bank[k / 17]! ||| bank[k % 17]!]
        ∀ tail : List (BitVec 58), tail.length ≤ 24 →
          (∀ j : Fin tail.length, let pool := start ++ tail.take j.val
            ∃ u ∈ pool, ∃ v ∈ pool, tail.get j = u &&& v ∨ tail.get j = u ||| v) →
          (2097151 : BitVec 58) ∉ start ++ tail)
    : have x1 : List (BitVec (58 : ℕ)) := [(0 : BitVec (58 : ℕ)), BitVec.allOnes (58 : ℕ), (95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))]; ∀ (x2 : List (BitVec (58 : ℕ))),   x2.length ≤ (25 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x4) x2;         ∃ x6 ∈ x5, ∃ x7 ∈ x5, x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7) →       (2097151 : BitVec (58 : ℕ)) ∉ x1 ++ x2 := by
  let bank := ([0, 288230376151711743, 95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat).map (BitVec.ofNat 58)
  let andKeys : List Nat := [0, 43, 44, 169, 78, 82, 94, 98, 109, 91, 56, 75, 58, 84, 77, 79, 81, 21, 37, 61, 186, 64, 20, 101, 95, 22, 237, 33, 164, 217, 199, 182, 166, 27, 26, 235, 30, 18]
  let orKeys : List Nat := [0, 4, 74, 3, 55, 5, 73, 56, 75, 16, 84, 101, 10, 78, 112, 61, 95, 9, 77, 60, 163, 182, 94, 62, 181, 13, 81, 115, 64, 183, 98, 203, 237, 166, 235, 169, 1]
  -- Relabel the 58 test rows by Heawood graph symmetries fixing the extra input.
  let shuffle (p : List Nat) (x : BitVec 58) : BitVec 58 :=
    (BitVec.ofBoolListLE (p.map fun i => x.getLsbD i)).setWidth 58
  let perms : List (List Nat) := [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57],
    [0, 2, 1, 3, 4, 5, 12, 13, 14, 9, 11, 10, 6, 7, 8, 19, 18, 20, 16, 15, 17, 21, 22, 28, 29, 25, 26, 31, 23, 24, 30, 27, 38, 39, 43, 41, 40, 42, 32, 33, 36, 35, 37, 34, 44, 45, 46, 47, 50, 49, 48, 51, 54, 55, 52, 53, 56, 57],
    [0, 2, 1, 3, 5, 4, 16, 17, 15, 9, 10, 11, 18, 20, 19, 8, 6, 7, 12, 14, 13, 21, 22, 28, 29, 46, 47, 50, 23, 24, 30, 48, 32, 33, 36, 52, 34, 53, 38, 39, 43, 54, 55, 40, 44, 45, 25, 26, 31, 49, 27, 51, 35, 37, 41, 42, 56, 57],
    [0, 1, 2, 3, 5, 4, 18, 20, 19, 9, 11, 10, 16, 17, 15, 14, 12, 13, 6, 8, 7, 21, 22, 23, 24, 46, 47, 48, 28, 29, 30, 50, 38, 39, 40, 54, 43, 55, 32, 33, 34, 52, 53, 36, 44, 45, 25, 26, 27, 49, 31, 51, 41, 42, 35, 37, 56, 57],
    [3, 5, 4, 0, 2, 1, 8, 7, 6, 9, 10, 11, 19, 20, 18, 16, 15, 17, 14, 12, 13, 21, 22, 46, 47, 28, 29, 50, 25, 26, 49, 31, 32, 33, 52, 36, 35, 37, 38, 39, 54, 43, 55, 41, 44, 56, 23, 24, 48, 30, 27, 51, 34, 53, 40, 42, 45, 57],
    [3, 5, 4, 0, 1, 2, 14, 13, 12, 9, 11, 10, 15, 17, 16, 18, 19, 20, 8, 6, 7, 21, 22, 46, 47, 23, 24, 48, 25, 26, 49, 27, 38, 39, 54, 40, 41, 42, 32, 33, 52, 34, 53, 35, 44, 56, 28, 29, 50, 30, 31, 51, 43, 55, 36, 37, 45, 57],
    [3, 4, 5, 0, 1, 2, 15, 17, 16, 9, 10, 11, 14, 13, 12, 6, 8, 7, 19, 18, 20, 21, 22, 25, 26, 23, 24, 27, 46, 47, 49, 48, 32, 33, 35, 34, 52, 53, 38, 39, 41, 40, 42, 54, 44, 56, 28, 29, 31, 30, 50, 51, 36, 37, 43, 55, 45, 57],
    [3, 4, 5, 0, 2, 1, 19, 20, 18, 9, 11, 10, 8, 7, 6, 12, 14, 13, 15, 16, 17, 21, 22, 25, 26, 28, 29, 31, 46, 47, 49, 50, 38, 39, 41, 43, 54, 55, 32, 33, 35, 36, 37, 52, 44, 56, 23, 24, 27, 30, 48, 51, 40, 42, 34, 53, 45, 57]]
  let maps := perms.map shuffle
  have laws : ∀ f ∈ maps, ∀ x y, f (x &&& y) = f x &&& f y ∧
      f (x ||| y) = f x ||| f y := by
    intro f hf x y
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hf
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    all_goals by_cases hp : i < p.length
    all_goals simp only [shuffle, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map]
    all_goals simp [hi, hp]
  -- Corresponding action on the input columns, including both constants.
  let images : Array (Array Nat) := #[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
    #[0, 1, 2, 3, 6, 5, 4, 8, 7, 9, 12, 11, 10, 14, 13, 15, 16],
    #[0, 1, 2, 3, 7, 5, 8, 4, 6, 9, 12, 15, 10, 13, 14, 11, 16],
    #[0, 1, 2, 3, 8, 5, 7, 6, 4, 9, 10, 15, 12, 14, 13, 11, 16],
    #[0, 1, 3, 2, 4, 5, 8, 7, 6, 9, 15, 12, 11, 13, 14, 10, 16],
    #[0, 1, 3, 2, 8, 5, 4, 6, 7, 9, 11, 12, 15, 14, 13, 10, 16],
    #[0, 1, 3, 2, 7, 5, 6, 4, 8, 9, 11, 10, 15, 13, 14, 12, 16],
    #[0, 1, 3, 2, 6, 5, 7, 8, 4, 9, 15, 10, 11, 14, 13, 12, 16]]
  have permutes : ∀ z : Fin 8, ∀ i : Fin 17,
      let j := images[z.val]![i.val]!
      j < bank.length ∧ shuffle perms[z.val]! bank[i.val]! = bank[j]! := by
    intro z
    fin_cases z <;> decide +kernel
  have stable : ∀ f ∈ maps, ∀ u ∈ bank, f u ∈ bank := by
    intro f hf u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    obtain ⟨z,hz,rfl⟩ := List.mem_iff_getElem.mp hp
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨hj,he⟩ := permutes ⟨z,hz⟩ ⟨i,hi⟩
    change _ < bank.length at hj
    have : shuffle perms[z] bank[i] = bank[images[z]![i]!] := by
      simpa only [getElem!_pos perms z hz, getElem!_pos bank i hi,
        getElem!_pos bank (images[z]![i]!) hj] using he
    rw [this]
    exact List.getElem_mem _
  have fixed : ∀ f ∈ maps, f 2097151 = 2097151 := by
    change ∀ f ∈ (perms.map shuffle), _
    simpa only [List.forall_mem_map] using
      (show ∀ p ∈ perms, shuffle p 2097151 = 2097151 by decide +kernel)
  have coverAnd : ∀ u ∈ bank, ∀ v ∈ bank, ∃ f ∈ maps, ∃ k ∈ andKeys,
      f (u &&& v) = bank[k / 17]! &&& bank[k % 17]! := by
    -- For each ordered pair the entry is 512 times a symmetry index plus a key.
    let table : Array Nat := #[
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 18, 2068, 20, 21, 22, 533, 1045, 1557, 26, 27, 3099, 539, 30, 542, 2075, 33,
      0, 2068, 2068, 37, 3130, 2104, 3642, 2106, 2618, 43, 44, 3133, 556, 2112, 2624, 2109, 2068,
      0, 20, 37, 20, 1082, 56, 1594, 58, 570, 2091, 61, 3116, 573, 64, 576, 2092, 20,
      0, 21, 3130, 1082, 21, 603, 3181, 75, 621, 77, 78, 79, 2127, 81, 82, 2126, 84,
      0, 22, 2104, 56, 603, 22, 91, 1627, 1115, 94, 95, 3167, 607, 98, 610, 2143, 101,
      0, 533, 3642, 1594, 3181, 91, 533, 109, 587, 589, 2639, 591, 590, 594, 593, 2638, 596,
      0, 1045, 2106, 58, 75, 1627, 109, 1045, 2157, 1101, 3151, 3150, 1102, 1105, 1106, 1103, 1108,
      0, 1557, 2618, 570, 621, 1115, 587, 2157, 1557, 1613, 1614, 3662, 3663, 1618, 1617, 1615, 1620,
      0, 26, 43, 2091, 77, 94, 589, 1101, 1613, 26, 2724, 164, 2212, 166, 678, 1188, 169,
      0, 27, 44, 61, 78, 95, 2639, 3151, 1614, 2724, 27, 711, 182, 1241, 729, 1223, 186,
      0, 3099, 3133, 3116, 79, 3167, 591, 3150, 3662, 164, 711, 3099, 199, 2265, 2777, 2230, 3258,
      0, 539, 556, 573, 2127, 607, 590, 1102, 3663, 2212, 182, 199, 539, 217, 1753, 1735, 698,
      0, 30, 2112, 64, 81, 98, 594, 1105, 1618, 166, 1241, 2265, 217, 30, 235, 3289, 237,
      0, 542, 2624, 576, 82, 610, 593, 1106, 1617, 678, 729, 2777, 1753, 235, 542, 3801, 749,
      0, 2075, 2109, 2092, 2126, 2143, 2638, 1103, 1615, 1188, 1223, 2230, 1735, 3289, 3801, 2075, 2234,
      0, 33, 2068, 20, 84, 101, 596, 1108, 1620, 169, 186, 3258, 698, 237, 749, 2234, 33]
    have checked : ∀ i j : Fin 17,
        let c := table[i.val * 17 + j.val]!
        let k := c % 512
        c / 512 < perms.length ∧ k ∈ andKeys ∧
          (bank[images[c / 512]![i.val]!]! &&& bank[images[c / 512]![j.val]!]!) =
          bank[k / 17]! &&& bank[k % 17]! := by
      intro i
      fin_cases i <;> decide +kernel
    intro u hu v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hv
    obtain ⟨hp,hk,he⟩ := checked ⟨i,hi⟩ ⟨j,hj⟩
    let c := table[i*17+j]!
    change c / 512 < perms.length at hp
    have pp : perms[c / 512]! ∈ perms := by
      rw [getElem!_pos perms (c / 512) hp]
      exact List.getElem_mem hp
    let f := shuffle perms[c / 512]!
    have hf : f ∈ maps := List.mem_map_of_mem pp
    have hu := (permutes ⟨c / 512,hp⟩ ⟨i,hi⟩).2
    have hv := (permutes ⟨c / 512,hp⟩ ⟨j,hj⟩).2
    change f bank[i]! = bank[images[c / 512]![i]!]! at hu
    change f bank[j]! = bank[images[c / 512]![j]!]! at hv
    simp only [getElem!_pos bank i hi] at hu
    simp only [getElem!_pos bank j hj] at hv
    refine ⟨f,hf,_,hk,?_⟩
    rw [(laws f hf _ _).1, hu, hv]
    exact he
  have coverOr : ∀ u ∈ bank, ∀ v ∈ bank, ∃ f ∈ maps, ∃ k ∈ orKeys,
      f (u ||| v) = bank[k / 17]! ||| bank[k % 17]! := by
    let table : Array Nat := #[
      0, 1, 2051, 3, 4, 5, 516, 1028, 1540, 9, 10, 3082, 522, 13, 525, 2058, 16,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      2051, 1, 2051, 16, 2103, 2104, 2615, 3127, 3639, 2108, 2622, 3133, 2110, 2112, 2624, 2109, 16,
      3, 1, 16, 3, 55, 56, 567, 1079, 1591, 60, 61, 62, 573, 64, 576, 1086, 16,
      4, 1, 2103, 55, 4, 73, 74, 75, 2122, 77, 78, 3696, 624, 81, 627, 2126, 84,
      5, 1, 2104, 56, 73, 5, 585, 1097, 1609, 94, 95, 3167, 607, 98, 610, 2143, 101,
      516, 1, 2615, 567, 74, 585, 516, 2634, 587, 589, 112, 3184, 590, 115, 593, 2638, 596,
      1028, 1, 3127, 1079, 75, 1097, 2634, 1028, 1098, 1101, 1648, 3150, 1102, 1105, 1651, 2672, 1108,
      1540, 1, 3639, 1591, 2122, 1609, 587, 1098, 1540, 1613, 1614, 3662, 1136, 1139, 1617, 2160, 1620,
      9, 1, 2108, 60, 77, 94, 589, 1101, 1613, 9, 163, 3235, 675, 166, 678, 2211, 169,
      10, 1, 2622, 61, 78, 95, 112, 1648, 1614, 163, 10, 181, 182, 183, 1719, 1717, 2763,
      3082, 1, 3133, 62, 3696, 3167, 3184, 3150, 3662, 3235, 181, 3082, 693, 3255, 3767, 2230, 203,
      522, 1, 2110, 573, 624, 607, 590, 1102, 1136, 675, 182, 693, 522, 1207, 695, 1205, 2251,
      13, 1, 2112, 64, 81, 98, 115, 1105, 1139, 166, 183, 3255, 1207, 13, 235, 2231, 237,
      525, 1, 2624, 576, 627, 610, 593, 1651, 1617, 678, 1719, 3767, 695, 235, 525, 2743, 749,
      2058, 1, 2109, 1086, 2126, 2143, 2638, 2672, 2160, 2211, 1717, 2230, 1205, 2231, 2743, 2058, 1227,
      16, 1, 16, 16, 84, 101, 596, 1108, 1620, 169, 2763, 203, 2251, 237, 749, 1227, 16]
    have checked : ∀ i j : Fin 17,
        let c := table[i.val * 17 + j.val]!
        let k := c % 512
        c / 512 < perms.length ∧ k ∈ orKeys ∧
          (bank[images[c / 512]![i.val]!]! ||| bank[images[c / 512]![j.val]!]!) =
          bank[k / 17]! ||| bank[k % 17]! := by
      intro i
      fin_cases i <;> decide +kernel
    intro u hu v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hv
    obtain ⟨hp,hk,he⟩ := checked ⟨i,hi⟩ ⟨j,hj⟩
    let c := table[i*17+j]!
    change c / 512 < perms.length at hp
    have pp : perms[c / 512]! ∈ perms := by
      rw [getElem!_pos perms (c / 512) hp]
      exact List.getElem_mem hp
    let f := shuffle perms[c / 512]!
    have hf : f ∈ maps := List.mem_map_of_mem pp
    have hu := (permutes ⟨c / 512,hp⟩ ⟨i,hi⟩).2
    have hv := (permutes ⟨c / 512,hp⟩ ⟨j,hj⟩).2
    change f bank[i]! = bank[images[c / 512]![i]!]! at hu
    change f bank[j]! = bank[images[c / 512]![j]!]! at hv
    simp only [getElem!_pos bank i hi] at hu
    simp only [getElem!_pos bank j hj] at hv
    refine ⟨f,hf,_,hk,?_⟩
    rw [(laws f hf _ _).2, hu, hv]
    exact he
  -- Transport the remainder of the computation through the chosen symmetry.
  let legal (start xs : List (BitVec 58)) := ∀ j : Fin xs.length,
    let pool := start ++ xs.take j.val
    ∃ u ∈ pool, ∃ v ∈ pool, xs.get j = u &&& v ∨ xs.get j = u ||| v
  change ∀ xs : List (BitVec 58), xs.length ≤ 25 → legal bank xs →
    (2097151 : BitVec 58) ∉ bank ++ xs
  intro xs n hx target
  have absent : (2097151 : BitVec 58) ∉ bank := by decide +kernel
  cases xs with
  | nil => exact absent (by simpa using target)
  | cons first rest =>
    have transfer (f : BitVec 58 → BitVec 58) (hf : f ∈ maps) :
        legal (bank ++ [f first]) (rest.map f) := by
      intro j
      let i : Fin rest.length := ⟨j.val, by simpa using j.isLt⟩
      have step := hx i.succ
      change ∃ u ∈ bank ++ (first :: rest).take (i.val + 1),
        ∃ v ∈ bank ++ (first :: rest).take (i.val + 1),
          rest.get i = u &&& v ∨ rest.get i = u ||| v at step
      obtain ⟨u,hu,v,hv,hop⟩ := step
      have image (w : BitVec 58) (hw : w ∈ bank ++ (first :: rest).take (i.val + 1)) :
          f w ∈ (bank ++ [f first]) ++ (rest.map f).take j.val := by
        simp only [List.take_succ_cons, List.mem_append, List.mem_cons] at hw
        rcases hw with h | rfl | h
        · exact List.mem_append_left _ (List.mem_append_left _ (stable f hf _ h))
        · exact List.mem_append_left _ (List.mem_append_right _ (by simp))
        · apply List.mem_append_right
          rw [← List.map_take]
          exact List.mem_map_of_mem h
      refine ⟨f u, image u hu, f v, image v hv, ?_⟩
      simp only [List.get_eq_getElem, List.getElem_map]
      change f (rest.get i) = _ ∨ f (rest.get i) = _
      rcases hop with h | h
      · exact Or.inl ((congrArg f h).trans (laws f hf u v).1)
      · exact Or.inr ((congrArg f h).trans (laws f hf u v).2)
    have reaches (f : BitVec 58 → BitVec 58) (hf : f ∈ maps) :
        (2097151 : BitVec 58) ∈ (bank ++ [f first]) ++ rest.map f := by
      have h := (List.mem_append.mp target).resolve_left absent
      rw [← fixed f hf]
      rcases List.mem_cons.mp h with he | he
      · exact List.mem_append_left _ (List.mem_append_right _ (by simp [he]))
      · exact List.mem_append_right _ (List.mem_map_of_mem he)
    have small (f : BitVec 58 → BitVec 58) : (rest.map f).length ≤ 24 := by
      simp at n ⊢
      omega
    obtain ⟨u,hu,v,hv,h⟩ := hx ⟨0, by simp⟩
    change first = u &&& v ∨ first = u ||| v at h
    have hu' : u ∈ bank := by simpa using hu
    have hv' : v ∈ bank := by simpa using hv
    rcases h with h | h
    · obtain ⟨f,hf,k,hk,he⟩ := coverAnd u hu' v hv'
      rw [← h] at he
      have ht := transfer f hf
      have hr := reaches f hf
      rw [he] at ht hr
      exact hand k hk (rest.map f) (small f) ht hr
    · obtain ⟨f,hf,k,hk,he⟩ := coverOr u hu' v hv'
      rw [← h] at he
      have ht := transfer f hf
      have hr := reaches f hf
      rw [he] at ht hr
      exact hor k hk (rest.map f) (small f) ht hr
