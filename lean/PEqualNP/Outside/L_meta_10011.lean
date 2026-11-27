import PEqualNP.Defs

-- The mask-to-Finset verifier is adapted from L-meta-10015.

namespace PEqualNP.Outside.L_meta_10011_aux

def boxes : List (ℕ × ℕ) := [(3834113, 537012263), (817905736, 34193729), (1074792081, 283381763), (5115916, 1209040953), (1417748608, 352388737), (470155680, 538707232), (840442144, 1080108096), (550538272, 9445770), (1094734881, 155223300), (1140985914, 340942848), (125109256, 266584), (1080048066, 1103102480), (1829405248, 135400064), (310527750, 101190660), (940644373, 572551168), (16818375, 587563016), (134857226, 1359089730), (178274452, 9076912), (34408529, 405340676), (27535880, 69224490), (604304656, 746586177)]
def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

set_option maxRecDepth 100000 in
theorem sound : ∀ p ∈ boxes, ∀ i : Fin 31, ∀ j : Fin 31, p.1.testBit i.val = true → p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete : ∀ i : Fin 31, ∀ j : Fin 31, (rows.getD i.val 0).testBit j.val = false → ∃ p ∈ boxes, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10011_aux

open PEqualNP.Outside.L_meta_10011_aux

theorem PEqualNP.Outside.L_meta_10011 : ∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 21 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨boxes.map (fun p => (members p.1, members p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact sound p hp i j (by simpa [members] using hi) (by simpa [members] using hj)
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := complete i j h
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [members] using hi, by simpa [members] using hj⟩
