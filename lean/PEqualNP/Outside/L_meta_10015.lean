import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10015_aux

def boxes : List (ℕ × ℕ) := [(538444066, 1616061506), (9060480, 269124787), (688032256, 168823426), (405291850, 1091045440), (1078560787, 78342), (268560774, 1728118784), (715129076, 11174016), (33857602, 1350928968), (1090781342, 68522000), (201594896, 948982320), (7479304, 1078222907), (1981955386, 71311360), (1141424461, 151193601), (1073748864, 1173357056), (1313022980, 134489232), (329681152, 67111716), (432051272, 51413312), (268566549, 571269157), (319817216, 40115396), (539821705, 2625547), (620826656, 738346312), (203425090, 562825296), (12584996, 26828972), (1410684033, 268440833), (1074811507, 281165828), (270904, 472137826)]
def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

set_option maxRecDepth 100000 in
theorem sound : ∀ p ∈ boxes, ∀ i : Fin 31, ∀ j : Fin 31, p.1.testBit i.val = true → p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete : ∀ i : Fin 31, ∀ j : Fin 31, (rows.getD i.val 0).testBit j.val = false → ∃ p ∈ boxes, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10015_aux

open PEqualNP.Outside.L_meta_10015_aux

theorem PEqualNP.Outside.L_meta_10015 : ∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 27 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨boxes.map (fun p => (members p.1, members p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact sound p hp i j (by simpa [members] using hi) (by simpa [members] using hj)
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := complete i j h
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [members] using hi, by simpa [members] using hj⟩
