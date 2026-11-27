import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10029_aux

def boxes : List (ℕ × ℕ) := [(1057, 830820574), (1081345, 208284446), (32800, 727489918), (1049600, 380888766), (2114, 823797149), (2162690, 214225469), (65600, 716815069), (2099200, 392646013), (4228, 808766235), (4325380, 227091579), (131200, 727970235), (4198400, 383655643), (8456, 812193335), (8650760, 219334871), (262400, 718759767), (8396800, 397195703), (16912, 818063471), (17301520, 204805519), (524800, 732843695), (16793600, 391770959)]
def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

set_option maxRecDepth 100000 in
theorem sound : ∀ p ∈ boxes, ∀ i : Fin 25, ∀ j : Fin 30, p.1.testBit i.val = true → p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete : ∀ i : Fin 25, ∀ j : Fin 30, (rows.getD i.val 0).testBit j.val = false → ∃ p ∈ boxes, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10029_aux

open PEqualNP.Outside.L_meta_10029_aux

theorem PEqualNP.Outside.L_meta_10029 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 21 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨boxes.map (fun p => (members p.1, members p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact sound p hp i j (by simpa [members] using hi) (by simpa [members] using hj)
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := complete i j h
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [members] using hi, by simpa [members] using hj⟩
