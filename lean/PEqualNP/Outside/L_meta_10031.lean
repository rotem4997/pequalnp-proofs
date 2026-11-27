import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10031_aux

def boxes : List (ℕ × ℕ) := [(10526880, 50633008), (8597568, 44601489), (2117764, 268487433), (15213571, 92540928), (17825910, 403735816), (792320, 579225090), (21091648, 34607680), (5382312, 4260018), (90386, 549466149), (557832, 673842726), (3155264, 312542740), (6619141, 210045520), (25297220, 136847681), (17105538, 138732161), (5408770, 71967800), (671781, 562643210), (25429544, 16826566), (197892, 547446896), (16845841, 69542092), (788672, 588450177), (3152513, 274876424), (12603416, 336730179)]
def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

set_option maxRecDepth 100000 in
theorem sound : ∀ p ∈ boxes, ∀ i : Fin 25, ∀ j : Fin 30, p.1.testBit i.val = true → p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete : ∀ i : Fin 25, ∀ j : Fin 30, (rows.getD i.val 0).testBit j.val = false → ∃ p ∈ boxes, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10031_aux

open PEqualNP.Outside.L_meta_10031_aux

theorem PEqualNP.Outside.L_meta_10031 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 24 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨boxes.map (fun p => (members p.1, members p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact sound p hp i j (by simpa [members] using hi) (by simpa [members] using hj)
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := complete i j h
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [members] using hi, by simpa [members] using hj⟩
