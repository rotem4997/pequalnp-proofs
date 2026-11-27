import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10037_aux

def boxes : List (ℕ × ℕ) := [(41068, 266785), (13829, 141352), (27808, 74881), (14602, 136212), (546, 557389), (25424, 82456), (388, 557490), (1048, 553282), (53248, 491842), (41107, 280708), (2113, 560706)]
def rows : List ℕ := [69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

set_option maxRecDepth 100000 in
theorem sound : ∀ p ∈ boxes, ∀ i : Fin 16, ∀ j : Fin 20, p.1.testBit i.val = true → p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete : ∀ i : Fin 16, ∀ j : Fin 20, (rows.getD i.val 0).testBit j.val = false → ∃ p ∈ boxes, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_10037_aux

open PEqualNP.Outside.L_meta_10037_aux

theorem PEqualNP.Outside.L_meta_10037 : ∃ L : List (Finset (Fin 16) × Finset (Fin 20)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 20), (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨boxes.map (fun p => (members p.1, members p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact sound p hp i j (by simpa [members] using hi) (by simpa [members] using hj)
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := complete i j h
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [members] using hi, by simpa [members] using hj⟩
