import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9351

/-- Five triples of rectangles, related within each triple by translation by seven. -/
def cover : List (Finset (Fin 21) × Finset (Fin 21)) := [
    ({0, 6, 9}, {1, 3, 4, 10, 12, 15, 18, 19}),
    ({7, 13, 16}, {1, 4, 5, 8, 10, 11, 17, 19}),
    ({2, 14, 20}, {3, 5, 8, 11, 12, 15, 17, 18}),
    ({0, 2, 6, 15, 19}, {4, 8, 10, 12, 16}),
    ({1, 5, 7, 9, 13}, {2, 11, 15, 17, 19}),
    ({8, 12, 14, 16, 20}, {1, 3, 5, 9, 18}),
    ({2, 3, 11, 12, 13, 17}, {0, 4, 5, 6, 14, 15}),
    ({3, 9, 10, 18, 19, 20}, {0, 1, 7, 11, 12, 13}),
    ({4, 5, 6, 10, 16, 17}, {7, 8, 14, 18, 19, 20}),
    ({0, 1, 8, 17, 19, 20}, {2, 9, 10, 11, 12, 14}),
    ({3, 5, 6, 7, 8, 15}, {0, 9, 16, 17, 18, 19}),
    ({1, 10, 12, 13, 14, 15}, {2, 3, 4, 5, 7, 16}),
    ({4, 8, 9, 11, 14, 19}, {1, 2, 6, 12, 17, 20}),
    ({0, 5, 11, 15, 16, 18}, {3, 6, 8, 9, 13, 19}),
    ({1, 2, 4, 7, 12, 18}, {5, 10, 13, 15, 16, 20})]

end PEqualNP.Outside.L_meta_9351

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_9351 : ∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 15 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 21) (j : Fin 21), (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  let L := PEqualNP.Outside.L_meta_9351.cover
  let M : List ℕ := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
  have sound : ∀ k : Fin L.length, ∀ i j : Fin 21, i ∈ (L.get k).1 → j ∈ (L.get k).2 →
      (M.getD i.val 0).testBit j.val = false := by decide +kernel
  have hits : ∀ i j : Fin 21, (M.getD i.val 0).testBit j.val = false →
      ∃ k : Fin L.length, i ∈ (L.get k).1 ∧ j ∈ (L.get k).2 := by decide +kernel
  refine ⟨L, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hr
    exact sound k i j hi hj
  · intro i j h
    obtain ⟨k, hi, hj⟩ := hits i j h
    exact ⟨L.get k, List.get_mem L k, hi, hj⟩
