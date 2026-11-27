import Mathlib
import PEqualNP.Defs
-- The step: the 0-entries of the 25 by 30 matrix in the statement (row i is number i of the list,
-- entry (i, j) is binary digit j of it) are covered by at most 18 rectangles of rows times columns
-- that hold only 0-entries.
-- The proof is the explicit list cover of 18 rectangles. The kernel checks two facts by
-- evaluation: every entry of every listed rectangle is 0 (sound), and every 0-entry of the matrix
-- lies in a listed rectangle (hits). The closing lines turn the two facts into the statement.
-- The cover was found by a search program outside this file and is only checked in it.
-- Credit: the shape of this proof (the list cover, the facts sound and hits and the closing
-- lines) follows the merged file L_meta_9351.lean (pull request 13338, by DPS0340).

namespace PEqualNP.Outside.L_meta_10027

def cover : List (Finset (Fin 25) × Finset (Fin 30)) := [
    ({0, 5, 12, 13, 22, 23}, {1, 4, 7, 11, 12, 18, 19, 23, 28}),
    ({0, 6, 9, 11, 14, 15}, {2, 3, 6, 11, 13, 17, 19, 24, 29}),
    ({0, 7, 8, 17, 18, 20}, {1, 4, 8, 13, 14, 16, 17, 22, 27}),
    ({0, 10, 16, 19, 21, 24}, {2, 3, 9, 12, 14, 16, 18, 21, 26}),
    ({1, 6, 17, 19}, {0, 3, 7, 8, 10, 12, 17, 23, 24, 27, 29}),
    ({1, 8, 15, 16}, {2, 4, 5, 9, 12, 13, 18, 19, 20, 22, 29}),
    ({1, 12, 14, 20, 21}, {3, 8, 9, 14, 15, 17, 22, 23, 26, 28}),
    ({2, 5, 7, 11}, {3, 4, 5, 8, 11, 14, 16, 18, 20, 24, 28}),
    ({2, 8, 9, 12}, {0, 1, 6, 9, 10, 14, 19, 21, 23, 28, 29}),
    ({2, 15, 17, 23, 24}, {1, 6, 8, 13, 15, 19, 21, 24, 26, 27}),
    ({3, 6, 7, 10, 13}, {4, 7, 9, 12, 15, 16, 21, 24, 28, 29}),
    ({3, 18, 21, 22}, {0, 4, 6, 9, 10, 11, 16, 22, 24, 26, 27}),
    ({3, 19, 20, 23}, {1, 2, 5, 7, 11, 14, 17, 19, 20, 21, 27}),
    ({4, 5, 9, 16, 18}, {2, 6, 7, 11, 15, 18, 22, 23, 27, 29}),
    ({4, 10, 14, 22}, {1, 3, 5, 6, 12, 13, 16, 17, 20, 23, 26}),
    ({4, 11, 13, 24}, {0, 2, 7, 8, 10, 13, 18, 21, 22, 26, 28}),
    ({5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 21, 22}, {5, 10, 25}),
    ({6, 7, 8, 11, 12, 14, 16, 18, 19, 22, 23, 24}, {0, 20, 25})]

end PEqualNP.Outside.L_meta_10027

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_10027 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 18 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  let L := PEqualNP.Outside.L_meta_10027.cover
  let M : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
  have sound : ∀ k : Fin L.length, ∀ (i : Fin 25) (j : Fin 30), i ∈ (L.get k).1 → j ∈ (L.get k).2 →
      (M.getD i.val 0).testBit j.val = false := by decide +kernel
  have hits : ∀ (i : Fin 25) (j : Fin 30), (M.getD i.val 0).testBit j.val = false →
      ∃ k : Fin L.length, i ∈ (L.get k).1 ∧ j ∈ (L.get k).2 := by decide +kernel
  refine ⟨L, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hr
    exact sound k i j hi hj
  · intro i j h
    obtain ⟨k, hi, hj⟩ := hits i j h
    exact ⟨L.get k, List.get_mem L k, hi, hj⟩
