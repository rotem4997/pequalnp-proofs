import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9361

def rs : List (ℕ × ℕ) := [(266048, 1576971), (700928, 1237), (12359, 115736), (66181, 273424), (596000, 1073728), (1311234, 48264), (550017, 67862), (482710, 1048608), (1163360, 394120), (1607840, 140037), (262315, 633344), (41362, 721956), (411669, 37184), (196905, 805440), (1119256, 286882), (559692, 135185)]
def M : List ℕ := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def fs (a : ℕ) : Finset (Fin 21) := Finset.univ.filter fun i => a.testBit i.val = true
theorem c1 : ∀ p ∈ rs, ∀ i j : Fin 21, p.1.testBit i.val = true → p.2.testBit j.val = true → (M.getD i.val 0).testBit j.val = false := by decide +kernel
theorem c2 : ∀ i j : Fin 21, (M.getD i.val 0).testBit j.val = false → ∃ p ∈ rs, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_9361

theorem PEqualNP.Outside.L_meta_9361 : ∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 17 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 21) (j : Fin 21), (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_9361.rs.map fun p => (PEqualNP.Outside.L_meta_9361.fs p.1, PEqualNP.Outside.L_meta_9361.fs p.2), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact PEqualNP.Outside.L_meta_9361.c1 p hp i j (by simpa [PEqualNP.Outside.L_meta_9361.fs] using hi) (by simpa [PEqualNP.Outside.L_meta_9361.fs] using hj)
  · intro i j h
    obtain ⟨p, hp, h1, h2⟩ := PEqualNP.Outside.L_meta_9361.c2 i j h
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, by simpa [PEqualNP.Outside.L_meta_9361.fs] using h1, by simpa [PEqualNP.Outside.L_meta_9361.fs] using h2⟩
