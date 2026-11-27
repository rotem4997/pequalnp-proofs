import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9985

def rs : List (ℕ × ℕ) := [(1034, 8512), (8512, 1034), (16793, 512), (512, 16793), (4108, 2336), (2336, 4108), (615, 16384), (16384, 615), (2066, 4288), (4288, 2066), (1, 32256), (32256, 1), (8212, 1184), (1184, 8212)]
def M : List ℕ := [32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615]
def fs (a : ℕ) : Finset (Fin 15) := Finset.univ.filter fun i => a.testBit i.val = true
theorem c1 : ∀ p ∈ rs, ∀ i j : Fin 15, p.1.testBit i.val = true → p.2.testBit j.val = true → (M.getD i.val 0).testBit j.val = true := by decide +kernel
theorem c2 : ∀ i j : Fin 15, (M.getD i.val 0).testBit j.val = true → ∃ p ∈ rs, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

end PEqualNP.Outside.L_meta_9985

theorem PEqualNP.Outside.L_meta_9985 : ∃ L : List (Finset (Fin 15) × Finset (Fin 15)), L.length ≤ 14 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 15) (j : Fin 15), (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_9985.rs.map fun p => (PEqualNP.Outside.L_meta_9985.fs p.1, PEqualNP.Outside.L_meta_9985.fs p.2), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact PEqualNP.Outside.L_meta_9985.c1 p hp i j (by simpa [PEqualNP.Outside.L_meta_9985.fs] using hi) (by simpa [PEqualNP.Outside.L_meta_9985.fs] using hj)
  · intro i j h
    obtain ⟨p, hp, h1, h2⟩ := PEqualNP.Outside.L_meta_9985.c2 i j h
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, by simpa [PEqualNP.Outside.L_meta_9985.fs] using h1, by simpa [PEqualNP.Outside.L_meta_9985.fs] using h2⟩
