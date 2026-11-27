import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11105

def A (i j : Fin 20) : Bool := (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val

def RM : List ℕ := [439725, 184833, 617232, 739332, 262218, 2409, 4818, 525492, 369666]

def CM : List ℕ := [33825, 135885, 591942, 543536, 367434, 420105, 836114, 734340, 271770]

def RR (k : ℕ) : Finset (Fin 20) := Finset.univ.filter (fun i => (RM.getD k 0).testBit i.val = true)

def CC (k : ℕ) : Finset (Fin 20) := Finset.univ.filter (fun j => (CM.getD k 0).testBit j.val = true)

set_option maxRecDepth 100000 in
theorem hmono : ∀ k : Fin 9, ∀ i j : Fin 20, (RM.getD k.val 0).testBit i.val = true →
    (CM.getD k.val 0).testBit j.val = true → A i j = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem hcov : ∀ i j : Fin 20, A i j = false → ∃ k : Fin 9, (RM.getD k.val 0).testBit i.val = true ∧
    (CM.getD k.val 0).testBit j.val = true := by decide +kernel

theorem main_aux : ∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 9 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨(List.range 9).map (fun k => (RR k, CC k)), by simp, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    simp only [RR, CC, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hmono ⟨k, List.mem_range.1 hk⟩ i j hi hj
  · intro i j h
    obtain ⟨k, h1, h2⟩ := hcov i j h
    refine ⟨(RR k.val, CC k.val), List.mem_map.2 ⟨k.val, List.mem_range.2 k.isLt, rfl⟩, ?_, ?_⟩
    · simp only [RR, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1
    · simp only [CC, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h2

end PEqualNP.Outside.L_meta_11105

theorem PEqualNP.Outside.L_meta_11105 : ∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 9 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 :=
  PEqualNP.Outside.L_meta_11105.main_aux
