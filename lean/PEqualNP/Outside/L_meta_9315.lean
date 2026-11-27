import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9315

def A (i j : Fin 13) : Bool := (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val

def RM : List ℕ := [2599, 2205, 1133, 4353, 4270, 3130, 322, 7692, 6260, 2792, 784, 1408]

def CM : List ℕ := [136, 544, 2304, 70, 1280, 4160, 532, 48, 129, 4098, 3076, 13]

def RR (k : ℕ) : Finset (Fin 13) := Finset.univ.filter (fun i => (RM.getD k 0).testBit i.val = true)

def CC (k : ℕ) : Finset (Fin 13) := Finset.univ.filter (fun j => (CM.getD k 0).testBit j.val = true)

set_option maxRecDepth 100000 in
theorem hmono : ∀ k : Fin 12, ∀ i j : Fin 13, (RM.getD k.val 0).testBit i.val = true →
    (CM.getD k.val 0).testBit j.val = true → A i j = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem hcov : ∀ i j : Fin 13, A i j = false → ∃ k : Fin 12, (RM.getD k.val 0).testBit i.val = true ∧
    (CM.getD k.val 0).testBit j.val = true := by decide +kernel

theorem main_aux : ∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨(List.range 12).map (fun k => (RR k, CC k)), by simp, ?_, ?_⟩
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

end PEqualNP.Outside.L_meta_9315

theorem PEqualNP.Outside.L_meta_9315 : ∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 :=
  PEqualNP.Outside.L_meta_9315.main_aux
