import Mathlib

namespace PEqualNP.Outside.L_meta_9993_aux

def rows : List ℕ := [252, 504, 497, 483, 455, 399, 287, 63, 126]

def pairs : List (ℕ × ℕ) := [(7, 240), (385, 60), (12, 481), (48, 391), (192, 31), (98, 264), (280, 66)]

def f (p : ℕ × ℕ) : Finset (Fin 9) × Finset (Fin 9) :=
  (Finset.univ.filter (fun i : Fin 9 => p.1.testBit i.val), Finset.univ.filter (fun j : Fin 9 => p.2.testBit j.val))

def L : List (Finset (Fin 9) × Finset (Fin 9)) := pairs.map f

set_option maxRecDepth 100000 in
theorem hsub : ∀ p ∈ pairs, ∀ (i : Fin 9) (j : Fin 9), p.1.testBit i.val = true → p.2.testBit j.val = true →
    (rows.getD i.val 0).testBit j.val = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hcov : ∀ (i : Fin 9) (j : Fin 9), (rows.getD i.val 0).testBit j.val = true →
    ∃ p ∈ pairs, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by
  decide +kernel

theorem h1 : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (rows.getD i.val 0).testBit j.val = true := by
  intro r hr i hi j hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hsub p hp i j hi hj

theorem h2 : ∀ (i : Fin 9) (j : Fin 9), (rows.getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  intro i j h
  obtain ⟨p, hp, h1, h2⟩ := hcov i j h
  refine ⟨f p, List.mem_map_of_mem hp, ?_, ?_⟩
  · simp only [f, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1
  · simp only [f, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h2

theorem hlen : L.length ≤ 7 := by
  simp [L, pairs]

end PEqualNP.Outside.L_meta_9993_aux

theorem PEqualNP.Outside.L_meta_9993 : ∃ L : List (Finset (Fin 9) × Finset (Fin 9)), L.length ≤ 7 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 9) (j : Fin 9), (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  exact ⟨PEqualNP.Outside.L_meta_9993_aux.L, PEqualNP.Outside.L_meta_9993_aux.hlen, PEqualNP.Outside.L_meta_9993_aux.h1, PEqualNP.Outside.L_meta_9993_aux.h2⟩
