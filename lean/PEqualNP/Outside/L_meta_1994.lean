import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 20000 in
theorem PEqualNP.Outside.L_meta_1994 :
    ∀ (x1 : SimpleGraph (Fin (10 : ℕ))),   (x1 = SimpleGraph.fromRel fun (x2 x3 : Fin (10 : ℕ)) => (↑x2, ↑x3) ∈ [((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ)), ((2 : ℕ), (3 : ℕ)), ((3 : ℕ), (4 : ℕ)), ((4 : ℕ), (0 : ℕ)), ((0 : ℕ), (5 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((3 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((9 : ℕ), (6 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((8 : ℕ), (5 : ℕ))]) →     have x3 : ℕ → Finset (Fin (10 : ℕ)) := fun (x3 : ℕ) => {x4 : Fin (10 : ℕ) | x3.testBit ↑x4 = Bool.true};     have x4 : List ℕ := [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)];     ∀ (x5 : Finset (Fin (10 : ℕ))), (∀ x6 ∈ x5, ∀ x8 ∈ x5, ¬x1.Adj x6 x8) → (∀ x7 ∉ x5, ∃ x9 ∈ x5, x1.Adj x9 x7) → (∃ x8 ∈ x4, x5 = x3 x8) ∧ (x5.card = (3 : ℕ) ∨ ∀ x8 ∉ x5, ∃ x10 ∈ x4, (x3 x10).card = (3 : ℕ) ∧ ∃ x11 ∉ x3 x10, Insert.insert x11 (x3 x10) ⊆ Insert.insert x8 x5) := by
  intro G hG
  subst G
  simp only [SimpleGraph.fromRel_adj, List.exists_mem_cons_iff, List.not_mem_nil,
    false_and, exists_false, or_false]
  decide +kernel
