import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_272 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ (∃ A : Finset ℕ, A.card = 5 ∧ (∀ j ∈ A, j < C.size) ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ j ∈ A)) ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ⟨{0, 1, 3, 4, 6}, by decide, by decide, ?_⟩, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    all_goals first | exact absurd h id | (constructor <;> simp)
  · intro j g hg
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp
  · decide
