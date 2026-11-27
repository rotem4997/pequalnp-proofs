import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_161 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ i j : Fin C.gates.length, i ≠ j ∧ ∀ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ (k = i ∨ k = j)) ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) := by
  -- Wires 0..3 are the inputs. Split the inputs by each binary digit of their index:
  -- wire 8 = (x0 ∨ x1) ∧ (x2 ∨ x3), wire 9 = (x0 ∨ x2) ∧ (x1 ∨ x3), output = wire 8 ∨ wire 9.
  -- Two distinct indices differ in some binary digit, so some split separates them.
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩,
      ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · refine ⟨⟨4, by simp⟩, ⟨5, by simp⟩, by simp [Fin.ext_iff], ?_⟩
    intro k
    change Fin 7 at k
    fin_cases k <;> simp [Fin.ext_iff]
  · intro x
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : Bool, x = ![a, b, c, d] :=
      ⟨x 0, x 1, x 2, x 3, by ext i; fin_cases i <;> rfl⟩
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
