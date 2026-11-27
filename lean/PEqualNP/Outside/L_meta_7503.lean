import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7503 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x1.size < (64 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size ≤ x1.size ∧ (∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = x1.eval (List.ofFn x7)) ∧ ¬∃ (x7 : ℕ) (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x7 x8 := by
  intro x1 h1 h2
  obtain ⟨g, hg, hn⟩ := h1
  rcases h2.1 g hg with h | h <;> simp_all
