import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18675 : ∀ (x1 : ℕ) (x2 : List PEqualNP.CircuitLowerBounds.Gate),   (∀ (x3 : Fin x2.length),       have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.getD ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };       (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x4.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < x1 + ↑x3 ∧ x6 < x1 + ↑x3) →     PEqualNP.TopForm.IsAO2 x1 { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ x4 ∈ x2, x4.inputs.Nodup := by
  intro n gs h
  have hm : ∀ g ∈ gs, ∃ j : Fin gs.length, gs.getD j.val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
    exact ⟨j, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]; simpa using hj⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨j, rfl⟩ := hm g hg
    exact (h j).1
  · intro j hj i hi
    obtain ⟨a, b, hab, _, ha, hb⟩ := (h ⟨j, hj⟩).2
    have : i ∈ [a, b] := by
      change i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
      rw [hab] at hi; exact hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨j, rfl⟩ := hm g hg
    obtain ⟨a, b, hab, _, _, _⟩ := (h j).2
    rw [hab]; rfl
  · intro g hg
    obtain ⟨j, rfl⟩ := hm g hg
    obtain ⟨a, b, hab, hne, _, _⟩ := (h j).2
    rw [hab]; simp [hne]
