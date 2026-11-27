import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5693 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x7 : ℕ) (x8 : ℕ) (x9 : Finset ℕ) (x10 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).inputs = [x7, x8] ∧ x7 ∈ x10 ∧ x8 ∈ x9 ∧ (∀ x11 ∈ x9, x11 < x1 ∨ ∃ x13 < x3.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).inputs, x14 ∈ x9) ∧ ∀ x11 ∈ x10, x1 ≤ x11 ∧ x11 < x1 + x2 ∨ ∃ x13 < x3.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x13).inputs, x14 ∈ x10) → ∃ (x5 : Finset ℕ) (x6 : Finset ℕ), (∀ x7 ∈ x5, x7 < x1 ∨ ∃ x9 < x3.gates.length, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x5) ∧ (∀ x7 ∈ x6, x1 ≤ x7 ∧ x7 < x1 + x2 ∨ ∃ x9 < x3.gates.length, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x6) ∧ ∀ x7 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x6 ∧ x11 ∈ x5 := by
  classical
  intro n m C h
  choose a b P L hin ha hb hP hL using h
  refine ⟨(Finset.range C.gates.length).biUnion (fun j =>
      if h1 : j < C.gates.length then
        (if h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and then P j h1 h2 else ∅) else ∅),
    (Finset.range C.gates.length).biUnion (fun j =>
      if h1 : j < C.gates.length then
        (if h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and then L j h1 h2 else ∅) else ∅), ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨j, hj, hw⟩ := hw
    rw [Finset.mem_range] at hj
    rw [dif_pos hj] at hw
    by_cases h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and
    · rw [dif_pos h2] at hw
      rcases hP j hj h2 w hw with h3 | ⟨k, hk, hwk, hop, hall⟩
      · exact Or.inl h3
      · refine Or.inr ⟨k, hk, hwk, hop, fun i hi => ?_⟩
        rw [Finset.mem_biUnion]
        refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
        rw [dif_pos hj, dif_pos h2]
        exact hall i hi
    · rw [dif_neg h2] at hw
      exact absurd hw (Finset.notMem_empty w)
  · intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨j, hj, hw⟩ := hw
    rw [Finset.mem_range] at hj
    rw [dif_pos hj] at hw
    by_cases h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and
    · rw [dif_pos h2] at hw
      rcases hL j hj h2 w hw with h3 | ⟨k, hk, hwk, hop, hall⟩
      · exact Or.inl h3
      · refine Or.inr ⟨k, hk, hwk, hop, fun i hi => ?_⟩
        rw [Finset.mem_biUnion]
        refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
        rw [dif_pos hj, dif_pos h2]
        exact hall i hi
    · rw [dif_neg h2] at hw
      exact absurd hw (Finset.notMem_empty w)
  · intro j hj h2
    refine ⟨a j hj h2, b j hj h2, hin j hj h2, ?_, ?_⟩
    · rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      rw [dif_pos hj, dif_pos h2]
      exact ha j hj h2
    · rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      rw [dif_pos hj, dif_pos h2]
      exact hb j hj h2
