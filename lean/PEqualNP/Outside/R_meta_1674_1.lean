import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1674_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = i) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ i j : Fin C.gates.length, i ≠ j ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not → k = i ∨ k = j) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ i j k : Fin C.gates.length, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro h0 h1 h2 h3 C hF hfirst hfun
  by_cases hA : ∃ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨i, hi⟩ := hA
    by_cases hB : ∃ j : Fin C.gates.length, j ≠ i ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not
    · obtain ⟨j, hji, hj⟩ := hB
      by_cases hC : ∃ k : Fin C.gates.length, k ≠ i ∧ k ≠ j ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not
      · obtain ⟨k, hki, hkj, hk⟩ := hC
        exact h3 C hF ⟨i, j, k, hji.symm, hki.symm, hkj.symm, hi, hj, hk⟩ hfirst hfun
      · refine h2 C hF ⟨i, j, hji.symm, hi, hj, ?_⟩ hfirst hfun
        intro k hk
        by_contra hne
        exact hC ⟨k, fun e => hne (Or.inl e), fun e => hne (Or.inr e), hk⟩
    · refine h1 C hF ⟨i, hi, ?_⟩ hfirst hfun
      intro j hj
      by_contra hne
      exact hB ⟨j, hne, hj⟩
  · refine h0 C hF ?_ hfirst hfun
    intro g hg hnot
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hg
    exact hA ⟨i, hnot⟩
