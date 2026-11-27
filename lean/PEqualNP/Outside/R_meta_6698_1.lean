import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6698_1
    (structureStep : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin x1) => List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;   (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → x2 ≠ ⊥ → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x12 ∉ x4, (x6 x12).length ≤ (3 : ℕ) ∧ ((x6 x12).length = (3 : ℕ) → ∀ x15 ∈ x6 x12, x15.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x13 ∉ x4, ∀ (x15 x16 : Finset (Fin x1)), (x15 ∪ x16).card ≤ (2 : ℕ) → x13 ∉ x15 ∪ x16 → x2.IsIndepSet ↑x15 → Disjoint x4 x15 → Disjoint x15 x16 → ¬∀ x22 ∈ x6 x13, ∃ (x24 : Fin x1), ↑x24 ∈ x22.inputs ∧ (x24 ∈ x15 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x24 ∈ x16 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.and)) → ∃ v ∉ x4, ∃ J : Finset ℕ, 4 ≤ J.card ∧
    ∀ j ∈ J, j < x5.size ∧ ∃ p < x1 + j, ∀ x : Fin x1 → Bool,
      let w := x5.wires (List.ofFn (Function.update x v false))
      w.getD (x1+j) false = w.getD p false)
    (compress : ∀ (n : ℕ) (v : Fin n) (J : Finset ℕ), ∀ C : Circuit, FanInTwo C →
      (∀ j ∈ J, j < C.size ∧ ∃ p < n + j, ∀ x : Fin n → Bool,
        let w := C.wires (List.ofFn (Function.update x v false))
        w.getD (n + j) false = w.getD p false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + J.card ≤ C.size ∧
        ∀ x, circuitFun n D x = circuitFun n C (Function.update x v false)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin x1) => List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;   (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → x2 ≠ ⊥ → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x12 ∉ x4, (x6 x12).length ≤ (3 : ℕ) ∧ ((x6 x12).length = (3 : ℕ) → ∀ x15 ∈ x6 x12, x15.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x13 ∉ x4, ∀ (x15 x16 : Finset (Fin x1)), (x15 ∪ x16).card ≤ (2 : ℕ) → x13 ∉ x15 ∪ x16 → x2.IsIndepSet ↑x15 → Disjoint x4 x15 → Disjoint x15 x16 → ¬∀ x22 ∈ x6 x13, ∃ (x24 : Fin x1), ↑x24 ∈ x22.inputs ∧ (x24 ∈ x15 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x24 ∈ x16 ∧ x22.op = PEqualNP.CircuitLowerBounds.GateOp.and)) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x16 x14 Bool.false)) x15 := by
  intro n G inst A C
  dsimp only
  intro hdeg hgirth hne hmin hfun hread hblock
  obtain ⟨v, hv, J, hcard, hdup⟩ :=
    structureStep n G A C hdeg hgirth hne hmin hfun hread hblock
  obtain ⟨D, hf, hsize, heq⟩ := compress n v J C hmin.1 hdup
  refine ⟨v, hv, D.size, by omega, D, hf, le_rfl, fun x => ?_⟩
  exact (heq x).trans (congrFun hfun (Function.update x v false))
