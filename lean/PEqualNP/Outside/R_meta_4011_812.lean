import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4011_812
    (counting : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ a b, G.Adj a b → a ∉ A) → (∃ a b, G.Adj a b) →
    IsMinimalCircuit n C → circuitFun n C = graphFun G A →
    (∀ T : Finset (Fin n), Disjoint A T →
      (∀ a b, G.Adj a b → a∈T ∨ b∈T) →
      C.size+1 < A.card+G.edgeFinset.card+T.card) →
    ∃ a b, G.Adj a b ∧
      (C.gates.filter (fun g => (g.inputs.take
        (bif g.op.eval [false] then 1 else 2)).contains a.val)).length ≤ 2 ∧
      (C.gates.filter (fun g => (g.inputs.take
        (bif g.op.eval [false] then 1 else 2)).contains b.val)).length ≤ 2)
    (adjacent : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ a b, G.Adj a b → a ∉ A) → (∃ a b, G.Adj a b) →
    IsMinimalCircuit n C → circuitFun n C = graphFun G A →
    (∀ v ∉ A, let rs := C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) →
    (∃ a b, G.Adj a b ∧
      (C.gates.filter (fun g => (g.inputs.take
        (bif g.op.eval [false] then 1 else 2)).contains a.val)).length ≤ 2 ∧
      (C.gates.filter (fun g => (g.inputs.take
        (bif g.op.eval [false] then 1 else 2)).contains b.val)).length ≤ 2) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →             PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →               (∀ x12 ∉ x4,                   have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;                   x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                 (∀ (x13 : Finset (Fin x1)), Disjoint x4 x13 → (∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → x15 ∈ x13 ∨ x16 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + x13.card) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15 := by
  intro n G _ A C hdeg hgirth hA hedge hminimal hfun hread hsmall
  exact adjacent n G A C hdeg hgirth hA hedge hminimal hfun hread
    (counting n G A C hdeg hA hedge hminimal hfun hsmall)
