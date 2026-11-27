import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The reader count comes from the checked density theorem L-meta-4149.
-- The local case now involves one vertex and all three of its neighbors.
theorem PEqualNP.Outside.R_meta_1973_734
    (concentrate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A
    let r := fun v : Fin n => (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A, 2 ≤ r v ∧ r v ≤ 3) → ∃ v ∉ A, r v = 2 ∧ ∀ w, G.Adj v w → r w = 2)
    (localized : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A
    let r := fun v : Fin n => C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
      ((r v).length = 3 → ∀ g ∈ r v, g.op = .or)) →
    (∃ v ∉ A, (r v).length = 2 ∧ ∀ w, G.Adj v w → (r w).length = 2) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C degree girth noMarked edge fSpec fan computes minimal readBounds _
  classical
  let graphTarget := PEqualNP.MetaComplexity.NestedCover.graphFun G A
  have sameTarget : graphTarget = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧
      x u = true ∧ x v = true)) = true ↔ f x = true
    rw [fSpec x]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have computesGraph : circuitFun n C = graphTarget := computes.trans sameTarget.symm
  have leastGraph (s : ℕ) (h : HasCircuitSize n graphTarget s) : C.size ≤ s :=
    minimal s (sameTarget ▸ h)
  have found := concentrate n G A C degree girth noMarked edge fan computesGraph leastGraph
    (fun v hv => ⟨(readBounds v hv).1,(readBounds v hv).2.1⟩)
  have result := localized n G A C degree girth noMarked edge fan computesGraph leastGraph readBounds found
  change ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
    HasCircuitSize n (fun x => graphTarget (Function.update x v false)) s at result
  rwa [sameTarget] at result
