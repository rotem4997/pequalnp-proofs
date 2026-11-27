import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- An input on an edge must have a reader. A sole NOT reader and a sole binary-operation
-- reader require different constant propagation arguments after fixing the input.
theorem PEqualNP.Outside.R_meta_4905_1
    (needed :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v w : Fin n),
        G.Adj v w → FanInTwo C → circuitFun n C = graphFun G ∅ →
        ∃ g ∈ C.gates, v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2))
    (inverting :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
        let read (v : Fin n) := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u w, G.Adj u w → u ∉ A) →
        IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
        (∀ v ∉ A, (read v).length ≤ 3 ∧ ((read v).length = 3 → ∀ g ∈ read v, g.op = GateOp.or)) →
        (∃ v ∉ A, ∃ g, read v = [g] ∧ g.op = GateOp.not) →
        ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
          HasCircuitSize n (fun x => graphFun G ∅ (Function.update x v false)) s)
    (other :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
        let read (v : Fin n) := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u w, G.Adj u w → u ∉ A) →
        IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
        (∀ v ∉ A, (read v).length ≤ 3 ∧ ((read v).length = 3 → ∀ g ∈ read v, g.op = GateOp.or)) →
        (∃ v ∉ A, ∃ g, read v = [g] ∧ g.op ≠ GateOp.not) →
        ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
          HasCircuitSize n (fun x => graphFun G ∅ (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>     have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x6.gates;     (∀ x8 ∉ x4, (x7 x8).length ≤ (3 : ℕ) ∧ ((x7 x8).length = (3 : ℕ) → ∀ x11 ∈ x7 x8, x11.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧ ∃ x8 ∉ x4, (x7 x8).length ≤ (1 : ℕ);   (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x5 → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update x16 x14 Bool.false)) x15 := by
  intro n G decG A C
  dsimp only
  intro degree girth isolated _ minimal computes sparse
  rcases sparse with ⟨bound, v, outside, rare⟩
  have positive : 0 < (G.neighborSet v).ncard := by rw [degree v outside]; decide
  obtain ⟨w, edge⟩ := (Set.ncard_pos (Set.toFinite _)).mp positive
  obtain ⟨g, gate, used⟩ := needed n G C v w edge minimal.1 computes
  let read (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  have member : g ∈ read v := by simpa [read, gate] using used
  have one : (read v).length = 1 := Nat.le_antisymm rare (List.length_pos_of_mem member)
  obtain ⟨only, reader⟩ := List.length_eq_one_iff.mp one
  by_cases op : only.op = GateOp.not
  · exact inverting n G A C degree girth isolated minimal computes bound ⟨v, outside, only, reader, op⟩
  · exact other n G A C degree girth isolated minimal computes bound ⟨v, outside, only, reader, op⟩
