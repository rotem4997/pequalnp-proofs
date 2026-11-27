import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split the residual NOT 2-reader case of L-meta-1973 on the other reader.
theorem PEqualNP.Outside.R_meta_2629_2
    (hAND :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := NestedCover.graphFun G A
      let r := fun v : Fin n => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
        ((r v).length = 3 → ∀ g ∈ r v, g.op = GateOp.or)) →
      (∃ v ∉ A, (r v).length = 2 ∧ (∃ g ∈ r v, g.op = GateOp.not) ∧
        (∃ h ∈ r v, h.op = GateOp.and)) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (hOR :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := NestedCover.graphFun G A
      let r := fun v : Fin n => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
        ((r v).length = 3 → ∀ g ∈ r v, g.op = GateOp.or)) →
      (∃ v ∉ A, (r v).length = 2 ∧ (∃ g ∈ r v, g.op = GateOp.not) ∧
        (∃ h ∈ r v, h.op = GateOp.or)) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (hNOT :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := NestedCover.graphFun G A
      let r := fun v : Fin n => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
        ((r v).length = 3 → ∀ g ∈ r v, g.op = GateOp.or)) →
      (∃ v ∉ A, (r v).length = 2 ∧ (∃ g ∈ r v, g.op = GateOp.not) ∧
        (∀ h ∈ r v, h.op = GateOp.not)) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G _ A C
  dsimp only
  intro hdeg hgirth hA hedge hfan hcomp hmin hread hnot
  obtain ⟨v, hv, htwo, g, hg, hgnot⟩ := hnot
  let r := fun u : Fin n => C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains u.val
  have hmem : ∀ h ∈ r v, h ∈ C.gates := fun h hh => (List.mem_filter.mp hh).1
  by_cases hAnd : ∃ h ∈ r v, h.op = GateOp.and
  · exact hAND n G A C hdeg hgirth hA hedge hfan hcomp hmin hread
      ⟨v, hv, htwo, ⟨g, hg, hgnot⟩, hAnd⟩
  by_cases hOr : ∃ h ∈ r v, h.op = GateOp.or
  · exact hOR n G A C hdeg hgirth hA hedge hfan hcomp hmin hread
      ⟨v, hv, htwo, ⟨g, hg, hgnot⟩, hOr⟩
  refine hNOT n G A C hdeg hgirth hA hedge hfan hcomp hmin hread
    ⟨v, hv, htwo, ⟨g, hg, hgnot⟩, ?_⟩
  intro h hh
  have hop := (hfan h (hmem h hh)).1
  rcases (Set.mem_insert_iff.mp hop) with hnd | hop
  · exact (hAnd ⟨h, hh, hnd⟩).elim
  rcases (Set.mem_insert_iff.mp hop) with hor | hnt
  · exact (hOr ⟨h, hh, hor⟩).elim
  · exact Set.mem_singleton_iff.mp hnt
