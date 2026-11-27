import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2629_739
    (ports : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G A →
    (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.MetaComplexity.NestedCover.graphFun G A) s → C.size ≤ s) →
    A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) +
      (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size+1)
    (drop : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (v : Fin n),
    (∀ a ∉ A, (G.neighborSet a).ncard = 3) → (∀ i j, G.Adj i j → i ∉ A) →
    T ⊆ Aᶜ → (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → v ∈ T →
    ∃ s, s+5 ≤ A.card + G.edgeFinset.card + T.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x => PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update x v false)) s)
    (residual : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ T : Finset (Fin x1), T ⊆ x4ᶜ → (∀ i j, x2.Adj i j → i∈T ∨ j∈T) →
      (∑ v ∈ x4ᶜ, (x7 v).length) + (x5.gates.filter (fun g => g.op.eval [false])).length <
        x2.edgeFinset.card + T.card) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G dec A C F R cubic girth isolated nonempty fan computes minimal degrees inverter
  have paid := ports n G A C fan computes minimal
  change A.card + (∑ v ∈ Aᶜ, (R v).length) + (C.gates.filter (fun g => g.op.eval [false])).length ≤ C.size+1 at paid
  let cover (T : Finset (Fin n)) := ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T
  by_cases affordable : ∃ T : Finset (Fin n), T ⊆ Aᶜ ∧ cover T ∧
      G.edgeFinset.card + T.card ≤ (∑ v ∈ Aᶜ, (R v).length) + (C.gates.filter (fun g => g.op.eval [false])).length
  · obtain ⟨T,sub,cov,cost⟩ := affordable
    obtain ⟨i,j,edge⟩ := nonempty
    have occupied : T.Nonempty := (cov i j edge).elim (fun h => ⟨i,h⟩) (fun h => ⟨j,h⟩)
    obtain ⟨v,hv⟩ := occupied
    obtain ⟨s,hs,works⟩ := drop n G A T v cubic isolated sub cov hv
    exact ⟨v,Finset.mem_compl.mp (sub hv),s,by omega,works⟩
  · apply residual n G A C cubic girth isolated nonempty fan computes minimal degrees inverter
    intro T sub cov
    exact Nat.lt_of_not_ge (fun h => affordable ⟨T,sub,cov,h⟩)
