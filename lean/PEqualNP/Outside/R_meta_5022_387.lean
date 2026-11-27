import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5022_387
    (slots : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let r := fun (v : Fin n) => (C.gates.filter (fun g =>
        (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)).length
      PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) →
        (∑ v : Fin n, r v) ≤ C.size + 1)
    (chargeCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ w (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∀ x y, G.Adj x y → x ∉ A) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G A →
      let R (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, 2 ≤ (R v).length ∧ ((R v).length = 2 → ∀ g ∈ R v, g.op = .or)) →
      (∃ v ∉ A, (R v).length = 2) →
      ∃ T : Finset (Fin n), (∀ x y, G.Adj x y → x ∈ T ∨ y ∈ T) ∧
        A.card + G.edgeSet.ncard + T.card ≤ ∑ v : Fin n, (R v).length) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∀ x17 ∉ x4,                           have x19 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x17) x6.gates;                           x19.length = (2 : ℕ) → ∀ x21 ∈ x19, x21.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                         (∃ x18 ∉ x4, (List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x18) x6.gates).length = (2 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n k G A f C hdegree hgirth hapart he hminimum hfun hfan hcomputes hsize hreads hor htwo
  have correct : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G A := by
    rw [hcomputes]
    funext x
    apply Bool.eq_iff_iff.mpr
    refine (hfun x).trans ?_
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have minimal : PEqualNP.MetaComplexity.IsMinimalCircuit n C := by
    refine ⟨hfan, fun D hD hEq => hsize D.size ?_⟩
    exact ⟨D, hD, le_rfl, fun x => congrFun (hEq.trans hcomputes) x⟩
  have outputsUnequal : ∃ x y, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y := by
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    rw [hcomputes]
    have p : f (fun _ => true) = true := by
      obtain ⟨u, v, huv⟩ := he
      exact (hfun _).mpr (Or.inr ⟨u, v, huv, rfl, rfl⟩)
    have q : f (fun _ => false) = false := by
      cases h : f (fun _ => false)
      · rfl
      · rcases (hfun _).mp h with ⟨a, _, ha⟩ | ⟨u, v, _, hu, _⟩
        · exact absurd ha (by decide)
        · exact absurd hu (by decide)
    rw [p, q]
    decide
  have sum := slots n C minimal outputsUnequal
  obtain ⟨T, hT, hb⟩ := chargeCover n G A C hdegree hgirth hapart minimal correct
    (fun v hv => ⟨hreads v hv, hor v hv⟩) htwo
  have hk := hminimum T hT
  simp only at sum hb
  omega
