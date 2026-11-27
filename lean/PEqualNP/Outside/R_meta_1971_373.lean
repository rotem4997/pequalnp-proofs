import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Strip the marked variables while retaining a suitable sparse minimum, rescue an
-- ordinary vertex of the unmarked function, and reattach the marked variables.
theorem PEqualNP.Outside.R_meta_1971_373 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let sparse := fun (D : Circuit) =>
      let read (v : Fin n) := D.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (read v).length ≤ 3 ∧ ((read v).length = 3 → ∀ g ∈ read v, g.op = .or)) ∧
      ∃ v ∉ A, (read v).length ≤ 1
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A → sparse C →
    ∃ D : Circuit, IsMinimalCircuit n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ sparse D) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let sparse := fun (D : Circuit) =>
      let read (v : Fin n) := D.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (read v).length ≤ 3 ∧ ((read v).length = 3 → ∀ g ∈ read v, g.op = .or)) ∧
      ∃ v ∉ A, (read v).length ≤ 1
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ → sparse C →
    ∃ v ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => NestedCover.graphFun G ∅ (Function.update x v false)) t) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (s k : ℕ),
    let e := NestedCover.graphFun G ∅
    let f := NestedCover.graphFun G A
    (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) → HasCircuitSize n f s →
    (∀ b, HasCircuitSize n e b → k ≤ b) →
    (∃ v ∉ A, ∃ t, t+4 ≤ k ∧ HasCircuitSize n (fun x => e (Function.update x v false)) t) →
    ∃ v ∉ A, ∃ t, t+4 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro strip rescue attach n G A f C deg girth iso edge spec fan eval least bound rare
  classical
  have same : f = NestedCover.graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change f x = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
    rw [spec]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  rw [same] at eval least ⊢
  have minC : IsMinimalCircuit n C := ⟨fan,fun D fd ed =>
    least _ ⟨D,fd,le_rfl,congrFun (ed.trans eval)⟩⟩
  obtain ⟨D,minD,evalD,sparseD⟩ := strip n G A C deg girth iso edge minC eval ⟨bound,rare⟩
  apply attach n G A C.size D.size iso edge ⟨C,fan,le_rfl,congrFun eval⟩
  · rintro b ⟨Q,fanQ,sQ,funQ⟩
    exact (minD.2 Q fanQ ((funext funQ).trans evalD.symm)).trans sQ
  · exact rescue n G A D deg girth iso edge minD evalD sparseD
