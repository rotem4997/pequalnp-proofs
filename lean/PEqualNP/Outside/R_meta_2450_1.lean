import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2450_1
    (pivotal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧
          PEqualNP.EdgeOwnership.gateVal n C j
            (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
          PEqualNP.MetaComplexity.circuitFun n
            (PEqualNP.CircuitMoves.eraseGate n C j (n + C.gates.length))
            (PEqualNP.EdgeOwnership.pairInput u v) = false)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
        a = c ∨ b = d) →
      let bad := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
        {j : ℕ | j < D.gates.length ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ u v : Fin n, G.Adj u v →
            ¬PEqualNP.EdgeOwnership.Owns n D j u v}.ncard
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
        PEqualNP.MetaComplexity.circuitFun n C =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        PEqualNP.EdgeOwnership.HasStarProfile n G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ u v : Fin n, G.Adj u v → ¬PEqualNP.EdgeOwnership.Owns n C j u v) →
          (∀ i < j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
            ∃ a b : Fin n, G.Adj a b ∧ PEqualNP.EdgeOwnership.Owns n C i a b) →
          ∀ u v : Fin n, G.Adj u v →
            PEqualNP.EdgeOwnership.gateVal n C j
              (PEqualNP.EdgeOwnership.pairInput u v) = true →
            PEqualNP.MetaComplexity.circuitFun n
              (PEqualNP.CircuitMoves.eraseGate n C j (n + C.gates.length))
              (PEqualNP.EdgeOwnership.pairInput u v) = false →
            ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
              PEqualNP.MetaComplexity.Monotone2 D ∧
              PEqualNP.MetaComplexity.circuitFun n D =
                PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
              D.size ≤ C.size ∧ PEqualNP.EdgeOwnership.HasStarProfile n G D ∧
              bad D < bad C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 →
        x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 =
        PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 =
          PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 =
          PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧
            PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by
  open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
    PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
  (intro n G _ C noTriangle noFour monotone correct least star
   classical
   let bad := fun D : Circuit =>
     {j : ℕ | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧
       ∀ u v : Fin n, G.Adj u v → ¬Owns n D j u v}.ncard
   let admissible := fun k : ℕ =>
     ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
       D.size ≤ C.size ∧ HasStarProfile n G D ∧ bad D = k
   have existsAdmissible : ∃ k, admissible k :=
     ⟨bad C, C, monotone, correct, le_rfl, star, rfl⟩
   obtain ⟨D, monotoneD, correctD, sizeD, starD, costD⟩ :=
     Nat.find_spec existsAdmissible
   have minimumD : IsMinimalMonoCircuit n D := by
     refine ⟨monotoneD, ?_⟩
     intro E monotoneE sameE
     exact sizeD.trans (least E monotoneE (sameE.trans correctD))
   refine ⟨D, monotoneD, correctD, sizeD, starD, ?_⟩
   intro j boundj andj
   by_contra noOwner
   have unowned : ∀ u v : Fin n, G.Adj u v → ¬Owns n D j u v := by
     intro u v adjacent owns
     exact noOwner ⟨u, v, adjacent, owns⟩
   have existsBad : ∃ i : ℕ,
       i < D.gates.length ∧ (gateAt D i).op = GateOp.and ∧
         ∀ u v : Fin n, G.Adj u v → ¬Owns n D i u v :=
     ⟨j, boundj, andj, unowned⟩
   let first := Nat.find existsBad
   have firstBad := Nat.find_spec existsBad
   obtain ⟨firstBound, firstAnd, firstUnowned⟩ := firstBad
   have earlier (i : ℕ) (hi : i < first)
       (iAnd : (gateAt D i).op = GateOp.and) :
       ∃ a b : Fin n, G.Adj a b ∧ Owns n D i a b := by
     by_contra noEdge
     push Not at noEdge
     have iBad : i < D.gates.length ∧ (gateAt D i).op = GateOp.and ∧
         ∀ u v : Fin n, G.Adj u v → ¬Owns n D i u v :=
       ⟨hi.trans firstBound, iAnd, noEdge⟩
     exact (not_le_of_gt hi) (Nat.find_min' existsBad iBad)
   obtain ⟨u, v, adjacent, gateTrue, erasedFalse⟩ :=
     pivotal n G D minimumD correctD first firstBound firstAnd
   obtain ⟨E, monotoneE, correctE, sizeE, starE, costDrop⟩ :=
     repair n G noTriangle noFour D minimumD correctD starD first firstBound
       firstAnd firstUnowned earlier u v adjacent gateTrue erasedFalse
   have admissibleE : admissible (bad E) :=
     ⟨E, monotoneE, correctE, sizeE.trans sizeD, starE, rfl⟩
   have leastCost := Nat.find_min' existsAdmissible admissibleE
   change bad E < bad D at costDrop
   rw [costD] at costDrop
   omega)
