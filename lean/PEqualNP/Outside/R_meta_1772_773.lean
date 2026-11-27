import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1772_773
    (existsLeast : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅)
    (pivotal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
          circuitFun n (eraseGate n C j (n + C.gates.length)) (pairInput u v) = false)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let cost := fun D : Circuit =>
        {j : ℕ | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧
          ∀ u v, G.Adj u v → ¬ Owns n D j u v}.ncard
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      (∀ i < j, (gateAt C i).op = GateOp.and → ∃ a b, G.Adj a b ∧ Owns n C i a b) →
      ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
      circuitFun n (eraseGate n C j (n + C.gates.length)) (pairInput u v) = false →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ cost D < cost C) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G _ noTriangle noFour
  classical
  let bad (D : Circuit) : Set ℕ :=
    {j : ℕ | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧
      ∀ u v, G.Adj u v → ¬ Owns n D j u v}
  let cost := fun D => (bad D).ncard
  let admissible (k : ℕ) :=
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧ cost D = k
  obtain ⟨C₀, minimum₀, correct₀⟩ := existsLeast n G
  have existsAdmissible : ∃ k, admissible k := ⟨cost C₀, C₀, minimum₀, correct₀, rfl⟩
  obtain ⟨C, minimum, correct, costEq⟩ := Nat.find_spec existsAdmissible
  refine ⟨C, minimum, correct, ?_⟩
  intro j hj hand
  by_contra noWitness
  have unowned (u v : Fin n) (adj : G.Adj u v) : ¬ Owns n C j u v :=
    fun owns => noWitness ⟨u, v, adj, owns⟩
  have existsBad : ∃ i : ℕ, i ∈ bad C := ⟨j, hj, hand, unowned⟩
  let first := Nat.find existsBad
  have firstBad : first ∈ bad C := Nat.find_spec existsBad
  obtain ⟨firstBound, firstAnd, firstUnowned⟩ := firstBad
  have earlier (i : ℕ) (hi : i < first) (iAnd : (gateAt C i).op = GateOp.and) :
      ∃ a b : Fin n, G.Adj a b ∧ Owns n C i a b := by
    by_contra noEdge
    have iBad : i ∈ bad C :=
      ⟨hi.trans firstBound, iAnd, fun a b adj owns => noEdge ⟨a, b, adj, owns⟩⟩
    exact (not_le_of_gt hi) (Nat.find_min' existsBad iBad)
  obtain ⟨u, v, adj, gateTrue, erasedFalse⟩ :=
    pivotal n G C minimum correct first firstBound firstAnd
  obtain ⟨D, monotoneD, correctD, sizeD, costDrop⟩ :=
    repair n G noTriangle noFour C minimum correct first firstBound firstAnd
      firstUnowned earlier u v adj gateTrue erasedFalse
  have minimumD : IsMinimalMonoCircuit n D :=
    ⟨monotoneD, fun E monotoneE correctE =>
      sizeD.trans (minimum.2 E monotoneE (correctE.trans (correctD.trans correct.symm)))⟩
  have leastCost := Nat.find_min' existsAdmissible
    (show admissible (cost D) from ⟨D, minimumD, correctD, rfl⟩)
  change cost D < cost C at costDrop
  omega
