import Mathlib.Order.Nat
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

-- Adapt the erasure certificate cut of R-meta-2270-26 to circuits below the cover bound.
theorem PEqualNP.Outside.R_meta_4111_219 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (D : PEqualNP.CircuitLowerBounds.Circuit),
    ¬ G.Colorable 2 →
    (∀ a : Fin n, (∃ b : Fin n, G.Adj a b) → (G.neighborSet a).ncard = 3) →
    (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) →
    (∃ u v : Fin n, G.Adj u v) →
    PEqualNP.MetaComplexity.IsMinimalCircuit n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
      D.size + 1 < G.edgeSet.ncard + T.card) →
    ∃ u v : Fin n, G.Adj u v ∧
      ∃ C : ℕ → PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo (C 0) ∧ (C 0).size ≤ D.size ∧
      PEqualNP.MetaComplexity.circuitFun n (C 0) = PEqualNP.MetaComplexity.circuitFun n D ∧
      ∀ i : ℕ, i < 7 → ∃ m p : ℕ,
      m < (C i).size ∧ (p < n + m ∨ n + (C i).size ≤ p) ∧
      C (i + 1) = PEqualNP.CircuitMoves.eraseGate n (C i) m p ∧
      ((∀ x : Fin n → Bool,
        let w := (C i).wires (List.ofFn (Function.update (Function.update x u false) v false))
        w.getD (n + m) false = w.getD p false) ∨
      ((C i).output ≠ n + m ∧ ∀ g ∈ (C i).gates.drop (m + 1), n + m ∉ g.inputs))) →
  (∀ (n k : ℕ) (u v : Fin n) (C : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo (C 0) →
    (∀ i : ℕ, i < k → ∃ m p : ℕ,
      m < (C i).size ∧ (p < n + m ∨ n + (C i).size ≤ p) ∧
      C (i + 1) = PEqualNP.CircuitMoves.eraseGate n (C i) m p ∧
      ((∀ x : Fin n → Bool,
        let w := (C i).wires (List.ofFn (Function.update (Function.update x u false) v false))
        w.getD (n + m) false = w.getD p false) ∨
      ((C i).output ≠ n + m ∧ ∀ g ∈ (C i).gates.drop (m + 1), n + m ∉ g.inputs))) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + k = (C 0).size ∧
      ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) =
          (C 0).eval (List.ofFn (Function.update (Function.update x u false) v false))) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  intro hStructure hReplay n G f hNonbipartite hCubic hGirth hEdge hFunction s hBudget hSize
  classical
  have hex : ∃ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hSize⟩
  obtain ⟨D, hFanIn, hBound, hEval⟩ := Nat.find_spec hex
  have hDs : D.size ≤ s := hBound.trans (Nat.find_min' hex hSize)
  have hLeast : PEqualNP.MetaComplexity.IsMinimalCircuit n D := by
    refine ⟨hFanIn, ?_⟩
    intro E hEFanIn hEquivalent
    have hESize : PEqualNP.MetaComplexity.HasCircuitSize n f E.size := by
      refine ⟨E, hEFanIn, le_rfl, ?_⟩
      intro x
      exact (congrFun hEquivalent x).trans (hEval x)
    exact hBound.trans (Nat.find_min' hex hESize)
  have hDSemantics (x : Fin n → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [hEval x]
    exact hFunction x
  have hDBudget (T : Finset (Fin n))
      (hCover : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) :
      D.size + 1 < G.edgeSet.ncard + T.card :=
    lt_of_le_of_lt (Nat.add_le_add_right hDs 1) (hBudget T hCover)
  obtain ⟨u, v, huv, S, hStartFanIn, hStartBound, hStartEval, hSteps⟩ :=
    hStructure n G D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics hDBudget
  obtain ⟨E, hEFanIn, hECount, hEEval⟩ := hReplay n 7 u v S hStartFanIn hSteps
  refine ⟨u, v, huv, E.size, hECount.le.trans (hStartBound.trans hDs), E, hEFanIn, le_rfl, ?_⟩
  intro x
  rw [hEEval x]
  exact (congrFun hStartEval _).trans (hEval _)
