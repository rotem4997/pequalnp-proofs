import Mathlib.Order.Nat
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2270_26 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (D : PEqualNP.CircuitLowerBounds.Circuit),
    ¬ G.Colorable 2 →
    (∀ a ∉ A, (G.neighborSet a).ncard = 3) →
    (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) →
    (∀ u v : Fin n, G.Adj u v → u ∉ A) →
    (∃ u v : Fin n, G.Adj u v) →
    PEqualNP.MetaComplexity.IsMinimalCircuit n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
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
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro hstruct hcollapse n G A f hnon hdeg hgirth hiso hedge hfun s hsize
  classical
  have hex : ∃ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hsize⟩
  obtain ⟨D, hfan, hbound, hval⟩ := Nat.find_spec hex
  have hDs : D.size ≤ s := hbound.trans (Nat.find_min' hex hsize)
  have hmin : PEqualNP.MetaComplexity.IsMinimalCircuit n D := by
    refine ⟨hfan, ?_⟩
    intro E hE heq
    have hEs : PEqualNP.MetaComplexity.HasCircuitSize n f E.size := by
      refine ⟨E, hE, le_rfl, ?_⟩
      intro x
      have hx := congrFun heq x
      change E.eval (List.ofFn x) = D.eval (List.ofFn x) at hx
      exact hx.trans (hval x)
    exact hbound.trans (Nat.find_min' hex hEs)
  have hsem (x : Fin n → Bool) : D.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [hval x]
    exact hfun x
  obtain ⟨u, v, huv, C, hzeroFan, hzeroSize, hzeroFun, hsteps⟩ :=
    hstruct n G A D hnon hdeg hgirth hiso hedge hmin hsem
  obtain ⟨E, hE, hcount, heval⟩ := hcollapse n 7 u v C hzeroFan hsteps
  refine ⟨u, v, hiso u v huv, hiso v u (G.adj_symm huv), huv, E.size, ?_, ?_⟩
  · exact hcount.le.trans (hzeroSize.trans hDs)
  · refine ⟨E, hE, le_rfl, ?_⟩
    intro x
    rw [heval x]
    have hx := congrFun hzeroFun (Function.update (Function.update x u false) v false)
    exact hx.trans (hval (Function.update (Function.update x u false) v false))
