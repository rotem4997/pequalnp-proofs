import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The minimum-circuit extraction follows R-meta-4111-219.
-- Pin both endpoints. A gate whose whole truth column becomes false or repeats an earlier
-- column can be omitted in one forward pass, including when the earlier gate is also omitted.
theorem PEqualNP.Outside.R_meta_4111_617
    (compress : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
    FanInTwo C → (let W := fun (i : ℕ) (x : Fin n → Bool) => PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update (Function.update x u false) v false)) i; ∀ j ∈ S, j < C.size ∧ ((∀ x, W (n+j) x = false) ∨ ∃ i < n+j, W (n+j) = W i)) →
    ∃ s, s + S.card ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) s)
    (structureStep : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    ¬ G.Colorable 2 →
    (∀ a, (∃ b, G.Adj a b) → (G.neighborSet a).ncard = 3) →
    (∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
    (∃ u v, G.Adj u v) → IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
    (∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeSet.ncard + T.card ≤ C.size+1) ∨
    ∃ u v, G.Adj u v ∧ ∃ S : Finset ℕ, 7 ≤ S.card ∧ (let W := fun (i : ℕ) (x : Fin n → Bool) => PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update (Function.update x u false) v false)) i; ∀ j ∈ S, j < C.size ∧ ((∀ x, W (n+j) x = false) ∨ ∃ i < n+j, W (n+j) = W i))) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  intro n G f hNonbipartite hCubic hGirth hEdge hFunction s hBudget hSize
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
  rcases structureStep n G D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics with
    ⟨T,covers,low⟩ | ⟨u,v,edge,S,seven,duplicates⟩
  · have := hBudget T covers
    omega
  · obtain ⟨r,count,cert⟩ := compress n D u v S hFanIn duplicates
    refine ⟨u,v,edge,r,by omega,?_⟩
    have eq : circuitFun n D = f := funext hEval
    simpa only [eq] using cert
