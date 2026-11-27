import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- On an internal edge of a minimum cover, deleting the endpoints removes five
-- edges and two cover vertices. The circuit question is preservation of the discount.
theorem PEqualNP.Outside.R_meta_4111_736
    (accounting : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    let covers := fun T : Finset (Fin n) => ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T
    ¬G.Colorable 2 → (∀ v, (∃ w, G.Adj v w) → (G.neighborSet v).ncard = 3) → ∃ T, covers T ∧
    (∀ S, covers S → T.card ≤ S.card) ∧ (∀ u ∈ T, ∃ w ∉ T, G.Adj u w) ∧ (∃ u ∈ T, ∃ v ∈ T, G.Adj u v) ∧
    ∀ u ∈ T, ∀ v ∈ T, G.Adj u v →
      (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard + ((T.erase u).erase v).card + 7 = G.edgeSet.ncard + T.card)
    (descend : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)),
    let covers := fun T : Finset (Fin n) => ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T
    covers T → (∀ S, covers S → T.card ≤ S.card) → (∀ u ∈ T, ∃ w ∉ T, G.Adj u w) → (∃ u ∈ T, ∃ v ∈ T, G.Adj u v) →
    (∀ v, (∃ w, G.Adj v w) → (G.neighborSet v).ncard = 3) → (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    ∀ (f : (Fin n → Bool) → Bool),
    (∀ x, f x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
    ∀ s d : ℕ, 0 < d → s+1+d = G.edgeSet.ncard + T.card → HasCircuitSize n f s →
    ∃ u ∈ T, ∃ v ∈ T, G.Adj u v ∧ ∃ r : ℕ,
      r+1+d ≤ (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard + ((T.erase u).erase v).card ∧
      HasCircuitSize n (fun x => f (Function.update (Function.update x u false) v false)) r) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  intro n G f nonbip cubic girth _ semantics s below computed
  obtain ⟨T,cov,least,privateNbr,edge,count⟩ := accounting n G nonbip cubic
  have low := below T cov
  let d := G.edgeSet.ncard + T.card - (s+1)
  have pos : 0 < d := by dsimp [d]; omega
  have eq : s+1+d = G.edgeSet.ncard+T.card := by dsimp [d]; omega
  obtain ⟨u,hu,v,hv,adj,r,saves,computes⟩ :=
    descend n G T cov least privateNbr edge cubic girth f semantics s d pos eq computed
  have cost := count u hu v hv adj
  exact ⟨u,v,adj,r,by omega,computes⟩
