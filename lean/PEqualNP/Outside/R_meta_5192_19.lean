import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Thin the nonedge witnesses at each owning gate so that they can all be
-- activated together by one independent input.
theorem PEqualNP.Outside.R_meta_5192_19
    (pack : ∀ r : ℕ, ∃ M : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), M ≤ F.card →
      (∀ t ∈ F, ¬ G.Adj t.1 t.2) →
      let outside := fun t : Fin n × Fin n => ({t.1,t.2} : Finset (Fin n)) \ {u,v}
      (∀ t ∈ F, ∀ s ∈ F, t ≠ s → Disjoint (outside t) (outside s)) →
      ∃ T ⊆ F, T.card = r ∧ G.IsIndepSet (↑(T.biUnion (fun p => {p.1,p.2} : _ → Finset (Fin n))) : Set (Fin n)))
    (count : ∃ r c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset,
        (∀ (u v : Fin n), s(u,v) ∈ T → ∀ j : ℕ, Owns n C j u v →
          let outside := fun t : Fin n × Fin n => ({t.1,t.2} : Finset (Fin n)) \ {u,v}
          ∃ F : Finset (Fin n × Fin n), F.card = r ∧
            G.IsIndepSet (↑(F.biUnion (fun p => {p.1,p.2} : _ → Finset (Fin n))) : Set (Fin n)) ∧
            (∀ t ∈ F, gateVal n C j (pairInput t.1 t.2) = true) ∧
            (∀ t ∈ F, ∀ s ∈ F, t ≠ s → Disjoint (outside t) (outside s))) →
        T.card ≤ c*(C.size+1)) :
∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ))
:= by
  classical
  obtain ⟨r,c,counts⟩ := count
  obtain ⟨M,thin⟩ := pack r
  refine ⟨M,c,?_⟩
  intro n G inst degree girth C least correct T sub many
  refine counts n G degree girth C least correct T sub ?_
  intro u v member j owns
  obtain ⟨F,full,nonedges,separated⟩ := many _ member u v rfl ⟨j,owns.1⟩ owns
  obtain ⟨P,part,card,independent⟩ := thin n G girth u v F (by omega) (fun t ht => (nonedges t ht).2) separated
  exact ⟨P,card,independent,fun t ht => (nonedges t (part ht)).1,
    fun a ha b hb ne => separated a (part ha) b (part hb) ne⟩
