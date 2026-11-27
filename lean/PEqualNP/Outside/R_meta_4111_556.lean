import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4111_556
    (monotoneCase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (C : Circuit),
      (∀ v, (∃ w, G.Adj v w) → (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ x, circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      IsMinCover G T →
      (∀ u ∈ T, ∃ w ∉ T, G.Adj u w) →
      (∃ u ∈ T, ∃ v ∈ T, G.Adj u v) →
      (∀ u ∈ T, ∀ v ∈ T, G.Adj u v →
        (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard +
          ((T.erase u).erase v).card + 7 = G.edgeSet.ncard + T.card) →
      IsMinimalCircuit n C → C.size + 1 < G.edgeSet.ncard + T.card →
      AndOrOnly C →
      ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t)
    (hasNotCase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (C : Circuit),
      (∀ v, (∃ w, G.Adj v w) → (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ x, circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      IsMinCover G T →
      (∀ u ∈ T, ∃ w ∉ T, G.Adj u w) →
      (∃ u ∈ T, ∃ v ∈ T, G.Adj u v) →
      (∀ u ∈ T, ∀ v ∈ T, G.Adj u v →
        (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard +
          ((T.erase u).erase v).card + 7 = G.edgeSet.ncard + T.card) →
      IsMinimalCircuit n C → C.size + 1 < G.edgeSet.ncard + T.card →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  intro n G f nonbip cubic girth _ edgeFunction s below computed
  classical
  obtain ⟨D, dFan, dBound, dEval⟩ := computed
  have circuitSizes : ∃ k : ℕ, ∃ C : Circuit,
      FanInTwo C ∧ circuitFun n C = f ∧ C.size = k :=
    ⟨D.size, D, dFan, funext dEval, rfl⟩
  obtain ⟨C, cFan, cFun, cSize⟩ := Nat.find_spec circuitSizes
  have cMinimal : IsMinimalCircuit n C := by
    refine ⟨cFan, fun E eFan eFun => ?_⟩
    rw [cSize]
    exact Nat.find_min' circuitSizes ⟨E, eFan, eFun.trans cFun, rfl⟩
  have cBound : C.size ≤ s :=
    (cMinimal.2 D dFan ((funext dEval).trans cFun.symm)).trans dBound
  have cSemantics : ∀ x, circuitFun n C x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [cFun]
    exact edgeFunction
  have coverSizes : ∃ k : ℕ, ∃ T : Finset (Fin n),
      G.IsVertexCover (T : Set (Fin n)) ∧ T.card = k :=
    ⟨Finset.univ.card, Finset.univ, fun {_ _} _ => Or.inl (Finset.mem_univ _), rfl⟩
  obtain ⟨T, cover, tSize⟩ := Nat.find_spec coverSizes
  have minimum : IsMinCover G T := by
    refine ⟨cover, fun S sCover => ?_⟩
    rw [tSize]
    exact Nat.find_min' coverSizes ⟨S, sCover, rfl⟩
  have privateNeighbor : ∀ u ∈ T, ∃ w ∉ T, G.Adj u w := by
    intro u hu
    by_contra noOutside
    have staysInside (w : Fin n) (h : G.Adj u w) : w ∈ T := by
      by_contra hw
      exact noOutside ⟨w, hw, h⟩
    have eraseCover : G.IsVertexCover ((T.erase u : Finset (Fin n)) : Set (Fin n)) := by
      intro a b hab
      rcases cover hab with ha | hb
      · by_cases h : a = u
        · subst a
          exact Or.inr (Finset.mem_erase.mpr ⟨hab.ne.symm, staysInside b hab⟩)
        · exact Or.inl (Finset.mem_erase.mpr ⟨h, ha⟩)
      · by_cases h : b = u
        · subst b
          exact Or.inl (Finset.mem_erase.mpr ⟨hab.ne, staysInside a hab.symm⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨h, hb⟩)
    exact (Finset.card_erase_lt_of_mem hu).not_ge (minimum.2 _ eraseCover)
  have internalEdge : ∃ u ∈ T, ∃ v ∈ T, G.Adj u v := by
    by_contra noInternal
    apply nonbip
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ T then 0 else 1) ?_⟩
    intro u v huv
    rcases cover huv with hu | hv
    · have hv : v ∉ T := fun h => noInternal ⟨u, hu, v, h, huv⟩
      simp only [Finset.mem_coe] at hu
      simp [hu, hv]
    · have hu : u ∉ T := fun h => noInternal ⟨u, h, v, hv, huv⟩
      simp only [Finset.mem_coe] at hv
      simp [hu, hv]
  have deletionCount : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v →
      (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard +
        ((T.erase u).erase v).card + 7 = G.edgeSet.ncard + T.card := by
    intro u hu v hv huv
    have incidenceCount (a b : Fin n) (hab : G.Adj a b) : (G.incidenceSet a).ncard = 3 := by
      rw [G.ncard_incidenceSet, ← G.ncard_neighborSet]
      exact cubic a ⟨b, hab⟩
    have unionCount := Set.ncard_union_add_ncard_inter (G.incidenceSet u) (G.incidenceSet v)
    rw [G.incidenceSet_inter_incidenceSet_of_adj huv, Set.ncard_singleton,
      incidenceCount u v huv, incidenceCount v u huv.symm] at unionCount
    have subset : G.incidenceSet u ∪ G.incidenceSet v ⊆ G.edgeSet :=
      Set.union_subset (G.incidenceSet_subset u) (G.incidenceSet_subset v)
    have edgeCount := Set.ncard_sdiff_add_ncard_of_subset subset
    have hEraseU := Finset.card_erase_add_one hu
    have hv' : v ∈ T.erase u := Finset.mem_erase.mpr ⟨huv.ne.symm, hv⟩
    have hEraseV := Finset.card_erase_add_one hv'
    omega
  have cBelow : C.size + 1 < G.edgeSet.ncard + T.card :=
    lt_of_le_of_lt (Nat.add_le_add_right cBound 1) (below T (fun _ _ h => cover h))
  have descend : ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t := by
    by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
    · exact hasNotCase n G T C cubic girth cSemantics minimum privateNeighbor internalEdge
        deletionCount cMinimal cBelow hasNot
    · have monotone : AndOrOnly C := by
        intro g hg
        have allowed := (cFan g hg).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
        rcases allowed with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hasNot ⟨g, hg, h⟩).elim
      exact monotoneCase n G T C cubic girth cSemantics minimum privateNeighbor internalEdge
        deletionCount cMinimal cBelow monotone
  obtain ⟨u, v, huv, t, saves, restricted⟩ := descend
  rw [cFun] at restricted
  exact ⟨u, v, huv, t, saves.trans cBound, restricted⟩
