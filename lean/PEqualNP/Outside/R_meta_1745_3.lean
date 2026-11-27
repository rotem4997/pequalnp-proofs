import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- The marked star-cover construction is the earlier checked L-meta-198.
-- The remaining child concerns only circuits strictly below its budget.
theorem PEqualNP.Outside.R_meta_1745_3 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n))
        (s : ℕ),
      (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
      s + 1 = A.card + G.edgeFinset.card + T.card →
      HasCircuitSize n (fun x : Fin n → Bool => decide
        ((∃ a ∈ A, x a = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, let rs := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
       rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) →
      (∀ T : Finset (Fin n), Disjoint A T →
        (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro stars residual n G A f C hdeg hcycle hend hedge hspec hfan hfun hmin hread
  let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have hgraph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [hspec]
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases benchmark : ∃ T : Finset (Fin n), Disjoint A T ∧
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      A.card + G.edgeFinset.card + T.card ≤ C.size + 1
  · obtain ⟨T, hdisjoint, hcover, hbudget⟩ := benchmark
    obtain ⟨i,j,hij⟩ := hedge
    have marked_partner : ∃ v ∈ T, ∃ u, G.Adj u v := by
      rcases hcover i j hij with h | h
      · exact ⟨i,h,j,hij.symm⟩
      · exact ⟨j,h,i,hij⟩
    obtain ⟨v,hv,u,huv⟩ := marked_partner
    have hvA : v ∉ A := fun h => (Finset.disjoint_left.mp hdisjoint) h hv
    let H := G.deleteIncidenceSet v
    let T' := T.erase v
    have keep : ∃ j, G.Adj u j ∧ j ≠ v := by
      by_contra! h
      have sub : G.neighborSet u ⊆ {v} := fun j hj =>
        Set.mem_singleton_iff.mpr (h j hj)
      have small := Set.ncard_le_ncard sub
      have deg := hdeg u (hend u v huv)
      rw [deg, Set.ncard_singleton] at small
      omega
    obtain ⟨j,huj,hjv⟩ := keep
    have kept : H.Adj u j := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huj,huv.ne,hjv⟩
    have no_empty : 0 < H.edgeFinset.card :=
      Finset.card_pos.mpr ⟨s(u,j), SimpleGraph.mem_edgeFinset.mpr kept⟩
    have cover' : ∀ a b : Fin n, H.Adj a b → a ∈ T' ∨ b ∈ T' := by
      intro a b hab
      obtain ⟨old, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
      exact (hcover a b old).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨hb,h⟩)
    have he : H.edgeFinset.card = G.edgeFinset.card - 3 := by
      have hd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (hdeg v hvA)
      exact (G.card_edgeFinset_deleteIncidenceSet v).trans (by rw [hd])
    have ht : T'.card = T.card - 1 := Finset.card_erase_of_mem hv
    let s := A.card + H.edgeFinset.card + T'.card - 1
    have hs : s + 1 = A.card + H.edgeFinset.card + T'.card := by
      dsimp [s]
      omega
    have size : s + 4 ≤ C.size := by
      have htp := Finset.card_pos.mpr ⟨v,hv⟩
      omega
    have cut := stars n H A T' s (Or.inr ⟨u,j,kept⟩) cover' hs
    have eval_cut :
        (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨
          ∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true)) =
        (fun x : Fin n → Bool => f (Function.update x v false)) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, hspec]
      constructor
      · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
        · have haz : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
        · obtain ⟨old,ha,hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
          exact Or.inr ⟨a,b,old,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
      · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
        · have haz : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
        · have ha : a ≠ v := by intro e; simp [e] at hxa
          have hb : b ≠ v := by intro e; simp [e] at hxb
          exact Or.inr ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab,ha,hb⟩,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
    exact ⟨v,hvA,s,size,eval_cut ▸ cut⟩
  · have hminimal : IsMinimalCircuit n C := by
      refine ⟨hfan, fun D hD he => hmin D.size ⟨D,hD,le_rfl,?_⟩⟩
      exact fun x => congrFun (he.trans hfun) x
    have only_small (T : Finset (Fin n)) (hdisjoint : Disjoint A T)
        (hcover : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
        C.size + 1 < A.card + G.edgeFinset.card + T.card :=
      lt_of_not_ge fun h => benchmark ⟨T,hdisjoint,hcover,h⟩
    simpa only [hfun] using
      residual n G A C hdeg hcycle hend hedge hminimal (hfun.trans hgraph) hread only_small
