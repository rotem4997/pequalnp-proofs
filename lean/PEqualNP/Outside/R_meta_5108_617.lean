import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The construction child is already checked as L_meta_2086.
-- The graph deletion argument adapts R_meta_2270_731; the other child retains
-- the sparse-alias hypothesis and only asks about circuits below every cover construction.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5108_617
  (star : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : ℕ), (x3.Nonempty ∨ ∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∈ x4 ∨ x9 ∈ x4) → x6 + (1 : ℕ) = x3.card + x2.edgeSet.ncard + x4.card → (∀ (x10 : Fin x1 → Bool), x5 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x6)
  (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
  ¬G.Colorable 2 → (∀ z ∉ A, (G.neighborSet z).ncard = 3) →
  (∀ z (w : G.Walk z z), w.IsCycle → 7 ≤ w.length) →
  (∀ u v, G.Adj u v → u ∉ A) → (∃ u v,G.Adj u v) →
  FanInTwo C → (∀ x, C.eval (List.ofFn x) = NestedCover.graphFun G A x) →
  (∀ T : Finset (Fin n), (∀ u v,G.Adj u v → u ∈ T ∨ v ∈ T) →
    C.size+1 < A.card+G.edgeSet.ncard+T.card) →
  (∀ u v,G.Adj u v → ∀ S : Finset ℕ,(∀ j ∈ S,j < C.size) →
      (∀ j ∈ S,∃ q : ℕ,(q < n+j ∨ n+C.size ≤ q) ∧ ∀ x : Fin n → Bool,
        let w := C.wires (List.ofFn (Function.update (Function.update x u false) v false))
        w.getD (n+j) false = w.getD q false) → S.card < 7) →
  ∃ u v,G.Adj u v ∧ ∃ t,t+7 ≤ C.size ∧ HasCircuitSize n
    (fun x => NestedCover.graphFun G A (Function.update (Function.update x u false) v false)) t) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →               ∀ (x11 : ℕ),                 PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 →                   (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo x13 →                         x13.size ≤ x11 →                           (∀ (x16 : Fin x1 → Bool), x13.eval (List.ofFn x16) = x4 x16) →                             ∀ (x17 x18 : Fin x1),                               x2.Adj x17 x18 →                                 ∀ (x20 : Finset ℕ),                                   (∀ x21 ∈ x20, x21 < x13.size) →                                     (∀ x22 ∈ x20,                                         ∃ (x24 : ℕ),                                           (x24 < x1 + x22 ∨ x1 + x13.size ≤ x24) ∧                                             ∀ (x25 : Fin x1 → Bool),                                               have x26 : List Bool := x13.wires (List.ofFn (Function.update (Function.update x25 x17 Bool.false) x18 Bool.false));                                               x26.getD (x1 + x22) Bool.false = x26.getD x24 Bool.false) →                                       x20.card < (7 : ℕ)) →                     ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ∉ x3 ∧ x15 ∉ x3 ∧ x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  classical
  intro n G A f hnon hdeg hgirth hiso hedge hsem s hs few
  by_cases large : ∃ T : Finset (Fin n),
      (∀ u v,G.Adj u v → u ∈ T ∨ v ∈ T) ∧ A.card+G.edgeSet.ncard+T.card ≤ s+1
  · obtain ⟨T,covers,fits⟩ := large
    have inside : ∃ u v, G.Adj u v ∧ u ∈ T ∧ v ∈ T := by
      by_contra! independent
      apply hnon
      refine ⟨SimpleGraph.Coloring.mk (fun w => if w ∈ T then (0 : Fin 2) else 1) ?_⟩
      intro u v huv
      rcases covers u v huv with hu | hv
      · have hv : v ∉ T := independent u v huv hu
        simp [hu, hv]
      · have hu : u ∉ T := fun hu => independent u v huv hu hv
        simp [hu, hv]
    obtain ⟨u, v, huv, huT, hvT⟩ := inside
    let J := G.deleteIncidenceSet u
    let K := J.deleteIncidenceSet v
    let T' := (T.erase u).erase v
    have keep {a b : Fin n} :
        K.Adj a b ↔ G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧ a ≠ v ∧ b ≠ v := by
      simp only [K, J, SimpleGraph.deleteIncidenceSet_adj]
      tauto
    have coverCut : ∀ a b, K.Adj a b → a ∈ T' ∨ b ∈ T' := by
      intro a b h
      obtain ⟨hab, hau, hbu, hav, hbv⟩ := keep.mp h
      rcases covers a b hab with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hav, Finset.mem_erase.mpr ⟨hau, ha⟩⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, Finset.mem_erase.mpr ⟨hbu, hb⟩⟩)
    have cardCover : T'.card + 2 = T.card := by
      have h1 := Finset.card_erase_add_one huT
      have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv.symm.ne, hvT⟩)
      dsimp only [T']
      omega
    have degree (a b : Fin n) (h : G.Adj a b) : G.degree a = 3 := by
      simpa only [SimpleGraph.ncard_neighborSet] using hdeg a (hiso a b h)
    have neigh (a : Fin n) (ha : a ≠ u) : J.neighborFinset a = (G.neighborFinset a).erase u := by
      ext b
      simp [J, SimpleGraph.deleteIncidenceSet_adj, ha, and_comm]
    have degreeV : J.degree v = 2 := by
      rw [← J.card_neighborFinset_eq_degree, neigh v huv.symm.ne]
      have h := Finset.card_erase_add_one (G.mem_neighborFinset v u |>.mpr huv.symm)
      rw [G.card_neighborFinset_eq_degree, degree v u huv.symm] at h
      omega
    have degree_le (L : SimpleGraph (Fin n)) [DecidableRel L.Adj] (w : Fin n) :
        L.degree w ≤ L.edgeFinset.card := by
      rw [← L.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (L.incidenceFinset_subset w)
    have card_eq (L : SimpleGraph (Fin n)) [DecidableRel L.Adj] :
        L.edgeFinset.card = L.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    have cardEdges : K.edgeSet.ncard + 5 = G.edgeSet.ncard := by
      have h1 : J.edgeFinset.card = G.edgeFinset.card - 3 := by
        dsimp only [J]
        rw [G.card_edgeFinset_deleteIncidenceSet, degree u v huv]
      have h2 : K.edgeFinset.card = J.edgeFinset.card - 2 := by
        dsimp only [K]
        rw [J.card_edgeFinset_deleteIncidenceSet, degreeV]
      have h3 := degree_le J v
      rw [degreeV, h1] at h3
      rw [← card_eq K, ← card_eq G]
      omega
    have hedgeK : ∃ a b, K.Adj a b := by
      have hns : ¬ G.neighborFinset u ⊆ ({v} : Finset (Fin n)) := by
        intro h
        have hh := Finset.card_le_card h
        rw [G.card_neighborFinset_eq_degree, degree u v huv, Finset.card_singleton] at hh
        omega
      obtain ⟨a, ha, hnv⟩ := Finset.not_subset.mp hns
      have hua : G.Adj u a := by simpa using ha
      have hns : ¬ G.neighborFinset a ⊆ ({u, v} : Finset (Fin n)) := by
        intro h
        have hh := Finset.card_le_card h
        rw [G.card_neighborFinset_eq_degree, degree a u hua.symm,
          Finset.card_insert_of_notMem (by simpa using huv.ne), Finset.card_singleton] at hh
        omega
      obtain ⟨b, hb, hbn⟩ := Finset.not_subset.mp hns
      have hab : G.Adj a b := by simpa using hb
      have hbne : b ≠ u ∧ b ≠ v := by simpa using hbn
      exact ⟨a, b, keep.mpr ⟨hab, hua.symm.ne, hbne.1, by simpa using hnv, hbne.2⟩⟩
    have positive : 0 < K.edgeSet.ncard := by
      rw [← card_eq K]
      apply Finset.card_pos.mpr
      obtain ⟨a, b, hab⟩ := hedgeK
      exact ⟨s(a,b), by simpa using hab⟩
    let b := A.card + K.edgeSet.ncard + T'.card - 1
    have eqBudget : b + 1 = A.card + K.edgeSet.ncard + T'.card := by dsimp [b]; omega
    refine ⟨u, v, hiso u v huv, hiso v u huv.symm, huv, b, by omega, ?_⟩
    apply star n K A T' _ b (Or.inr hedgeK) coverCut
    · simpa using eqBudget
  
    · intro x
      have hup (z : Fin n) :
          Function.update (Function.update x u false) v false z = true ↔
            z ≠ u ∧ z ≠ v ∧ x z = true := by
        by_cases huz : z = u
        · subst z; simp [huv.ne]
        · by_cases hvz : z = v
          · subst z; simp
          · simp [huz, hvz]
      have hA : (∃ z ∈ A, Function.update (Function.update x u false) v false z = true) ↔
          ∃ z ∈ A,x z=true := by
        constructor <;> rintro ⟨z,hz,hval⟩ <;> refine ⟨z,hz,?_⟩
        all_goals
          have hzu : z ≠ u := fun e => hiso u v huv (e ▸ hz)
          have hzv : z ≠ v := fun e => hiso v u huv.symm (e ▸ hz)
          simpa [Function.update_of_ne hzu, Function.update_of_ne hzv] using hval
      rw [hsem, hA]
      apply or_congr Iff.rfl
      simp only [hup]
      constructor
      · rintro ⟨a,b,hab,⟨hau,hav,ha⟩,hbu,hbv,hb⟩
        exact ⟨a,b,keep.mpr ⟨hab,hau,hbu,hav,hbv⟩,ha,hb⟩
      · rintro ⟨a,b,hab,ha,hb⟩
        obtain ⟨hab,hau,hbu,hav,hbv⟩ := keep.mp hab
        exact ⟨a,b,hab,⟨hau,hav,ha⟩,hbu,hbv,hb⟩
  · obtain ⟨C,hC,hsize,hcorrect⟩ := hs
    have heq (x : Fin n → Bool) : f x = NestedCover.graphFun G A x := by
      apply Bool.eq_iff_iff.mpr
      change f x = true ↔ (decide (∃ z ∈ A,x z=true) ||
        decide (∃ a b,G.Adj a b ∧ x a=true ∧ x b=true)) = true
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hsem x
    have below : ∀ T : Finset (Fin n), (∀ u v,G.Adj u v → u ∈ T ∨ v ∈ T) →
        C.size+1 < A.card+G.edgeSet.ncard+T.card := by
      intro T hT
      have hn : ¬ A.card+G.edgeSet.ncard+T.card ≤ s+1 := fun h => large ⟨T,hT,h⟩
      omega
    obtain ⟨u,v,huv,t,ht,hcut⟩ := core n G A C hnon hdeg hgirth hiso hedge hC
      (fun x => (hcorrect x).trans (heq x)) below (by
        intro u v huv S hS hAlias
        exact few C hC hsize hcorrect u v huv S hS hAlias)
    refine ⟨u,v,hiso u v huv,hiso v u huv.symm,huv,t,by omega,?_⟩
    have hf : f = NestedCover.graphFun G A := funext heq
    rw [hf]
    exact hcut
