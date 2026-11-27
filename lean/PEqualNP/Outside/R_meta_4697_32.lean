import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Isolated vertices can be dropped before normalizing the active cubic graph.
-- Each OR pool is then carried back along the embedding of that graph.
theorem PEqualNP.Outside.R_meta_4697_32
    (strip : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      ∃ (k : Nat) (H : SimpleGraph (Fin k)) (hH : DecidableRel H.Adj) (e : Fin k ↪ Fin n),
        (∀ v, (H.neighborSet v).ncard = 3) ∧
        (∀ v (p : H.Walk v v), p.IsCycle → 7 ≤ p.length) ∧
        (∃ u v, H.Adj u v) ∧
        (∀ x : Fin n → Bool, graphFun G ∅ x = @graphFun k H hH ∅ (x ∘ e)) ∧
        (∀ s, HasCircuitSize n (graphFun G ∅) s → HasCircuitSize k (@graphFun k H hH ∅) s))
    (pure : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∃ u v, G.Adj u v) →
      ∀ s, HasCircuitSize n (graphFun G ∅) s →
      ∃ (B : List (Finset (Fin n))) (m : Nat) (X Y : Fin m → Finset (Fin n)),
        (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (T : List (Finset (Fin n))),
          B = P ++ a :: T → ∃ b c, a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
        (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
        (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧ B.length + 2*m ≤ s+1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  classical
  intro n G inst A deg girth isolates edge s small
  obtain ⟨k,H,hH,e,allCubic,cycles,hasEdge,rename,conserve⟩ :=
    strip n G A deg girth isolates edge
  letI : DecidableRel H.Adj := hH
  obtain ⟨B,m,X,Y,trace,bounds,computes,cost⟩ :=
    pure k H allCubic cycles hasEdge s (conserve s small)
  let lift (b : Finset (Fin k)) := b.map e
  have lifts (T : List (Finset (Fin k))) (u : Finset (Fin k))
      (h : u.card ≤ 1 ∨ u ∈ T) : (lift u).card ≤ 1 ∨ lift u ∈ T.map lift := by
    rcases h with h | h
    · exact Or.inl (by simpa only [lift, Finset.card_map] using h)
    · exact Or.inr (List.mem_map_of_mem h)
  refine ⟨B.map lift,m,lift ∘ X,lift ∘ Y,?_,?_,?_,?_⟩
  · intro P a T split
    obtain ⟨P',suffix,hs,_,ht⟩ := List.map_eq_append_iff.mp split
    obtain ⟨u,T',ht',eqU,eqT⟩ := List.map_eq_cons_iff.mp ht
    have before : B = P' ++ u :: T' := hs.trans (congrArg (P' ++ ·) ht')
    obtain ⟨v,w,uv,afterV,afterW⟩ := trace P' u T' before
    refine ⟨lift v,lift w,?_,?_,?_⟩
    · rw [← eqU, uv]
      exact Finset.map_union (f := e) v w
    · simpa only [eqT] using lifts T' v afterV
    · simpa only [eqT] using lifts T' w afterW
  · intro j
    exact ⟨lifts B (X j) (bounds j).1, lifts B (Y j) (bounds j).2⟩
  · intro x
    have accepts (z : Finset (Fin k)) :
        (∃ v ∈ lift z, x v = true) ↔ ∃ v ∈ z, (x ∘ e) v = true := by
      constructor
      · rintro ⟨w, hw, on⟩
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
        exact ⟨v,hv,on⟩
      · rintro ⟨v,hv,on⟩
        exact ⟨e v,Finset.mem_map.mpr ⟨v,hv,rfl⟩,on⟩
    have edges : (∃ u v, H.Adj u v ∧ (x ∘ e) u = true ∧ (x ∘ e) v = true) ↔
        (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
      have same : graphFun H ∅ (x ∘ e) = true ↔ graphFun G ∅ x = true := by rw [rename x]
      change
        (decide (∃ a ∈ (∅ : Finset (Fin k)), (x ∘ e) a = true) ||
          decide (∃ u v, H.Adj u v ∧ (x ∘ e) u = true ∧ (x ∘ e) v = true)) = true ↔
        (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true at same
      simpa only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] using same
    change (∃ j, (∃ v ∈ lift (X j), x v = true) ∧ ∃ v ∈ lift (Y j), x v = true) ↔ _
    simp only [accepts]
    exact (computes (x ∘ e)).trans edges
  · simpa only [List.length_map] using cost
