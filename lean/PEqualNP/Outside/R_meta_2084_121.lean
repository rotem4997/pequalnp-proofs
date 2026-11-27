import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2084_121 :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∉ x4) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → ∀ (x7 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x7 → ∃ (x9 : ℕ), x9 + x4.card ≤ x7 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
    (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (T : List (Finset (Fin n))), B = P ++ a :: T → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) →
    (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) →
    (∀ z : Fin n → Bool, (∃ i, (∃ u ∈ X i, z u = true) ∧ ∃ v ∈ Y i, z v = true) ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) →
      ∃ V : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧ G.edgeSet.ncard + V.card ≤ B.length + 2*m) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ A : Finset (Fin n),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    ∀ s, HasCircuitSize n (graphFun G ∅) s →
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
    (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (T : List (Finset (Fin n))), B = P ++ a :: T → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
    (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
    (∀ z : Fin n → Bool, (∃ i, (∃ u ∈ X i, z u = true) ∧ ∃ v ∈ Y i, z v = true) ↔ ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧ B.length + 2*m ≤ s+1) →
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  intro strip price normalize n k G A f cubic girth iso edge demand spec s small
  classical
  have eq : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    unfold graphFun
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  subst f
  obtain ⟨t, ht, pure⟩ := strip n G A iso edge s small
  obtain ⟨B,m,X,Y,built,ready,truth,cheap⟩ := normalize n G A cubic girth iso edge t pure
  obtain ⟨V,covered,paid⟩ := price n G (fun v p h => (by have := girth v p h; omega)) B m X Y built ready truth
  have hk := demand V covered
  omega
