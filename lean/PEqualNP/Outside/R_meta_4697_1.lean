import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.BicliqueBlockCost

-- Separate the numerical full-basis bound from a purely combinatorial star cover.
-- The explicit OR-pool construction follows R_meta_4697_448.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_4697_1
    (coverBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      ∀ s, HasCircuitSize n (graphFun G ∅) s →
        ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
          G.edgeSet.ncard + T.card ≤ s+1)
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        HasBlockCost G (G.edgeSet.ncard + T.card - 1)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  classical
  have compile : ∀ (n : Nat) (G : SimpleGraph (Fin n)) (s : Nat), HasBlockCost G s →
      ∃ (B : List (Finset (Fin n))) (m : Nat) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) a T, B = P ++ a :: T →
        ∃ (b c : Finset (Fin n)), a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
      (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
      (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧ B.length + 2*m ≤ s+1 := by
    classical
    intro n G s witness
    obtain ⟨F,hF,small⟩ := witness
    let avail (B : List (Finset (Fin n))) (a : Finset (Fin n)) := a.card ≤ 1 ∨ a ∈ B
    let good (B : List (Finset (Fin n))) := ∀ (P : List (Finset (Fin n))) a T, B = P ++ a :: T →
      ∃ b c : Finset (Fin n), a = b ∪ c ∧ avail T b ∧ avail T c
    have nilGood : good [] := by
      intro P a T eq
      simp at eq
    have consGood (a : Finset (Fin n)) B : good (a::B) ↔
        (∃ b c : Finset (Fin n), a = b ∪ c ∧ avail B b ∧ avail B c) ∧ good B := by
      constructor
      · intro h
        exact ⟨h [] a B rfl,fun P z T eq => h (a::P) z T (by simp [eq])⟩
      · rintro ⟨head,tail⟩ P z T eq
        cases P with
        | nil =>
          obtain ⟨rfl,rfl⟩ := List.cons.inj eq
          exact head
        | cons x P =>
          exact tail P z T (List.cons.inj eq).2
    have left (B D : List (Finset (Fin n))) {a} (h : avail B a) : avail (B++D) a :=
      h.imp_right (List.mem_append_left _)
    have right (B D : List (Finset (Fin n))) {a} (h : avail D a) : avail (B++D) a :=
      h.imp_right (List.mem_append_right _)
    have append (B D : List (Finset (Fin n))) (hb : good B) (hd : good D) : good (B++D) := by
      induction B with
      | nil => exact hd
      | cons a B ih =>
        obtain ⟨⟨u,v,eq,hu,hv⟩,tail⟩ := (consGood a B).mp hb
        exact (consGood a (B++D)).mpr ⟨⟨u,v,eq,left _ _ hu,left _ _ hv⟩,ih tail⟩
    have singletonPool (S : Finset (Fin n)) : ∃ B, good B ∧ avail B S ∧ B.length ≤ S.card-1 := by
      induction S using Finset.induction_on with
      | empty => exact ⟨[],nilGood,Or.inl (by simp),by simp⟩
      | @insert x S h ih =>
        by_cases zero : S = ∅
        · subst S
          exact ⟨[],nilGood,Or.inl (by simp),by simp⟩
        obtain ⟨B,bGood,ready,count⟩ := ih
        refine ⟨insert x S :: B,(consGood _ _).mpr ⟨⟨{x},S,by simp,Or.inl (by simp),ready⟩,bGood⟩,Or.inr (by simp),?_⟩
        have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr zero)
        simp only [List.length_cons,Finset.card_insert_of_notMem h]
        omega
    let extra (p : Block n) := p.1.card-1+(p.2.card-1)
    have pool (T : Finset (Block n)) :
        ∃ B, good B ∧ (∀ p ∈ T, avail B p.1 ∧ avail B p.2) ∧ B.length ≤ ∑ p ∈ T, extra p := by
      induction T using Finset.induction_on with
      | empty => exact ⟨[],nilGood,by simp,by simp⟩
      | @insert p T notin ih =>
        obtain ⟨B,bgood,ready,cost⟩ := ih
        obtain ⟨U,ug,ur,uc⟩ := singletonPool p.1
        obtain ⟨V,vg,vr,vc⟩ := singletonPool p.2
        refine ⟨(U++V)++B,append _ _ (append _ _ ug vg) bgood,?_,?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl|mem
          · exact ⟨left _ _ (left _ _ ur),left _ _ (right _ _ vr)⟩
          · exact ⟨right _ _ (ready z mem).1,right _ _ (ready z mem).2⟩
        · simp only [List.length_append,Finset.sum_insert notin]
          change U.length + V.length + B.length ≤ (p.1.card-1+(p.2.card-1)) + ∑ z ∈ T, extra z
          omega
    obtain ⟨B,bgood,ready,cost⟩ := pool F
    let ix : F ≃ Fin F.card := Fintype.equivFinOfCardEq (by simp)
    let pair (j : Fin F.card) : Block n := (ix.symm j).val
    refine ⟨B,F.card,fun i => (pair i).1,fun i => (pair i).2,bgood,fun i => ready _ (ix.symm i).property,?_,?_⟩
    · intro x
      constructor
      · rintro ⟨i,⟨u,hu,onU⟩,v,hv,onV⟩
        exact ⟨u,v,(hF.1 _ (ix.symm i).property).2.2.2 _ hu _ hv,onU,onV⟩
      · rintro ⟨u,v,edge,onU,onV⟩
        obtain ⟨p,hp,hits⟩ := hF.2 u v edge
        refine ⟨ix ⟨p,hp⟩,?_⟩
        have eq : pair (ix ⟨p,hp⟩) = p := by simp [pair]
        dsimp only
        rw [eq]
        rcases hits with ⟨xp,yp⟩|⟨yp,xp⟩
        · exact ⟨⟨u,xp,onU⟩,v,yp,onV⟩
        · exact ⟨⟨v,yp,onV⟩,u,xp,onU⟩
    · have compare : (∑ p ∈ F, extra p) + 2*F.card = (∑ p ∈ F, blockCost p) + F.card := by
        calc
          _ = ∑ p ∈ F, (extra p+2) := by simp [Finset.sum_add_distrib,Nat.mul_comm]
          _ = ∑ p ∈ F, (blockCost p+1) := by
            apply Finset.sum_congr rfl
            intro p hp
            have x := (hF.1 _ hp).2.1.card_pos
            have y := (hF.1 _ hp).2.2.1.card_pos
            unfold extra blockCost
            omega
          _ = _ := by simp [Finset.sum_add_distrib]
      unfold familyCost at small
      omega
  intro n G inst A degree girth isolated edge s small
  obtain ⟨T,cover,bound⟩ := coverBound n G A degree girth isolated edge s small
  obtain ⟨F,blocks,cost⟩ := stars n G T cover
  apply compile n G s
  exact ⟨F,blocks,by omega⟩
