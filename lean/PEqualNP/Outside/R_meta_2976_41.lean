import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_2976_41
    (dense : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      N < E.card → 2*N ≤ C.size+1 → (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → (∀ i, (i,p i) ∈ E) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) → E.card + N ≤ C.size + 1)
    (support : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ i, (i,p i) ∈ E) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) → 2*N ≤ C.size+1)
    (padding : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty → PEqualNP.TopForm.IsAO2 (n+m) C → (∀ x : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)) →
      let N := n+m
      let A := E.image (fun p => (Fin.castAdd m p.1, Fin.natAdd n p.2))
      ∀ B : Finset (Fin N × Fin N), ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N+N) D ∧ D.size ≤ C.size + 2*B.card ∧ (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) D x = decide (∃ a b, (a,b) ∈ (A ∪ B) ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)))
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : Circuit) (S : Bool → Finset ℕ),
        IsAO2 (n+m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := NestedCover.gateAt D
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n+m+i ∧ (g i).op = GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = GateOp.and →
          ∃ a b, (g i).inputs = [a,b] ∧ a ∈ S false ∧ b ∈ S true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  classical
  have perfect : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → (∀ i, (i,p i) ∈ E) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) → E.card + N ≤ C.size + 1 := by
    intro N E p C sq mat ao he
    have low := support N E p C mat ao he
    by_cases more : N < E.card
    · exact dense N E p C more low sq mat ao he
    · omega
  have charge : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
    classical

    have completion : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)),
        (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → M ⊆ E → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
        let A := E.image (fun p => (Fin.castAdd m p.1, Fin.natAdd n p.2))
        ∃ B : Finset (Fin (n+m) × Fin (n+m)), Disjoint A B ∧ B.card + M.card = n+m ∧
          (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ (A ∪ B) ∧ (a,d) ∈ (A ∪ B) ∧ (b,c) ∈ (A ∪ B) ∧ (b,d) ∈ (A ∪ B))) ∧ ∃ p : Equiv.Perm (Fin (n+m)), ∀ i, (i,p i) ∈ A ∪ B := by
      classical
      intro n m E M hcy sub hrow hcol
      let l : Fin n → Fin (n+m) := Fin.castAdd m
      let r : Fin m → Fin (n+m) := Fin.natAdd n
      have li : Function.Injective l := fun a b h => Fin.ext (congrArg (fun i : Fin (n+m) => i.val) h)
      have ri : Function.Injective r := by
        intro a b h
        have eq := congrArg Fin.val h
        change n + a.val = n + b.val at eq
        exact Fin.ext (by omega)
      have apart (i j) : l i ≠ r j := by
        intro h
        have eq := congrArg Fin.val h
        change i.val = n + j.val at eq
        omega
      have extend : ∀ T : Finset (Fin n × Fin m), T ⊆ M → ∃ p : Equiv.Perm (Fin (n+m)),
          ∀ i j, p (l i) = r j ↔ (i,j) ∈ T := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          intro _
          exact ⟨Equiv.refl _, fun i j => by simp [apart]⟩
        | @insert e T fresh ih =>
          intro hsub
          have inM := hsub (Finset.mem_insert_self e T)
          have old : T ⊆ M := fun _ h => hsub (Finset.mem_insert_of_mem h)
          obtain ⟨p, hp⟩ := ih old
          have freeCol (i) : p (l i) ≠ r e.2 := by
            intro he
            have hm := (hp i e.2).mp he
            have heq := hcol (i,e.2) (old hm) e inM rfl
            exact fresh (heq ▸ hm)
          refine ⟨p.trans (Equiv.swap (p (l e.1)) (r e.2)), ?_⟩
          intro i j
          change Equiv.swap (p (l e.1)) (r e.2) (p (l i)) = r j ↔ _
          by_cases h : i = e.1
          · subst i
            rw [Equiv.swap_apply_left]
            constructor
            · intro he
              have z := ri he
              subst j
              exact Finset.mem_insert_self _ _
            · intro hm
              rcases Finset.mem_insert.mp hm with he | he
              · exact congrArg r (congrArg Prod.snd he).symm
              · exact False.elim (fresh ((hrow (e.1,j) (old he) e inM rfl) ▸ he))
          · rw [Equiv.swap_apply_of_ne_of_ne (fun eq => h (li (p.injective eq))) (freeCol i), hp,Finset.mem_insert]
            exact ⟨Or.inr, fun he => he.resolve_left (fun eq => h (congrArg Prod.fst eq))⟩
      obtain ⟨p,hp⟩ := extend M (fun _ h => h)
      let f := fun t : Fin n × Fin m => (l t.1, r t.2)
      have fi : Function.Injective f := fun _ _ h => Prod.ext (li (congrArg Prod.fst h)) (ri (congrArg Prod.snd h))
      let A := E.image f
      let P := Finset.univ.image (fun i => (i,p i))
      have memP (i j : Fin (n+m)) : (i,j) ∈ P ↔ p i = j := by simp [P]
      have memA (a b) : (l a,r b) ∈ A ↔ (a,b) ∈ E := by
        change f (a,b) ∈ E.image f ↔ (a,b) ∈ E
        constructor
        · intro h
          obtain ⟨u,hu,he⟩ := Finset.mem_image.mp h
          exact fi he ▸ hu
        · exact fun h => Finset.mem_image.mpr ⟨_,h,rfl⟩
      have inter : P ∩ A = M.image f := by
        ext t
        constructor
        · intro h
          obtain ⟨hP,hA⟩ := Finset.mem_inter.mp h
          obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hA
          exact Finset.mem_image.mpr ⟨(a,b),(hp a b).mp ((memP _ _).mp hP),rfl⟩
        · intro h
          obtain ⟨⟨a,b⟩,hM,rfl⟩ := Finset.mem_image.mp h
          exact Finset.mem_inter.mpr ⟨(memP _ _).mpr ((hp a b).mpr hM),(memA a b).mpr (sub hM)⟩
      have cardP : P.card = n+m := by
        simpa [P] using Finset.card_image_of_injective (Finset.univ : Finset (Fin (n+m))) (fun _ _ h => congrArg Prod.fst h : Function.Injective (fun i : Fin (n+m) => (i,p i)))
      let B := P \ A
      have Bsub : B ⊆ P := Finset.sdiff_subset
      have oldBlock (a b) (h : (l a,r b) ∈ A ∪ B) : (a,b) ∈ E := by
        rcases Finset.mem_union.mp h with h | h
        · exact (memA a b).mp h
        · exact sub ((hp a b).mp ((memP _ _).mp (Bsub h)))
      have row (i j k) (hjk : j ≠ k) (h1 : (i,j) ∈ A ∪ B) (h2 : (i,k) ∈ A ∪ B) : ∃ a, l a = i := by
        by_contra! no
        have force (v) (h : (i,v) ∈ A ∪ B) : p i = v := by
          rcases Finset.mem_union.mp h with h | h
          · obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
            exact False.elim (no t.1 (congrArg Prod.fst ht))
          · exact (memP _ _).mp (Bsub h)
        exact hjk ((force _ h1).symm.trans (force _ h2))
      have col (j i k) (hik : i ≠ k) (h1 : (i,j) ∈ A ∪ B) (h2 : (k,j) ∈ A ∪ B) : ∃ b, r b = j := by
        by_contra! no
        have force (v) (h : (v,j) ∈ A ∪ B) : p v = j := by
          rcases Finset.mem_union.mp h with h | h
          · obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
            exact False.elim (no t.2 (congrArg Prod.snd ht))
          · exact (memP _ _).mp (Bsub h)
        exact hik (p.injective ((force _ h1).trans (force _ h2).symm))
      refine ⟨B, Finset.disjoint_sdiff, ?_, ?_, p, ?_⟩
      · have hc := Finset.card_sdiff_add_card_inter P A
        rwa [inter,Finset.card_image_of_injective _ fi,cardP] at hc
      · intro i k j v hik hjv h
        obtain ⟨ij,iv,kj,kv⟩ := h
        obtain ⟨a,rfl⟩ := row i j v hjv ij iv
        obtain ⟨b,rfl⟩ := row k j v hjv kj kv
        obtain ⟨c,rfl⟩ := col j (l a) (l b) hik ij kj
        obtain ⟨d,rfl⟩ := col v (l a) (l b) hik iv kv
        exact hcy a b c d (fun h => hik (congrArg l h)) (fun h => hjv (congrArg r h))
          ⟨oldBlock _ _ ij, oldBlock _ _ iv, oldBlock _ _ kj, oldBlock _ _ kv⟩
      · intro i
        by_cases h : (i,p i) ∈ A
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(memP _ _).mpr rfl,h⟩)
    intro n m E M C cycle ao runs sub left right
    by_cases e : E.Nonempty
    · let A := E.image (fun p => (Fin.castAdd m p.1, Fin.natAdd n p.2))
      obtain ⟨B,hd,hn,hcycle,p,hp⟩ := completion n m E M cycle sub left right
      obtain ⟨D,hD,hsize,hruns⟩ := padding n m E C e ao runs B
      have bound := perfect (n+m) (A ∪ B) p D hcycle hp hD hruns
      have ha : A.card = E.card := by
        apply Finset.card_image_of_injective
        intro a b eq
        apply Prod.ext
        · exact Fin.ext (congrArg (fun z : Fin (n+m) × Fin (n+m) => z.1.val) eq)
        · apply Fin.ext
          have h := congrArg (fun z : Fin (n+m) × Fin (n+m) => z.2.val) eq
          change n + a.2.val = n + b.2.val at h
          omega
      rw [Finset.card_union_of_disjoint hd,ha] at bound
      omega
    · have E0 := Finset.not_nonempty_iff_eq_empty.mp e
      subst E
      have M0 : M = ∅ := Finset.subset_empty.mp sub
      simp [M0]

  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  intro n m I _ C square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  obtain ⟨M,A,B,sub,points,lines,cover,dual⟩ := matchingCover n m E
  have budget := charge n m E M C (by simpa only [mem] using square) ao
    (by simpa only [mem] using correct) sub
    (fun _ he _ hf h => points he hf h) (fun _ he _ hf h => lines he hf h)
  obtain ⟨D,S,strict,size,eval,closed,ands⟩ := stars n m E A B cover
  refine ⟨D,S false,S true,strict,by simpa only [mem] using eval,by omega,?_,?_,?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_,side⟩ | gate
    · exact Or.inl (by simpa using side)
    · exact Or.inr gate
  · intro w hw
    rcases closed true w hw with ⟨bound,side⟩ | gate
    · exact Or.inl ⟨by simpa using side,bound⟩
    · exact Or.inr gate
  · intro i hi hand
    exact ands i hi hand
