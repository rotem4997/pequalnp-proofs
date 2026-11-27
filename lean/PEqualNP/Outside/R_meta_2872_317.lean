import Mathlib
import PEqualNP.Defs

-- Complete the matching by adding a private neighbor to each uncovered vertex.
-- For each original matched edge, the two unused copies form an isolated edge.
-- Each new edge needs one binary AND and one binary OR in the lifted circuit.
-- The extra gates cancel exactly in the perfect-matching lower bound.
theorem PEqualNP.Outside.R_meta_2872_317
    (perfect : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)) (p : Equiv.Perm (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → (∀ i, (i,p i) ∈ E) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true)) → E.card + N ≤ C.size + 1)
    (padding : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty → PEqualNP.TopForm.IsAO2 (n+m) C → (∀ x : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C x = decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)) →
      let N := n+m
      let A := E.image (fun p => (Fin.castAdd m p.1, Fin.natAdd n p.2))
      ∀ B : Finset (Fin N × Fin N), ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N+N) D ∧ D.size ≤ C.size + 2*B.card ∧ (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) D x = decide (∃ a b, (a,b) ∈ (A ∪ B) ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true))) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
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
