import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5162_814
    (shortCertificate :
      let row (P L : Finset (Fin 13)) := List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ L))
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → andPairs 26 C = 1 →
      ∀ P L, C.eval (row P L) = true ↔ ∃ U V : Finset (Fin 13),
        U.card + V.card ≤ 3 ∧ U ⊆ P ∧ V ⊆ L ∧ C.eval (row U V) = true)
    (extension :
      let hit (P L : Finset (Fin 13)) := ∃ p ∈ P, ∃ l ∈ L, p ∈ singerLines3 l
      let exceptional (P L : Finset (Fin 13)) :=
        (L = ∅ ∧ P.card = 3 ∧ ∃ l : Fin 13, P ⊆ singerLines3 l) ∨
        (P = ∅ ∧ L.card = 3 ∧ ∃ p : Fin 13, ∀ l ∈ L, p ∈ singerLines3 l)
      ∀ P L, P.card + L.card ≤ 3 → ¬ hit P L → ¬ exceptional P L →
        ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧ P ⊆ Q ∧ L ⊆ missLines singerLines3 Q)
    (exactLowerBound :
      let row (P L : Finset (Fin 13)) := List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ L))
      let hit (P L : Finset (Fin 13)) := ∃ p ∈ P, ∃ l ∈ L, p ∈ singerLines3 l
      let exceptional (P L : Finset (Fin 13)) :=
        (L = ∅ ∧ P.card = 3 ∧ ∃ l : Fin 13, P ⊆ singerLines3 l) ∨
        (P = ∅ ∧ L.card = 3 ∧ ∃ p : Fin 13, ∀ l ∈ L, p ∈ singerLines3 l)
      ∀ W : Set (Finset (Fin 13) × Finset (Fin 13)),
      (∀ t ∈ W, exceptional t.1 t.2) →
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
      (∀ P L, C.eval (row P L) = true ↔ hit P L ∨ ∃ t ∈ W, t.1 ⊆ P ∧ t.2 ⊆ L) →
      (∀ D : Circuit, Monotone2 D → ReadsBack 26 D →
         (∀ P L, D.eval (row P L) = C.eval (row P L)) → C.size ≤ D.size) →
      andPairs 26 C = 1 → 64 ≤ C.size) :
have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  classical
  let row (P L : Finset (Fin 13)) := List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ L))
  let hit (P L : Finset (Fin 13)) := ∃ p ∈ P, ∃ l ∈ L, p ∈ singerLines3 l
  let exceptional (P L : Finset (Fin 13)) :=
        (L = ∅ ∧ P.card = 3 ∧ ∃ l : Fin 13, P ⊆ singerLines3 l) ∨
        (P = ∅ ∧ L.card = 3 ∧ ∃ p : Fin 13, ∀ l ∈ L, p ∈ singerLines3 l)
  change ∀ C : Circuit, Monotone2 C ∧ ReadsBack 26 C ∧
    (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
      (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
    (∀ Q, IsQuadrangle singerLines3 Q → C.eval (row Q (missLines singerLines3 Q)) = false) →
    _ → _ → _
  intro C correct least one
  obtain ⟨mono,back,yes,no⟩ := correct
  let W : Set (Finset (Fin 13) × Finset (Fin 13)) :=
    {t | exceptional t.1 t.2 ∧ C.eval (row t.1 t.2) = true}
  have short (P L) := shortCertificate C mono back one P L
  have ps (p l : Fin 13) : row {p} {l} =
      List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)) := by
    simp [row]
  apply exactLowerBound W (fun t ht => ht.1) C mono back
  · intro P L
    constructor
    · intro ons
      obtain ⟨U,V,small,uP,vL,fire⟩ := (short P L).mp ons
      by_cases inc : hit U V
      · obtain ⟨p,hp,l,hl,adj⟩ := inc
        exact Or.inl ⟨p,uP hp,l,vL hl,adj⟩
      by_cases ex : exceptional U V
      · exact Or.inr ⟨(U,V),⟨ex,fire⟩,uP,vL⟩
      obtain ⟨Q,hQ,uQ,vQ⟩ := extension U V small inc ex
      have qfire := (short Q (missLines singerLines3 Q)).mpr ⟨U,V,small,uQ,vQ,fire⟩
      rw [no Q hQ] at qfire
      exact (Bool.false_ne_true qfire).elim
    · rintro (⟨p,hp,l,hl,adj⟩ | ⟨t,ht,uP,vL⟩)
      · apply (short P L).mpr
        exact ⟨{p},{l},by simp,Finset.singleton_subset_iff.mpr hp,Finset.singleton_subset_iff.mpr hl,
          (congrArg C.eval (ps p l)).trans (yes p l adj)⟩
      · have facts : exceptional t.1 t.2 ∧ C.eval (row t.1 t.2) = true := ht
        have small : t.1.card + t.2.card ≤ 3 := by
          rcases facts.1 with ⟨e,h,_⟩ | ⟨e,h,_⟩ <;> simp [e,h]
        exact (short P L).mpr ⟨_,_,small,uP,vL,facts.2⟩
  · intro D dm db same
    apply least D
    refine ⟨dm,db,?_,?_⟩
    · intro p l h
      exact (congrArg D.eval (ps p l)).symm.trans ((same _ _).trans ((congrArg C.eval (ps p l)).trans (yes p l h)))
    · intro Q h
      exact (same Q _).trans (no Q h)
  · exact one
