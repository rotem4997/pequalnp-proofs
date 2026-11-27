import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open scoped Classical

theorem PEqualNP.Outside.R_meta_8181_317
    (compileStars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (T : Finset (Fin (n+m))),
      (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size ≤ E.card + T.card - 1 ∧
        ∀ z, circuitFun (n+m) D z = decide
          (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true))
    (core : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit) (G : SimpleGraph (Fin (n+m))),
      let fit := fun (F : Finset (Fin n × Fin m)) (D : Circuit) =>
        IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide
          (∃ a b, (a,b) ∈ F ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
      let high := ∃ v : Fin (n+m), let d := (G.neighborSet v).ncard
        let R := readers 0 C v.val
        2 ≤ d ∧ (d < R.card ∨ d = R.card ∧
          ∃ r ∈ R, (gateAt C r).op = .and ∧ ¬ readers (n+m) C r ⊆ R)
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
      ¬G.IsAcyclic → fit E C →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 ∨ e.2 = f.2 → e = f) →
      M ⊆ E →
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)) →
      (∀ e ∈ E, ((∀ f ∈ E, f.1 = e.1 → f = e) ∨ ∀ f ∈ E, f.2 = e.2 → f = e) →
        (E.erase e).Nonempty → e ∈ M) →
      ¬high →
      (∀ e ∈ E \ M, ∃ f ∈ M, f.1 = e.1 ∨ f.2 = e.2) →
      (∀ e ∈ E \ M, ∀ T : Finset (Fin (n+m)),
        (∀ f ∈ E.erase e, Fin.castAdd m f.1 ∈ T ∨ Fin.natAdd n f.2 ∈ T) →
        C.size ≤ (E.erase e).card + T.card - 1) →
      ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ fit (E.erase e) D) : (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19) := by

  classical
  intro n m E M C G fit high adj cyc hC ml mr mE no4 leaf low
  let eligible := E.powerset.filter (fun N =>
    M ⊆ N ∧ Set.InjOn Prod.fst (N : Set (Fin n × Fin m)) ∧ Set.InjOn Prod.snd (N : Set (Fin n × Fin m)))
  have init : M ∈ eligible := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr mE,
    Finset.Subset.rfl,fun _ ha _ hb eq => ml _ ha _ hb eq,fun _ ha _ hb eq => mr _ ha _ hb eq⟩
  obtain ⟨N,mem,largest⟩ := Finset.exists_max_image eligible Finset.card ⟨M,init⟩
  obtain ⟨ne',mn,rows,cols⟩ := Finset.mem_filter.mp mem
  have ne := Finset.mem_powerset.mp ne'
  have sat : ∀ e ∈ E \ N, ∃ f ∈ N, f.1 = e.1 ∨ f.2 = e.2 := by
    intro e he
    apply Classical.byContradiction
    intro apart
    obtain ⟨ee,en⟩ := Finset.mem_sdiff.mp he
    have insertInj {α : Type} (k : Fin n × Fin m → α) (inj : Set.InjOn k (N : Set (Fin n × Fin m)))
        (sep : ∀ f ∈ N, k f ≠ k e) : Set.InjOn k (↑(insert e N) : Set _) := by
      intro f hf g hg eq
      obtain ef | fn := Finset.mem_insert.mp hf
      · obtain eg | gn := Finset.mem_insert.mp hg
        · exact ef.trans eg.symm
        · exact False.elim (sep _ gn (eq.symm.trans (congrArg k ef)))
      · obtain eg | gn := Finset.mem_insert.mp hg
        · exact False.elim (sep _ fn (eq.trans (congrArg k eg)))
        · exact inj fn gn eq
    have mem' : insert e N ∈ eligible := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset ee ne), mn.trans (Finset.subset_insert _ _),
        insertInj Prod.fst rows (fun f hf eq => apart ⟨f,hf,Or.inl eq⟩),
        insertInj Prod.snd cols (fun f hf eq => apart ⟨f,hf,Or.inr eq⟩)⟩
    have card := largest _ mem'
    rw [Finset.card_insert_of_notMem en] at card
    omega
  let cheap := ∃ e ∈ E \ N, ∃ T : Finset (Fin (n+m)),
    (∀ f ∈ E.erase e, Fin.castAdd m f.1 ∈ T ∨ Fin.natAdd n f.2 ∈ T) ∧
    (E.erase e).card + T.card - 1 < C.size
  by_cases h : cheap
  · obtain ⟨e,he,T,cov,cost⟩ := h
    obtain ⟨D,ao,size,ev⟩ := compileStars n m (E.erase e) T cov
    obtain ⟨ee,en⟩ := Finset.mem_sdiff.mp he
    exact ⟨e,ee,fun hm => en (mn hm),D,size.trans_lt cost,ao,ev⟩
  · have expensive : ∀ e ∈ E \ N, ∀ T : Finset (Fin (n+m)),
        (∀ f ∈ E.erase e, Fin.castAdd m f.1 ∈ T ∨ Fin.natAdd n f.2 ∈ T) →
        C.size ≤ (E.erase e).card + T.card - 1 :=
      fun e he T cov => Nat.le_of_not_gt (fun cost => h ⟨e,he,T,cov,cost⟩)
    obtain ⟨e,ee,en,D,ds,df⟩ := core n m E N C G adj cyc hC (fun _ ha _ hb eq => eq.elim (rows ha hb) (cols ha hb)) ne no4
      (fun e ee l pos => mn (leaf e ee l pos)) low sat expensive
    exact ⟨e,ee,fun hm => en (mn hm),D,ds,df⟩
