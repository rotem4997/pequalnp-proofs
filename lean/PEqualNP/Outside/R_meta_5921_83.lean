import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_5921_83
    (stars : let S := PEqualNP.HeptadCover.singerLines3
      let E := PEqualNP.HeptadCover.incidences S
      ∀ (C : Circuit) (U : Finset (Finset ℕ)), Monotone2 C → C.size ≤ 38 →
        let val := fun (i : ℕ) (x : List Bool) => (C.wires x).getD i false
        let fires := fun (t : Finset ℕ) (x : List Bool) => ∀ i ∈ t, val i x = true
        let wins := fun t => E.filter fun e => fires t (incidenceInput {e.1} {e.2})
        let left := E \ U.biUnion wins
        13 ≤ U.card + left.card →
        (∀ t ∈ U, t.card ≤ 2 ∧ t ⊆ Finset.range (26 + C.size)) →
        (∀ X Y, IsMaximalFalse S X Y → (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
          ∀ t ∈ U, ¬fires t (incidenceInput X Y)) →
        (∀ t ∈ U, 2 ≤ (wins t \ (U.erase t).biUnion wins).card) →
        (∀ t ∈ U, (∃ p, ∀ e ∈ wins t, e.1 = p) ∨ (∃ l, ∀ e ∈ wins t, e.2 = l)) → 65 ≤ C.size + 2 * (U.card + left.card))
    (mixed : let S := PEqualNP.HeptadCover.singerLines3
      let E := PEqualNP.HeptadCover.incidences S
      ∀ (C : Circuit) (U : Finset (Finset ℕ)), Monotone2 C → C.size ≤ 38 →
        let val := fun (i : ℕ) (x : List Bool) => (C.wires x).getD i false
        let fires := fun (t : Finset ℕ) (x : List Bool) => ∀ i ∈ t, val i x = true
        let wins := fun t => E.filter fun e => fires t (incidenceInput {e.1} {e.2})
        let left := E \ U.biUnion wins
        13 ≤ U.card + left.card →
        (∀ t ∈ U, t.card ≤ 2 ∧ t ⊆ Finset.range (26 + C.size)) →
        (∀ X Y, IsMaximalFalse S X Y → (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
          ∀ t ∈ U, ¬fires t (incidenceInput X Y)) →
        (∀ t ∈ U, 2 ≤ (wins t \ (U.erase t).biUnion wins).card) →
        (∃ t ∈ U, ∃ a ∈ wins t, ∃ b ∈ wins t, a.1 ∉ S b.2 ∧
          ∃ i ∈ t, val i (incidenceInput {a.1} {a.2}) = true ∧
            val i (incidenceInput {b.1} {b.2}) = true ∧
            val i (incidenceInput {a.1} (Finset.univ.filter fun l => a.1 ∉ S l)) = false) → 65 ≤ C.size + 2 * (U.card + left.card)) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x3.size ≤ (38 : ℕ) →       (13 : ℕ) ≤ x4.card →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           have x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) → (∀ (x11 x12 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x2 x11 x12 → ¬PEqualNP.GenericRejection.InNoLine x2 x11 ∨ ¬PEqualNP.GenericRejection.InNoPencil x2 x12 → ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput x11 x12)) → (∀ (x12 x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 → ∃ x15 ∈ x4, x9 x15 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) → (65 : ℕ) ≤ x3.size + (2 : ℕ) * x4.card := by
  classical
  intro D S C T mono small many ports fires own safe cover
  have same : S = singerLines3 := by
    funext l
    exact (by decide : ∀ j, S j = singerLines3 j) l
  let E := incidences S
  let win (t : Finset ℕ) := E.filter fun e => fires t (incidenceInput {e.1} {e.2})
  let left (V : Finset (Finset ℕ)) := E \ V.biUnion win
  let privateRows (V : Finset (Finset ℕ)) (t : Finset ℕ) := win t \ (V.erase t).biUnion win
  have finalCover : left T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨inE,miss⟩ := Finset.mem_sdiff.mp he
    obtain ⟨t,ht,hit⟩ := cover e.1 e.2 (Finset.mem_filter.mp inE).2
    exact miss (Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr ⟨inE,hit⟩⟩)
  have shrink : ∀ V : Finset (Finset ℕ), V ⊆ T → ∃ U ⊆ V,
      U.card + (left U).card = V.card + (left V).card ∧
      ∀ t ∈ U, 2 ≤ (privateRows U t).card := by
    intro V
    induction V using Finset.strongInductionOn
    rename_i V ih
    intro VT
    by_cases done : ∀ t ∈ V, 2 ≤ (privateRows V t).card
    · exact ⟨V,Finset.Subset.rfl,rfl,done⟩
    push Not at done
    obtain ⟨t,ht,low⟩ := done
    obtain ⟨p,l,inc,hit,unique⟩ := own t (VT ht)
    have flag : (p,l) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩
    have nonempty : (p,l) ∈ privateRows V t := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨flag,hit⟩,?_⟩
      intro mem
      obtain ⟨u,hu,hwin⟩ := Finset.mem_biUnion.mp mem
      obtain ⟨ne,hin⟩ := Finset.mem_erase.mp hu
      exact unique u (VT hin) ne (Finset.mem_filter.mp hwin).2
    have one : (privateRows V t).card = 1 := by
      have := Finset.card_pos.mpr ⟨_,nonempty⟩
      omega
    have removed : left (V.erase t) = left V ∪ privateRows V t := by
      ext e
      simp only [left,privateRows,Finset.mem_sdiff,Finset.mem_union,Finset.mem_biUnion,Finset.mem_erase]
      have sub (u) (h : e ∈ win u) : e ∈ E := (Finset.mem_filter.mp h).1
      constructor
      · rintro ⟨edge,absent⟩
        by_cases on : e ∈ win t
        · exact Or.inr ⟨on,absent⟩
        · refine Or.inl ⟨edge,?_⟩
          rintro ⟨u,hu,hit⟩
          by_cases eq : u = t
          · exact on (eq ▸ hit)
          · exact absent ⟨u,⟨eq,hu⟩,hit⟩
      · rintro (⟨edge,absent⟩ | ⟨on,absent⟩)
        · refine ⟨edge,?_⟩
          rintro ⟨u,hp,hit⟩
          exact absent ⟨u,hp.2,hit⟩
        · exact ⟨sub _ on,absent⟩
    have dis : Disjoint (left V) (privateRows V t) := by
      apply Finset.disjoint_left.mpr
      intro e hLeft hPrivate
      exact (Finset.mem_sdiff.mp hLeft).2
        (Finset.mem_biUnion.mpr ⟨t,ht,(Finset.mem_sdiff.mp hPrivate).1⟩)
    obtain ⟨U,hU,eq,big⟩ := ih (V.erase t) (Finset.erase_ssubset ht) (Finset.Subset.trans (Finset.erase_subset t V) VT)
    refine ⟨U,hU.trans (Finset.erase_subset t V),?_,big⟩
    rw [eq,removed,Finset.card_union_of_disjoint dis,one]
    have := Finset.card_erase_add_one ht
    omega
  obtain ⟨U,hU,count,big⟩ := shrink T Finset.Subset.rfl
  rw [finalCover,Finset.card_empty,Nat.add_zero] at count
  have Uports := fun t ht => ports t (hU ht)
  have Usafe := fun X Y hm hd t ht => safe X Y hm hd t (hU ht)
  have enough : 13 ≤ U.card + (left U).card := count ▸ many
  let star (t : Finset ℕ) := (∃ p, ∀ e ∈ win t, e.1 = p) ∨ (∃ l, ∀ e ∈ win t, e.2 = l)
  have premiseStars := stars C U mono small
  have premiseMixed := mixed C U mono small
  rw [←same] at premiseStars premiseMixed
  rw [←count]
  by_cases straight : ∀ t ∈ U, star t
  · exact premiseStars enough Uports Usafe big straight
  apply premiseMixed enough Uports Usafe big
  push Not at straight
  obtain ⟨t,ht,hstar⟩ := straight
  have cross : ∃ a ∈ win t, ∃ b ∈ win t, a.1 ∉ S b.2 := by
    by_contra! allInc
    apply hstar
    by_cases one : ∃ p, ∀ e ∈ win t, e.1 = p
    · exact Or.inl one
    right
    obtain ⟨e,he⟩ : (win t).Nonempty := by
      have n := big t ht
      have sub : privateRows U t ⊆ win t := Finset.sdiff_subset
      have pos := Finset.card_le_card sub
      apply Finset.card_pos.mp
      omega
    obtain ⟨f,hf,ne⟩ : ∃ f ∈ win t, f.1 ≠ e.1 := by
      by_contra! h
      exact one ⟨_,h⟩
    have lineUnique : ∀ p q l m : Fin 13, p ≠ q → p ∈ S l → q ∈ S l →
      p ∈ S m → q ∈ S m → l = m := by decide
    exact ⟨e.2,fun b hb => lineUnique _ _ _ _ ne (allInc f hf b hb)
      (allInc e he b hb) (allInc f hf e he) (allInc e he e he)⟩
  obtain ⟨a,ha,b,hb,missing⟩ := cross
  let off (p : Fin 13) := Finset.univ.filter fun l => p ∉ S l
  have geometry : ∀ p : Fin 13, IsMaximalFalse S {p} (off p) ∧ ¬InNoLine S {p} := by decide
  have rejects := Usafe {a.1} (off a.1) (geometry a.1).1 (Or.inl (geometry a.1).2) t ht
  change ¬∀ i ∈ t, (C.wires (incidenceInput {a.1} (off a.1))).getD i false = true at rejects
  push Not at rejects
  obtain ⟨i,hi,hzero⟩ := rejects
  exact ⟨t,ht,a,ha,b,hb,missing,i,hi,(Finset.mem_filter.mp ha).2 i hi,
    (Finset.mem_filter.mp hb).2 i hi,Bool.eq_false_iff.mpr hzero⟩
