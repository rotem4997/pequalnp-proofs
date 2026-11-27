import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6228_aux

private def inc (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

private instance (p l : Fin 13) : Decidable (inc p l) := by
  unfold inc; infer_instance

private structure Coll where
  sp : Equiv.Perm (Fin 13)
  sl : Equiv.Perm (Fin 13)
  pres : ∀ p l : Fin 13, inc (sp p) (sl l) ↔ inc p l

private lemma Coll.pres_symm (c : Coll) (p l : Fin 13) :
    inc (c.sp.symm p) (c.sl.symm l) ↔ inc p l := by
  have h := c.pres (c.sp.symm p) (c.sl.symm l)
  simpa using h.symm

private def Coll.id : Coll where
  sp := Equiv.refl _
  sl := Equiv.refl _
  pres _ _ := Iff.rfl

private def Coll.comp (c2 c1 : Coll) : Coll where
  sp := c1.sp.trans c2.sp
  sl := c1.sl.trans c2.sl
  pres p l := (c2.pres (c1.sp p) (c1.sl l)).trans (c1.pres p l)

private lemma inc_add (a p l : Fin 13) : inc (p + a) (l + a) ↔ inc p l := by
  revert a p l; decide

private lemma inc_neg (p l : Fin 13) : inc p l ↔ inc (-l) (-p) := by
  revert p l; decide

private def Coll.shift (a : Fin 13) : Coll where
  sp := Equiv.addRight a
  sl := Equiv.addRight a
  pres p l := inc_add a p l

private def invFn (f : Fin 13 → Fin 13) (y : Fin 13) : Fin 13 :=
  ((List.finRange 13).find? fun x => f x == y).getD 0

private def collOfFn (fp fl : Fin 13 → Fin 13)
    (hpl : ∀ x : Fin 13, invFn fp (fp x) = x)
    (hpr : ∀ y : Fin 13, fp (invFn fp y) = y)
    (hll : ∀ x : Fin 13, invFn fl (fl x) = x)
    (hlr : ∀ y : Fin 13, fl (invFn fl y) = y)
    (hpres : ∀ p l : Fin 13, inc (fp p) (fl l) ↔ inc p l) : Coll where
  sp := ⟨fp, invFn fp, hpl, hpr⟩
  sl := ⟨fl, invFn fl, hll, hlr⟩
  pres p l := hpres p l

private def fnFrob (x : Fin 13) : Fin 13 := 3 * x

private def colFrob : Coll :=
  collOfFn fnFrob fnFrob (by decide) (by decide) (by decide) (by decide) (by decide)

private def colFrob2 : Coll := colFrob.comp colFrob

private def fnOfList (l : List ℕ) (x : Fin 13) : Fin 13 :=
  Fin.ofNat 13 (l.getD x.val 0)

private def colP2 : Coll :=
  collOfFn (fnOfList [0,2,1,12,4,7,6,5,9,8,10,11,3])
           (fnOfList [12,1,11,3,4,6,5,9,8,7,10,2,0])
           (by decide) (by decide) (by decide) (by decide) (by decide)

private def colP4 : Coll :=
  collOfFn (fnOfList [0,2,10,12,1,9,7,3,6,8,4,5,11])
           (fnOfList [12,1,9,11,0,6,7,3,5,8,4,2,10])
           (by decide) (by decide) (by decide) (by decide) (by decide)

private def colP7 : Coll :=
  collOfFn (fnOfList [0,2,6,12,9,3,5,1,11,8,7,4,10])
           (fnOfList [12,6,3,9,0,2,5,11,8,7,4,1,10])
           (by decide) (by decide) (by decide) (by decide) (by decide)

private def colL2 : Coll :=
  collOfFn (fnOfList [0,8,1,2,5,4,11,7,9,12,6,10,3])
           (fnOfList [12,5,1,2,4,8,11,6,9,3,10,7,0])
           (by decide) (by decide) (by decide) (by decide) (by decide)

private def colL7 : Coll :=
  collOfFn (fnOfList [0,8,3,2,7,5,6,4,1,12,10,11,9])
           (fnOfList [12,7,2,6,4,5,3,1,11,9,10,8,0])
           (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma exists_pt_to_01 (d : Fin 13) (hd : d ≠ 0) :
    ∃ c : Coll, c.sp 0 = 0 ∧ c.sp d = 1 := by
  fin_cases d
  · exact absurd rfl hd
  · exact ⟨Coll.id, by decide, by decide⟩
  · exact ⟨colP2, by decide, by decide⟩
  · exact ⟨colFrob2, by decide, by decide⟩
  · exact ⟨colP4, by decide, by decide⟩
  · exact ⟨colP2.comp colFrob, by decide, by decide⟩
  · exact ⟨colP2.comp colFrob2, by decide, by decide⟩
  · exact ⟨colP7, by decide, by decide⟩
  · exact ⟨colP7.comp colFrob2, by decide, by decide⟩
  · exact ⟨colFrob, by decide, by decide⟩
  · exact ⟨colP4.comp colFrob, by decide, by decide⟩
  · exact ⟨colP7.comp colFrob, by decide, by decide⟩
  · exact ⟨colP4.comp colFrob2, by decide, by decide⟩

private lemma exists_pt_ln (d : Fin 13) :
    ∃ c : Coll, c.sp 0 = 0 ∧ (c.sl d = 0 ∨ c.sl d = 1) := by
  fin_cases d
  · exact ⟨Coll.id, by decide, Or.inl (by decide)⟩
  · exact ⟨Coll.id, by decide, Or.inr (by decide)⟩
  · exact ⟨colL2, by decide, Or.inr (by decide)⟩
  · exact ⟨colFrob2, by decide, Or.inr (by decide)⟩
  · exact ⟨colP4, by decide, Or.inl (by decide)⟩
  · exact ⟨colL2.comp colFrob, by decide, Or.inr (by decide)⟩
  · exact ⟨colL2.comp colFrob2, by decide, Or.inr (by decide)⟩
  · exact ⟨colL7, by decide, Or.inr (by decide)⟩
  · exact ⟨colL7.comp colFrob2, by decide, Or.inr (by decide)⟩
  · exact ⟨colFrob, by decide, Or.inr (by decide)⟩
  · exact ⟨colP4.comp colFrob, by decide, Or.inl (by decide)⟩
  · exact ⟨colL7.comp colFrob, by decide, Or.inr (by decide)⟩
  · exact ⟨colP4.comp colFrob2, by decide, Or.inl (by decide)⟩

private def Coll.toFin26 (c : Coll) : Equiv.Perm (Fin 26) :=
  (finSumFinEquiv (m := 13) (n := 13)).symm.trans
    ((Equiv.sumCongr c.sp c.sl).trans (finSumFinEquiv (m := 13) (n := 13)))

private lemma Coll.toFin26_castAdd (c : Coll) (p : Fin 13) :
    c.toFin26 (Fin.castAdd 13 p) = Fin.castAdd 13 (c.sp p) := by
  have h : (finSumFinEquiv (m := 13) (n := 13)).symm (Fin.castAdd 13 p) = Sum.inl p := by
    rw [Equiv.symm_apply_eq]; rfl
  change finSumFinEquiv (Sum.map c.sp c.sl ((finSumFinEquiv (m := 13) (n := 13)).symm (Fin.castAdd 13 p))) =
    Fin.castAdd 13 (c.sp p)
  rw [h]; rfl

private lemma Coll.toFin26_natAdd (c : Coll) (l : Fin 13) :
    c.toFin26 (Fin.natAdd 13 l) = Fin.natAdd 13 (c.sl l) := by
  have h : (finSumFinEquiv (m := 13) (n := 13)).symm (Fin.natAdd 13 l) = Sum.inr l := by
    rw [Equiv.symm_apply_eq]; rfl
  change finSumFinEquiv (Sum.map c.sp c.sl ((finSumFinEquiv (m := 13) (n := 13)).symm (Fin.natAdd 13 l))) =
    Fin.natAdd 13 (c.sl l)
  rw [h]; rfl

private def polarity : Equiv.Perm (Fin 26) :=
  (finSumFinEquiv (m := 13) (n := 13)).symm.trans
    ((Equiv.sumComm (Fin 13) (Fin 13)).trans
      ((Equiv.sumCongr (Equiv.neg (Fin 13)) (Equiv.neg (Fin 13))).trans
        (finSumFinEquiv (m := 13) (n := 13))))

private lemma polarity_castAdd (p : Fin 13) :
    polarity (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := by
  have h : (finSumFinEquiv (m := 13) (n := 13)).symm (Fin.castAdd 13 p) = Sum.inl p := by
    rw [Equiv.symm_apply_eq]; rfl
  change finSumFinEquiv (Sum.map (fun x : Fin 13 => -x) (fun x : Fin 13 => -x)
    (Sum.swap ((finSumFinEquiv (m := 13) (n := 13)).symm (Fin.castAdd 13 p)))) = Fin.natAdd 13 (-p)
  rw [h]; rfl

private lemma polarity_natAdd (l : Fin 13) :
    polarity (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := by
  have h : (finSumFinEquiv (m := 13) (n := 13)).symm (Fin.natAdd 13 l) = Sum.inr l := by
    rw [Equiv.symm_apply_eq]; rfl
  change finSumFinEquiv (Sum.map (fun x : Fin 13 => -x) (fun x : Fin 13 => -x)
    (Sum.swap ((finSumFinEquiv (m := 13) (n := 13)).symm (Fin.natAdd 13 l)))) = Fin.castAdd 13 (-l)
  rw [h]; rfl

private def hit (x : Fin 26 → Bool) : Prop :=
  ∃ (u t : Fin 13), inc u t ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true

private lemma coll_pres_hit (c : Coll) (x : Fin 26 → Bool) :
    hit x ↔ hit (fun i => x (c.toFin26 i)) := by
  constructor
  · rintro ⟨u, t, hinc, hu, ht⟩
    refine ⟨c.sp.symm u, c.sl.symm t, (c.pres_symm u t).mpr hinc, ?_, ?_⟩
    · dsimp only; rw [c.toFin26_castAdd]; simpa using hu
    · dsimp only; rw [c.toFin26_natAdd]; simpa using ht
  · rintro ⟨u, t, hinc, hu, ht⟩
    dsimp only at hu ht
    rw [c.toFin26_castAdd] at hu
    rw [c.toFin26_natAdd] at ht
    exact ⟨c.sp u, c.sl t, (c.pres u t).mpr hinc, hu, ht⟩

private lemma polarity_pres_hit (x : Fin 26 → Bool) :
    hit x ↔ hit (fun i => x (polarity i)) := by
  constructor
  · rintro ⟨u, t, hinc, hu, ht⟩
    refine ⟨-t, -u, (inc_neg u t).mp hinc, ?_, ?_⟩
    · dsimp only; rw [polarity_castAdd, neg_neg]; exact ht
    · dsimp only; rw [polarity_natAdd, neg_neg]; exact hu
  · rintro ⟨u, t, hinc, hu, ht⟩
    dsimp only at hu ht
    rw [polarity_castAdd] at hu
    rw [polarity_natAdd] at ht
    exact ⟨-t, -u, (inc_neg (-t) (-u)).mpr (by simpa using hinc), ht, hu⟩

private lemma case_point_first (x2 x3 : Fin 26) (hne : x2 ≠ x3) (h2 : x2.val < 13) :
    ∃ c : Coll, c.toFin26 x2 = (0 : Fin 26) ∧
      (c.toFin26 x3 = (1 : Fin 26) ∨ c.toFin26 x3 = (13 : Fin 26) ∨ c.toFin26 x3 = (14 : Fin 26)) := by
  let p2 : Fin 13 := ⟨x2.val, h2⟩
  have hx2 : x2 = Fin.castAdd 13 p2 := rfl
  by_cases h3 : x3.val < 13
  · let p3 : Fin 13 := ⟨x3.val, h3⟩
    have hx3 : x3 = Fin.castAdd 13 p3 := rfl
    have hdp : p3 - p2 ≠ 0 := by
      intro h; apply hne; ext
      have hpeq : p3 = p2 := sub_eq_zero.mp h
      exact (congrArg Fin.val hpeq).symm
    obtain ⟨c0, hc0, hc1⟩ := exists_pt_to_01 (p3 - p2) hdp
    let c := c0.comp (Coll.shift (-p2))
    refine ⟨c, ?_, Or.inl ?_⟩
    · rw [hx2, c.toFin26_castAdd]
      have : c.sp p2 = 0 := by change c0.sp (p2 + -p2) = 0; simp [hc0]
      rw [this]; rfl
    · rw [hx3, c.toFin26_castAdd]
      have : c.sp p3 = 1 := by change c0.sp (p3 + -p2) = 1; rw [← sub_eq_add_neg]; exact hc1
      rw [this]; rfl
  · let l3 : Fin 13 := ⟨x3.val - 13, by omega⟩
    have hx3 : x3 = Fin.natAdd 13 l3 := by ext; simp [l3]; omega
    obtain ⟨c0, hc0, hcl⟩ := exists_pt_ln (l3 - p2)
    let c := c0.comp (Coll.shift (-p2))
    refine ⟨c, ?_, ?_⟩
    · rw [hx2, c.toFin26_castAdd]
      have : c.sp p2 = 0 := by change c0.sp (p2 + -p2) = 0; simp [hc0]
      rw [this]; rfl
    · rcases hcl with h0 | h1
      · right; left
        rw [hx3, c.toFin26_natAdd]
        have : c.sl l3 = 0 := by change c0.sl (l3 + -p2) = 0; rw [← sub_eq_add_neg]; exact h0
        rw [this]; rfl
      · right; right
        rw [hx3, c.toFin26_natAdd]
        have : c.sl l3 = 1 := by change c0.sl (l3 + -p2) = 1; rw [← sub_eq_add_neg]; exact h1
        rw [this]; rfl

private lemma main_proof :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
    ∀ (x2 x3 : Fin (26 : ℕ)), x2 ≠ x3 →
      ∃ (x5 : Equiv.Perm (Fin (26 : ℕ))), x5 x2 = (0 : Fin (26 : ℕ)) ∧
        (x5 x3 = (1 : Fin (26 : ℕ)) ∨ x5 x3 = (13 : Fin (26 : ℕ)) ∨ x5 x3 = (14 : Fin (26 : ℕ))) ∧
        ∀ (x6 : Fin (26 : ℕ) → Bool), x1 x6 ↔ x1 fun (x7 : Fin (26 : ℕ)) => x6 (x5 x7) := by
  intro x1 x2 x3 hne
  by_cases h2 : x2.val < 13
  · obtain ⟨c, h0, h1⟩ := case_point_first x2 x3 hne h2
    exact ⟨c.toFin26, h0, h1, fun x6 => coll_pres_hit c x6⟩
  · let l2 : Fin 13 := ⟨x2.val - 13, by omega⟩
    have hx2 : x2 = Fin.natAdd 13 l2 := by ext; simp [l2]; omega
    have hpol2 : (polarity x2).val < 13 := by
      rw [hx2, polarity_natAdd]; exact (-l2).isLt
    have hne' : polarity x2 ≠ polarity x3 := fun h => hne (polarity.injective h)
    obtain ⟨c, h0, h1⟩ := case_point_first (polarity x2) (polarity x3) hne' hpol2
    refine ⟨polarity.trans c.toFin26, h0, h1, fun x6 => ?_⟩
    exact (coll_pres_hit c x6).trans (polarity_pres_hit (fun i => x6 (c.toFin26 i)))

end PEqualNP.Outside.L_meta_6228_aux

theorem PEqualNP.Outside.L_meta_6228 :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 x3 : Fin (26 : ℕ)), x2 ≠ x3 → ∃ (x5 : Equiv.Perm (Fin (26 : ℕ))), x5 x2 = (0 : Fin (26 : ℕ)) ∧ (x5 x3 = (1 : Fin (26 : ℕ)) ∨ x5 x3 = (13 : Fin (26 : ℕ)) ∨ x5 x3 = (14 : Fin (26 : ℕ))) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), x1 x6 ↔ x1 fun (x7 : Fin (26 : ℕ)) => x6 (x5 x7) :=
  PEqualNP.Outside.L_meta_6228_aux.main_proof
