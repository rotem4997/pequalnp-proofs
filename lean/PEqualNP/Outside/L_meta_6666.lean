import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6666_aux

open PEqualNP.HeptadCover PEqualNP.LowMerge

private structure Coll where
  sp : Equiv.Perm (Fin 13)
  sl : Equiv.Perm (Fin 13)
  pres : ∀ p l : Fin 13, sp p ∈ singerLines3 (sl l) ↔ p ∈ singerLines3 l

private lemma Coll.pres_symm (c : Coll) (p l : Fin 13) :
    c.sp.symm p ∈ singerLines3 (c.sl.symm l) ↔ p ∈ singerLines3 l := by
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

private lemma mem_singerLines3_iff (p l : Fin 13) :
    p ∈ singerLines3 l ↔ (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ) := by
  simp [singerLines3]

private lemma mem_singerLines3_add (a p l : Fin 13) :
    p + a ∈ singerLines3 (l + a) ↔ p ∈ singerLines3 l := by
  revert a p l; decide

private lemma mem_singerLines3_neg (p l : Fin 13) :
    p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p) := by
  revert p l; decide

private def Coll.shift (a : Fin 13) : Coll where
  sp := Equiv.addRight a
  sl := Equiv.addRight a
  pres p l := mem_singerLines3_add a p l

private def Coll.dual (c : Coll) : Coll where
  sp := (Equiv.neg (Fin 13)).trans (c.sl.trans (Equiv.neg (Fin 13)))
  sl := (Equiv.neg (Fin 13)).trans (c.sp.trans (Equiv.neg (Fin 13)))
  pres p l := by
    change -(c.sl (-p)) ∈ singerLines3 (-(c.sp (-l))) ↔ p ∈ singerLines3 l
    rw [mem_singerLines3_neg, neg_neg, neg_neg, c.pres, ← mem_singerLines3_neg]

private def invFn (f : Fin 13 → Fin 13) (y : Fin 13) : Fin 13 :=
  ((List.finRange 13).find? fun x => f x == y).getD 0

private def collOfFn (fp fl : Fin 13 → Fin 13)
    (hpl : ∀ x : Fin 13, invFn fp (fp x) = x)
    (hpr : ∀ y : Fin 13, fp (invFn fp y) = y)
    (hll : ∀ x : Fin 13, invFn fl (fl x) = x)
    (hlr : ∀ y : Fin 13, fl (invFn fl y) = y)
    (hpres : ∀ p l : Fin 13, fp p ∈ singerLines3 (fl l) ↔ p ∈ singerLines3 l) : Coll where
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

private def Coll.toFin26 (c : Coll) : Fin 26 ≃ Fin 26 :=
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

private lemma map_ofFn_append (c : Coll) (f g : Fin 13 → Bool) :
    (List.ofFn fun i : Fin 26 => (List.ofFn f ++ List.ofFn g).getD (c.toFin26 i).val false) =
      List.ofFn (fun p : Fin 13 => f (c.sp p)) ++ List.ofFn (fun l : Fin 13 => g (c.sl l)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hi : i < 13
    · have hcast : (⟨i, h1⟩ : Fin 26) = Fin.castAdd 13 ⟨i, hi⟩ := rfl
      rw [hcast, c.toFin26_castAdd]
      have hlt := (c.sp ⟨i, hi⟩).isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
      simp only [Fin.val_castAdd, hlt, ↓reduceDIte, Option.getD_some]
      rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    · have hi' : i - 13 < 13 := by omega
      have hnat : (⟨i, h1⟩ : Fin 26) = Fin.natAdd 13 ⟨i - 13, hi'⟩ := by
        ext; simp; omega
      rw [hnat, c.toFin26_natAdd]
      have hlt := (c.sl ⟨i - 13, hi'⟩).isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_ofFn]
      have hsub : 13 + (c.sl ⟨i - 13, hi'⟩).val - (List.ofFn f).length = (c.sl ⟨i - 13, hi'⟩).val := by simp
      simp only [Fin.val_natAdd, hsub, hlt, ↓reduceDIte, Option.getD_some]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn]

private lemma map_pointLineInput (c : Coll) (p l : Fin 13) :
    (List.ofFn fun i : Fin 26 => (pointLineInput 13 13 p l).getD (c.toFin26 i).val false) =
      pointLineInput 13 13 (c.sp.symm p) (c.sl.symm l) := by
  unfold pointLineInput restrictInput
  rw [map_ofFn_append]
  congr 1
  · congr 1; funext q; simp [Equiv.eq_symm_apply]
  · congr 1; funext v; simp [Equiv.eq_symm_apply]

private lemma quad_image_mem (c : Coll) (Q : Finset (Fin 13)) :
    Q ∈ quadrangles singerLines3 → Q.image c.sp.symm ∈ quadrangles singerLines3 := by
  intro hQ
  simp only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hQ ⊢
  refine ⟨by rw [Finset.card_image_of_injective _ c.sp.symm.injective, hQ.1], ?_⟩
  intro l
  have hcard : (Q.image c.sp.symm ∩ singerLines3 l).card = (Q ∩ singerLines3 (c.sl l)).card := by
    apply Finset.card_bij (fun p _ => c.sp p)
    · intro p hp
      simp only [Finset.mem_inter, Finset.mem_image] at hp ⊢
      rcases hp with ⟨⟨q, hq, rfl⟩, hl⟩
      exact ⟨by simpa using hq, (c.pres _ _).mpr hl⟩
    · intro a _ b _ h; exact c.sp.injective h
    · intro q hq
      simp only [Finset.mem_inter] at hq
      refine ⟨c.sp.symm q, ?_, by simp⟩
      simp only [Finset.mem_inter, Finset.mem_image]
      exact ⟨⟨q, hq.1, rfl⟩, (c.pres (c.sp.symm q) l).mp (by simpa using hq.2)⟩
  rw [hcard]
  exact hQ.2 (c.sl l)

private lemma missLines_image (c : Coll) (Q : Finset (Fin 13)) (l : Fin 13) :
    c.sl l ∈ missLines singerLines3 Q ↔ l ∈ missLines singerLines3 (Q.image c.sp.symm) := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, Finset.mem_image]
  constructor
  · intro h p hp ⟨q, hq, hqp⟩
    have hp' : c.sp p ∈ singerLines3 (c.sl l) := (c.pres p l).mpr hp
    have hqeq : c.sp p = q := by rw [← hqp]; simp
    exact h hp' (hqeq ▸ hq)
  · intro h q hq hqQ
    exact h ((c.pres (c.sp.symm q) l).mp (by simpa using hq)) ⟨q, hqQ, rfl⟩

private lemma map_quadInput (c : Coll) (Q : Finset (Fin 13)) :
    (List.ofFn fun i : Fin 26 =>
      ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
       List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)).getD (c.toFin26 i).val false) =
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q.image c.sp.symm)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 (Q.image c.sp.symm)) := by
  rw [map_ofFn_append]
  congr 1
  · congr 1; funext p
    simp only [Finset.mem_image]
    by_cases hp : c.sp p ∈ Q
    · simp only [hp, decide_true]
      exact (decide_eq_true ⟨c.sp p, hp, by simp⟩).symm
    · simp only [hp, decide_false]
      symm; apply decide_eq_false
      rintro ⟨q, hq, hqp⟩
      have : c.sp p = q := by rw [← hqp]; simp
      exact hp (this ▸ hq)
  · congr 1; funext l
    simp only [missLines_image]

private lemma image_x1_eq (c : Coll) :
    let x1 := Finset.image (fun pl : Fin 13 × Fin 13 => pointLineInput 13 13 pl.1 pl.2) (incidences singerLines3)
    let x8 := fun (l : List Bool) => List.ofFn fun i : Fin 26 => l.getD (c.toFin26 i).val false
    Finset.image x8 x1 = x1 := by
  intro x1 x8
  ext v
  simp only [Finset.mem_image, x1, incidences, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨⟨p, l⟩, hpl, rfl⟩, rfl⟩
    refine ⟨(c.sp.symm p, c.sl.symm l), (c.pres_symm p l).mpr hpl, ?_⟩
    exact (map_pointLineInput c p l).symm
  · rintro ⟨⟨p, l⟩, hpl, rfl⟩
    refine ⟨pointLineInput 13 13 (c.sp p) (c.sl l),
      ⟨(c.sp p, c.sl l), (c.pres p l).mpr hpl, rfl⟩, ?_⟩
    dsimp only [x8]
    rw [map_pointLineInput]
    simp

private lemma image_x2_eq (c : Coll) :
    let x2 := Finset.image (fun Q : Finset (Fin 13) =>
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) (quadrangles singerLines3)
    let x8 := fun (l : List Bool) => List.ofFn fun i : Fin 26 => l.getD (c.toFin26 i).val false
    Finset.image x8 x2 = x2 := by
  intro x2 x8
  ext v
  simp only [Finset.mem_image, x2]
  constructor
  · rintro ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q.image c.sp.symm, quad_image_mem c Q hQ, (map_quadInput c Q).symm⟩
  · rintro ⟨Q, hQ, rfl⟩
    let cInv : Coll := ⟨c.sp.symm, c.sl.symm, c.pres_symm⟩
    have hQ' : Q.image c.sp ∈ quadrangles singerLines3 := by
      have := quad_image_mem cInv Q hQ
      simpa [cInv] using this
    refine ⟨(List.ofFn fun p : Fin 13 => decide (p ∈ Q.image c.sp)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 (Q.image c.sp)),
      ⟨Q.image c.sp, hQ', rfl⟩, ?_⟩
    dsimp only [x8]
    rw [map_quadInput]
    have hback : (Q.image c.sp).image c.sp.symm = Q := by
      ext q; simp
    rw [hback]

private lemma main_proof :
    have x1 : Finset (List Bool) := Finset.image (fun (x1 : Fin (13 : ℕ) × Fin (13 : ℕ)) => PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x1.1 x1.2) (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3);
    have x2 : Finset (List Bool) := Finset.image (fun (x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) (PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3);
    have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => (Min.min x3 x4, Max.max x3 x4) ∈ [((0 : ℕ), (1 : ℕ)), ((13 : ℕ), (14 : ℕ)), ((0 : ℕ), (13 : ℕ)), ((0 : ℕ), (14 : ℕ))];
    ∀ (x4 x5 : Fin (26 : ℕ)), x4 ≠ x5 →
      ∃ (x7 : Fin (26 : ℕ) ≃ Fin (26 : ℕ)), x3 ↑(x7 x4) ↑(x7 x5) ∧
        have x8 : List Bool → List Bool := fun (x8 : List Bool) => List.ofFn fun (x9 : Fin (26 : ℕ)) => x8.getD (↑(x7 x9)) Bool.false;
        Finset.image x8 x1 = x1 ∧ Finset.image x8 x2 = x2 := by
  intro x1 x2 x3 x4 x5 hne
  have hofColl : ∀ c : Coll, x3 ↑(c.toFin26 x4) ↑(c.toFin26 x5) →
      ∃ (x7 : Fin 26 ≃ Fin 26), x3 ↑(x7 x4) ↑(x7 x5) ∧
        have x8 : List Bool → List Bool := fun x8 => List.ofFn fun x9 : Fin 26 => x8.getD ↑(x7 x9) false;
        Finset.image x8 x1 = x1 ∧ Finset.image x8 x2 = x2 :=
    fun c hx3 => ⟨c.toFin26, hx3, image_x1_eq c, image_x2_eq c⟩
  by_cases h4 : x4.val < 13
  · let p4 : Fin 13 := ⟨x4.val, h4⟩
    have hx4 : x4 = Fin.castAdd 13 p4 := rfl
    by_cases h5 : x5.val < 13
    · let p5 : Fin 13 := ⟨x5.val, h5⟩
      have hx5 : x5 = Fin.castAdd 13 p5 := rfl
      have hdp : p5 - p4 ≠ 0 := by
        intro h; apply hne; ext
        have hpeq : p5 = p4 := sub_eq_zero.mp h
        exact (congrArg Fin.val hpeq).symm
      obtain ⟨c0, hc0, hc1⟩ := exists_pt_to_01 (p5 - p4) hdp
      let c := c0.comp (Coll.shift (-p4))
      apply hofColl c
      have hA : c.toFin26 x4 = Fin.castAdd 13 (0 : Fin 13) := by
        rw [hx4, c.toFin26_castAdd]; congr 1
        change c0.sp (p4 + -p4) = 0; simp [hc0]
      have hB : c.toFin26 x5 = Fin.castAdd 13 (1 : Fin 13) := by
        rw [hx5, c.toFin26_castAdd]; congr 1
        change c0.sp (p5 + -p4) = 1; rw [← sub_eq_add_neg]; exact hc1
      rw [hA, hB]; simp [x3]
    · let l5 : Fin 13 := ⟨x5.val - 13, by omega⟩
      have hx5 : x5 = Fin.natAdd 13 l5 := by ext; simp [l5]; omega
      obtain ⟨c0, hc0, hcl⟩ := exists_pt_ln (l5 - p4)
      let c := c0.comp (Coll.shift (-p4))
      apply hofColl c
      have hA : c.toFin26 x4 = Fin.castAdd 13 (0 : Fin 13) := by
        rw [hx4, c.toFin26_castAdd]; congr 1
        change c0.sp (p4 + -p4) = 0; simp [hc0]
      rcases hcl with h0 | h1
      · have hB : c.toFin26 x5 = Fin.natAdd 13 (0 : Fin 13) := by
          rw [hx5, c.toFin26_natAdd]; congr 1
          change c0.sl (l5 + -p4) = 0; rw [← sub_eq_add_neg]; exact h0
        rw [hA, hB]; simp [x3]
      · have hB : c.toFin26 x5 = Fin.natAdd 13 (1 : Fin 13) := by
          rw [hx5, c.toFin26_natAdd]; congr 1
          change c0.sl (l5 + -p4) = 1; rw [← sub_eq_add_neg]; exact h1
        rw [hA, hB]; simp [x3]
  · let l4 : Fin 13 := ⟨x4.val - 13, by omega⟩
    have hx4 : x4 = Fin.natAdd 13 l4 := by ext; simp [l4]; omega
    by_cases h5 : x5.val < 13
    · let p5 : Fin 13 := ⟨x5.val, h5⟩
      have hx5 : x5 = Fin.castAdd 13 p5 := rfl
      obtain ⟨c0, hc0, hcl⟩ := exists_pt_ln (l4 - p5)
      let c := c0.comp (Coll.shift (-p5))
      apply hofColl c
      have hB : c.toFin26 x5 = Fin.castAdd 13 (0 : Fin 13) := by
        rw [hx5, c.toFin26_castAdd]; congr 1
        change c0.sp (p5 + -p5) = 0; simp [hc0]
      rcases hcl with h0 | h1
      · have hA : c.toFin26 x4 = Fin.natAdd 13 (0 : Fin 13) := by
          rw [hx4, c.toFin26_natAdd]; congr 1
          change c0.sl (l4 + -p5) = 0; rw [← sub_eq_add_neg]; exact h0
        rw [hA, hB]; simp [x3]
      · have hA : c.toFin26 x4 = Fin.natAdd 13 (1 : Fin 13) := by
          rw [hx4, c.toFin26_natAdd]; congr 1
          change c0.sl (l4 + -p5) = 1; rw [← sub_eq_add_neg]; exact h1
        rw [hA, hB]; simp [x3]
    · let l5 : Fin 13 := ⟨x5.val - 13, by omega⟩
      have hx5 : x5 = Fin.natAdd 13 l5 := by ext; simp [l5]; omega
      have hdl : -(l5 - l4) ≠ 0 := by
        intro h; apply hne; ext
        have h1 : l5 - l4 = 0 := neg_eq_zero.mp h
        have h2 : l5 = l4 := sub_eq_zero.mp h1
        have h3 := congrArg Fin.val h2
        dsimp only [l4, l5] at h3; omega
      obtain ⟨c0, hc0, hc1⟩ := exists_pt_to_01 (-(l5 - l4)) hdl
      let c := (Coll.shift 1).comp (c0.dual.comp (Coll.shift (-l4)))
      apply hofColl c
      have hA : c.toFin26 x4 = Fin.natAdd 13 (1 : Fin 13) := by
        rw [hx4, c.toFin26_natAdd]; congr 1
        change -(c0.sp (-(l4 + -l4))) + 1 = 1
        simp [hc0]
      have hB : c.toFin26 x5 = Fin.natAdd 13 (0 : Fin 13) := by
        rw [hx5, c.toFin26_natAdd]; congr 1
        change -(c0.sp (-(l5 + -l4))) + 1 = 0
        rw [← sub_eq_add_neg, hc1]; decide
      rw [hA, hB]; simp [x3]

end PEqualNP.Outside.L_meta_6666_aux

theorem PEqualNP.Outside.L_meta_6666 :
    have x1 : Finset (List Bool) := Finset.image (fun (x1 : Fin (13 : ℕ) × Fin (13 : ℕ)) => PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x1.1 x1.2) (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3); have x2 : Finset (List Bool) := Finset.image (fun (x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) (PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3); have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => (Min.min x3 x4, Max.max x3 x4) ∈ [((0 : ℕ), (1 : ℕ)), ((13 : ℕ), (14 : ℕ)), ((0 : ℕ), (13 : ℕ)), ((0 : ℕ), (14 : ℕ))]; ∀ (x4 x5 : Fin (26 : ℕ)),   x4 ≠ x5 →     ∃ (x7 : Fin (26 : ℕ) ≃ Fin (26 : ℕ)),       x3 ↑(x7 x4) ↑(x7 x5) ∧         have x8 : List Bool → List Bool := fun (x8 : List Bool) => List.ofFn fun (x9 : Fin (26 : ℕ)) => x8.getD (↑(x7 x9)) Bool.false;         Finset.image x8 x1 = x1 ∧ Finset.image x8 x2 = x2 :=
  PEqualNP.Outside.L_meta_6666_aux.main_proof
