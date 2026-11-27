import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1683_713
    (assemble : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p w : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
      ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size+40 ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 C x =
          (decide (∃ p w : Fin 13, 5 ≤ p.val ∧ near p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) ||
          circuitFun 20 D (pins x)))
    (search : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p w : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 23 ∧
        (∀ p w : Fin 13, p.val < 5 → near p w → circuitFun 20 D
          (pins (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w))) = true) ∧
        (∀ x : Fin 26 → Bool, (∀ p w : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 w) = true → ¬ near p w) →
          ((∃ l : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → near p l) ∨
           (∃ q : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → near q w)) →
          circuitFun 20 D (pins x) = false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  have incidence : ∀ p w : Fin 13,
      (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = w+d) ↔
      (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d) := by decide +kernel
  obtain ⟨D,hD,sizeD,pos,neg⟩ := search
  obtain ⟨C,hC,sizeC,formula⟩ := assemble D hD
  refine ⟨C,hC,by omega,?_,?_⟩
  · intro p w h
    rw [formula]
    by_cases hp : p.val < 5
    · rw [pos p w hp ((incidence p w).mp h), Bool.or_true]
    · apply Bool.or_eq_true_iff.mpr
      left
      apply decide_eq_true ⟨p,w,by omega,(incidence p w).mp h,by simp,by simp⟩
  · intro P _ degenerate
    let I (p w : Fin 13) := ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = w+d
    let Y (w : Fin 13) := ∀ p ∈ P, ¬ I p w
    let z (kk : Fin (13+13)) := decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
      (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0,1,3,9} : Finset (Fin 13)), pp = ww+dd))))
    change circuitFun 26 C z = false
    have leftbit (p : Fin 13) : z (Fin.castAdd 13 p) = true ↔ p ∈ P := by
      have disj (w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
        intro e
        have h := congrArg Fin.val e
        change p.val = 13+w.val at h
        omega
      simp only [z,decide_eq_true_eq,disj,false_and,exists_false,or_false,Fin.castAdd_inj]
      constructor
      · rintro ⟨q,hq,rfl⟩
        exact hq
      · intro hp
        exact ⟨p,hp,rfl⟩
    have rightbit (w : Fin 13) : z (Fin.natAdd 13 w) = true ↔ Y w := by
      have disj (p : Fin 13) : Fin.natAdd 13 w ≠ Fin.castAdd 13 p := by
        intro e
        have h := congrArg Fin.val e
        change 13+w.val = p.val at h
        omega
      simp only [z,decide_eq_true_eq,disj,and_false,exists_false,false_or]
      constructor
      · rintro ⟨v,h,hv⟩
        have ev : w=v := Fin.ext (by have h' := congrArg Fin.val h; change 13+w.val = 13+v.val at h'; omega)
        exact ev.symm ▸ hv
      · intro h
        exact ⟨w,rfl,h⟩
    have miss (p w : Fin 13) (hp : z (Fin.castAdd 13 p) = true) (hw : z (Fin.natAdd 13 w) = true) :
        ¬ (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p=w+d) := fun h =>
      (rightbit w).mp hw p ((leftbit p).mp hp) ((incidence p w).mpr h)
    have noOutside : ¬ ∃ p w : Fin 13, 5 ≤ p.val ∧ (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p=w+d) ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 w) = true := by
      rintro ⟨p,w,_,hi,hp,hw⟩
      exact miss p w hp hw hi
    rw [formula, neg z miss]
    · simpa only [Bool.or_false] using decide_eq_false noOutside
    · rcases degenerate with ⟨l,hl⟩ | ⟨p,hp⟩
      · exact Or.inl ⟨l,fun i hi => (incidence i l).mp (hl i ((leftbit i).mp hi))⟩
      · exact Or.inr ⟨p,fun w hw => (incidence p w).mp (hp w ((rightbit w).mp hw))⟩
