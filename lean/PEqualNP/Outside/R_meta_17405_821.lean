import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_17405_821
    (search :
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        ∀ r ∈ ([67117057,67239937,67100672,25018369,7962627,24444933,7405575,6815755,
                 23330829,5799955,22282261,21757977,19988517,19415081,6619269,2179233] : List ℕ),
        ∀ a ∈ ([1,3,9] : List (Fin 13)), ∀ (b : Fin 13) (e : Bool),
          let P := fun i : Fin 13 => r.testBit (a*i+b).val
          let L := fun i : Fin 13 => r.testBit ((a*i+b).val+13)
          circuitFun 26 C (if e then Fin.append (fun i => L (-i)) (fun i => P (-i))
                          else Fin.append P L) = r.testBit 26)
    (orbits : ∀ S : Finset (Fin 13), S.card ≤ 3 →
      ∃ r ∈ ([67100672,25018369,7962627,24444933,7405575,6815755,23330829,5799955,
               22282261,21757977,19988517,19415081,6619269,2179233] : List ℕ),
      ∃ a ∈ ([1,3,9] : List (Fin 13)), ∃ b : Fin 13,
        ∀ i : Fin 13, decide (i ∈ S) = r.testBit (a*i+b).val) :
have x1 : Finset (Fin (13 : ℕ)) := Finset.univ; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x3)) fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 {x5} {x6}) = Bool.true) ∧ (∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 x5 ({x7 ∈ x1 | ∀ x8 ∈ x5, ¬x2 x8 x7})) = Bool.false) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 ({x7 ∈ x1 | ∀ x8 ∈ x5, ¬x2 x7 x8}) x5) = Bool.false := by
  let bad : List ℕ := [67100672,25018369,7962627,24444933,7405575,6815755,23330829,
    5799955,22282261,21757977,19988517,19415081,6619269,2179233]
  let good : List ℕ := [67117057,67239937]
  let A : List (Fin 13) := [1,3,9]
  let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
  let left := fun (r : ℕ) (a b i : Fin 13) => r.testBit (a*i+b).val
  let right := fun (r : ℕ) (a b i : Fin 13) => r.testBit ((a*i+b).val+13)
  let vals := fun (S : Finset (Fin 13)) (i : Fin 13) => decide (i ∈ S)
  let avoid := fun (S : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ S, ¬ I p l)
  let avoid' := fun (S : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l)
  have high : (∀ r ∈ good, r.testBit 26 = true) ∧ (∀ r ∈ bad, r.testBit 26 = false) := by
    dsimp only [good,bad]
    decide +kernel
  have masks : ∀ r ∈ bad, ∀ j : Fin 13,
      r.testBit (j.val+13) = decide (∀ i : Fin 13, r.testBit i.val = true → ¬ I i j) := by
    dsimp only [bad,I]
    decide +kernel
  have geom : ∀ a ∈ A, ∀ b : Fin 13, (∀ t : Fin 13, ∃ i : Fin 13, a*i+b=t) ∧
      ∀ i j : Fin 13, I i j ↔ I (a*i+b) (a*j+b) := by
    dsimp only [A,I]
    decide +kernel
  have dual : ∀ p l : Fin 13, I p l ↔ I (-l) (-p) := by
    dsimp only [I]
    decide +kernel
  have flags : ∀ p l : Fin 13, I p l → ∃ r ∈ good, ∃ a ∈ A, ∃ b : Fin 13,
      (∀ i : Fin 13, decide (i=p) = left r a b i) ∧
      (∀ i : Fin 13, decide (i=l) = right r a b i) := by
    dsimp only [I,good,A,left,right]
    decide +kernel
  have boundaries (S : Finset (Fin 13)) (small : S.card ≤ 3) :
      ∃ r ∈ bad, ∃ a ∈ A, ∃ b : Fin 13,
        vals S = left r a b ∧ vals (avoid S) = right r a b := by
    obtain ⟨r,hr,a,ha,b,h⟩ := orbits S small
    refine ⟨r,hr,a,ha,b,funext h,?_⟩
    funext j
    change decide (j ∈ Finset.univ.filter _) = r.testBit ((a*j+b).val+13)
    rw [masks r hr]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply decide_eq_decide.mpr
    constructor
    · intro hn t ht
      obtain ⟨i,rfl⟩ := (geom a ha b).1 t
      exact fun inc => hn i (of_decide_eq_true ((h i).trans ht)) ((geom a ha b).2 i j |>.mpr inc)
    · intro hn i hi inc
      exact hn (a*i+b) ((h i).symm.trans (decide_eq_true hi)) ((geom a ha b).2 i j |>.mp inc)
  obtain ⟨C,hm,hs,hc⟩ := search
  have check (r : ℕ) (hr : r ∈ good ++ bad) (a : Fin 13) (ha : a ∈ A) (b : Fin 13) :
      circuitFun 26 C (Fin.append (left r a b) (right r a b)) = r.testBit 26 ∧
      circuitFun 26 C (Fin.append (fun i => right r a b (-i)) (fun i => left r a b (-i))) = r.testBit 26 :=
    ⟨hc r hr a ha b false, hc r hr a ha b true⟩
  refine ⟨C,hm,hs,?_,?_,?_⟩
  · intro p l h
    obtain ⟨r,hr,a,ha,b,hp,hl⟩ := flags p l h
    have ep : vals {p} = left r a b := funext (by simpa [vals] using hp)
    have el : vals {l} = right r a b := funext (by simpa [vals] using hl)
    change circuitFun 26 C (Fin.append (vals {p}) (vals {l})) = true
    rw [ep,el,(check r (List.mem_append_left _ hr) a ha b).1,high.1 r hr]
  · intro S h
    obtain ⟨r,hr,a,ha,b,hp,hl⟩ := boundaries S h
    change circuitFun 26 C (Fin.append (vals S) (vals (avoid S))) = false
    rw [hp,hl,(check r (List.mem_append_right _ hr) a ha b).1,high.2 r hr]
  · intro S h
    let T := S.image (fun i : Fin 13 => -i)
    have ht : T.card ≤ 3 := (Finset.card_image_le).trans h
    have mem (i : Fin 13) : i ∈ T ↔ -i ∈ S := by
      simp only [T, Finset.mem_image]
      constructor
      · rintro ⟨j,hj,rfl⟩
        simpa only [neg_neg] using hj
      · intro hi
        exact ⟨-i,hi,neg_neg i⟩
    obtain ⟨r,hr,a,ha,b,hp,hl⟩ := boundaries T ht
    have ep : vals (avoid' S) = fun i => right r a b (-i) := by
      funext i
      rw [← hl]
      change decide (i ∈ Finset.univ.filter _) = decide (-i ∈ Finset.univ.filter _)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply decide_eq_decide.mpr
      constructor
      · intro hn j hj hij
        exact hn (-j) ((mem j).mp hj) (by simpa only [neg_neg] using (dual j (-i)).mp hij)
      · intro hn j hj hij
        exact hn (-j) ((mem (-j)).mpr (by simpa only [neg_neg] using hj)) ((dual i j).mp hij)
    have el : vals S = fun i => left r a b (-i) := by
      funext i
      rw [← hp]
      change decide (i ∈ S) = decide (-i ∈ T)
      simp only [mem,neg_neg]
    change circuitFun 26 C (Fin.append (vals (avoid' S)) (vals S)) = false
    rw [ep,el,(check r (List.mem_append_right _ hr) a ha b).2,high.2 r hr]
