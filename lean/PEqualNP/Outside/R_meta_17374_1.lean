import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_17374_1
  (h1 : ∃ R : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 R ∧ R.size ≤ 58 ∧
    ∀ y : Fin 25 → Bool, PEqualNP.MetaComplexity.circuitFun 25 R y = (([1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)).any fun l =>
      y ⟨12+l.val,Nat.add_lt_add_left l.isLt 12⟩ && ([0,1,3,9] : List (Fin 13)).any
        (fun d => y (Fin.castAdd 12 (l+d)))))
  (h2 : ∀ R : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 R → R.size ≤ 58 →
    (∃ y : Fin 25 → Bool, PEqualNP.MetaComplexity.circuitFun 25 R y = true) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 62 ∧
      ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 27 C (Fin.snoc x (x 0 || x 1)) =
        (PEqualNP.MetaComplexity.circuitFun 25 R (fun i =>
          x (if i.val < 13 then (⟨i.val,Nat.lt_succ_of_lt i.isLt⟩ : Fin 26)
            else ⟨i.val+1,Nat.add_lt_add_right i.isLt 1⟩)) ||
          (x 13 && ((x 0 || x 1) || x 3 || x 9)))) :
  have x1 : (Fin (26 : ℕ) → Bool) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true); ∃ x2 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ))], ∃ (x3 : Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (62 : ℕ) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), (∀ (x6 : Fin (26 : ℕ)), x5 x6 = x1 x5 → x1 (Function.update x5 x6 !x5 x6) ≠ x1 x5) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (Fin.snoc x5 (if x3 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x2 else x5 (0 : Fin (26 : ℕ)) && x5 x2)) = x1 x5 := by
  classical
  let rest : (Fin 25 → Bool) → Bool := fun y => ([1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)).any fun l =>
      y ⟨12+l.val,Nat.add_lt_add_left l.isLt 12⟩ && ([0,1,3,9] : List (Fin 13)).any
        (fun d => y (Fin.castAdd 12 (l+d)))
  let proj : Fin 25 → Fin 26 := fun i =>
    if i.val < 13 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
  obtain ⟨R,hmono,hsize,hR⟩ := h1
  have hR' : ∀ y, PEqualNP.MetaComplexity.circuitFun 25 R y = rest y := hR
  have hpos : ∃ y : Fin 25 → Bool, PEqualNP.MetaComplexity.circuitFun 25 R y = true := by
    let y : Fin 25 → Bool := fun i => decide (i = 1 ∨ i = 13)
    refine ⟨y,?_⟩
    rw [hR']
    simp only [rest,List.any_eq_true,Bool.and_eq_true]
    refine ⟨1,by simp,?_,0,by simp,?_⟩ <;> simp [y]
  obtain ⟨C,hC,hCsize,hCeq⟩ := h2 R hmono hsize hpos
  refine ⟨1,by simp,true,C,hC,hCsize,?_⟩
  intro x _
  change PEqualNP.MetaComplexity.circuitFun 27 C (Fin.snoc x (x 0 || x 1)) = _
  rw [hCeq x, hR']
  let full : (Fin 26 → Bool) → Bool := fun x =>
    decide (∃ p l : Fin 13, (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  let plane : (Fin 26 → Bool) → Bool := fun x =>
    ([0,1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)).any fun l =>
      x (Fin.natAdd 13 l) && ([0,1,3,9] : List (Fin 13)).any
        (fun d => x (Fin.castAdd 13 (l+d)))
  have hplane : plane x = full x := by
    apply Bool.eq_iff_iff.mpr
    have hall (l : Fin 13) : l ∈ ([0,1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)) := by
      fin_cases l <;> decide
    simp only [plane,full,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨l,_,hl,d,hd,hp⟩
      exact ⟨l+d,l,⟨d,hd,rfl⟩,hp,hl⟩
    · rintro ⟨p,l,⟨d,hd,rfl⟩,hp,hl⟩
      exact ⟨l,hall l,hl,d,hd,hp⟩
  have hp (p : Fin 13) : proj (Fin.castAdd 12 p) = Fin.castAdd 13 p := by
    apply Fin.ext
    simp [proj]
  have hl (l : Fin 13) (h : l ∈ ([1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13))) :
      proj ⟨12+l.val,Nat.add_lt_add_left l.isLt 12⟩ = Fin.natAdd 13 l := by
    fin_cases l <;> simp_all [proj]
  have hr : rest (x ∘ proj) =
      ([1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)).any (fun l =>
        x (Fin.natAdd 13 l) && ([0,1,3,9] : List (Fin 13)).any
          (fun d => x (Fin.castAdd 13 (l+d)))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [rest,List.any_eq_true,Bool.and_eq_true,Function.comp_def]
    constructor
    · rintro ⟨l,hL,hx,d,hd,hp'⟩
      exact ⟨l,hL,(hl l hL) ▸ hx,d,hd,(hp (l+d)) ▸ hp'⟩
    · rintro ⟨l,hL,hx,d,hd,hp'⟩
      exact ⟨l,hL,(hl l hL).symm ▸ hx,d,hd,(hp (l+d)).symm ▸ hp'⟩
  have hs : plane x =
      ((x 13 && ((x 0 || x 1) || x 3 || x 9)) ||
        ([1,2,3,4,5,6,7,8,9,10,11,12] : List (Fin 13)).any (fun l =>
          x (Fin.natAdd 13 l) && ([0,1,3,9] : List (Fin 13)).any
            (fun d => x (Fin.castAdd 13 (l+d))))) := by
    simp [plane,List.any,Bool.or_assoc]
  change (rest (x ∘ proj) || (x 13 && ((x 0 || x 1) || x 3 || x 9))) = full x
  rw [← hplane,hs,hr]
  exact Bool.or_comm _ _
