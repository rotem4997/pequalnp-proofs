import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.HeptadCover

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_7261_36
    (affine :
      ∃ (D : Circuit) (d : Fin 13 → ℕ), D.size ≤ 50 ∧ IsAO2 26 D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output < 26+D.size ∧
        (∀ p ∈ singerLines3 0, d p < 26+D.size ∧ d p ≠ p.val) ∧
        ∀ x : Fin 26 → Bool,
          (D.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13,
            p ∉ singerLines3 0 ∧ l≠0 ∧ p ∈ singerLines3 l ∧
            x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) ∧
          ∀ p ∈ singerLines3 0, wireValue D 26 x (d p)=true ↔
            ∃ l : Fin 13,l≠0 ∧ p∈singerLines3 l ∧ x (Fin.natAdd 13 l)=true)
    (finish : ∀ (D : Circuit) (d : Fin 13 → ℕ), IsAO2 26 D →
      (∀ g ∈ D.gates,g.inputs.Nodup) → D.output < 26+D.size →
      (∀ p ∈ singerLines3 0,d p < 26+D.size ∧ d p ≠ p.val) →
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ D.size+14 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates,g.inputs.Nodup) ∧ C.output=26+j ∧ C.gates[j]?=some ⟨.and,[a,b]⟩ ∧
        ∀ x : Fin 26 → Bool,
          let h := decide (∃ p ∈ singerLines3 0,x (Fin.castAdd 13 p)=true)
          let y := decide (∃ p ∈ singerLines3 0,x (Fin.castAdd 13 p)=true ∧ wireValue D 26 x (d p)=true)
          let z := D.eval (List.ofFn x)
          wireValue C 26 x a=(z || h) ∧ wireValue C 26 x b=((z || y) || x 13)) : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Bool) (x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x7 x8) (if x2 x7 x8 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by

  intro incident makeRow
  obtain ⟨D,d,limit,shape,nodup,outD,ports,core⟩ := affine
  obtain ⟨C,j,a,b,cost,ao,distinct,out,gate,last⟩ := finish D d shape nodup outD ports
  have inc : ∀p l : Fin 13,incident p l ↔ p∈singerLines3 l := by decide +kernel
  refine ⟨C,j,a,b,by omega,ao,distinct,out,gate,?_,?_⟩
  · intro p l flag
    let x : Fin 26 → Bool := fun i=>decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
    have hp : x (Fin.castAdd 13 p)=true := by simp [x]
    have hl : x (Fin.natAdd 13 l)=true := by simp [x]
    change wireValue C 26 x a=true ∧ wireValue C 26 x b=true
    have member := (inc p l).mp flag
    obtain ⟨front,back⟩ := last x
    by_cases atInfinity : p∈singerLines3 0
    · have first : decide (∃ q ∈ singerLines3 0,x (Fin.castAdd 13 q)=true)=true :=
        decide_eq_true ⟨p,atInfinity,hp⟩
      refine ⟨by simp only [front,first,Bool.or_true],?_⟩
      by_cases zero : l=0
      · subst l
        change x 13=true at hl
        simp only [back,hl,Bool.or_true]
      · have port := ((core x).2 p atInfinity).mpr ⟨l,zero,member,hl⟩
        have present : decide (∃ q ∈ singerLines3 0,x (Fin.castAdd 13 q)=true ∧
            wireValue D 26 x (d q)=true)=true := decide_eq_true ⟨p,atInfinity,hp,port⟩
        simp only [back,present,Bool.or_true,Bool.true_or]
    · have lne : l≠0 := by intro h;subst l;exact atInfinity member
      have present := (core x).1.mpr ⟨p,l,atInfinity,lne,member,hp,hl⟩
      simp only [front,back,present,Bool.true_or,and_self]
  · intro side S _
    let x := makeRow side S
    have independent (p l : Fin 13) (e : incident p l) :
        ¬(x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) := by
      cases side with
      | true =>
        simp only [x,makeRow,ite_true,Fin.append_left,Fin.append_right]
        rintro ⟨pIn,lFree⟩
        exact (of_decide_eq_true lFree p (of_decide_eq_true pIn)) e
      | false =>
        simp only [x,makeRow,Bool.false_eq_true,ite_false,Fin.append_left,Fin.append_right]
        rintro ⟨pFree,lIn⟩
        exact (of_decide_eq_true pFree l (of_decide_eq_true lIn)) e
    have zOff : D.eval (List.ofFn x)=false := by
      apply Bool.eq_false_of_not_eq_true
      intro bad
      obtain ⟨p,l,_,_,mem,px,lx⟩:=(core x).1.mp bad
      exact independent p l ((inc p l).mpr mem) ⟨px,lx⟩
    obtain ⟨front,back⟩:=last x
    change wireValue C 26 x (if x 13=true then a else b)=false
    cases latch : x 13 with
    | true =>
      have noPoint : ¬∃p∈singerLines3 0,x (Fin.castAdd 13 p)=true := by
        rintro ⟨p,atInf,on⟩
        exact independent p 0 ((inc p 0).mpr atInf) ⟨on,latch⟩
      simp only [latch,ite_true,front,zOff,Bool.false_or,decide_eq_false noPoint]
    | false =>
      have noDirection : ¬∃p∈singerLines3 0,x (Fin.castAdd 13 p)=true ∧ wireValue D 26 x (d p)=true := by
        rintro ⟨p,atInf,on,port⟩
        obtain ⟨l,_,e,selected⟩:=((core x).2 p atInf).mp port
        exact independent p l ((inc _ _).mpr e) ⟨on,selected⟩
      simp only [latch,Bool.false_eq_true,ite_false,back,zOff,Bool.false_or,Bool.or_false,decide_eq_false noDirection]
