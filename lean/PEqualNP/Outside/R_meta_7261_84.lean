import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.HeptadCover
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_7261_84
    (body : ∃ D : Circuit, D.size ≤ 58 ∧ IsAO2 29 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      29 ≤ D.output ∧ D.output < 29+D.size ∧
      ∀ x : Fin 26 → Bool,
        let a := x 0 || x 1
        let b := x 3 || x 9
        D.eval (List.ofFn x ++ [a,b,a || b]) = true ↔
          ∃ p l : Fin 13, l ≠ 0 ∧ p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (assembly : ∀ D : Circuit, IsAO2 29 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
      29 ≤ D.output → D.output < 29+D.size →
      ∃ (C : Circuit) (j a b : ℕ), C.size = D.size+6 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output=26+j ∧ C.gates[j]? = some ⟨.and,[a,b]⟩ ∧
        ∀ x : Fin 26 → Bool,
          let u := x 0 || x 1
          let v := x 3 || x 9
          let z := D.eval (List.ofFn x ++ [u,v,u || v])
          wireValue C 26 x a = (z || (u || v)) ∧ wireValue C 26 x b = (z || x 13)) : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Bool) (x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x7 x8) (if x2 x7 x8 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by

  intro edge row
  obtain ⟨D,size,legal,distinct,lo,hi,fn⟩ := body
  obtain ⟨C,j,a,b,sz,ao,nd,out,gate,signals⟩ := assembly D legal distinct lo hi
  have incidence : ∀ u v : Fin 13, edge u v ↔ u ∈ singerLines3 v := by decide +kernel
  refine ⟨C,j,a,b,by omega,ao,nd,out,gate,?_,?_⟩
  have flags (u v : Fin 13) (x : Fin 26 → Bool)
      (hu : x (Fin.castAdd 13 u)=true) (hv : x (Fin.natAdd 13 v)=true) (e : edge u v) :
      wireValue C 26 x a = true ∧ wireValue C 26 x b = true := by
    obtain ⟨ha,hb⟩ := signals x
    rw [ha,hb]
    by_cases z : v=0
    · subst v
      have u0 : u=0 ∨ u=1 ∨ u=3 ∨ u=9 := by
        simpa only [edge,show (0:Fin 13)+1=1 by decide,show (0:Fin 13)+3=3 by decide,show (0:Fin 13)+9=9 by decide] using e
      have h13 : x 13=true := hv
      rcases u0 with rfl|rfl|rfl|rfl <;>
        first | change x 0=true at hu | change x 1=true at hu | change x 3=true at hu | change x 9=true at hu
      all_goals simp [hu,h13]
    · have yes := (fn x).mpr ⟨u,v,z,(incidence _ _).mp e,hu,hv⟩
      simp only [yes,Bool.true_or,true_and]
  · intro u v e
    exact flags u v _ (by simp) (by simp) e
  · intro side s _
    let x := row side s
    have independent (u v : Fin 13) (e : edge u v) :
        ¬(x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true) := by
      cases side with
      | true =>
        simp only [x,row,ite_true,Fin.append_left,Fin.append_right]
        rintro ⟨hu,hv⟩
        exact (of_decide_eq_true hv u (of_decide_eq_true hu)) e
      | false =>
        simp only [x,row,Bool.false_eq_true,ite_false,Fin.append_left,Fin.append_right]
        rintro ⟨hu,hv⟩
        exact (of_decide_eq_true hu v (of_decide_eq_true hv)) e
    let z := D.eval (List.ofFn x ++ [x 0 || x 1,x 3 || x 9,(x 0 || x 1) || (x 3 || x 9)])
    have off : z = false := by
      apply Bool.eq_false_of_not_eq_true
      intro on
      obtain ⟨u,v,_,e,hu,hv⟩ := (fn x).mp on
      exact independent u v ((incidence _ _).mpr e) ⟨hu,hv⟩
    obtain ⟨ha,hb⟩ := signals x
    change wireValue C 26 x a = (z || ((x 0 || x 1) || (x 3 || x 9))) at ha
    change wireValue C 26 x b = (z || x 13) at hb
    change wireValue C 26 x (if x 13 = true then a else b) = false
    cases line : x 13 with
    | false => simpa [line,off] using hb
    | true =>
      have empty (u : Fin 13) (e : edge u 0) : x (Fin.castAdd 13 u) = false :=
        Bool.eq_false_of_not_eq_true (fun hu => independent u 0 e ⟨hu,line⟩)
      have e0 : x 0 = false := empty 0 (by decide)
      have e1 : x 1 = false := empty 1 (by decide)
      have e3 : x 3 = false := empty 3 (by decide)
      have e9 : x 9 = false := empty 9 (by decide)
      simpa only [line,ite_true,off,e0,e1,e3,e9,Bool.false_or] using ha
