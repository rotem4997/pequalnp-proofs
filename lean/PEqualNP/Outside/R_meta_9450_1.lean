import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_9450_1
    (first : ∃ C : Circuit, C.size ≤ 28 ∧ IsAO2 27 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 27 ≤ C.output ∧ C.output < 27+C.size ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x ++ [x 1 || x 2])=true ↔ ∃ p l : Fin 13, l.val ∈ ([0,2,5,6,11,12] : List Nat) ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)
    (second : ∀ m : Nat, ∃ D : Circuit, D.size ≤ 29 ∧ IsAO2 (27+m) D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ 27+m ≤ D.output ∧ D.output < 27+m+D.size ∧
      ∀ (x : Fin 26 → Bool) (t : List Bool), t.length=m →
        (D.eval ((List.ofFn x ++ [x 1 || x 2]) ++ t)=true ↔ ∃ p l : Fin 13, l.val ∈ ([3,4,7,8,9,10] : List Nat) ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)) :
have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool) (x4 : Fin ((27 : ℕ) + x2.size)) (x5 : List (Fin ((27 : ℕ) + x2.size))),   x5 ≠ [] ∧     (x4 :: x5).Nodup ∧       x2.size + x5.length ≤ (58 : ℕ) ∧         PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧           (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧             ∀ (x6 : Fin (26 : ℕ) → Bool),               Minimal x1 x6 ∨ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x1 x7) x6 →                 have x8 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (1 : Fin (26 : ℕ)) || x6 (2 : Fin (26 : ℕ))]);                 (if x3 = Bool.true then (x4 :: x5).any fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false else (x4 :: x5).all fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false) = Bool.true ↔ x1 x6 := by

  classical
  obtain ⟨A,ha,hA,ndA,loA,upA,funA⟩ := first
  obtain ⟨B,hb,hB,ndB,loB,upB,funB⟩ := second A.size
  let C : Circuit := ⟨A.gates ++ B.gates,0⟩
  let step := fun (u : List Bool) (g : Gate) =>
    u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  have sz : C.size=A.size+B.size := by
    change (A.gates++B.gates).length=A.gates.length+B.gates.length
    exact List.length_append
  have len (gs : List Gate) (u : List Bool) :
      (gs.foldl step u).length=u.length+gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have keep (gs : List Gate) (u : List Bool) (i : Nat) (hi : i<u.length) :
      (gs.foldl step u).getD i false=u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step u g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have extension (gs : List Gate) (u : List Bool) :
      ∃ t : List Bool, t.length=gs.length ∧ gs.foldl step u=u++t := by
    induction gs generalizing u with
    | nil => exact ⟨[],rfl,by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht,he⟩ := ih (step u g)
      refine ⟨[g.op.eval (g.inputs.map fun i => u.getD i false)]++t,?_,?_⟩
      · simp [ht]
      · simpa [List.foldl_cons,step,List.append_assoc] using he
  have ao : IsAO2 27 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg|hg
      · exact hA.1 g hg
      · exact hB.1 g hg
    · intro j hj w hw
      by_cases before : j<A.gates.length
      · have eqg : gateAt C j=gateAt A j := by
          change (A.gates++B.gates).getD j ⟨GateOp.or,[]⟩=A.gates.getD j ⟨GateOp.or,[]⟩
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left before]
        rw [eqg] at hw
        exact hA.2.1 j before w hw
      · have after : A.gates.length ≤ j := by omega
        have eqg : gateAt C j=gateAt B (j-A.gates.length) := by
          change (A.gates++B.gates).getD j ⟨GateOp.or,[]⟩=B.gates.getD (j-A.gates.length) ⟨GateOp.or,[]⟩
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right after]
        rw [eqg] at hw
        have hj' : j<A.gates.length+B.gates.length := by simpa [C] using hj
        have bound := hB.2.1 (j-A.gates.length) (by omega) w hw
        change w<27+A.gates.length+(j-A.gates.length) at bound
        omega
    · intro g hg
      rcases List.mem_append.mp hg with hg|hg
      · exact hA.2.2 g hg
      · exact hB.2.2 g hg
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact ndA g hg
    · exact ndB g hg
  let a : Fin (27+C.size) := ⟨A.output,by omega⟩
  let b : Fin (27+C.size) := ⟨B.output,by omega⟩
  have ne : a≠b := by
    intro eq
    have eq' := congrArg Fin.val eq
    change A.output=B.output at eq'
    omega
  have split (x : Fin 26 → Bool) :
      (∃ p l : Fin 13, l≠1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
        x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) ↔
      (∃ p l : Fin 13, l.val ∈ ([0,2,5,6,11,12] : List Nat) ∧
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
        x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) ∨
      (∃ p l : Fin 13, l.val ∈ ([3,4,7,8,9,10] : List Nat) ∧
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
        x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) := by
    have sides : ∀ l : Fin 13, l≠1 ↔
        l.val ∈ ([0,2,5,6,11,12] : List Nat) ∨
        l.val ∈ ([3,4,7,8,9,10] : List Nat) := by decide +kernel
    constructor
    · rintro ⟨p,l,hl,hi,hp,he⟩
      rcases (sides l).mp hl with h|h
      · exact Or.inl ⟨p,l,h,hi,hp,he⟩
      · exact Or.inr ⟨p,l,h,hi,hp,he⟩
    · rintro (⟨p,l,hl,hi,hp,he⟩|⟨p,l,hl,hi,hp,he⟩)
      · exact ⟨p,l,(sides l).mpr (Or.inl hl),hi,hp,he⟩
      · exact ⟨p,l,(sides l).mpr (Or.inr hl),hi,hp,he⟩
  refine ⟨C,true,a,[b],by simp,?_,?_,ao,nd,?_⟩
  · simpa using ne
  · simp only [List.length_singleton]
    omega
  · intro x hx
    let u := List.ofFn x ++ [x 1 || x 2]
    obtain ⟨t,ht,he⟩ := extension A.gates u
    have evalB := funB x t ht
    have wiring : C.wires u=B.wires (A.wires u) := by
      change (A.gates++B.gates).foldl step u=B.gates.foldl step (A.gates.foldl step u)
      exact List.foldl_append
    have firstWire : (C.wires u).getD a.val false=A.eval u := by
      rw [wiring]
      change (B.gates.foldl step (A.wires u)).getD A.output false=_
      rw [keep _ _ _ (by
        change A.output<(A.gates.foldl step u).length
        rw [len]
        change A.output<27+A.gates.length at upA
        simpa [u] using upA)]
      rfl
    have secondWire : (C.wires u).getD b.val false=B.eval (u++t) := by
      rw [wiring]
      change B.eval (A.gates.foldl step u)=_
      rw [he]
    change ([a,b].any fun i => (C.wires u).getD i.val false)=true ↔ _
    simp only [List.any_cons,List.any_nil,Bool.or_false]
    rw [firstWire,secondWire,Bool.or_eq_true,funA x,evalB,← split x]
