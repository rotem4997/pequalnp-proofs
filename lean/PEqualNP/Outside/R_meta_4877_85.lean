import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK PEqualNP.GenericRejection PEqualNP.HeptadCover
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4877_85
    (findFlag : ∃ (C : Circuit) (p l : Fin 13), C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ComputesIncidence singerLines3 C ∧ p ∈ singerLines3 l ∧ (∀ m ∈ [p.val,13+l.val], lineSingle C 26 (fun i => decide (i=m)) p.val (13+l.val) = false))
    (relocate : ∀ (C : Circuit) (p l : Fin 13), IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence singerLines3 C →
      p ∈ singerLines3 l → (∀ m ∈ [p.val,13+l.val], lineSingle C 26 (fun i => decide (i=m)) p.val (13+l.val) = false) → ∃ D : Circuit, D.size=C.size ∧ IsAO2 26 D ∧ (∀ g ∈ D.gates,g.inputs.Nodup) ∧
        ComputesIncidence singerLines3 D ∧ (∀ m ∈ [0,13], lineSingle D 26 (fun i => decide (i=m)) 0 13 = false))
    (dual : ∀ C : Circuit, IsAO2 26 C → (∀ m ∈ [0,13], lineSingle C 26 (fun i => decide (i=m)) 0 13 = false) → ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       C.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := C.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 C.output = Bool.false) : have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧             ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       x4.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 x4.output = Bool.false := by

  intro free pack singleton
  obtain ⟨C,p,l,size,ao,nd,funC,edge,bad⟩ := findFlag
  obtain ⟨D,sz,legal,dist,exactD,zero⟩ := relocate C p l ao nd funC edge bad
  have value (X Y : Fin 13 → Bool) : D.eval (pack X Y) = true ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ X p = true ∧ Y l = true := by
    let a := Finset.univ.filter fun i => X i = true
    let b := Finset.univ.filter fun i => Y i = true
    have split : pack X Y = List.ofFn X ++ List.ofFn Y := by
      change List.ofFn (Fin.append X Y) = _
      exact List.ofFn_fin_append X Y
    have lhs : incidenceInput a b = pack X Y := by
      rw [split]
      change (List.ofFn (fun i => decide (i∈a)) ++ List.ofFn (fun i => decide (i∈b))) = _
      simp [a,b]
    rw [←lhs,exactD]
    change decide (∃ p ∈ a, ∃ l ∈ b, p ∈ singerLines3 l) = true ↔ _
    simp only [decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and,a,b]
    grind
  refine ⟨D,by omega,legal,dist,?_,?_,dual D legal zero⟩
  · intro p l h
    have inc : ∀ p l : Fin 13, free (singleton p) l = false → p ∈ singerLines3 l := by decide +kernel
    exact (value _ _).mpr ⟨p,l,inc p l h,by simp [singleton],by simp [singleton]⟩
  · intro f _
    have plus : ∀ p l : Fin 13, p ∈ singerLines3 l → p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9 := by decide +kernel
    have minus : ∀ p l : Fin 13, p ∈ singerLines3 l → l=p ∨ l=p-1 ∨ l=p-3 ∨ l=p-9 := by decide +kernel
    constructor
    · apply Bool.eq_false_of_not_eq_true
      intro h
      obtain ⟨p,l,edge,on,off⟩ := (value _ _).mp h
      change !(f l || f (l+1) || f (l+3) || f (l+9)) = true at off
      rcases plus p l edge with rfl|rfl|rfl|rfl <;> simp [on] at off
    · apply Bool.eq_false_of_not_eq_true
      intro h
      obtain ⟨p,l,edge,off,on⟩ := (value _ _).mp h
      rcases minus p l edge with rfl|rfl|rfl|rfl <;> simp [on] at off
