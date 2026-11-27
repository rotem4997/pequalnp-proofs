import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7698_2
    (remaining : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, let first := PEqualNP.MetaComplexity.NestedCover.gateAt C 0; C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
  (∀ k < C.size, PEqualNP.TopForm.opnd C k 0 ≠ PEqualNP.TopForm.opnd C k 1) →
  first.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
  ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
  ∀ j < C.size, 0 < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  let a := PEqualNP.TopForm.opnd C j 0; let b := PEqualNP.TopForm.opnd C j 1;
  (let w0 := (C.wires (List.ofFn fun i : Fin 14 => decide (i = 0))); let w7 := (C.wires (List.ofFn fun i : Fin 14 => decide (i = 7))); let wp := (C.wires (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)));
  
  wp.getD a false = true ∧ wp.getD b false = true ∧
  ((w0.getD a false = false ∧ w0.getD b false = false) ∨ (w7.getD a false = false ∧ w7.getD b false = false)) ∧
  ((w0.getD a false = false ∧ w7.getD a false = false) ∨ (w0.getD b false = false ∧ w7.getD b false = false))) →
  ¬ ((first.inputs = [0,7] ∨ first.inputs = [7,0]) ∧ (a = 14 ∨ b = 14)) → False)
    (direct_case : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C → C.size ≤ 27 → (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
  ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
  ∀ j < C.size, 0 < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs = [0,7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs = [7,0]) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.TopForm.opnd C j 0 = 14 ∨ PEqualNP.TopForm.opnd C j 1 = 14) →
  (C.wires (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7))).getD (PEqualNP.TopForm.opnd C j 0) false = true → (C.wires (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7))).getD (PEqualNP.TopForm.opnd C j 1) false = true → False) :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        (∀ j < C.size, PEqualNP.TopForm.opnd C j (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd C j (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x : Fin (14 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p : Fin (7 : ℕ)) (l : Fin (7 : ℕ)),
            (p = l ∨ p = l + (1 : Fin (7 : ℕ)) ∨ p = l + (3 : Fin (7 : ℕ))) ∧
            x (Fin.castAdd (7 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) l) = Bool.true) →
        (∃ g < C.size, 0 < g ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          let w0 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (0 : Fin (14 : ℕ))))
          let w7 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (7 : Fin (14 : ℕ))))
          let w07 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (0 : Fin (14 : ℕ)) ∨ i = (7 : Fin (14 : ℕ))))
          let a := PEqualNP.TopForm.opnd C g (0 : Fin (2 : ℕ))
          let b := PEqualNP.TopForm.opnd C g (1 : Fin (2 : ℕ))
          w07.getD a Bool.false = Bool.true ∧ w07.getD b Bool.false = Bool.true ∧
          ((w0.getD a Bool.false = Bool.false ∧ w0.getD b Bool.false = Bool.false) ∨
           (w7.getD a Bool.false = Bool.false ∧ w7.getD b Bool.false = Bool.false)) ∧
          ((w0.getD a Bool.false = Bool.false ∧ w7.getD a Bool.false = Bool.false) ∨
           (w0.getD b Bool.false = Bool.false ∧ w7.getD b Bool.false = Bool.false))) →
        False := by
  classical
  intro C hs hAO hdistinct hfirst hcompute hwitness
  obtain ⟨j,hj,hpos,hgate,ha,hb,hleft,hemergent⟩ := hwitness
  by_cases hpair : ((PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs = [0,7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs = [7,0])
  · by_cases hdirect : (PEqualNP.TopForm.opnd C j 0 = 14 ∨ PEqualNP.TopForm.opnd C j 1 = 14)
    · exact direct_case C hAO hs hcompute j hj hpos hfirst hpair hgate hdirect ha hb
    · exact remaining C hs hAO hdistinct hfirst hcompute j hj hpos hgate
        ⟨ha,hb,hleft,hemergent⟩ (by simp [hdirect])
  · exact remaining C hs hAO hdistinct hfirst hcompute j hj hpos hgate
      ⟨ha,hb,hleft,hemergent⟩ (by simp [hpair])
