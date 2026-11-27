import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6066_1
    (h63 : ∀ (x1 : Circuit), x1.size = 63 → 26 ≤ x1.output → x1.output < 26 + x1.size →
      PEqualNP.TopForm.IsAO2 26 x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      (∀ (x6 : Fin 26 → Bool), x1.eval (List.ofFn x6) = true ↔
        ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧
          x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      PEqualNP.ReadK.lineSingle x1 26 (fun x7 => decide (x7 = 13)) 0 13 = false →
      PEqualNP.ReadK.lineSingle x1 26 (fun x8 => decide (x8 = 0)) 13 0 = false →
      let x9 : Finset ℕ → ℕ → Bool := fun x9 => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW 26 x9)
      let x10 : ℕ → ℕ → Prop := fun x10 x11 => ∃ x12 x13 x14 x15, x1.gates[x12]? = some x13 ∧ x11 = 26 + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = GateOp.or ∧ x10 = if x9 {0, 13} x14 = true then x14 else x15) ∧ x9 {0, 13} x10 = true ∧ x9 {0, 13} x11 = true
      let x11 : ℕ → ℕ → Prop := fun x11 x12 => Relation.ReflTransGen x10 (26 + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {0, 13} x13 = true ∧ x9 {x11} x13 = false
      (∃ x12 x13, x12 ≠ x13 ∧ x11 0 x12 ∧ x11 13 x13 ∧ x9 {13} (26 + x12) = false ∧ x9 {0} (26 + x13) = false) → False)
    (h64 : ∀ (x1 : Circuit), x1.size = 64 → 26 ≤ x1.output → x1.output < 26 + x1.size →
      PEqualNP.TopForm.IsAO2 26 x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      (∀ (x6 : Fin 26 → Bool), x1.eval (List.ofFn x6) = true ↔
        ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧
          x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      PEqualNP.ReadK.lineSingle x1 26 (fun x7 => decide (x7 = 13)) 0 13 = false →
      PEqualNP.ReadK.lineSingle x1 26 (fun x8 => decide (x8 = 0)) 13 0 = false →
      let x9 : Finset ℕ → ℕ → Bool := fun x9 => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW 26 x9)
      let x10 : ℕ → ℕ → Prop := fun x10 x11 => ∃ x12 x13 x14 x15, x1.gates[x12]? = some x13 ∧ x11 = 26 + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = GateOp.or ∧ x10 = if x9 {0, 13} x14 = true then x14 else x15) ∧ x9 {0, 13} x10 = true ∧ x9 {0, 13} x11 = true
      let x11 : ℕ → ℕ → Prop := fun x11 x12 => Relation.ReflTransGen x10 (26 + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {0, 13} x13 = true ∧ x9 {x11} x13 = false
      (∃ x12 x13, x12 ≠ x13 ∧ x11 0 x12 ∧ x11 13 x13 ∧ x9 {13} (26 + x12) = false ∧ x9 {0} (26 + x13) = false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size → x1.size ≤ (64 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false → have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9); have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true; have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false; (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) = Bool.false ∧ x9 {(0 : ℕ)} ((26 : ℕ) + x13) = Bool.false) → False := by
  intro x1 hs1 hs2 hAO hNodup hSpec hL1 hL2 x9 x10 x11 hWit
  have hWiresLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp; omega
  have hWiresPrefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih _ _ (by simp; omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp [List.getElem?_append_left hi]
  have hOutLt : x1.output < 26 + x1.size := by
    by_contra hge
    have hle : 26 + x1.size ≤ x1.output := Nat.le_of_not_lt hge
    let f00 : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13))
    have hTrue : x1.eval (List.ofFn f00) = true := (hSpec f00).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    unfold Circuit.eval Circuit.wires at hTrue
    have hLen26 : (List.ofFn f00).length = 26 := by simp
    have hFullLen : (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn f00)).length = 26 + x1.size := by
      rw [hWiresLen, hLen26]; rfl
    rw [List.getD_eq_default _ _ (by rw [hFullLen]; exact hle)] at hTrue
    cases hTrue
  have hOutGe : 26 ≤ x1.output := by
    by_contra hlt
    have hlt26 : x1.output < 26 := Nat.lt_of_not_ge hlt
    let fAll : Fin 26 → Bool := fun k => decide (k.val = x1.output)
    have hEval : x1.eval (List.ofFn fAll) = true := by
      unfold Circuit.eval Circuit.wires
      rw [hWiresPrefix _ _ _ (by simp [hlt26])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hlt26, fAll]
    have hEdge := (hSpec fAll).mp hEval
    rcases hEdge with ⟨a, b, _, ha, hb⟩
    simp only [fAll, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at ha hb
    omega
  have hCases : x1.size = 63 ∨ x1.size = 64 := by omega
  rcases hCases with hs | hs
  · exact h63 x1 hs hOutGe hOutLt hAO hNodup hSpec hL1 hL2 hWit
  · exact h64 x1 hs hOutGe hOutLt hAO hNodup hSpec hL1 hL2 hWit
