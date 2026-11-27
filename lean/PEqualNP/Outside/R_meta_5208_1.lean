import PEqualNP.Defs

-- Cut L-meta-5208 into three sharper structural cases by extracting forced 3-AND and 4-AND chains:
-- (1) k1 fires on singleton p13, forcing a cleaner AND gate k3 strictly between k1 and k2;
-- (2) k1 is false on p13 and k2 fires on singleton p0, forcing a pair-born AND gate k0 below k1
--     and a cleaner AND gate k4 above k2 (a 4-AND chain k0 < k1 < k2 < k4);
-- (3) both k1 and k2 are false on p0 and p13, forcing a pair-born AND gate k0 below k1
--     (a 3-AND chain k0 < k1 < k2 of strictly pair-active AND gates on p013).
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5208_1
    (hK1Single : ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) C;
      have gv : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C;
      have isA : ℕ → Prop := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      have live : ℕ → Prop := fun k => (26 : ℕ) + k = C.output ∨ ic k (C.output - (26 : ℕ));
      have p0 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
      have p13 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have p013 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have ok : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun k z =>
        isA k ∧ live k ∧ gv k p013 = Bool.true ∧
        ∀ b : Fin (2 : ℕ), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C k b) z = Bool.false;
      C.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
        ∃ (u v : Fin (13 : ℕ)), u - v ∈ D ∧
          x (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) v) = Bool.true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ (x : Fin (26 : ℕ) → Bool), gv d x = Bool.true ∧ C.eval (List.ofFn x) = Bool.false) ∧
      ∃ (k1 k3 k2 : ℕ),
        ic k1 k3 ∧ ic k3 k2 ∧
        ok k1 p0 ∧ gv k1 p13 = Bool.true ∧
        isA k3 ∧ gv k3 p13 = Bool.false ∧
        ok k2 p13)
    (hK2Single : ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) C;
      have gv : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C;
      have isA : ℕ → Prop := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      have live : ℕ → Prop := fun k => (26 : ℕ) + k = C.output ∨ ic k (C.output - (26 : ℕ));
      have p0 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
      have p13 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have p013 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have ok : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun k z =>
        isA k ∧ live k ∧ gv k p013 = Bool.true ∧
        ∀ b : Fin (2 : ℕ), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C k b) z = Bool.false;
      C.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
        ∃ (u v : Fin (13 : ℕ)), u - v ∈ D ∧
          x (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) v) = Bool.true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ (x : Fin (26 : ℕ) → Bool), gv d x = Bool.true ∧ C.eval (List.ofFn x) = Bool.false) ∧
      ∃ (k0 k1 k2 k4 : ℕ),
        ic k0 k1 ∧ ic k1 k2 ∧ ic k2 k4 ∧
        isA k0 ∧ gv k0 p013 = Bool.true ∧ gv k0 p0 = Bool.false ∧ gv k0 p13 = Bool.false ∧
        ok k1 p0 ∧ gv k1 p13 = Bool.false ∧
        ok k2 p13 ∧ gv k2 p0 = Bool.true ∧
        isA k4 ∧ live k4 ∧ gv k4 p0 = Bool.false)
    (hBothClean : ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      have D : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) C;
      have gv : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C;
      have isA : ℕ → Prop := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      have live : ℕ → Prop := fun k => (26 : ℕ) + k = C.output ∨ ic k (C.output - (26 : ℕ));
      have p0 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
      have p13 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have p013 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have ok : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun k z =>
        isA k ∧ live k ∧ gv k p013 = Bool.true ∧
        ∀ b : Fin (2 : ℕ), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C k b) z = Bool.false;
      C.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
        ∃ (u v : Fin (13 : ℕ)), u - v ∈ D ∧
          x (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) v) = Bool.true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ (x : Fin (26 : ℕ) → Bool), gv d x = Bool.true ∧ C.eval (List.ofFn x) = Bool.false) ∧
      ∃ (k0 k1 k2 : ℕ),
        ic k0 k1 ∧ ic k1 k2 ∧
        isA k0 ∧ gv k0 p013 = Bool.true ∧ gv k0 p0 = Bool.false ∧ gv k0 p13 = Bool.false ∧
        ok k1 p0 ∧ gv k1 p13 = Bool.false ∧
        ok k2 p13 ∧ gv k2 p0 = Bool.false) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x4 x10 x11 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  rintro ⟨C, hSize, hGates, hEval, hDirty, k1, k2, hCone12, hOk1, hOk2⟩
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let p0 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0
  let p13 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13
  let p013 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13
  -- Wire evaluation helpers
  let wstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hwfold_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl wstep w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (wstep w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      change gs.foldl wstep (wstep w g) = _
      rw [ht]; simp [wstep]
  have hwfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl wstep w).length = w.length + gs.length := by
    intro gs w; obtain ⟨t, ht, hl⟩ := hwfold_ext gs w; rw [ht, List.length_append, hl]
  have hwfold_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl wstep w).getD i false = w.getD i false := by
    intro gs w i hi; obtain ⟨t, ht, _⟩ := hwfold_ext gs w
    rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have hwfold_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate), gs[j]? = some g →
      (gs.foldl wstep w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl wstep w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; cases h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (wstep w g0).length := by simp [wstep]
        rw [hwfold_lt gs (wstep w g0) w.length hlt]
        have hself : (wstep w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) := by
          simp [wstep]
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, hwfold_lt gs (wstep w g0) i (by simp [wstep]; omega)]
          simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (wstep w g0).length + j' = w.length + (j' + 1) := by simp [wstep]; omega
        rw [List.foldl_cons, ← hlen]
        exact ih (wstep w g0) j' g hj
  have hwire_in : ∀ (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26),
      PEqualNP.CleanedNonEdge.wireVal 26 C w x = x ⟨w, hw⟩ := by
    intro x w hw
    change (C.gates.foldl wstep (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [hwfold_lt C.gates (List.ofFn x) w (by simp [hw]),
        List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
  have hwire_gate : ∀ (x : Fin 26 → Bool) (j : ℕ) (hj : j < C.gates.length),
      ∃ (a b : ℕ), C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧
        a < 26 + j ∧ b < 26 + j ∧
        PEqualNP.TopForm.opnd C j 0 = a ∧ PEqualNP.TopForm.opnd C j 1 = b ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal 26 C j x =
            (PEqualNP.CleanedNonEdge.wireVal 26 C a x && PEqualNP.CleanedNonEdge.wireVal 26 C b x)) ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          PEqualNP.EdgeOwnership.gateVal 26 C j x =
            (PEqualNP.CleanedNonEdge.wireVal 26 C a x || PEqualNP.CleanedNonEdge.wireVal 26 C b x)) := by
    intro x j hj
    have hgj : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
      exact List.getD_eq_getElem _ _ hj
    rw [hgat]
    obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates j C.gates[j] hgj
    refine ⟨a, b, hgj, hinp, ha, hb, ?_, ?_, ?_, ?_⟩
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a
      rw [hgat, hinp]; rfl
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b
      rw [hgat, hinp]; rfl
    · intro hand
      have hfg := hwfold_gate C.gates (List.ofFn x) j C.gates[j] hgj
      simp only [List.length_ofFn, hinp, hand, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb] at hfg
      change (C.gates.foldl wstep (List.ofFn x)).getD (26 + j) false =
        ((C.gates.foldl wstep (List.ofFn x)).getD a false &&
         ((C.gates.foldl wstep (List.ofFn x)).getD b false && true)) at hfg
      simp only [Bool.and_true] at hfg; exact hfg
    · intro hor
      have hfg := hwfold_gate C.gates (List.ofFn x) j C.gates[j] hgj
      simp only [List.length_ofFn, hinp, hor, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb] at hfg
      change (C.gates.foldl wstep (List.ofFn x)).getD (26 + j) false =
        ((C.gates.foldl wstep (List.ofFn x)).getD a false ||
         ((C.gates.foldl wstep (List.ofFn x)).getD b false || false)) at hfg
      simp only [Bool.or_false] at hfg; exact hfg
  -- Cone evaluation helpers (zero simp on coneStep/cones/InCone!)
  let cstep : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (List ℕ) :=
    PEqualNP.EdgeOwnership.coneStep 26
  have hcfold_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      ∃ t : List (List ℕ), gs.foldl cstep cs = cs ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro cs
      obtain ⟨t, ht, hl⟩ := ih (cstep cs g)
      refine ⟨((g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])) :: t, ?_, by simp [hl]⟩
      change gs.foldl cstep (cstep cs g) = _
      rw [ht]; change (cs ++ [_]) ++ t = _; rw [List.append_assoc]; rfl
  have hcfold_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl cstep cs).getD i [] = cs.getD i [] := by
    intro gs cs i hi; obtain ⟨t, ht, _⟩ := hcfold_ext gs cs
    rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have hcfold_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (j : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate), gs[j]? = some g →
      (gs.foldl cstep cs).getD (cs.length + j) [] =
        (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + (cs.length + j)))).flatMap
          (fun w => (w - 26) :: (gs.foldl cstep cs).getD (w - 26) []) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; cases h
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlen1 : (cstep cs g0).length = cs.length + 1 := by
          change (cs ++ [_]).length = cs.length + 1; simp
        rw [hcfold_lt gs (cstep cs g0) cs.length (by omega)]
        have hself : (cstep cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
              (fun w => (w - 26) :: cs.getD (w - 26) []) := by
          change (cs ++ [_]).getD cs.length [] = _; simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        congr 1
        have hwlt : w - 26 < cs.length := by omega
        rw [hcfold_lt gs (cstep cs g0) (w - 26) (by omega)]
        change cs.getD (w - 26) [] = (cs ++ [_]).getD (w - 26) []
        symm; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt, ← List.getD_eq_getElem?_getD]
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen1 : (cstep cs g0).length + j' = cs.length + (j' + 1) := by
          change (cs ++ [_]).length + j' = cs.length + (j' + 1); simp; omega
        rw [List.foldl_cons, ← hlen1]
        exact ih (cstep cs g0) j' g hj
  have hcones_len : (PEqualNP.EdgeOwnership.cones 26 C).length = C.gates.length := by
    obtain ⟨t, ht, hl⟩ := hcfold_ext C.gates []
    change (C.gates.foldl cstep []).length = C.gates.length
    rw [ht, List.nil_append, hl]
  have hcone_iff : ∀ (i j : ℕ), j < C.gates.length →
      (PEqualNP.EdgeOwnership.InCone 26 C i j ↔
        ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          26 ≤ w ∧ w < 26 + j ∧ (w - 26 = i ∨ PEqualNP.EdgeOwnership.InCone 26 C i (w - 26))) := by
    intro i j hj
    have hgj : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
      exact List.getD_eq_getElem _ _ hj
    have hfg := hcfold_gate C.gates [] j C.gates[j] hgj
    simp only [List.length_nil, Nat.zero_add] at hfg
    change i ∈ (C.gates.foldl cstep []).getD j [] ↔ _
    rw [hfg, hgat, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hiw⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hiw
      rcases hiw with rfl | hmem
      · exact ⟨w, hw.1, hw.2.1, hw.2.2, Or.inl rfl⟩
      · exact ⟨w, hw.1, hw.2.1, hw.2.2, Or.inr hmem⟩
    · rintro ⟨w, hw, hge, hlt, hcase⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, by simp [hge, hlt]⟩, List.mem_cons.mpr ?_⟩
      rcases hcase with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr hmem
  have hcone_lt : ∀ (i j : ℕ), PEqualNP.EdgeOwnership.InCone 26 C i j → i < j ∧ j < C.gates.length := by
    intro i j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hic
      have hjl : j < C.gates.length := by
        by_contra hge
        have hnone : (PEqualNP.EdgeOwnership.cones 26 C)[j]? = none :=
          List.getElem?_eq_none (by rw [hcones_len]; omega)
        change i ∈ (PEqualNP.EdgeOwnership.cones 26 C).getD j [] at hic
        rw [List.getD_eq_getElem?_getD, hnone] at hic
        cases hic
      obtain ⟨w, _, hge, hlt, hcase⟩ := (hcone_iff i j hjl).mp hic
      rcases hcase with rfl | hsub
      · exact ⟨by omega, hjl⟩
      · have := ih (w - 26) (by omega) hsub
        exact ⟨by omega, hjl⟩
  have hcone_trans : ∀ (i j m : ℕ),
      PEqualNP.EdgeOwnership.InCone 26 C i j → PEqualNP.EdgeOwnership.InCone 26 C j m →
      PEqualNP.EdgeOwnership.InCone 26 C i m := by
    intro i j m hij hjm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have hml : m < C.gates.length := (hcone_lt j m hjm).2
      obtain ⟨w, hw, hge, hlt, hcase⟩ := (hcone_iff j m hml).mp hjm
      refine (hcone_iff i m hml).mpr ⟨w, hw, hge, hlt, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 26) (by omega) hsub
  -- Key Lemma 1 (Cleaner extraction): if InCone i m, gv i x = true, gv m x = false,
  -- then some AND gate k' has InCone i k', (k' = m ∨ InCone k' m), and gv k' x = false.
  have hCleaner : ∀ (x : Fin 26 → Bool) (i m : ℕ),
      PEqualNP.EdgeOwnership.InCone 26 C i m →
      PEqualNP.EdgeOwnership.gateVal 26 C i x = true →
      PEqualNP.EdgeOwnership.gateVal 26 C m x = false →
      ∃ k' : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C k').op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C i k' ∧
        (k' = m ∨ PEqualNP.EdgeOwnership.InCone 26 C k' m) ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k' x = false := by
    intro x i m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro him hti hfm
      have hml : m < C.gates.length := (hcone_lt i m him).2
      obtain ⟨a, b, hgm, hinp, ha, hb, _, _, _, hor⟩ := hwire_gate x m hml
      have hmg_op := (hGates m _ hgm).1
      rcases hmg_op with hand | horop
      · exact ⟨m, hand, him, Or.inl rfl, hfm⟩
      · have hev := hor horop
        rw [hfm] at hev
        have hfa : PEqualNP.CleanedNonEdge.wireVal 26 C a x = false := by
          cases ha_v : PEqualNP.CleanedNonEdge.wireVal 26 C a x
          · rfl
          · rw [ha_v] at hev; cases hev
        have hfb : PEqualNP.CleanedNonEdge.wireVal 26 C b x = false := by
          cases hb_v : PEqualNP.CleanedNonEdge.wireVal 26 C b x
          · rfl
          · rw [hb_v, Bool.or_true] at hev; cases hev
        obtain ⟨w, hw, hge, hlt, hcase⟩ := (hcone_iff i m hml).mp him
        rw [hinp] at hw
        have hfw : PEqualNP.EdgeOwnership.gateVal 26 C (w - 26) x = false := by
          have hw_eq : 26 + (w - 26) = w := by omega
          change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + (w - 26)) x = false
          rw [hw_eq]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hfa
          · exact hfb
        rcases hcase with heq | hsub
        · rw [heq] at hfw; rw [hti] at hfw; cases hfw
        · obtain ⟨k', hk'op, hik', hk'w, hk'f⟩ := ih (w - 26) (by omega) hsub hti hfw
          refine ⟨k', hk'op, hik', Or.inr ?_, hk'f⟩
          refine (hcone_iff k' m hml).mpr ⟨w, by rw [hinp]; exact hw, hge, hlt, ?_⟩
          rcases hk'w with rfl | hkw
          · exact Or.inl rfl
          · exact Or.inr hkw
  -- Key Lemma 2 (Pair-born AND extraction): any wire true on p013 and false on both p0 and p13
  -- contains an AND gate k0 with the same property!
  have hPairBorn : ∀ (w : ℕ), w < 26 + C.gates.length →
      PEqualNP.CleanedNonEdge.wireVal 26 C w p013 = true →
      PEqualNP.CleanedNonEdge.wireVal 26 C w p0 = false →
      PEqualNP.CleanedNonEdge.wireVal 26 C w p13 = false →
      ∃ k0 : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C k0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (w = 26 + k0 ∨ (26 ≤ w ∧ PEqualNP.EdgeOwnership.InCone 26 C k0 (w - 26))) ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p013 = true ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p0 = false ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p13 = false := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwlt ht013 hf0 hf13
      by_cases hin : w < 26
      · rw [hwire_in p013 w hin] at ht013
        rw [hwire_in p0 w hin] at hf0
        rw [hwire_in p13 w hin] at hf13
        have h013 : w = 0 ∨ w = 13 := by
          change decide ((⟨w, hin⟩ : Fin 26) = 0 ∨ (⟨w, hin⟩ : Fin 26) = 13) = true at ht013
          simp only [decide_eq_true_eq, Fin.ext_iff] at ht013
          exact ht013
        rcases h013 with rfl | rfl
        · change decide ((0 : Fin 26) = 0 ∨ (0 : Fin 26) = 0) = false at hf0
          simp at hf0
        · change decide ((13 : Fin 26) = 13 ∨ (13 : Fin 26) = 13) = false at hf13
          simp at hf13
      · let j := w - 26
        have hjl : j < C.gates.length := by omega
        have hwj : w = 26 + j := by omega
        obtain ⟨a, b, hgj, hinp, ha, hb, _, _, _, hor013⟩ := hwire_gate p013 j hjl
        obtain ⟨a0, b0, hgj0, hinp0, _, _, _, _, _, hor0⟩ := hwire_gate p0 j hjl
        obtain ⟨a13, b13, hgj13, hinp13, _, _, _, _, _, hor13⟩ := hwire_gate p13 j hjl
        have hab0 : a0 = a ∧ b0 = b := by rw [hinp] at hinp0; injection hinp0 with h1 h2; injection h2 with h2'; exact ⟨h1.symm, h2'.symm⟩
        have hab13 : a13 = a ∧ b13 = b := by rw [hinp] at hinp13; injection hinp13 with h1 h2; injection h2 with h2'; exact ⟨h1.symm, h2'.symm⟩
        rcases (hGates j _ hgj).1 with hand | horop
        · refine ⟨j, hand, Or.inl hwj, ?_, ?_, ?_⟩
          · change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p013 = true; rw [← hwj]; exact ht013
          · change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p0 = false; rw [← hwj]; exact hf0
          · change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p13 = false; rw [← hwj]; exact hf13
        · have hv013 := hor013 horop
          have hv0 := hor0 horop; rw [hab0.1, hab0.2] at hv0
          have hv13 := hor13 horop; rw [hab13.1, hab13.2] at hv13
          have hjt013 : PEqualNP.EdgeOwnership.gateVal 26 C j p013 = true := by
            change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p013 = true; rw [← hwj]; exact ht013
          have hjf0 : PEqualNP.EdgeOwnership.gateVal 26 C j p0 = false := by
            change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p0 = false; rw [← hwj]; exact hf0
          have hjf13 : PEqualNP.EdgeOwnership.gateVal 26 C j p13 = false := by
            change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + j) p13 = false; rw [← hwj]; exact hf13
          rw [hjt013] at hv013; rw [hjf0] at hv0; rw [hjf13] at hv13
          have ha0 : PEqualNP.CleanedNonEdge.wireVal 26 C a p0 = false := by
            cases h : PEqualNP.CleanedNonEdge.wireVal 26 C a p0; rfl; rw [h] at hv0; cases hv0
          have hb0 : PEqualNP.CleanedNonEdge.wireVal 26 C b p0 = false := by
            cases h : PEqualNP.CleanedNonEdge.wireVal 26 C b p0; rfl; rw [h, Bool.or_true] at hv0; cases hv0
          have ha13 : PEqualNP.CleanedNonEdge.wireVal 26 C a p13 = false := by
            cases h : PEqualNP.CleanedNonEdge.wireVal 26 C a p13; rfl; rw [h] at hv13; cases hv13
          have hb13 : PEqualNP.CleanedNonEdge.wireVal 26 C b p13 = false := by
            cases h : PEqualNP.CleanedNonEdge.wireVal 26 C b p13; rfl; rw [h, Bool.or_true] at hv13; cases hv13
          have hab013 : PEqualNP.CleanedNonEdge.wireVal 26 C a p013 = true ∨
              PEqualNP.CleanedNonEdge.wireVal 26 C b p013 = true := by
            cases h1 : PEqualNP.CleanedNonEdge.wireVal 26 C a p013
            · rw [h1, Bool.false_or] at hv013; exact Or.inr hv013.symm
            · exact Or.inl rfl
          rcases hab013 with hat | hbt
          · obtain ⟨k0, hk0op, hk0w, hk0t, hk0f0, hk0f13⟩ := ih a (by omega) (by omega) hat ha0 ha13
            refine ⟨k0, hk0op, Or.inr ⟨by omega, ?_⟩, hk0t, hk0f0, hk0f13⟩
            refine (hcone_iff k0 j hjl).mpr ⟨a, by rw [hinp]; simp, ?_, ha, ?_⟩
            · rcases hk0w with rfl | ⟨hge, _⟩ <;> omega
            · rcases hk0w with rfl | ⟨_, hic⟩
              · exact Or.inl (by omega)
              · exact Or.inr hic
          · obtain ⟨k0, hk0op, hk0w, hk0t, hk0f0, hk0f13⟩ := ih b (by omega) (by omega) hbt hb0 hb13
            refine ⟨k0, hk0op, Or.inr ⟨by omega, ?_⟩, hk0t, hk0f0, hk0f13⟩
            refine (hcone_iff k0 j hjl).mpr ⟨b, by rw [hinp]; simp, ?_, hb, ?_⟩
            · rcases hk0w with rfl | ⟨hge, _⟩ <;> omega
            · rcases hk0w with rfl | ⟨_, hic⟩
              · exact Or.inl (by omega)
              · exact Or.inr hic
  -- Build IsAO2 and Nodup from hGates
  have hGateFacts : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2 ∧ g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hop, a, b, hinp, hne, _, _⟩ := hGates j g hj
    exact ⟨hop, by simp [hinp], by simp [hinp, hne]⟩
  have hAO2 : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hg => (hGateFacts g hg).1, ?_, fun g hg => (hGateFacts g hg).2.1⟩
    intro j hj w hw
    have hgj : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates j C.gates[j] hgj
    change w ∈ (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem _ _ hj, hinp] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl; exact ha; exact hb
  have hNodup : ∀ g ∈ C.gates, g.inputs.Nodup := fun g hg => (hGateFacts g hg).2.2
  -- Now split on gv k1 p13 and gv k2 p0!
  have hk2l : k2 < C.gates.length := (hcone_lt k1 k2 hCone12).2
  have hk1l : k1 < C.gates.length := by have := hcone_lt k1 k2 hCone12; omega
  cases hk1_13 : PEqualNP.EdgeOwnership.gateVal 26 C k1 p13
  · -- Case A: gv k1 p13 = false -> extract pair-born k0 < k1!
    obtain ⟨a1, b1, hgk1, hinp1, ha1, hb1, hop10, hop11, hand1_013, _⟩ := hwire_gate p013 k1 hk1l
    obtain ⟨a1', b1', _, hinp1', _, _, _, _, hand1_13, _⟩ := hwire_gate p13 k1 hk1l
    have hab1 : a1' = a1 ∧ b1' = b1 := by rw [hinp1] at hinp1'; injection hinp1' with h1 h2; injection h2 with h2'; exact ⟨h1.symm, h2'.symm⟩
    have hev013 := hand1_013 hOk1.1
    rw [hOk1.2.2.1] at hev013
    have ha1_013 : PEqualNP.CleanedNonEdge.wireVal 26 C a1 p013 = true := by
      cases h : PEqualNP.CleanedNonEdge.wireVal 26 C a1 p013; rw [h] at hev013; cases hev013; rfl
    have hb1_013 : PEqualNP.CleanedNonEdge.wireVal 26 C b1 p013 = true := by
      cases h : PEqualNP.CleanedNonEdge.wireVal 26 C b1 p013; rw [h, Bool.and_false] at hev013; cases hev013; rfl
    have ha1_0 : PEqualNP.CleanedNonEdge.wireVal 26 C a1 p0 = false := by
      rw [← hop10]; exact hOk1.2.2.2 0
    have hb1_0 : PEqualNP.CleanedNonEdge.wireVal 26 C b1 p0 = false := by
      rw [← hop11]; exact hOk1.2.2.2 1
    have hev13 := hand1_13 hOk1.1; rw [hab1.1, hab1.2, hk1_13] at hev13
    have hab1_13 : PEqualNP.CleanedNonEdge.wireVal 26 C a1 p13 = false ∨
        PEqualNP.CleanedNonEdge.wireVal 26 C b1 p13 = false := by
      cases h1 : PEqualNP.CleanedNonEdge.wireVal 26 C a1 p13
      · exact Or.inl rfl
      · rw [h1, Bool.true_and] at hev13; exact Or.inr hev13.symm
    have hk0_ex : ∃ k0 : ℕ,
        PEqualNP.EdgeOwnership.InCone 26 C k0 k1 ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p013 = true ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p0 = false ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k0 p13 = false := by
      rcases hab1_13 with ha1_13 | hb1_13
      · obtain ⟨k0, hk0op, hk0w, hk0t, hk0f0, hk0f13⟩ := hPairBorn a1 (by omega) ha1_013 ha1_0 ha1_13
        refine ⟨k0, (hcone_iff k0 k1 hk1l).mpr ⟨a1, by rw [hinp1]; simp, ?_, ha1, ?_⟩, hk0op, hk0t, hk0f0, hk0f13⟩
        · rcases hk0w with rfl | ⟨hge, _⟩ <;> omega
        · rcases hk0w with rfl | ⟨_, hic⟩; exact Or.inl (by omega); exact Or.inr hic
      · obtain ⟨k0, hk0op, hk0w, hk0t, hk0f0, hk0f13⟩ := hPairBorn b1 (by omega) hb1_013 hb1_0 hb1_13
        refine ⟨k0, (hcone_iff k0 k1 hk1l).mpr ⟨b1, by rw [hinp1]; simp, ?_, hb1, ?_⟩, hk0op, hk0t, hk0f0, hk0f13⟩
        · rcases hk0w with rfl | ⟨hge, _⟩ <;> omega
        · rcases hk0w with rfl | ⟨_, hic⟩; exact Or.inl (by omega); exact Or.inr hic
    obtain ⟨k0, hCone01, hk0op, hk0t, hk0f0, hk0f13⟩ := hk0_ex
    cases hk2_0 : PEqualNP.EdgeOwnership.gateVal 26 C k2 p0
    · -- Subcase A1: gv k2 p0 = false -> hBothClean!
      exact hBothClean ⟨C, hSize, hAO2, hNodup, hEval, hDirty, k0, k1, k2,
        hCone01, hCone12, hk0op, hk0t, hk0f0, hk0f13, hOk1, hk1_13, hOk2, hk2_0⟩
    · -- Subcase A2: gv k2 p0 = true -> extract cleaner AND gate k4 above k2 (4-AND chain!)
      have hev_p0 : C.eval (List.ofFn p0) = false := by
        cases h : C.eval (List.ofFn p0)
        · rfl
        · obtain ⟨u, v, _, _, hv⟩ := (hEval p0).mp h
          have hv' : (Fin.natAdd 13 v : Fin 26) = 0 := by
            change decide ((Fin.natAdd 13 v : Fin 26) = 0 ∨ (Fin.natAdd 13 v : Fin 26) = 0) = true at hv
            simp only [or_self, decide_eq_true_eq] at hv; exact hv
          have hvval := congrArg Fin.val hv'
          simp only [Fin.val_natAdd, Fin.val_zero] at hvval; omega
      have hne_out : 26 + k2 ≠ C.output := by
        intro heq
        have h1 : C.eval (List.ofFn p0) = PEqualNP.EdgeOwnership.gateVal 26 C k2 p0 := by
          change (C.wires (List.ofFn p0)).getD C.output false = (C.wires (List.ofFn p0)).getD (26 + k2) false
          rw [heq]
        rw [hev_p0, hk2_0] at h1; cases h1
      have hCone2Out : PEqualNP.EdgeOwnership.InCone 26 C k2 (C.output - 26) :=
        hOk2.2.1.resolve_left hne_out
      have hout_ge : 26 ≤ C.output := by
        by_contra hlt
        have hz : C.output - 26 = 0 := by omega
        rw [hz] at hCone2Out
        have := (hcone_lt k2 0 hCone2Out).1; omega
      have hout_f : PEqualNP.EdgeOwnership.gateVal 26 C (C.output - 26) p0 = false := by
        change (C.wires (List.ofFn p0)).getD (26 + (C.output - 26)) false = false
        rw [Nat.add_sub_of_le hout_ge]; exact hev_p0
      obtain ⟨k4, hk4op, hCone24, hk4out, hk4f0⟩ := hCleaner p0 k2 (C.output - 26) hCone2Out hk2_0 hout_f
      have hk4_live : 26 + k4 = C.output ∨ PEqualNP.EdgeOwnership.InCone 26 C k4 (C.output - 26) := by
        rcases hk4out with heq | hic
        · left; omega
        · right; exact hic
      exact hK2Single ⟨C, hSize, hAO2, hNodup, hEval, hDirty, k0, k1, k2, k4,
        hCone01, hCone12, hCone24, hk0op, hk0t, hk0f0, hk0f13, hOk1, hk1_13, hOk2, hk2_0,
        hk4op, hk4_live, hk4f0⟩
  · -- Case B: gv k1 p13 = true -> extract cleaner AND gate k3 strictly between k1 and k2!
    obtain ⟨a2, b2, _, hinp2, _, _, hop20, hop21, _, _⟩ := hwire_gate p13 k2 hk2l
    obtain ⟨w, hw, hge, hlt, hcase⟩ := (hcone_iff k1 k2 hk2l).mp hCone12
    rw [hinp2] at hw
    have hfw13 : PEqualNP.EdgeOwnership.gateVal 26 C (w - 26) p13 = false := by
      have hw_eq : 26 + (w - 26) = w := by omega
      change PEqualNP.CleanedNonEdge.wireVal 26 C (26 + (w - 26)) p13 = false
      rw [hw_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [← hop20]; exact hOk2.2.2.2 0
      · rw [← hop21]; exact hOk2.2.2.2 1
    rcases hcase with heq | hsub
    · rw [heq] at hfw13; rw [hk1_13] at hfw13; cases hfw13
    · obtain ⟨k3, hk3op, hCone13, hk3w, hk3f13⟩ := hCleaner p13 k1 (w - 26) hsub hk1_13 hfw13
      have hCone32 : PEqualNP.EdgeOwnership.InCone 26 C k3 k2 := by
        refine (hcone_iff k3 k2 hk2l).mpr ⟨w, by rw [hinp2]; exact hw, hge, hlt, ?_⟩
        rcases hk3w with rfl | hic
        · exact Or.inl rfl
        · exact Or.inr hic
      exact hK1Single ⟨C, hSize, hAO2, hNodup, hEval, hDirty, k1, k3, k2,
        hCone13, hCone32, hOk1, hk1_13, hk3op, hk3f13, hOk2⟩
