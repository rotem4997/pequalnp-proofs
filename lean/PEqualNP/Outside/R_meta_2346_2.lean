import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

-- Eliminate non-edge first AND gates (shrinking size to at most 26, or at most 24 on AND collapse)
-- and reduce edge first AND gates to four flag-stabilizer orbit representatives.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2346_2
    (noSmall24 :
      ∀ D : Circuit, D.size ≤ 24 → IsAO2 14 D →
        (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        False)
    (noDouble26 :
      ∀ D : Circuit, D.size ≤ 26 → IsAO2 14 D →
        (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        ¬ IsSingleRead D 14 (fun i => decide (7 ≤ i)) [(0, 7)] →
        False)
    (noFourEdges :
      ∀ D : Circuit, D.size ≤ 27 → IsAO2 14 D →
        (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
        (∃ p ∈ ([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)),
          gateAt D 0 = ⟨GateOp.and, [p.1, p.2]⟩) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        ¬ IsSingleRead D 14 (fun i => decide (7 ≤ i)) [(0, 7)] →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C hSize hAO hDist hFirst hFano hDeriv
  -- Basic foldl helpers for Circuit.wires and linearParts
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have gate_inputs2 : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.size,
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
      ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧
      opnd D j 0 < 14 + j ∧ opnd D j 1 < 14 + j := by
    intro D hD j hj
    have hmem : gateAt D j ∈ D.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hlen : (gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt D j).inputs = [a, b] := by
      cases h : (gateAt D j).inputs with
      | nil => simp [h] at hlen
      | cons a l1 =>
        cases l1 with
        | nil => simp [h] at hlen
        | cons b l2 =>
          cases l2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [h] at hlen
    have ha : opnd D j 0 = a := by unfold opnd; rw [hab]; rfl
    have hb : opnd D j 1 = b := by unfold opnd; rw [hab]; rfl
    refine ⟨by rw [hab, ha, hb], hD.1 _ hmem, ?_, ?_⟩
    · rw [ha]; exact hD.2.1 j hj a (by simp [hab])
    · rw [hb]; exact hD.2.1 j hj b (by simp [hab])
  have wire_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      (D.wires (List.ofFn x)).getD r false = x ⟨r, hr⟩ := by
    intro D x r hr
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt _ _ r (by simpa using hr), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wire_gate : ∀ (D : Circuit), IsAO2 14 D → ∀ (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.size),
      (D.wires (List.ofFn x)).getD (14 + j) false =
        (gateAt D j).op.eval
          [(D.wires (List.ofFn x)).getD (opnd D j 0) false,
           (D.wires (List.ofFn x)).getD (opnd D j 1) false] := by
    intro D hD x j hj
    have hj' : j < D.gates.length := hj
    obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 D hD j hj
    have hgj : D.gates[j] = gateAt D j := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj']
    have hsplit : D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
      rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
    let pref := (D.gates.take j).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + j := by
      dsimp only [pref]; rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hwstep_len : (wstep pref (gateAt D j)).length = 14 + j + 1 := by
      simp only [wstep, List.length_append, List.length_singleton, hpref_len]
    have hwires : D.wires (List.ofFn x) =
        (D.gates.drop (j + 1)).foldl wstep (wstep pref (gateAt D j)) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + j, pref.getD i false = (D.wires (List.ofFn x)).getD i false := by
      intro i hi
      rw [hwires, wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) i (by omega)]
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.length)]
    conv_lhs => rw [hwires]
    rw [wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) (14 + j) (by omega)]
    have hstep_at : (wstep pref (gateAt D j)).getD (14 + j) false =
        (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]; simp
    rw [hstep_at, hinp]
    simp only [List.map_cons, List.map_nil, hpref_get _ ha, hpref_get _ hb]
  -- Monotonicity of any IsAO2 14 circuit
  have eval_mono : ∀ (D : Circuit), IsAO2 14 D → ∀ (x y : Fin 14 → Bool),
      (∀ i, x i = true → y i = true) →
      ∀ r < 14 + D.size, (D.wires (List.ofFn x)).getD r false = true →
        (D.wires (List.ofFn y)).getD r false = true := by
    intro D hD x y hxy r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr hx
      by_cases h14 : r < 14
      · rw [wire_input D x r h14] at hx
        rw [wire_input D y r h14]
        exact hxy ⟨r, h14⟩ hx
      · let j := r - 14
        have hj : j < D.size := by omega
        have hrj : r = 14 + j := by omega
        rw [hrj] at hx ⊢
        obtain ⟨_, hop, ha, hb⟩ := gate_inputs2 D hD j hj
        rw [wire_gate D hD x j hj] at hx
        rw [wire_gate D hD y j hj]
        rcases hop with hand | hor
        · rw [hand, eval_and, Bool.and_eq_true] at hx ⊢
          exact ⟨ih _ (by omega) (by omega) hx.1, ih _ (by omega) (by omega) hx.2⟩
        · rw [hor, eval_or, Bool.or_eq_true] at hx ⊢
          rcases hx with h1 | h2
          · exact Or.inl (ih _ (by omega) (by omega) h1)
          · exact Or.inr (ih _ (by omega) (by omega) h2)
  -- Equivalence between linearParts / lineSingle and the witness recurrence for IsAO2 14 circuits
  let lpStep : List (Bool × Bool) → Gate → List (Bool × Bool) := fun w g =>
    let ins := g.inputs.map fun i => w.getD i (false, false)
    w ++ [GateOp.casesOn g.op
      (ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
      (ins.any (·.1), ins.any (·.2))
      (false, false)
      (fun _ => (false, false))
      (false, false)]
  have linearParts_eq_foldl : ∀ (D : Circuit) (isL : ℕ → Bool) (x : List Bool),
      linearParts D isL x = D.gates.foldl lpStep
        ((x.zipIdx).map fun p => if isL p.2 then (false, p.1) else (p.1, false)) := by
    intro D isL x
    unfold linearParts
    congr 1
    funext w g
    dsimp only [lpStep]
    cases g.op <;> rfl
  have lpfold_len : ∀ (gs : List Gate) (xs : List (Bool × Bool)),
      (gs.foldl lpStep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, lpStep, List.length_append, List.length_cons, List.length_nil]
      omega
  have lpfold_getD_lt : ∀ (gs : List Gate) (xs : List (Bool × Bool)) (r : ℕ),
      r < xs.length → (gs.foldl lpStep xs).getD r (false, false) = xs.getD r (false, false) := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (lpStep xs g).length := by
        simp only [lpStep, List.length_append, List.length_singleton]; omega
      rw [ih (lpStep xs g) r hr']
      simp only [lpStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have lp_eq_witness : ∀ (D : Circuit), IsAO2 14 D → ∀ (s : Bool) (v : ℕ → Bool),
      let W := D.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
      (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
      (∀ j < D.size,
        ((gateAt D j).op = GateOp.and →
          v (14 + j) = ((W.getD (opnd D j 0) false && v (opnd D j 1)) ||
            (v (opnd D j 0) && W.getD (opnd D j 1) false))) ∧
        ((gateAt D j).op = GateOp.or →
          v (14 + j) = (v (opnd D j 0) || v (opnd D j 1)))) →
      let isL : ℕ → Bool := if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))
      let lp := linearParts D isL ((List.range 14).map fun i => i == 0 || i == 7)
      ∀ r < 14 + D.size, lp.getD r (false, false) = (W.getD r false, v r) := by
    intro D hD s v W hv0 hvstep isL lp r
    let base : List (Bool × Bool) :=
      (((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun p =>
        if isL p.2 then (false, p.1) else (p.1, false)
    have hbase_len : base.length = 14 := by simp [base]
    have hlp_def : lp = D.gates.foldl lpStep base := linearParts_eq_foldl D isL _
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr
      by_cases h14 : r < 14
      · rw [hlp_def, lpfold_getD_lt _ _ r (by omega)]
        rw [wire_input D _ r h14, hv0 r h14]
        have hbase_get : base.getD r (false, false) =
            (decide ((⟨r, h14⟩ : Fin 14) = if s then 0 else 7), decide (r = if s then 7 else 0)) := by
          have hfin : ∀ (sb : Bool) (k : Fin 14),
            ((((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun p =>
              if (if sb then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))) p.2
              then (false, p.1) else (p.1, false)).getD k.val (false, false) =
            (decide (k = if sb then 0 else 7), decide (k.val = if sb then 7 else 0)) := by decide +kernel
          exact hfin s ⟨r, h14⟩
        exact hbase_get
      · let j := r - 14
        have hj : j < D.size := by omega
        have hj' : j < D.gates.length := hj
        have hrj : r = 14 + j := by omega
        rw [hrj]
        obtain ⟨hinp, hop, ha, hb⟩ := gate_inputs2 D hD j hj
        have hgj : D.gates[j] = gateAt D j := by
          unfold gateAt; rw [List.getD_eq_getElem _ _ hj']
        have hsplit : D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
          rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
        let pref := (D.gates.take j).foldl lpStep base
        have hpref_len : pref.length = 14 + j := by
          dsimp only [pref]; rw [lpfold_len, hbase_len, List.length_take]; omega
        have hlpstep_len : (lpStep pref (gateAt D j)).length = 14 + j + 1 := by
          simp only [lpStep, List.length_append, List.length_singleton, hpref_len]
        have hlpeq : lp = (D.gates.drop (j + 1)).foldl lpStep (lpStep pref (gateAt D j)) := by
          rw [hlp_def]; conv_lhs => rw [hsplit]
          rw [List.foldl_append, List.foldl_cons]
        have hpref_get : ∀ i < 14 + j, pref.getD i (false, false) = lp.getD i (false, false) := by
          intro i hi
          rw [hlpeq, lpfold_getD_lt (D.gates.drop (j + 1)) (lpStep pref (gateAt D j)) i (by omega)]
          simp only [lpStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.length)]
        rw [hlpeq, lpfold_getD_lt (D.gates.drop (j + 1)) (lpStep pref (gateAt D j)) (14 + j) (by omega)]
        have hstep_at : (lpStep pref (gateAt D j)).getD (14 + j) (false, false) =
            let ins := (gateAt D j).inputs.map fun i => pref.getD i (false, false)
            GateOp.casesOn (gateAt D j).op
              (ins.foldl (fun (acc : Bool × Bool) p =>
                (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
              (ins.any (·.1), ins.any (·.2))
              (false, false)
              (fun _ => (false, false))
              (false, false) := by
          simp only [lpStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hpref_len]; simp
        rw [hstep_at, hinp]
        simp only [List.map_cons, List.map_nil, hpref_get _ ha, hpref_get _ hb]
        rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
        have hwj := wire_gate D hD (fun i : Fin 14 => decide (i = if s then 0 else 7)) j hj
        have hvs := hvstep j hj
        rcases hop with hand | hor
        · rw [hand]
          have h1 : W.getD (14 + j) false =
              (W.getD (opnd D j 0) false && W.getD (opnd D j 1) false) := by
            simpa only [hand, eval_and] using hwj
          have h2 := hvs.1 hand
          rw [h1, h2]
          simp [Bool.true_and, Bool.false_and, Bool.or_false]
        · rw [hor]
          have h1 : W.getD (14 + j) false =
              (W.getD (opnd D j 0) false || W.getD (opnd D j 1) false) := by
            simpa only [hor, eval_or] using hwj
          have h2 := hvs.2 hor
          rw [h1, h2]
          simp
  have not_single_of_deriv : ∀ (D : Circuit), IsAO2 14 D → D.output < 14 + D.size →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < D.size,
          ((gateAt D j).op = GateOp.and →
            v (14 + j) = ((W.getD (opnd D j 0) false && v (opnd D j 1)) ||
              (v (opnd D j 0) && W.getD (opnd D j 1) false))) ∧
          ((gateAt D j).op = GateOp.or →
            v (14 + j) = (v (opnd D j 0) || v (opnd D j 1)))) ∧
        v D.output = false) →
      ¬ IsSingleRead D 14 (fun i => decide (7 ≤ i)) [(0, 7)] := by
    intro D hD hout hder hsr
    have hline : ∀ s : Bool,
        lineSingle D 14 (if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))) 0 7 = false := by
      intro s
      obtain ⟨v, hv0, hvstep, hvout⟩ := hder s
      unfold lineSingle
      rw [lp_eq_witness D hD s v hv0 hvstep D.output hout]
      exact hvout
    have ht := hline true
    have hf := hline false
    simp only [Bool.false_eq_true, ↓reduceIte] at ht hf
    dsimp only [IsSingleRead, doubleReread] at hsr
    simp only [List.filter_cons, List.filter_nil, ht, hf, Bool.not_false, Bool.and_self, ↓reduceIte] at hsr
    cases hsr
  -- Output of C is in bounds and C has at least one gate
  have hCsize_pos : 0 < C.size := by
    by_contra h0
    have h0' : ¬ 0 < C.gates.length := h0
    have he : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hop : (gateAt C 0).op = GateOp.or := by unfold gateAt; rw [he]; rfl
    rw [hop] at hFirst
    exact GateOp.noConfusion hFirst
  have hCout : C.output < 14 + C.size := by
    by_contra hge
    have hge' : ¬ C.output < 14 + C.gates.length := hge
    have h07 : C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = true :=
      (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hf : C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false := by
      change (C.gates.foldl wstep (List.ofFn _)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [wfold_len, List.length_ofFn]; omega)
    rw [h07] at hf
    exact Bool.noConfusion hf
  -- Inspect operands of gate 0
  obtain ⟨h0inp, _, ha0lt0, hb0lt0⟩ := gate_inputs2 C hAO 0 hCsize_pos
  have ha0ne : opnd C 0 0 ≠ opnd C 0 1 := hDist 0 hCsize_pos
  let a0 : ℕ := opnd C 0 0
  let b0 : ℕ := opnd C 0 1
  have ha0lt : a0 < 14 := ha0lt0
  have hb0lt : b0 < 14 := hb0lt0
  let fanoAdjB : ℕ → ℕ → Bool := fun u v =>
    (decide (u < 7) && decide (7 ≤ v) && decide (v < 14) &&
      decide ((u = v - 7) ∨ (u = (v - 7 + 1) % 7) ∨ (u = (v - 7 + 3) % 7))) ||
    (decide (v < 7) && decide (7 ≤ u) && decide (u < 14) &&
      decide ((v = u - 7) ∨ (v = (u - 7 + 1) % 7) ∨ (v = (u - 7 + 3) % 7)))
  have fanoAdj_iff : ∀ u t : Fin 7,
      fanoAdjB (Fin.castAdd 7 u).val (Fin.natAdd 7 t).val = true ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3) := by
    intro u t; revert u t; decide +kernel
  by_cases hedge : fanoAdjB a0 b0 = true
  · -- CASE 1: {a0, b0} is an edge of the Fano plane.
    -- Apply one of 13 automorphisms/correlations fixing {0, 7} to map {a0, b0} into the 4 orbit reps.
    let perms : List (Bool × List ℕ × List ℕ) := [
      (false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
      (false, [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11], [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11]),
      (false, [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11], [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11]),
      (false, [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13], [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13]),
      (false, [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13], [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13]),
      (false, [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11], [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11]),
      (false, [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11], [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11]),
      (false, [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13], [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13]),
      (true,  [7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1], [7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3]),
      (true,  [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3], [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3]),
      (true,  [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3], [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3]),
      (true,  [7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1], [7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3]),
      (true,  [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1], [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1])
    ]
    have hPermsValid : ∀ entry ∈ perms,
        let isDual := entry.1
        let f := entry.2.1
        let g := entry.2.2
        (∀ i : Fin 14, f.getD i.val 0 < 14 ∧ g.getD i.val 0 < 14 ∧
          g.getD (f.getD i.val 0) 0 = i.val ∧ f.getD (g.getD i.val 0) 0 = i.val) ∧
        f.getD 0 0 = (if isDual then 7 else 0) ∧
        f.getD 7 0 = (if isDual then 0 else 7) ∧
        (∀ u v : Fin 14, fanoAdjB (f.getD u.val 0) (f.getD v.val 0) = fanoAdjB u.val v.val) := by
      decide +kernel
    have hCover : ∀ u v : Fin 14, fanoAdjB u.val v.val = true →
        ∃ entry ∈ perms,
          let pa := entry.2.1.getD u.val 0
          let pb := entry.2.1.getD v.val 0
          (min pa pb, max pa pb) ∈ ([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)) := by
      decide +kernel
    obtain ⟨⟨isDual, fL, gL⟩, hentry, hrep⟩ := hCover ⟨a0, ha0lt⟩ ⟨b0, hb0lt⟩ hedge
    obtain ⟨hbij, hf0, hf7, hpres⟩ := hPermsValid (isDual, fL, gL) hentry
    let mapW : ℕ → ℕ := fun w => if w < 14 then fL.getD w 0 else w
    let invW : ℕ → ℕ := fun w => if w < 14 then gL.getD w 0 else w
    have hmapW_lt14 : ∀ w, mapW w < 14 ↔ w < 14 := by
      intro w
      by_cases hw : w < 14
      · dsimp only [mapW]; simp only [hw, ↓reduceIte, iff_true]; exact (hbij ⟨w, hw⟩).1
      · dsimp only [mapW]; simp only [hw, ↓reduceIte]
    have hinvW_mapW : ∀ w, invW (mapW w) = w := by
      intro w
      by_cases hw : w < 14
      · have h1 := (hbij ⟨w, hw⟩).1
        have h2 := (hbij ⟨w, hw⟩).2.2.1
        dsimp only [mapW, invW]; simp only [hw, h1, ↓reduceIte]; exact h2
      · dsimp only [mapW, invW]; simp only [hw, ↓reduceIte]
    have hmapW_invW : ∀ w, mapW (invW w) = w := by
      intro w
      by_cases hw : w < 14
      · have h1 := (hbij ⟨w, hw⟩).2.1
        have h2 := (hbij ⟨w, hw⟩).2.2.2
        dsimp only [mapW, invW]; simp only [hw, h1, ↓reduceIte]; exact h2
      · dsimp only [mapW, invW]; simp only [hw, ↓reduceIte]
    have hmapW_bound : ∀ w j, w < 14 + j → mapW w < 14 + j := by
      intro w j hw
      by_cases h14 : w < 14
      · have := (hmapW_lt14 w).2 h14; omega
      · simpa [mapW, h14] using hw
    have hmapW_inj : ∀ u v, mapW u = mapW v → u = v := by
      intro u v h
      have := congrArg invW h
      rwa [hinvW_mapW, hinvW_mapW] at this
    let pa := fL.getD a0 0
    let pb := fL.getD b0 0
    let swap0 : Gate → Gate := fun g =>
      if pa ≤ pb then g else ⟨g.op, [pb, pa]⟩
    let rawGates : List Gate := C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩
    let Dgates : List Gate :=
      List.casesOn rawGates [] (fun g0 rest => swap0 g0 :: rest)
    let D : Circuit := ⟨Dgates, mapW C.output⟩
    have hraw_len : rawGates.length = C.gates.length := List.length_map _
    have hDsize : D.size = C.size := by
      change Dgates.length = C.gates.length
      cases hr : rawGates with
      | nil => rw [← hraw_len]; simp [Dgates, hr]
      | cons g0 rest => rw [← hraw_len]; simp [Dgates, hr]
    have hDg0 : gateAt D 0 = ⟨GateOp.and, [min pa pb, max pa pb]⟩ := by
      have h0 : 0 < C.gates.length := hCsize_pos
      have hCg0 : C.gates[0] = gateAt C 0 := by unfold gateAt; rw [List.getD_eq_getElem _ _ h0]
      cases hCg : C.gates with
      | nil => simp [hCg] at h0
      | cons g0 rest =>
        have hg0eq : g0 = gateAt C 0 := by unfold gateAt; simp [hCg]
        have hg0op : g0.op = GateOp.and := hg0eq ▸ hFirst
        have hg0inp : g0.inputs = [a0, b0] := hg0eq ▸ h0inp
        have hmap0 : g0.inputs.map mapW = [pa, pb] := by
          rw [hg0inp]; simp only [List.map_cons, List.map_nil, mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
        have hDg : Dgates = swap0 ⟨g0.op, [pa, pb]⟩ :: rest.map (fun g => ⟨g.op, g.inputs.map mapW⟩) := by
          simp [Dgates, rawGates, hCg, hmap0]
        unfold gateAt
        change Dgates.getD 0 _ = _
        rw [hDg]
        simp only [List.getD_cons_zero, swap0, hg0op]
        by_cases hle : pa ≤ pb
        · simp [hle]
        · simp [hle, Nat.min_eq_right (Nat.le_of_not_ge hle), Nat.max_eq_left (Nat.le_of_not_ge hle)]
    have hDgate_pos : ∀ j, 0 < j → j < C.size →
        gateAt D j = ⟨(gateAt C j).op, (gateAt C j).inputs.map mapW⟩ := by
      intro j hjpos hjlt
      cases hCg : C.gates with
      | nil => change j < C.gates.length at hjlt; simp [hCg] at hjlt
      | cons g0 rest =>
        have hDg : Dgates = swap0 ⟨g0.op, g0.inputs.map mapW⟩ :: rest.map (fun g => ⟨g.op, g.inputs.map mapW⟩) := by
          simp [Dgates, rawGates, hCg]
        unfold gateAt
        change Dgates.getD j _ = ⟨(C.gates.getD j _).op, (C.gates.getD j _).inputs.map mapW⟩
        rw [hDg, hCg]
        cases j with
        | zero => omega
        | succ k =>
          have hk : k < rest.length := by change k + 1 < C.gates.length at hjlt; simp [hCg] at hjlt; omega
          simp [List.getD_eq_getElem?_getD, hk]
    have hDAO : IsAO2 14 D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
        have hjlt : j < D.size := (List.getElem?_eq_some_iff.mp hj).1
        have hge : gateAt D j = g := by unfold gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
        rw [← hge]
        by_cases hj0 : j = 0
        · subst hj0; rw [hDg0]; exact Or.inl rfl
        · rw [hDgate_pos j (by omega) (hDsize ▸ hjlt)]
          exact (gate_inputs2 C hAO j (hDsize ▸ hjlt)).2.1
      · intro j hj i hi
        by_cases hj0 : j = 0
        · subst hj0; rw [hDg0] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          have hpa : pa < 14 := (hbij ⟨a0, ha0lt⟩).1
          have hpb : pb < 14 := (hbij ⟨b0, hb0lt⟩).1
          rcases hi with rfl | rfl <;> omega
        · have hjC : j < C.size := hDsize ▸ hj
          rw [hDgate_pos j (by omega) hjC] at hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          exact hmapW_bound i0 j (hAO.2.1 j hjC i0 hi0)
      · intro g hg
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
        have hjlt : j < D.size := (List.getElem?_eq_some_iff.mp hj).1
        have hge : gateAt D j = g := by unfold gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
        rw [← hge]
        by_cases hj0 : j = 0
        · subst hj0; rw [hDg0]; rfl
        · rw [hDgate_pos j (by omega) (hDsize ▸ hjlt)]
          simp [(gate_inputs2 C hAO j (hDsize ▸ hjlt)).1]
    have hDdist : ∀ j < D.size, opnd D j 0 ≠ opnd D j 1 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have h0 : opnd D 0 0 = min pa pb ∧ opnd D 0 1 = max pa pb := by
          unfold opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
        rw [h0.1, h0.2]
        have hne : pa ≠ pb := by
          intro he
          have : mapW a0 = mapW b0 := by
            dsimp only [mapW]; simp only [ha0lt, hb0lt, ↓reduceIte]; exact he
          exact ha0ne (hmapW_inj a0 b0 this)
        omega
      · have hg := hDgate_pos j (by omega) (hDsize ▸ hj)
        obtain ⟨hinp, _, _, _⟩ := gate_inputs2 C hAO j (hDsize ▸ hj)
        have h0 : opnd D j 0 = mapW (opnd C j 0) ∧ opnd D j 1 = mapW (opnd C j 1) := by
          unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
        rw [h0.1, h0.2]
        intro he
        exact hDist j (hDsize ▸ hj) (hmapW_inj _ _ he)
    -- Wire values of D match C under permutation fL
    let finPerm : Fin 14 → Fin 14 := fun i => ⟨fL.getD i.val 0, (hbij i).1⟩
    let finInv : Fin 14 → Fin 14 := fun i => ⟨gL.getD i.val 0, (hbij i).2.1⟩
    have hDwire : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.size →
        (D.wires (List.ofFn x)).getD (mapW r) false =
          (C.wires (List.ofFn (fun i => x (finPerm i)))).getD r false := by
      intro x r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr
        by_cases h14 : r < 14
        · have hmr : mapW r < 14 := (hmapW_lt14 r).2 h14
          rw [wire_input D x (mapW r) hmr, wire_input C _ r h14]
          congr 1; ext; simp [mapW, finPerm, h14]
        · let j := r - 14
          have hj : j < C.size := by omega
          have hrj : r = 14 + j := by omega
          have hmr : mapW r = 14 + j := by simp [mapW, hrj]
          rw [hmr, hrj]
          rw [wire_gate D hDAO x j (hDsize.symm ▸ hj), wire_gate C hAO _ j hj]
          by_cases hj0 : j = 0
          · rw [hj0]
            have hd0 : opnd D 0 0 = min pa pb ∧ opnd D 0 1 = max pa pb := by
              unfold opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
            rw [hDg0, hFirst, hd0.1, hd0.2, eval_and, eval_and]
            have hpa_eq : min pa pb = mapW a0 ∧ max pa pb = mapW b0 ∨
                min pa pb = mapW b0 ∧ max pa pb = mapW a0 := by
              simp only [mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
              by_cases hle : fL.getD a0 0 ≤ fL.getD b0 0
              · exact Or.inl ⟨Nat.min_eq_left hle, Nat.max_eq_right hle⟩
              · exact Or.inr ⟨Nat.min_eq_right (Nat.le_of_not_ge hle), Nat.max_eq_left (Nat.le_of_not_ge hle)⟩
            rcases hpa_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2, ih a0 (by omega) (by omega), ih b0 (by omega) (by omega)]
            · rw [e1, e2, ih b0 (by omega) (by omega), ih a0 (by omega) (by omega), Bool.and_comm]
          · have hg := hDgate_pos j (by omega) hj
            obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 C hAO j hj
            have h0 : opnd D j 0 = mapW (opnd C j 0) ∧ opnd D j 1 = mapW (opnd C j 1) := by
              unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
            rw [hg, h0.1, h0.2, ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
    have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
      intro x
      have hev : D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (finPerm i))) :=
        hDwire x C.output hCout
      rw [hev, hFano]
      have hiff : ∀ y : Fin 14 → Bool,
          (∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            y (Fin.castAdd 7 u) = true ∧ y (Fin.natAdd 7 t) = true) ↔
          (∃ p q : Fin 14, fanoAdjB p.val q.val = true ∧ y p = true ∧ y q = true) := by
        intro y
        constructor
        · rintro ⟨u, t, hut, hu, ht⟩
          exact ⟨Fin.castAdd 7 u, Fin.natAdd 7 t, (fanoAdj_iff u t).2 hut, hu, ht⟩
        · rintro ⟨p, q, hpq, hp, hq⟩
          have hdisj : ∀ a b : Fin 14, fanoAdjB a.val b.val = true →
              (a.val < 7 ∧ 7 ≤ b.val) ∨ (b.val < 7 ∧ 7 ≤ a.val) := by decide +kernel
          rcases hdisj p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · let u : Fin 7 := ⟨p.val, h1⟩
            let t : Fin 7 := ⟨q.val - 7, by omega⟩
            have ep : p = Fin.castAdd 7 u := Fin.ext rfl
            have eq : q = Fin.natAdd 7 t := Fin.ext (by show q.val = 7 + (q.val - 7); omega)
            rw [ep] at hp; rw [eq] at hq; rw [ep, eq] at hpq
            exact ⟨u, t, (fanoAdj_iff u t).1 hpq, hp, hq⟩
          · let u : Fin 7 := ⟨q.val, h1⟩
            let t : Fin 7 := ⟨p.val - 7, by omega⟩
            have eq : q = Fin.castAdd 7 u := Fin.ext rfl
            have ep : p = Fin.natAdd 7 t := Fin.ext (by show p.val = 7 + (p.val - 7); omega)
            have hsym : ∀ a b : Fin 14, fanoAdjB a.val b.val = fanoAdjB b.val a.val := by decide +kernel
            rw [hsym, eq, ep] at hpq
            rw [eq] at hq; rw [ep] at hp
            exact ⟨u, t, (fanoAdj_iff u t).1 hpq, hq, hp⟩
      rw [hiff (fun i => x (finPerm i)), hiff x]
      constructor
      · rintro ⟨p, q, hpq, hp, hq⟩
        exact ⟨finPerm p, finPerm q, (hpres p q).trans hpq, hp, hq⟩
      · rintro ⟨p, q, hpq, hp, hq⟩
        have hinvP : finPerm (finInv p) = p := Fin.ext (hbij p).2.2.2
        have hinvQ : finPerm (finInv q) = q := Fin.ext (hbij q).2.2.2
        refine ⟨finInv p, finInv q, ?_, by simpa [hinvP] using hp, by simpa [hinvQ] using hq⟩
        have hpr := hpres (finInv p) (finInv q)
        have e1 : fL.getD (finInv p).val 0 = p.val := (hbij p).2.2.2
        have e2 : fL.getD (finInv q).val 0 = q.val := (hbij q).2.2.2
        rw [e1, e2] at hpr
        exact hpr.symm.trans hpq
    -- Transfer the double re-read witness to D
    have hDderiv : ∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < D.size,
          ((gateAt D j).op = GateOp.and →
            v (14 + j) = ((W.getD (opnd D j 0) false && v (opnd D j 1)) ||
              (v (opnd D j 0) && W.getD (opnd D j 1) false))) ∧
          ((gateAt D j).op = GateOp.or →
            v (14 + j) = (v (opnd D j 0) || v (opnd D j 1)))) ∧
        v D.output = false := by
      intro s
      let s' : Bool := if isDual then !s else s
      obtain ⟨v, hv0, hvstep, hvout⟩ := hDeriv s'
      have hunit : (fun i : Fin 14 => decide (finPerm i = if s then 0 else 7)) =
          (fun i : Fin 14 => decide (i = if s' then 0 else 7)) := by
        funext i
        apply Bool.decide_congr
        have h0eq : finPerm 0 = (if isDual then 7 else 0) := by
          apply Fin.ext; change fL.getD 0 0 = _; rw [hf0]; cases isDual <;> rfl
        have h7eq : finPerm 7 = (if isDual then 0 else 7) := by
          apply Fin.ext; change fL.getD 7 0 = _; rw [hf7]; cases isDual <;> rfl
        have htarget : finPerm (if s' then 0 else 7) = (if s then 0 else 7) := by
          dsimp only [s']
          cases isDual <;> cases s <;> simp at h0eq h7eq ⊢ <;> first | exact h0eq | exact h7eq
        rw [← htarget]
        constructor
        · intro h
          have := congrArg finInv h
          have hi1 : finInv (finPerm i) = i := Fin.ext (hbij i).2.2.1
          have hi2 : finInv (finPerm (if s' then 0 else 7)) = (if s' then 0 else 7) :=
            Fin.ext (hbij _).2.2.1
          rwa [hi1, hi2] at this
        · intro h; rw [h]
      have hWmap : ∀ w < 14 + C.size,
          (D.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))).getD (mapW w) false =
          (C.wires (List.ofFn fun i : Fin 14 => decide (i = if s' then 0 else 7))).getD w false := by
        intro w hw
        rw [hDwire _ w hw, hunit]
      refine ⟨fun w => v (invW w), ?_, ?_, ?_⟩
      · intro i hi
        dsimp only
        have hlt : invW i < 14 := by dsimp only [invW]; simp only [hi, ↓reduceIte]; exact (hbij ⟨i, hi⟩).2.1
        rw [hv0 (invW i) hlt]
        apply Bool.decide_congr
        have ht : mapW (if s' then 7 else 0) = (if s then 7 else 0) := by
          dsimp only [s', mapW]
          cases isDual <;> cases s <;> simp at hf0 hf7 ⊢ <;> first | exact hf0 | exact hf7
        rw [← ht]
        constructor
        · intro h; rw [← hmapW_invW i, h]
        · intro h; rw [h, hinvW_mapW]
      · intro j hj
        dsimp only
        have hjC : j < C.size := hDsize ▸ hj
        have hinvJ : invW (14 + j) = 14 + j := by simp [invW]
        have hs := hvstep j hjC
        by_cases hj0 : j = 0
        · subst hj0
          have hd0 : opnd D 0 0 = min pa pb ∧ opnd D 0 1 = max pa pb := by
            unfold opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
          rw [hDg0, hinvJ, hd0.1, hd0.2]
          constructor
          · intro _
            have hpa_eq : min pa pb = mapW a0 ∧ max pa pb = mapW b0 ∨
                min pa pb = mapW b0 ∧ max pa pb = mapW a0 := by
              simp only [mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
              by_cases hle : fL.getD a0 0 ≤ fL.getD b0 0
              · exact Or.inl ⟨Nat.min_eq_left hle, Nat.max_eq_right hle⟩
              · exact Or.inr ⟨Nat.min_eq_right (Nat.le_of_not_ge hle), Nat.max_eq_left (Nat.le_of_not_ge hle)⟩
            have h0s := hs.1 hFirst
            rcases hpa_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2, hinvW_mapW, hinvW_mapW, hWmap a0 (by omega), hWmap b0 (by omega)]
              exact h0s
            · rw [e1, e2, hinvW_mapW, hinvW_mapW, hWmap b0 (by omega), hWmap a0 (by omega), h0s]
              cases (C.wires (List.ofFn fun i : Fin 14 => decide (i = if s' then 0 else 7))).getD a0 false <;>
                cases (C.wires (List.ofFn fun i : Fin 14 => decide (i = if s' then 0 else 7))).getD b0 false <;>
                cases v a0 <;> cases v b0 <;> rfl
          · intro h; exact GateOp.noConfusion h
        · have hg := hDgate_pos j (by omega) hjC
          obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 C hAO j hjC
          have h0 : opnd D j 0 = mapW (opnd C j 0) ∧ opnd D j 1 = mapW (opnd C j 1) := by
            unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
          rw [hg, hinvJ, h0.1, h0.2, hinvW_mapW, hinvW_mapW, hWmap _ (by omega), hWmap _ (by omega)]
          exact hs
      · change v (invW (mapW C.output)) = false
        rw [hinvW_mapW]
        exact hvout
    have hDout : D.output < 14 + D.size := by
      rw [hDsize]; exact hmapW_bound C.output C.size hCout
    exact noFourEdges D (hDsize.symm ▸ hSize) hDAO hDdist
      ⟨(min pa pb, max pa pb), hrep, hDg0⟩ hDFano (not_single_of_deriv D hDAO hDout hDderiv)
  · -- CASE 2: {a0, b0} is NOT an edge of the Fano plane.
    -- Substitute wire 14 := false and propagate constants / identical operands.
    -- State after processing gates 0 .. j - 1: (gs, rep, coll)
    have h0_false_on_edge : ∀ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) →
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t))).getD 14 false = false := by
      intro u t hut
      have hw := wire_gate C hAO (fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)) 0 hCsize_pos
      rw [hFirst, eval_and, wire_input C _ a0 ha0lt, wire_input C _ b0 hb0lt] at hw
      rw [hw]
      cases h : (decide (⟨a0, ha0lt⟩ = Fin.castAdd 7 u ∨ ⟨a0, ha0lt⟩ = Fin.natAdd 7 t) &&
          decide (⟨b0, hb0lt⟩ = Fin.castAdd 7 u ∨ ⟨b0, hb0lt⟩ = Fin.natAdd 7 t)) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨ha | ha, hb | hb⟩
        · exact ha0ne (congrArg Fin.val (ha.trans hb.symm))
        · have ea : a0 = (Fin.castAdd 7 u).val := congrArg Fin.val ha
          have eb : b0 = (Fin.natAdd 7 t).val := congrArg Fin.val hb
          exact hedge (by rw [ea, eb]; exact (fanoAdj_iff u t).2 hut)
        · have ea : a0 = (Fin.natAdd 7 t).val := congrArg Fin.val ha
          have eb : b0 = (Fin.castAdd 7 u).val := congrArg Fin.val hb
          have hsym : ∀ p q : Fin 14, fanoAdjB p.val q.val = fanoAdjB q.val p.val := by decide +kernel
          exact hedge (by
            change fanoAdjB (⟨a0, ha0lt⟩ : Fin 14).val (⟨b0, hb0lt⟩ : Fin 14).val = true
            rw [hsym]; change fanoAdjB b0 a0 = true
            rw [ea, eb]; exact (fanoAdj_iff u t).2 hut)
        · exact ha0ne (congrArg Fin.val (ha.trans hb.symm))
    have h0_false_on_unit : ∀ s : Bool,
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))).getD 14 false = false := by
      intro s
      have hw := wire_gate C hAO (fun i : Fin 14 => decide (i = if s then 0 else 7)) 0 hCsize_pos
      rw [hFirst, eval_and, wire_input C _ a0 ha0lt, wire_input C _ b0 hb0lt] at hw
      rw [hw]
      cases h : (decide (⟨a0, ha0lt⟩ = if s then (0 : Fin 14) else 7) &&
          decide (⟨b0, hb0lt⟩ = if s then (0 : Fin 14) else 7)) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ha0ne (congrArg Fin.val (h.1.trans h.2.symm))
    have h0_v_false : ∀ (s : Bool) (v : ℕ → Bool),
        let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
        ((gateAt C 0).op = GateOp.and →
          v 14 = ((W.getD a0 false && v b0) || (v a0 && W.getD b0 false))) →
        v 14 = false := by
      intro s v W hv0 hv14
      rw [hv14 hFirst, wire_input C _ a0 ha0lt, wire_input C _ b0 hb0lt, hv0 a0 ha0lt, hv0 b0 hb0lt]
      have h07 : fanoAdjB 0 7 = true ∧ fanoAdjB 7 0 = true := by decide +kernel
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases h : ((decide (⟨a0, ha0lt⟩ = (7 : Fin 14)) && decide (b0 = 0)) ||
            (decide (a0 = 0) && decide (⟨b0, hb0lt⟩ = (7 : Fin 14)))) with
        | false => rfl
        | true =>
          exfalso
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · have ea : a0 = 7 := congrArg Fin.val ha
            exact hedge (by rw [ea, hb]; exact h07.2)
          · have eb : b0 = 7 := congrArg Fin.val hb
            exact hedge (by rw [ha, eb]; exact h07.1)
      · simp only [↓reduceIte]
        cases h : ((decide (⟨a0, ha0lt⟩ = (0 : Fin 14)) && decide (b0 = 7)) ||
            (decide (a0 = 7) && decide (⟨b0, hb0lt⟩ = (0 : Fin 14)))) with
        | false => rfl
        | true =>
          exfalso
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · have ea : a0 = 0 := congrArg Fin.val ha
            exact hedge (by rw [ea, hb]; exact h07.1)
          · have eb : b0 = 0 := congrArg Fin.val hb
            exact hedge (by rw [ha, eb]; exact h07.2)
    -- Build the simplified circuit by induction on j (1 ≤ j ≤ C.size)
    let optW (gs : List Gate) (x : Fin 14 → Bool) (o : Option ℕ) : Bool :=
      Option.casesOn o false (fun w => ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false)
    let optV (gs : List Gate) (s : Bool) (o : Option ℕ) : Bool :=
      Option.casesOn o false (fun w =>
        let isL : ℕ → Bool := if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))
        ((linearParts ⟨gs, 0⟩ isL ((List.range 14).map fun i => i == 0 || i == 7)).getD w (false, false)).2)
    have hBuild : ∀ j, 1 ≤ j → j ≤ C.size →
        ∃ (gs : List Gate) (rep : ℕ → Option ℕ) (coll : Bool),
          IsAO2 14 ⟨gs, 0⟩ ∧
          (∀ k < gs.length, opnd ⟨gs, 0⟩ k 0 ≠ opnd ⟨gs, 0⟩ k 1) ∧
          gs.length + 1 ≤ j ∧
          (coll = true → gs.length + 3 ≤ j) ∧
          (∀ w < 14 + j, ∀ w', rep w = some w' → w' < 14 + gs.length) ∧
          (∀ u v, u < 14 + j → v < 14 + j → u ≠ v → rep u = rep v → rep u ≠ none → gs.length + 2 ≤ j) ∧
          (∀ x : Fin 14 → Bool, ∀ w < 14 + j,
            optW gs x (rep w) = true → (C.wires (List.ofFn x)).getD w false = true) ∧
          (∀ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD 14 false = false →
            ∀ w < 14 + j, optW gs x (rep w) = (C.wires (List.ofFn x)).getD w false) ∧
          (coll = false → ∀ (s : Bool) (v : ℕ → Bool),
            let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
            (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
            (∀ k < C.size,
              ((gateAt C k).op = GateOp.and →
                v (14 + k) = ((W.getD (opnd C k 0) false && v (opnd C k 1)) ||
                  (v (opnd C k 0) && W.getD (opnd C k 1) false))) ∧
              ((gateAt C k).op = GateOp.or →
                v (14 + k) = (v (opnd C k 0) || v (opnd C k 1)))) →
            ∀ w < 14 + j, optV gs s (rep w) = v w) := by
      intro j hj1
      induction j with
      | zero => omega
      | succ j ih =>
        intro hjle
        by_cases hj0 : j = 0
        · subst hj0
          refine ⟨[], fun w => if w < 14 then some w else none, false, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨(by intro g hg; cases hg), (by intro k hk; cases hk), (by intro g hg; cases hg)⟩
          · intro k hk; cases hk
          · simp
          · intro h; exact Bool.noConfusion h
          · intro w hw w' hrep
            by_cases h14 : w < 14
            · simp [h14] at hrep; subst hrep; omega
            · simp [h14] at hrep
          · intro u v hu hv hne heq hnn
            by_cases hu14 : u < 14 <;> by_cases hv14 : v < 14
            · simp [hu14, hv14] at heq; exact (hne heq).elim
            · simp [hu14, hv14] at heq
            · simp [hu14] at hnn
            · simp [hu14] at hnn
          · intro x w hw hval
            by_cases h14 : w < 14
            · simp only [h14, ↓reduceIte, optW] at hval
              rw [wire_input ⟨[], 0⟩ x w h14] at hval
              rw [wire_input C x w h14]
              exact hval
            · simp [h14, optW] at hval
          · intro x hx14 w hw
            by_cases h14 : w < 14
            · simp only [h14, ↓reduceIte, optW]
              rw [wire_input ⟨[], 0⟩ x w h14, wire_input C x w h14]
            · have ew : w = 14 := by omega
              subst ew
              simp only [Nat.lt_irrefl, ↓reduceIte, optW]
              exact hx14.symm
          · intro _ s v W hv0 hvstep w hw
            by_cases h14 : w < 14
            · simp only [h14, ↓reduceIte, optV]
              have hlp := lp_eq_witness ⟨[], 0⟩
                ⟨(by intro g hg; cases hg), (by intro k hk; cases hk), (by intro g hg; cases hg)⟩ s
                (fun i => decide (i = if s then 7 else 0)) (fun i _ => rfl) (by intro k hk; cases hk)
                w (by change w < 14 + 0; omega)
              rw [hlp, hv0 w h14]
            · have ew : w = 14 := by omega
              subst ew
              simp only [Nat.lt_irrefl, ↓reduceIte, optV]
              exact (h0_v_false s v hv0 (hvstep 0 hCsize_pos).1).symm
        · obtain ⟨gs, rep, coll, hgsAO, hgsDist, hlen1, hcoll3, hrepLt, hInj, hUpper, hAgree, hTrace⟩ :=
            ih (by omega) (by omega)
          have hjlt : j < C.size := by omega
          obtain ⟨hjinp, hjop, hja, hjb⟩ := gate_inputs2 C hAO j hjlt
          let a := opnd C j 0
          let b := opnd C j 1
          have hab_ne : a ≠ b := hDist j hjlt
          -- Helper for no-emit step (gs unchanged, rep updated at 14+j to res)
          have noEmit : ∀ (res : Option ℕ) (coll' : Bool),
              (∀ w', res = some w' → w' < 14 + gs.length) →
              (coll' = true → gs.length + 3 ≤ j + 1) →
              (∀ x, optW gs x res = true → (C.wires (List.ofFn x)).getD (14 + j) false = true) →
              (∀ x, (C.wires (List.ofFn x)).getD 14 false = false →
                optW gs x res = (C.wires (List.ofFn x)).getD (14 + j) false) →
              (coll' = false → coll = false ∧ ∀ (s : Bool) (v : ℕ → Bool),
                let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
                (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
                (∀ k < C.size,
                  ((gateAt C k).op = GateOp.and →
                    v (14 + k) = ((W.getD (opnd C k 0) false && v (opnd C k 1)) ||
                      (v (opnd C k 0) && W.getD (opnd C k 1) false))) ∧
                  ((gateAt C k).op = GateOp.or →
                    v (14 + k) = (v (opnd C k 0) || v (opnd C k 1)))) →
                optV gs s res = v (14 + j)) →
              ∃ (gs' : List Gate) (rep' : ℕ → Option ℕ) (c' : Bool),
                IsAO2 14 ⟨gs', 0⟩ ∧
                (∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1) ∧
                gs'.length + 1 ≤ j + 1 ∧
                (c' = true → gs'.length + 3 ≤ j + 1) ∧
                (∀ w < 14 + (j + 1), ∀ w', rep' w = some w' → w' < 14 + gs'.length) ∧
                (∀ u v, u < 14 + (j + 1) → v < 14 + (j + 1) → u ≠ v → rep' u = rep' v → rep' u ≠ none → gs'.length + 2 ≤ j + 1) ∧
                (∀ x : Fin 14 → Bool, ∀ w < 14 + (j + 1),
                  optW gs' x (rep' w) = true → (C.wires (List.ofFn x)).getD w false = true) ∧
                (∀ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD 14 false = false →
                  ∀ w < 14 + (j + 1), optW gs' x (rep' w) = (C.wires (List.ofFn x)).getD w false) ∧
                (c' = false → ∀ (s : Bool) (v : ℕ → Bool),
                  let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
                  (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
                  (∀ k < C.size,
                    ((gateAt C k).op = GateOp.and →
                      v (14 + k) = ((W.getD (opnd C k 0) false && v (opnd C k 1)) ||
                        (v (opnd C k 0) && W.getD (opnd C k 1) false))) ∧
                    ((gateAt C k).op = GateOp.or →
                      v (14 + k) = (v (opnd C k 0) || v (opnd C k 1)))) →
                  ∀ w < 14 + (j + 1), optV gs' s (rep' w) = v w) := by
            intro res coll' hresLt hcoll' hresUp hresAg hresTr
            refine ⟨gs, fun w => if w = 14 + j then res else rep w, coll',
              hgsAO, hgsDist, by omega, hcoll', ?_, ?_, ?_, ?_, ?_⟩
            · intro w hw w' hrw
              by_cases hwj : w = 14 + j
              · simp [hwj] at hrw; exact hresLt w' hrw
              · simp [hwj] at hrw; exact hrepLt w (by omega) w' hrw
            · intro u v _ _ _ _ _; omega
            · intro x w hw hval
              by_cases hwj : w = 14 + j
              · subst hwj; simp only [↓reduceIte] at hval; exact hresUp x hval
              · simp only [hwj, ↓reduceIte] at hval; exact hUpper x w (by omega) hval
            · intro x hx14 w hw
              by_cases hwj : w = 14 + j
              · subst hwj; simp only [↓reduceIte]; exact hresAg x hx14
              · simp only [hwj, ↓reduceIte]; exact hAgree x hx14 w (by omega)
            · intro hc' s v W hv0 hvstep w hw
              obtain ⟨hc, htr⟩ := hresTr hc'
              by_cases hwj : w = 14 + j
              · subst hwj; simp only [↓reduceIte]; exact htr s v hv0 hvstep
              · simp only [hwj, ↓reduceIte]; exact hTrace hc s v hv0 hvstep w (by omega)
          -- Helper for emitting a new gate gnew = ⟨op, [a', b']⟩ with a' ≠ b'
          have doEmit : ∀ (op : GateOp) (a' b' : ℕ),
              (op = GateOp.and ∨ op = GateOp.or) →
              op = (gateAt C j).op →
              rep a = some a' → rep b = some b' → a' ≠ b' →
              ∃ (gs' : List Gate) (rep' : ℕ → Option ℕ) (c' : Bool),
                IsAO2 14 ⟨gs', 0⟩ ∧
                (∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1) ∧
                gs'.length + 1 ≤ j + 1 ∧
                (c' = true → gs'.length + 3 ≤ j + 1) ∧
                (∀ w < 14 + (j + 1), ∀ w', rep' w = some w' → w' < 14 + gs'.length) ∧
                (∀ u v, u < 14 + (j + 1) → v < 14 + (j + 1) → u ≠ v → rep' u = rep' v → rep' u ≠ none → gs'.length + 2 ≤ j + 1) ∧
                (∀ x : Fin 14 → Bool, ∀ w < 14 + (j + 1),
                  optW gs' x (rep' w) = true → (C.wires (List.ofFn x)).getD w false = true) ∧
                (∀ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD 14 false = false →
                  ∀ w < 14 + (j + 1), optW gs' x (rep' w) = (C.wires (List.ofFn x)).getD w false) ∧
                (c' = false → ∀ (s : Bool) (v : ℕ → Bool),
                  let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
                  (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
                  (∀ k < C.size,
                    ((gateAt C k).op = GateOp.and →
                      v (14 + k) = ((W.getD (opnd C k 0) false && v (opnd C k 1)) ||
                        (v (opnd C k 0) && W.getD (opnd C k 1) false))) ∧
                    ((gateAt C k).op = GateOp.or →
                      v (14 + k) = (v (opnd C k 0) || v (opnd C k 1)))) →
                  ∀ w < 14 + (j + 1), optV gs' s (rep' w) = v w) := by
            intro op a' b' hop hopEq ha' hb' hne'
            let gnew : Gate := ⟨op, [a', b']⟩
            let gs' : List Gate := gs ++ [gnew]
            have ha'lt : a' < 14 + gs.length := hrepLt a hja a' ha'
            have hb'lt : b' < 14 + gs.length := hrepLt b hjb b' hb'
            have hgs'len : gs'.length = gs.length + 1 := by simp [gs']
            have hgs'AO : IsAO2 14 ⟨gs', 0⟩ := by
              refine ⟨?_, ?_, ?_⟩
              · intro g hg
                simp only [gs', List.mem_append, List.mem_singleton] at hg
                rcases hg with hg | rfl
                · exact hgsAO.1 g hg
                · exact hop
              · intro k hk i hi
                change k < gs'.length at hk
                by_cases hklt : k < gs.length
                · have e : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                    unfold gateAt; change gs'.getD k _ = gs.getD k _
                    rw [List.getD_append _ _ _ _ hklt]
                  rw [e] at hi
                  exact hgsAO.2.1 k hklt i hi
                · have ek : k = gs.length := by omega
                  subst ek
                  have e : gateAt ⟨gs', 0⟩ gs.length = gnew := by
                    unfold gateAt; change (gs ++ [gnew]).getD gs.length _ = gnew; simp
                  rw [e] at hi
                  simp only [gnew, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> omega
              · intro g hg
                simp only [gs', List.mem_append, List.mem_singleton] at hg
                rcases hg with hg | rfl
                · exact hgsAO.2.2 g hg
                · rfl
            have hgs'Dist : ∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1 := by
              intro k hk
              by_cases hklt : k < gs.length
              · have e : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                  unfold gateAt; change gs'.getD k _ = gs.getD k _
                  rw [List.getD_append _ _ _ _ hklt]
                unfold opnd; rw [e]; exact hgsDist k hklt
              · have ek : k = gs.length := by omega
                subst ek
                have e : gateAt ⟨gs', 0⟩ gs.length = gnew := by
                  unfold gateAt; change (gs ++ [gnew]).getD gs.length _ = gnew; simp
                unfold opnd; rw [e]; exact hne'
            have hWold : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + gs.length →
                ((Circuit.mk gs' 0).wires (List.ofFn x)).getD w false =
                ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false := by
              intro x w hw
              change ((gs ++ [gnew]).foldl wstep (List.ofFn x)).getD w false = _
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              have hl : (gs.foldl wstep (List.ofFn x)).length = 14 + gs.length := by
                rw [wfold_len, List.length_ofFn]
              have hlt : w < (gs.foldl wstep (List.ofFn x)).length := hl ▸ hw
              dsimp only [wstep]
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
              rfl
            have hWnew : ∀ x : Fin 14 → Bool,
                ((Circuit.mk gs' 0).wires (List.ofFn x)).getD (14 + gs.length) false =
                op.eval [((Circuit.mk gs 0).wires (List.ofFn x)).getD a' false,
                         ((Circuit.mk gs 0).wires (List.ofFn x)).getD b' false] := by
              intro x
              have hw := wire_gate ⟨gs', 0⟩ hgs'AO x gs.length (by change gs.length < gs'.length; omega)
              have e : gateAt ⟨gs', 0⟩ gs.length = gnew := by
                unfold gateAt; change (gs ++ [gnew]).getD gs.length _ = gnew; simp
              have e0 : opnd ⟨gs', 0⟩ gs.length 0 = a' := by unfold opnd; rw [e]; rfl
              have e1 : opnd ⟨gs', 0⟩ gs.length 1 = b' := by unfold opnd; rw [e]; rfl
              rw [hw, e, e0, e1, hWold x a' ha'lt, hWold x b' hb'lt]
            have hOptOld : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + j →
                optW gs' x (rep w) = optW gs x (rep w) := by
              intro x w hw
              cases hr : rep w with
              | none => rfl
              | some w' => exact hWold x w' (hrepLt w hw w' hr)
            have hLPold : ∀ (s : Bool) (w : ℕ), w < 14 + gs.length →
                let isL : ℕ → Bool := if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))
                (linearParts ⟨gs', 0⟩ isL ((List.range 14).map fun i => i == 0 || i == 7)).getD w (false, false) =
                (linearParts ⟨gs, 0⟩ isL ((List.range 14).map fun i => i == 0 || i == 7)).getD w (false, false) := by
              intro s w hw isL
              rw [linearParts_eq_foldl, linearParts_eq_foldl]
              change ((gs ++ [gnew]).foldl lpStep _).getD w (false, false) = _
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              let baseS : List (Bool × Bool) :=
                (((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun p =>
                  if isL p.2 then (false, p.1) else (p.1, false)
              have hl : (gs.foldl lpStep baseS).length = 14 + gs.length := by
                rw [lpfold_len]; simp [baseS]
              have hlt : w < (gs.foldl lpStep baseS).length := hl ▸ hw
              dsimp only [lpStep]
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
              rfl
            have hOptVold : ∀ (s : Bool) (w : ℕ), w < 14 + j →
                optV gs' s (rep w) = optV gs s (rep w) := by
              intro s w hw
              cases hr : rep w with
              | none => rfl
              | some w' =>
                dsimp only [optV]
                rw [hLPold s w' (hrepLt w hw w' hr)]
            refine ⟨gs', fun w => if w = 14 + j then some (14 + gs.length) else rep w, coll,
              hgs'AO, hgs'Dist, by omega, fun h => by have := hcoll3 h; omega, ?_, ?_, ?_, ?_, ?_⟩
            · intro w hw w' hrw
              by_cases hwj : w = 14 + j
              · simp [hwj] at hrw; subst hrw; omega
              · simp [hwj] at hrw; have := hrepLt w (by omega) w' hrw; omega
            · intro u v hu hv hne heq hnn
              by_cases huj : u = 14 + j <;> by_cases hvj : v = 14 + j
              · exact (hne (huj.trans hvj.symm)).elim
              · simp only [huj, hvj, ↓reduceIte] at heq
                have := hrepLt v (by omega) (14 + gs.length) heq.symm
                omega
              · simp only [huj, hvj, ↓reduceIte] at heq
                have := hrepLt u (by omega) (14 + gs.length) heq
                omega
              · simp only [huj, hvj, ↓reduceIte] at heq hnn
                have := hInj u v (by omega) (by omega) hne heq hnn
                omega
            · intro x w hw hval
              by_cases hwj : w = 14 + j
              · subst hwj
                simp only [↓reduceIte, optW, hWnew] at hval
                rw [wire_gate C hAO x j hjlt, ← hopEq]
                have hua := hUpper x a hja
                have hub := hUpper x b hjb
                simp only [ha', hb', optW] at hua hub
                rcases hop with rfl | rfl
                · rw [eval_and, Bool.and_eq_true] at hval ⊢
                  exact ⟨hua hval.1, hub hval.2⟩
                · rw [eval_or, Bool.or_eq_true] at hval ⊢
                  rcases hval with h1 | h2
                  · exact Or.inl (hua h1)
                  · exact Or.inr (hub h2)
              · simp only [hwj, ↓reduceIte] at hval
                rw [hOptOld x w (by omega)] at hval
                exact hUpper x w (by omega) hval
            · intro x hx14 w hw
              by_cases hwj : w = 14 + j
              · subst hwj
                simp only [↓reduceIte, optW, hWnew]
                rw [wire_gate C hAO x j hjlt, ← hopEq]
                have haa := hAgree x hx14 a hja
                have hab := hAgree x hx14 b hjb
                simp only [ha', hb', optW] at haa hab
                rw [haa, hab]
              · simp only [hwj, ↓reduceIte]
                rw [hOptOld x w (by omega)]
                exact hAgree x hx14 w (by omega)
            · intro hcf s v W hv0 hvstep w hw
              by_cases hwj : w = 14 + j
              · subst hwj
                simp only [↓reduceIte, optV]
                let isL : ℕ → Bool := if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))
                let lpOld := linearParts ⟨gs, 0⟩ isL ((List.range 14).map fun i => i == 0 || i == 7)
                let baseS : List (Bool × Bool) :=
                  (((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun p =>
                    if isL p.2 then (false, p.1) else (p.1, false)
                have hlpOld_def : lpOld = gs.foldl lpStep baseS := linearParts_eq_foldl ⟨gs, 0⟩ isL _
                have hlenOld : lpOld.length = 14 + gs.length := by
                  rw [hlpOld_def, lpfold_len]; simp [baseS]
                have hlNew : (linearParts ⟨gs', 0⟩ isL ((List.range 14).map fun i => i == 0 || i == 7)).getD (14 + gs.length) (false, false) =
                    (lpStep lpOld gnew).getD (14 + gs.length) (false, false) := by
                  rw [linearParts_eq_foldl, hlpOld_def]
                  change ((gs ++ [gnew]).foldl lpStep baseS).getD (14 + gs.length) (false, false) = _
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                rw [hlNew]
                have hlpOld_1 : ∀ r < 14 + gs.length,
                    (lpOld.getD r (false, false)).1 =
                    ((Circuit.mk gs 0).wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))).getD r false := by
                  intro r
                  induction r using Nat.strong_induction_on with
                  | ind r ih1 =>
                    intro hr
                    by_cases hr14 : r < 14
                    · rw [hlpOld_def, lpfold_getD_lt gs baseS r (by simp [baseS]; omega), wire_input ⟨gs, 0⟩ _ r hr14]
                      have hfin : ∀ (sb : Bool) (k : Fin 14),
                        (((((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun p =>
                          if (if sb then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))) p.2
                          then (false, p.1) else (p.1, false)).getD k.val (false, false)).1 =
                        decide (k = if sb then 0 else 7) := by decide +kernel
                      exact hfin s ⟨r, hr14⟩
                    · let m := r - 14
                      have hm : m < gs.length := by omega
                      have hrm : r = 14 + m := by omega
                      rw [hrm]
                      obtain ⟨hminp, hmop, hma, hmb⟩ := gate_inputs2 ⟨gs, 0⟩ hgsAO m hm
                      have hgm : gs[m] = gateAt ⟨gs, 0⟩ m := by
                        unfold gateAt; rw [List.getD_eq_getElem _ _ hm]
                      have hsp : gs = gs.take m ++ gateAt ⟨gs, 0⟩ m :: gs.drop (m + 1) := by
                        rw [← hgm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
                      let pr := (gs.take m).foldl lpStep baseS
                      have hprlen : pr.length = 14 + m := by
                        dsimp only [pr]; rw [lpfold_len, List.length_take]; simp [baseS]; omega
                      have hprstep_len : (lpStep pr (gateAt ⟨gs, 0⟩ m)).length = 14 + m + 1 := by
                        simp only [lpStep, List.length_append, List.length_singleton, hprlen]
                      have hlpe : lpOld = (gs.drop (m + 1)).foldl lpStep (lpStep pr (gateAt ⟨gs, 0⟩ m)) := by
                        rw [hlpOld_def]; conv_lhs => rw [hsp]
                        rw [List.foldl_append, List.foldl_cons]
                      have hprg : ∀ i < 14 + m, pr.getD i (false, false) = lpOld.getD i (false, false) := by
                        intro i hi
                        rw [hlpe, lpfold_getD_lt (gs.drop (m + 1)) (lpStep pr (gateAt ⟨gs, 0⟩ m)) i (by omega)]
                        simp only [lpStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pr.length)]
                      have hstepm : lpOld.getD (14 + m) (false, false) =
                          (lpStep pr (gateAt ⟨gs, 0⟩ m)).getD (14 + m) (false, false) := by
                        rw [hlpe, lpfold_getD_lt (gs.drop (m + 1)) (lpStep pr (gateAt ⟨gs, 0⟩ m)) (14 + m) (by omega)]
                      rw [hstepm]
                      have hstepm2 : (lpStep pr (gateAt ⟨gs, 0⟩ m)).getD (14 + m) (false, false) =
                          let ins := (gateAt ⟨gs, 0⟩ m).inputs.map fun i => pr.getD i (false, false)
                          GateOp.casesOn (gateAt ⟨gs, 0⟩ m).op
                            (ins.foldl (fun (acc : Bool × Bool) p =>
                              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
                            (ins.any (·.1), ins.any (·.2))
                            (false, false)
                            (fun _ => (false, false))
                            (false, false) := by
                        simp only [lpStep, List.getD_eq_getElem?_getD]
                        rw [List.getElem?_append_right (by omega), hprlen]; simp
                      rw [hstepm2, hminp]
                      simp only [List.map_cons, List.map_nil, hprg _ hma, hprg _ hmb]
                      rw [wire_gate ⟨gs, 0⟩ hgsAO _ m hm]
                      have hih0 := ih1 (opnd ⟨gs, 0⟩ m 0) (by omega) (by omega)
                      have hih1 := ih1 (opnd ⟨gs, 0⟩ m 1) (by omega) (by omega)
                      rcases hmop with hand | hor
                      · rw [hand, eval_and]
                        simp only [List.foldl_cons, List.foldl_nil, Bool.true_and, hih0, hih1]
                      · rw [hor, eval_or]
                        simp only [List.any_cons, List.any_nil, Bool.or_false, hih0, hih1]
                have hWa : (lpOld.getD a' (false, false)).1 = W.getD a false := by
                  rw [hlpOld_1 a' ha'lt]
                  have hAg := hAgree _ (h0_false_on_unit s) a hja
                  simpa only [ha', optW] using hAg
                have hWb : (lpOld.getD b' (false, false)).1 = W.getD b false := by
                  rw [hlpOld_1 b' hb'lt]
                  have hAg := hAgree _ (h0_false_on_unit s) b hjb
                  simpa only [hb', optW] using hAg
                have hVa : (lpOld.getD a' (false, false)).2 = v a := by
                  have ht := hTrace hcf s v hv0 hvstep a hja
                  simpa only [ha', optV, lpOld, isL] using ht
                have hVb : (lpOld.getD b' (false, false)).2 = v b := by
                  have ht := hTrace hcf s v hv0 hvstep b hjb
                  simpa only [hb', optV, lpOld, isL] using ht
                have hstepNew : (lpStep lpOld gnew).getD (14 + gs.length) (false, false) =
                    let ins := gnew.inputs.map fun i => lpOld.getD i (false, false)
                    GateOp.casesOn gnew.op
                      (ins.foldl (fun (acc : Bool × Bool) p =>
                        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
                      (ins.any (·.1), ins.any (·.2))
                      (false, false)
                      (fun _ => (false, false))
                      (false, false) := by
                  simp only [lpStep, List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega), hlenOld]; simp
                rw [hstepNew]
                rcases hop with rfl | rfl
                · dsimp only [gnew]
                  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
                    Bool.true_and, Bool.false_and, Bool.or_false, hWa, hWb, hVa, hVb]
                  exact ((hvstep j hjlt).1 hopEq.symm).symm
                · dsimp only [gnew]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                    Bool.or_false, hVa, hVb]
                  exact ((hvstep j hjlt).2 hopEq.symm).symm
              · simp only [hwj, ↓reduceIte]
                rw [hOptVold s w (by omega)]
                exact hTrace hcf s v hv0 hvstep w (by omega)
          -- Dispatch on gate j's op and (rep a, rep b)
          rcases hjop with hand | hor
          · cases hra : rep a with
            | none =>
              refine noEmit none coll (by intro _ h; cases h) (fun h => by have := hcoll3 h; omega)
                (by intro x h; simp [optW] at h) ?_ ?_
              · intro x hx14
                rw [wire_gate C hAO x j hjlt, hand, eval_and]
                have haF := hAgree x hx14 a hja
                simp only [hra, optW] at haF
                rw [← haF]; rfl
              · intro hcf
                refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                rw [(hvstep j hjlt).1 hand]
                have hWa := hAgree _ (h0_false_on_unit s) a hja
                have hVa := hTrace hcf s v hv0 hvstep a hja
                simp only [hra, optW, optV] at hWa hVa
                rw [← hWa, ← hVa]; rfl
            | some a' =>
              cases hrb : rep b with
              | none =>
                refine noEmit none coll (by intro _ h; cases h) (fun h => by have := hcoll3 h; omega)
                  (by intro x h; simp [optW] at h) ?_ ?_
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hand, eval_and]
                  have hbF := hAgree x hx14 b hjb
                  simp only [hrb, optW] at hbF
                  rw [← hbF]; simp [optW]
                · intro hcf
                  refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                  rw [(hvstep j hjlt).1 hand]
                  have hWb := hAgree _ (h0_false_on_unit s) b hjb
                  have hVb := hTrace hcf s v hv0 hvstep b hjb
                  simp only [hrb, optW, optV] at hWb hVb
                  rw [← hWb, ← hVb]; simp [optV]
              | some b' =>
                by_cases heq : a' = b'
                · subst heq
                  -- AND gate collapse: rep a = some a' = rep b, with a ≠ b!
                  have h2 : gs.length + 2 ≤ j :=
                    hInj a b hja hjb hab_ne (hra.trans hrb.symm) (by simp [hra])
                  refine noEmit (some a') true
                    (by intro w' h; cases h; exact hrepLt a hja a' hra)
                    (by intro _; omega) ?_ ?_ (by intro h; exact Bool.noConfusion h)
                  · intro x hval
                    rw [wire_gate C hAO x j hjlt, hand, eval_and, Bool.and_eq_true]
                    have hua := hUpper x a hja
                    have hub := hUpper x b hjb
                    simp only [hra, hrb] at hua hub
                    exact ⟨hua hval, hub hval⟩
                  · intro x hx14
                    rw [wire_gate C hAO x j hjlt, hand, eval_and]
                    have haa := hAgree x hx14 a hja
                    have hab := hAgree x hx14 b hjb
                    simp only [hra, hrb] at haa hab
                    rw [← haa, ← hab, Bool.and_self]
                · exact doEmit GateOp.and a' b' (Or.inl rfl) hand.symm hra hrb heq
          · cases hra : rep a with
            | none =>
              cases hrb : rep b with
              | none =>
                refine noEmit none coll (by intro _ h; cases h) (fun h => by have := hcoll3 h; omega)
                  (by intro x h; simp [optW] at h) ?_ ?_
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; rfl
                · intro hcf
                  refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                  rw [(hvstep j hjlt).2 hor]
                  have hVa := hTrace hcf s v hv0 hvstep a hja
                  have hVb := hTrace hcf s v hv0 hvstep b hjb
                  simp only [hra, hrb, optV] at hVa hVb
                  rw [← hVa, ← hVb]; rfl
              | some b' =>
                refine noEmit (some b') coll
                  (by intro w' h; cases h; exact hrepLt b hjb b' hrb)
                  (fun h => by have := hcoll3 h; omega) ?_ ?_ ?_
                · intro x hval
                  rw [wire_gate C hAO x j hjlt, hor, eval_or, Bool.or_eq_true]
                  have hub := hUpper x b hjb
                  simp only [hrb] at hub
                  exact Or.inr (hub hval)
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; simp [optW]
                · intro hcf
                  refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                  rw [(hvstep j hjlt).2 hor]
                  have hVa := hTrace hcf s v hv0 hvstep a hja
                  have hVb := hTrace hcf s v hv0 hvstep b hjb
                  simp only [hra, hrb, optV] at hVa hVb
                  rw [← hVa, ← hVb]; simp [optV]
            | some a' =>
              cases hrb : rep b with
              | none =>
                refine noEmit (some a') coll
                  (by intro w' h; cases h; exact hrepLt a hja a' hra)
                  (fun h => by have := hcoll3 h; omega) ?_ ?_ ?_
                · intro x hval
                  rw [wire_gate C hAO x j hjlt, hor, eval_or, Bool.or_eq_true]
                  have hua := hUpper x a hja
                  simp only [hra] at hua
                  exact Or.inl (hua hval)
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; simp [optW]
                · intro hcf
                  refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                  rw [(hvstep j hjlt).2 hor]
                  have hVa := hTrace hcf s v hv0 hvstep a hja
                  have hVb := hTrace hcf s v hv0 hvstep b hjb
                  simp only [hra, hrb, optV] at hVa hVb
                  rw [← hVa, ← hVb]; simp [optV]
              | some b' =>
                by_cases heq : a' = b'
                · subst heq
                  refine noEmit (some a') coll
                    (by intro w' h; cases h; exact hrepLt a hja a' hra)
                    (fun h => by have := hcoll3 h; omega) ?_ ?_ ?_
                  · intro x hval
                    rw [wire_gate C hAO x j hjlt, hor, eval_or, Bool.or_eq_true]
                    have hua := hUpper x a hja
                    simp only [hra] at hua
                    exact Or.inl (hua hval)
                  · intro x hx14
                    rw [wire_gate C hAO x j hjlt, hor, eval_or]
                    have haa := hAgree x hx14 a hja
                    have hab := hAgree x hx14 b hjb
                    simp only [hra, hrb] at haa hab
                    rw [← haa, ← hab, Bool.or_self]
                  · intro hcf
                    refine ⟨hcf, fun s v hv0 hvstep => ?_⟩
                    rw [(hvstep j hjlt).2 hor]
                    have hVa := hTrace hcf s v hv0 hvstep a hja
                    have hVb := hTrace hcf s v hv0 hvstep b hjb
                    simp only [hra, hrb] at hVa hVb
                    rw [← hVa, ← hVb, Bool.or_self]
                · exact doEmit GateOp.or a' b' (Or.inr rfl) hor.symm hra hrb heq
    obtain ⟨gs, rep, coll, hgsAO, hgsDist, hlen1, hcoll3, hrepLt, _, hUpper, hAgree, hTrace⟩ :=
      hBuild C.size hCsize_pos (le_refl _)
    cases hrepOut : rep C.output with
    | none =>
      have h07 : C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7) ∨ i = Fin.natAdd 7 (0 : Fin 7))) = true :=
        (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
      have hAg := hAgree _ (h0_false_on_edge 0 0 (Or.inl rfl)) C.output hCout
      simp only [hrepOut, optW] at hAg
      exact Bool.noConfusion (hAg.trans h07)
    | some out' =>
      let D : Circuit := ⟨gs, out'⟩
      have hDAO : IsAO2 14 D := hgsAO
      have hDdist : ∀ k < D.size, opnd D k 0 ≠ opnd D k 1 := hgsDist
      have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
        intro x
        constructor
        · intro hx
          have hup := hUpper x C.output hCout
          simp only [hrepOut, optW] at hup
          exact (hFano x).mp (hup hx)
        · rintro ⟨u, t, hut, hu, ht⟩
          let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)
          have hCe : C.eval (List.ofFn e) = true := (hFano e).mpr ⟨u, t, hut, by simp [e], by simp [e]⟩
          have hDe : (D.wires (List.ofFn e)).getD out' false = true := by
            have hAg := hAgree e (h0_false_on_edge u t hut) C.output hCout
            simp only [hrepOut, optW] at hAg
            exact hAg.trans hCe
          have houtLt : out' < 14 + D.size := hrepLt C.output hCout out' hrepOut
          refine eval_mono D hDAO e x (fun i hi => ?_) out' houtLt hDe
          simp only [e, decide_eq_true_eq] at hi
          rcases hi with rfl | rfl
          · exact hu
          · exact ht
      cases hc : coll with
      | true =>
        have h24 : D.size ≤ 24 := by
          have := hcoll3 hc; change gs.length ≤ 24; omega
        exact noSmall24 D h24 hDAO hDdist hDFano
      | false =>
        have h26 : D.size ≤ 26 := by change gs.length ≤ 26; omega
        have hDsr : ¬ IsSingleRead D 14 (fun i => decide (7 ≤ i)) [(0, 7)] := by
          intro hsr
          have hline : ∀ s : Bool,
              lineSingle D 14 (if s then (fun i => decide (7 ≤ i)) else (fun i => !decide (7 ≤ i))) 0 7 = false := by
            intro s
            obtain ⟨v, hv0, hvstep, hvout⟩ := hDeriv s
            have ht := hTrace hc s v hv0 hvstep C.output hCout
            simp only [hrepOut, optV] at ht
            exact ht.trans hvout
          have ht := hline true
          have hf := hline false
          simp only [Bool.false_eq_true, ↓reduceIte] at ht hf
          dsimp only [IsSingleRead, doubleReread] at hsr
          simp only [List.filter_cons, List.filter_nil, ht, hf, Bool.not_false, Bool.and_self, ↓reduceIte] at hsr
          cases hsr
        exact noDouble26 D h26 hDAO hDdist hDFano hDsr
