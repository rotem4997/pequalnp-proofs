import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5206_1
    (h1 : ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      have D : Finset (Fin 13) := {0, 1, 3, 9}
      have wv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal 26 C
      have o : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd C
      have isA : ℕ → Prop := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and
      have p0 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0
      have p13 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13
      have bl : ℕ → ℕ → Prop := fun m w => 26 + m = w ∨ PEqualNP.EdgeOwnership.InCone 26 C m (w - 26)
      have dr : ℕ → Prop := fun m => isA m ∧ wv (26 + m) p0 = false ∧
        ∀ b : Fin 2, wv (o m b) p0 ≠ wv (o m b) p13
      C.size ≤ 64 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ x : Fin 26 → Bool, wv (26 + d) x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ k m : ℕ, isA k ∧ bl k C.output ∧
        wv (26 + k) (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true ∧
        (∀ b : Fin 2, wv (o k b) p0 = false ∧ wv (o k b) p13 = false ∧ bl m (o k b)) ∧
        dr m)
    (h2 : ¬∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
      have D : Finset (Fin 13) := {0, 1, 3, 9}
      have wv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal 26 C
      have o : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd C
      have isA : ℕ → Prop := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and
      have p0 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0
      have p13 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13
      have bl : ℕ → ℕ → Prop := fun m w => 26 + m = w ∨ PEqualNP.EdgeOwnership.InCone 26 C m (w - 26)
      have dr : ℕ → Prop := fun m => isA m ∧ wv (26 + m) p0 = false ∧
        ∀ b : Fin 2, wv (o m b) p0 ≠ wv (o m b) p13
      C.size ≤ 64 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ x : Fin 26 → Bool, wv (26 + d) x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ (k : ℕ) (m : Fin 2 → ℕ), Function.Injective m ∧ isA k ∧ bl k C.output ∧
        wv (26 + k) (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true ∧
        ∀ b : Fin 2, wv (o k b) p0 = false ∧ wv (o k b) p13 = false ∧
          bl (m b) (o k b) ∧ dr (m b)) : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨hSize, hGates, hEval, hJunk, k, hkA, hkLive, hkT, hkF⟩ := hC
  let wstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) (r : ℕ),
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
  have eval_and : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have wireVal_input : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 26 → Bool) (r : ℕ) (hr : r < 26),
      PEqualNP.CleanedNonEdge.wireVal 26 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlt : r < (List.ofFn x).length := by simp [hr]
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 26 → Bool) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 26 + k) →
      PEqualNP.CleanedNonEdge.wireVal 26 D (26 + k) x = g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 26 D i x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 := List.cons_getElem_drop_succ (l := D.gates) (n := k) (h := hk)
      have hg_eq : D.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hgk)
      rw [hg_eq] at h2
      rw [h2]; exact h1.symm
    have hlen_pre : ((D.gates.take k).foldl wstep (List.ofFn x)).length = 26 + k := by
      rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hpre_val : ∀ i, i < 26 + k →
        PEqualNP.CleanedNonEdge.wireVal 26 D i x = ((D.gates.take k).foldl wstep (List.ofFn x)).getD i false := by
      intro i hi
      change (D.gates.foldl wstep (List.ofFn x)).getD i false = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, wfold_getD_lt _ _ i (by omega)]
    change (D.gates.foldl wstep (List.ofFn x)).getD (26 + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlen_mid : (wstep ((D.gates.take k).foldl wstep (List.ofFn x)) g).length = 26 + k + 1 := by
      simp only [wstep, List.length_append, List.length_singleton, hlen_pre]
    rw [wfold_getD_lt _ _ (26 + k) (by omega)]
    have hmid_val : (wstep ((D.gates.take k).foldl wstep (List.ofFn x)) g).getD (26 + k) false =
        g.op.eval (g.inputs.map fun i => ((D.gates.take k).foldl wstep (List.ofFn x)).getD i false) := by
      generalize hpre_def : (D.gates.take k).foldl wstep (List.ofFn x) = pre at hlen_pre ⊢
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hlen_pre])]
      simp only [hlen_pre, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hmid_val]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (hpre_val i (hlt i hi)).symm
  have cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g rest ih =>
      intro cs
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + rest.length = cs.length + (g :: rest).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (r : ℕ),
      r < cs.length → (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) cs).getD r [] = cs.getD r [] := by
    intro gs
    induction gs with
    | nil => intro cs r _; rfl
    | cons g rest ih =>
      intro cs r hr
      simp only [List.foldl_cons]
      have hr' : r < (PEqualNP.EdgeOwnership.coneStep 26 cs g).length := by
        change r < (cs ++ [_]).length
        simp only [List.length_append, List.length_singleton]; omega
      rw [ih (PEqualNP.EdgeOwnership.coneStep 26 cs g) r hr']
      change (cs ++ [_]).getD r [] = cs.getD r []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have inCone_iff : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      PEqualNP.EdgeOwnership.InCone 26 D i j ↔ j < D.gates.length ∧
        ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs, 26 ≤ w ∧ w < 26 + j ∧
          (i = w - 26 ∨ PEqualNP.EdgeOwnership.InCone 26 D i (w - 26)) := by
    intro D i j
    change i ∈ (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD j [] ↔ _
    by_cases hj : j < D.gates.length
    · have hsplit : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j D.gates
        have h2 := List.cons_getElem_drop_succ (l := D.gates) (n := j) (h := hj)
        rw [h2]; exact h1.symm
      have hlen_pre : ((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []).length = j := by
        rw [cones_len, List.length_nil, Nat.zero_add, List.length_take]; omega
      have hpre_cone : ∀ m, m < j →
          (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD m [] =
            ((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD m [] := by
        intro m hm
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, cones_getD_lt _ _ m (by omega)]
      have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates[j] := by
        change D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = D.gates[j]
        rw [List.getD_eq_getElem _ _ hj]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      have hlen_mid : (PEqualNP.EdgeOwnership.coneStep 26 ((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []) D.gates[j]).length = j + 1 := by
        change (((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []) ++ [_]).length = j + 1
        simp only [List.length_append, List.length_singleton, hlen_pre]
      rw [cones_getD_lt _ _ j (by omega)]
      have hmid_val : (PEqualNP.EdgeOwnership.coneStep 26 ((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []) D.gates[j]).getD j [] =
          ((D.gates[j].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + j))).flatMap
            (fun w => (w - 26) :: ((D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD (w - 26) [])) := by
        generalize hpre_def : (D.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) [] = pre at hlen_pre ⊢
        change (pre ++ [((D.gates[j].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + pre.length))).flatMap
          (fun w => (w - 26) :: pre.getD (w - 26) []))]).getD j [] = _
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [hlen_pre])]
        simp only [hlen_pre, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hmid_val]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq, hgateAt]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨hj, w, hw, h1, h2, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · right
          change i ∈ (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD (w - 26) []
          rw [hpre_cone (w - 26) (by omega)]
          exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · right
          have h3c : i ∈ (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD (w - 26) [] := h3
          rw [hpre_cone (w - 26) (by omega)] at h3c
          exact h3c
    · have hlen : (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).length = D.gates.length := by
        rw [cones_len]; simp
      have hnone : (D.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD j [] = [] :=
        List.getD_eq_default _ _ (by omega)
      rw [hnone]
      simp [hj]
  have hp : ∀ (u v w : Fin 26), PEqualNP.EdgeOwnership.pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
  have bool4 : ∀ a b c d : Bool, (a && c) = false → (b && d) = false →
      ¬(a = false ∧ b = false) → ¬(c = false ∧ d = false) → a ≠ b ∧ c ≠ d := by decide
  have hfin2 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hshape : ∀ j : ℕ, j < C.gates.length → ∃ (g : PEqualNP.CircuitLowerBounds.Gate) (c d : ℕ),
      C.gates[j]? = some g ∧ PEqualNP.MetaComplexity.NestedCover.gateAt C j = g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs = [c, d] ∧ c < 26 + j ∧ d < 26 + j ∧ PEqualNP.TopForm.opnd C j 0 = c ∧ PEqualNP.TopForm.opnd C j 1 = d ∧
      (∀ i ∈ g.inputs, i < 26 + j) := by
    intro j hj
    have hgj : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    obtain ⟨hop, c, d, hinp, _, hc, hd⟩ := hGates j C.gates[j] hgj
    have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
      rw [List.getD_eq_getElem _ _ hj]
    refine ⟨C.gates[j], c, d, hgj, hgateAt, hop, hinp, hc, hd, ?_, ?_, ?_⟩
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = c
      rw [hgateAt, hinp]; rfl
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = d
      rw [hgateAt, hinp]; rfl
    · intro i hi
      rw [hinp] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hc
      · exact hd
  have hdesc : ∀ w : ℕ, w < 26 + C.gates.length →
      PEqualNP.CleanedNonEdge.wireVal 26 C w (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true →
      PEqualNP.CleanedNonEdge.wireVal 26 C w (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0) = false →
      PEqualNP.CleanedNonEdge.wireVal 26 C w (PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13) = false →
      ∃ m : ℕ, 26 ≤ w ∧ (m = w - 26 ∨ PEqualNP.EdgeOwnership.InCone 26 C m (w - 26)) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.CleanedNonEdge.wireVal 26 C (26 + m) (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0) = false ∧
        ∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C m b) (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0) ≠
          PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C m b) (PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw h013 h0 h13
      by_cases hw26 : w < 26
      · exfalso
        rw [wireVal_input C _ w hw26, hp] at h013 h0 h13
        rcases of_decide_eq_true h013 with h | h
        · rw [h] at h0
          exact absurd h0 (by decide)
        · rw [h] at h13
          exact absurd h13 (by decide)
      · have hj : w - 26 < C.gates.length := by omega
        have hwj : w = 26 + (w - 26) := by omega
        obtain ⟨g, c, d, hgj, hgateAt, hop, hinp, hc, hd, ho0, ho1, hlt⟩ := hshape (w - 26) hj
        rw [hwj, wireVal_gate C _ (w - 26) g hgj hlt, hinp] at h013 h0 h13
        simp only [List.map_cons, List.map_nil] at h013 h0 h13
        have hcone : ∀ (e m : ℕ), e ∈ g.inputs → e < 26 + (w - 26) → 26 ≤ e →
            (m = e - 26 ∨ PEqualNP.EdgeOwnership.InCone 26 C m (e - 26)) → PEqualNP.EdgeOwnership.InCone 26 C m (w - 26) := by
          intro e m he helt hege hm
          refine (inCone_iff C m (w - 26)).mpr ⟨hj, e, ?_, hege, helt, hm⟩
          rw [hgateAt]; exact he
        have hcmem : c ∈ g.inputs := by rw [hinp]; exact List.mem_cons_self
        have hdmem : d ∈ g.inputs := by
          rw [hinp]; exact List.mem_cons_of_mem _ List.mem_cons_self
        rcases hop with hand | hor
        · rw [hand, eval_and] at h013 h0 h13
          rw [Bool.and_eq_true] at h013
          by_cases hcr : PEqualNP.CleanedNonEdge.wireVal 26 C c (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0) = false ∧
              PEqualNP.CleanedNonEdge.wireVal 26 C c (PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13) = false
          · obtain ⟨m, hm26, hm, hdir⟩ := ih c (by omega) (by omega) h013.1 hcr.1 hcr.2
            exact ⟨m, by omega, Or.inr (hcone c m hcmem hc hm26 hm), hdir⟩
          · by_cases hdr : PEqualNP.CleanedNonEdge.wireVal 26 C d (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 0) = false ∧
                PEqualNP.CleanedNonEdge.wireVal 26 C d (PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) 13) = false
            · obtain ⟨m, hm26, hm, hdir⟩ := ih d (by omega) (by omega) h013.2 hdr.1 hdr.2
              exact ⟨m, by omega, Or.inr (hcone d m hdmem hd hm26 hm), hdir⟩
            · have hb4 := bool4 _ _ _ _ h0 h13 hcr hdr
              refine ⟨w - 26, by omega, Or.inl rfl, ?_, ?_, ?_⟩
              · rw [hgateAt]; exact hand
              · rw [wireVal_gate C _ (w - 26) g hgj hlt, hinp]
                simp only [List.map_cons, List.map_nil]
                rw [hand, eval_and]; exact h0
              · intro b
                rcases hfin2 b with rfl | rfl
                · rw [ho0]; exact hb4.1
                · rw [ho1]; exact hb4.2
        · rw [hor, eval_or] at h013 h0 h13
          rw [Bool.or_eq_true] at h013
          rw [Bool.or_eq_false_iff] at h0 h13
          rcases h013 with hc013 | hd013
          · obtain ⟨m, hm26, hm, hdir⟩ := ih c (by omega) (by omega) hc013 h0.1 h13.1
            exact ⟨m, by omega, Or.inr (hcone c m hcmem hc hm26 hm), hdir⟩
          · obtain ⟨m, hm26, hm, hdir⟩ := ih d (by omega) (by omega) hd013 h0.2 h13.2
            exact ⟨m, by omega, Or.inr (hcone d m hdmem hd hm26 hm), hdir⟩
  have hk : k < C.gates.length := by
    by_contra hge
    have hdef : PEqualNP.MetaComplexity.NestedCover.gateAt C k = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_default _ _ (by omega)
    rw [hdef] at hkA
    cases hkA
  obtain ⟨g, c, d, hgk, hgateAt, hop, hinp, hc, hd, ho0, ho1, hlt⟩ := hshape k hk
  have hkT' : PEqualNP.CleanedNonEdge.wireVal 26 C (26 + k) (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true := hkT
  have hgand : g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by rw [← hgateAt]; exact hkA
  rw [wireVal_gate C _ k g hgk hlt, hinp] at hkT'
  simp only [List.map_cons, List.map_nil] at hkT'
  rw [hgand, eval_and, Bool.and_eq_true] at hkT'
  have hF0 := hkF 0
  have hF1 := hkF 1
  rw [ho0] at hF0
  rw [ho1] at hF1
  obtain ⟨m1, hm26, hm1, hdir1⟩ := hdesc c (by omega) hkT'.1 hF0.1 hF0.2
  obtain ⟨m2, hn26, hm2, hdir2⟩ := hdesc d (by omega) hkT'.2 hF1.1 hF1.2
  have hbl1 : 26 + m1 = PEqualNP.TopForm.opnd C k 0 ∨ PEqualNP.EdgeOwnership.InCone 26 C m1 (PEqualNP.TopForm.opnd C k 0 - 26) := by
    rw [ho0]
    rcases hm1 with h | h
    · left; omega
    · exact Or.inr h
  have hbl2 : 26 + m2 = PEqualNP.TopForm.opnd C k 1 ∨ PEqualNP.EdgeOwnership.InCone 26 C m2 (PEqualNP.TopForm.opnd C k 1 - 26) := by
    rw [ho1]
    rcases hm2 with h | h
    · left; omega
    · exact Or.inr h
  by_cases hEq : m1 = m2
  · subst hEq
    refine h1 ⟨C, hSize, hGates, hEval, hJunk, k, m1, hkA, hkLive, hkT, ?_, hdir1⟩
    intro b
    rcases hfin2 b with rfl | rfl
    · exact ⟨(hkF 0).1, (hkF 0).2, hbl1⟩
    · exact ⟨(hkF 1).1, (hkF 1).2, hbl2⟩
  · refine h2 ⟨C, hSize, hGates, hEval, hJunk, k, fun b => if b = 0 then m1 else m2, ?_,
      hkA, hkLive, hkT, ?_⟩
    · intro a b hab
      rcases hfin2 a with rfl | rfl <;> rcases hfin2 b with rfl | rfl
      · rfl
      · exact absurd (show m1 = m2 from hab) hEq
      · exact absurd (show m2 = m1 from hab).symm hEq
      · rfl
    · intro b
      rcases hfin2 b with rfl | rfl
      · exact ⟨(hkF 0).1, (hkF 0).2, hbl1, hdir1⟩
      · exact ⟨(hkF 1).1, (hkF 1).2, hbl2, hdir2⟩
