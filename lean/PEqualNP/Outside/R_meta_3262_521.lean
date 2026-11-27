import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_3262_521
    (hTopForm : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsAO2 x1 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      ∃ x8 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO x2 x8 ∧
        PEqualNP.TopForm.TopForm x2 x8 ∧
        x8.size ≤ x4.size ∧
        ∀ x9 : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO x2 x9 →
          PEqualNP.TopForm.TopForm x2 x9 →
          (PEqualNP.TopForm.Ustar x2 x8).card ≤ (PEqualNP.TopForm.Ustar x2 x9).card)
    (hLedger : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle x2 →
      x2.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO x2 x4 →
      PEqualNP.TopForm.TopForm x2 x4 →
      x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card +
        (PEqualNP.TopForm.junk x2 x4).card +
        (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ≤
        x4.size + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) ∧
      ∀ x9 : Finset (Fin x1),
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (x2.deleteEdges ↑(PEqualNP.TopForm.Ustar x2 x4)) x9 →
        x9.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card)
    (hResidual : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
        (x4 : Fin x1 → Bool) (x5 : Fin x1 → Fin x1) (x6 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin x1, x2.Adj u v → x4 u ≠ x4 v) →
      Function.Involutive x5 →
      (∀ u : Fin x1, x2.Adj u (x5 u)) →
      PEqualNP.TopForm.NoFourCycle x2 →
      PEqualNP.TopForm.IsLeastAO x2 x6 →
      PEqualNP.TopForm.TopForm x2 x6 →
      (∀ K : Finset (Fin x1), (∀ u v : Fin x1, x2.Adj u v → u ∈ K ∨ v ∈ K) →
        x6.size + (1 : ℕ) < x2.edgeFinset.card + K.card) →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x6).card →
      (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x6).card →
      (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card +
        (PEqualNP.TopForm.junk x2 x6).card +
        (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card →
      (∀ A : Finset (Fin x1),
        (∀ e ∈ PEqualNP.TopForm.Ustar x2 x6, ∃ v ∈ A, v ∈ e) →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card +
          (PEqualNP.TopForm.junk x2 x6).card +
          (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card <
          A.card + (PEqualNP.TopForm.Ustar x2 x6).card) →
      False) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  have hCore : ∀ (nv : ℕ) (G : SimpleGraph (Fin nv)) [DecidableRel G.Adj]
      (col : Fin nv → Bool) (C : Circuit),
      0 < nv →
      (∀ u v : Fin nv, G.Adj u v → col u ≠ col v) →
      (∀ a b c : Fin nv, G.Adj a b → G.Adj b c → G.Adj a c → False) →
      NoFourCycle G →
      G.edgeFinset.Nonempty →
      (∀ x : Fin nv → Bool, graphFun G ∅ x = true ↔ ∃ u v : Fin nv, G.Adj u v ∧ x u = true ∧ x v = true) →
      IsLeastAO G C →
      TopForm G C →
      (∀ A : Finset (Fin nv), (∀ e ∈ Ustar G C, ∃ v ∈ A, v ∈ e) →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < A.card + (Ustar G C).card) →
      2 ≤ (junk G C).card ∧ 3 ≤ (Ustar G C).card ∧
        5 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
    classical
    let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    intro nv G _ col C hnvPos hCol hNoTri hNo4 hGne hG_hasEdge hLeast hTop hBudgetLtCov
    let stepWire : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
    have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
    have wires_def : ∀ (C' : Circuit) (x : List Bool), C'.wires x = C'.gates.foldl stepWire x :=
      fun _ _ => rfl
    have size_def : ∀ (C' : Circuit), C'.size = C'.gates.length := fun _ => rfl
    have eval_def : ∀ (C' : Circuit) (x : List Bool), C'.eval x = (C'.wires x).getD C'.output false :=
      fun _ _ => rfl
    have circuitFun_def : ∀ (k : ℕ) (C' : Circuit) (x : Fin k → Bool),
        circuitFun k C' x = (C'.wires (List.ofFn x)).getD C'.output false := fun _ _ _ => rfl
    have gateAt_def : ∀ (C' : Circuit) (j : ℕ), gateAt C' j = C'.gates.getD j ⟨GateOp.or, []⟩ :=
      fun _ _ => rfl
    have gateVal_def : ∀ (C' : Circuit) (j : ℕ) (x : Fin nv → Bool),
        gateVal nv C' j x = (C'.wires (List.ofFn x)).getD (nv + j) false := fun _ _ _ => rfl
    have opnd_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
        opnd C' a b = (gateAt C' a).inputs.getD b.val 0 := fun _ _ _ => rfl
    have pairInput_def : ∀ (u v w : Fin nv), pairInput u v w = decide (w = u ∨ w = v) :=
      fun _ _ _ => rfl
    have pairInput_symm : ∀ (u v : Fin nv), pairInput u v = pairInput v u := fun u v =>
      funext fun w => by simp only [pairInput_def, or_comm]
    have foldl_length : ∀ (gs : List Gate) (w : List Bool),
        (gs.foldl stepWire w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
        omega
    have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro _ _ _; rfl
      | cons g gs ih =>
        intro w i hi
        rw [List.foldl_cons, ih (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
        simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
      intro w i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
    have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
        coneStep nv cs g = cs ++ [(g.inputs.filter (fun w => decide (nv ≤ w ∧ w < nv + cs.length))).flatMap
          (fun w => (w - nv) :: cs.getD (w - nv) [])] := by
      intro cs g
      change cs ++ [(g.inputs.filter (fun w => @decide (nv ≤ w ∧ w < nv + cs.length) _)).flatMap
        (fun w => (w - nv) :: cs.getD (w - nv) [])] = _
      congr 2
    have cones_def : ∀ (C' : Circuit), cones nv C' = C'.gates.foldl (coneStep nv) [] := fun _ => rfl
    have inCone_def : ∀ (C' : Circuit) (i j : ℕ), InCone nv C' i j = (i ∈ (cones nv C').getD j []) :=
      fun _ _ _ => rfl
    have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
        orStep nv cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
          (g.inputs.filter (fun w => decide (nv ≤ w ∧ w < nv + cs.length))).flatMap
            (fun w => cs.getD (w - nv) [])
          else [])] := by
      intro cs g
      change cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
        ((g.inputs.filter (fun w => @decide (nv ≤ w ∧ w < nv + cs.length) _)).flatMap
          (fun w => cs.getD (w - nv) [])) [])] = _
      by_cases hop : g.op = GateOp.or
      · rw [if_pos hop]
      · rw [if_neg hop]
    have orSets_def : ∀ (C' : Circuit), orSets nv C' = C'.gates.foldl (orStep nv) [] := fun _ => rfl
    have orReaches_def : ∀ (C' : Circuit) (w g : ℕ),
        OrReaches nv C' w g = (nv ≤ w ∧ g ∈ (orSets nv C').getD (w - nv) []) := fun _ _ _ => rfl
    have orIn_def : ∀ (C' : Circuit) (w : ℕ) (i : Fin nv),
        i ∈ orIn nv C' w ↔ ((i : ℕ) = w ∨ ∃ k < C'.gates.length,
          OrReaches nv C' w k ∧ (gateAt C' k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C' k).inputs) := by
      intro C' w i
      exact (@Finset.mem_filter _ _ _ Finset.univ i).trans (by simp only [Finset.mem_univ, true_and])
    have side_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
        side (n := nv) C' a b = orIn nv C' (opnd C' a b) := fun _ _ _ => rfl
    have tops_mem : ∀ (C' : Circuit) (j : ℕ),
        j ∈ tops G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧ BelowF G C' j := by
      intro C' j
      exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
    have junk_mem : ∀ (C' : Circuit) (j : ℕ),
        j ∈ junk G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧
          ∃ x : Fin nv → Bool, gateVal nv C' j x = true ∧ graphFun G ∅ x = false := by
      intro C' j
      refine (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans ?_
      rw [Finset.mem_range]
      exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.1, h.2.2⟩⟩
    have orN_mem : ∀ (C' : Circuit) (j : ℕ),
        j ∈ orN G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.or ∧ ¬ BelowF G C' j := by
      intro C' j
      exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
    have lam_mem : ∀ (C' : Circuit) (h : ℕ),
        h ∈ lam G C' ↔ h ∈ orN G C' ∧ (orIn nv C' (opnd C' h 0)).Nonempty ∧
          (orIn nv C' (opnd C' h 1)).Nonempty ∧ ∃ a ∈ tops G C', ∃ b : Fin 2,
            (side (n := nv) C' a (1 - b)).card = 1 ∧ OrReaches nv C' (opnd C' a b) h := by
      intro C' h
      exact @Finset.mem_filter _ _ _ (orN G C') h
    have centreless_mem : ∀ (C' : Circuit) (a : ℕ),
        a ∈ centreless G C' ↔ a ∈ tops G C' ∧ (side (n := nv) C' a 0 = ∅ ∨ side (n := nv) C' a 1 = ∅) := by
      intro C' a
      exact @Finset.mem_filter _ _ _ (tops G C') a
    have readers_mem : ∀ (C' : Circuit) (j k : ℕ),
        k ∈ readers nv C' j ↔ k < C'.gates.length ∧ nv + j ∈ (gateAt C' k).inputs := by
      intro C' j k
      exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) k).trans (by rw [Finset.mem_range])
    have starEdges_def : ∀ (C' : Circuit),
        starEdges G C' = (tops G C').biUnion (fun a => (side (n := nv) C' a 0 ×ˢ side (n := nv) C' a 1).image (fun p => s(p.1, p.2))) :=
      fun _ => rfl
    have Ustar_def : ∀ (C' : Circuit), Ustar G C' = G.edgeFinset \ starEdges G C' := fun _ => rfl
    have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
        (gs.foldl stepWire w).getD (w.length + j) false =
          (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
      intro gs
      induction gs with
      | nil => intro _ _ hj; simp only [List.length_nil] at hj; omega
      | cons g gs ih =>
        intro w j hj
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepWire w g).length := by simp only [stepWire, List.length_append, List.length_singleton]; omega
          rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (stepWire w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
            simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]
            exact getD_ge w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
          have key := ih (stepWire w g) j hj'
          have hl : (stepWire w g).length = w.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key
    let val : Circuit → List Bool → ℕ → Bool := fun C' x u => (C'.wires x).getD u false
    have gateAt_eq : ∀ {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length), gateAt C' j = C'.gates[j] := by
      intro C' j hj
      rw [gateAt_def]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have gateAt_mem : ∀ {C' : Circuit} {j : ℕ}, j < C'.gates.length → gateAt C' j ∈ C'.gates := by
      intro C' j hj
      rw [gateAt_eq hj]
      exact List.getElem_mem hj
    have val_input : ∀ {C' : Circuit} {x : List Bool}, x.length = nv → ∀ {u : ℕ}, u < nv →
        val C' x u = x.getD u false := by
      intro C' x hx u hu
      change (C'.wires x).getD u false = _
      rw [wires_def]
      exact foldl_getD_lt _ _ _ (by omega)
    have val_ge : ∀ {C' : Circuit} {x : List Bool}, x.length = nv → ∀ {u : ℕ}, nv + C'.gates.length ≤ u →
        val C' x u = false := by
      intro C' x hx u hu
      change (C'.wires x).getD u false = false
      apply getD_ge
      rw [wires_def, foldl_length]
      omega
    have val_gate : ∀ {C' : Circuit} {x : List Bool}, x.length = nv → ∀ {j : ℕ}, j < C'.gates.length →
        val C' x (nv + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
          if i < nv + j then val C' x i else false) := by
      intro C' x hx j hj
      rw [← hx]
      change (C'.wires x).getD (x.length + j) false = _
      rw [wires_def, gateAt_eq hj]
      exact foldl_getD_gate C'.gates x j hj
    have val_or : ∀ {C' : Circuit} {x : List Bool}, x.length = nv → ∀ {r : ℕ}, r < C'.gates.length →
        (gateAt C' r).op = GateOp.or →
        (val C' x (nv + r) = true ↔ ∃ i ∈ (gateAt C' r).inputs, i < nv + r ∧ val C' x i = true) := by
      intro C' x hx r hr hop
      rw [val_gate hx hr, hop, eval_or]
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      constructor
      · rintro ⟨i, hi, h⟩
        by_cases hlt : i < nv + r
        · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
        · rw [if_neg hlt] at h; exact Bool.noConfusion h
      · rintro ⟨i, hi, hlt, h⟩
        exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
    have val_and : ∀ {C' : Circuit} {x : List Bool}, x.length = nv → ∀ {r : ℕ}, r < C'.gates.length →
        (gateAt C' r).op = GateOp.and →
        (val C' x (nv + r) = true ↔ ∀ i ∈ (gateAt C' r).inputs, i < nv + r ∧ val C' x i = true) := by
      intro C' x hx r hr hop
      rw [val_gate hx hr, hop, eval_and]
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have h' := h i hi
        by_cases hlt : i < nv + r
        · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
        · rw [if_neg hlt] at h'; exact Bool.noConfusion h'
      · intro h i hi
        rw [if_pos (h i hi).1]; exact (h i hi).2
    have val_ofFn : ∀ (C' : Circuit) (x : Fin nv → Bool) (u : Fin nv),
        val C' (List.ofFn x) u.val = x u := by
      intro C' x u
      rw [val_input List.length_ofFn u.isLt]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos u.isLt, Option.getD_some]
    have gateVal_eq_val : ∀ (C' : Circuit) (j : ℕ) (x : Fin nv → Bool),
        gateVal nv C' j x = val C' (List.ofFn x) (nv + j) := fun _ _ _ => rfl
    have pairInput_left : ∀ u v : Fin nv, pairInput u v u = true := by
      intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inl rfl)
    have pairInput_right : ∀ u v : Fin nv, pairInput u v v = true := by
      intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inr rfl)
    have pairInput_true : ∀ u v w : Fin nv, pairInput u v w = true ↔ w = u ∨ w = v := by
      intro u v w; rw [pairInput_def, decide_eq_true_eq]
    have graphFun_pair : ∀ u v : Fin nv, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
      intro u v
      rw [hG_hasEdge]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have ha' := (pairInput_true u v a).mp ha
        have hb' := (pairInput_true u v b).mp hb
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact (G.irrefl hab).elim
        · exact hab
        · exact hab.symm
        · exact (G.irrefl hab).elim
      · intro h
        exact ⟨u, v, h, pairInput_left u v, pairInput_right u v⟩
    have hOutLt : C.output < nv + C.gates.length := by
      by_contra hge
      obtain ⟨e0, he0⟩ := hGne
      induction e0 using Sym2.ind with
      | _ u0 v0 =>
        have hadj0 : G.Adj u0 v0 := SimpleGraph.mem_edgeFinset.mp he0
        have hv : val C (List.ofFn (pairInput u0 v0)) C.output = true := by
          have h : val C (List.ofFn (pairInput u0 v0)) C.output = graphFun G ∅ (pairInput u0 v0) :=
            congrFun hLeast.2.1 (pairInput u0 v0)
          rw [h]
          exact (graphFun_pair u0 v0).mpr hadj0
        rw [val_ge List.length_ofFn (by omega)] at hv
        exact Bool.noConfusion hv
    let shiftW : ℕ → ℕ → ℕ := fun k w => if w < nv + k then w else w - 1
    let unshiftW : ℕ → ℕ → ℕ := fun k w => if w < nv + k then w else w + 1
    let unshiftG : ℕ → ℕ → ℕ := fun k j => if j < k then j else j + 1
    let shiftGate : ℕ → Gate → Gate := fun k g => ⟨g.op, g.inputs.map (shiftW k)⟩
    let delDead : ℕ → Circuit → Circuit := fun k C' =>
      ⟨(C'.gates.eraseIdx k).map (shiftGate k), shiftW k C'.output⟩
    have unshiftW_shiftW : ∀ (k w : ℕ), w ≠ nv + k → unshiftW k (shiftW k w) = w := by
      intro k w hne; dsimp only [unshiftW, shiftW]; split_ifs <;> omega
    have delDead_length : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
        (delDead k C').gates.length = C'.gates.length - 1 := by
      intro k C' hk; dsimp only [delDead]; rw [List.length_map, List.length_eraseIdx_of_lt hk]
    have delDead_gateAt : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
        ∀ j, j < (delDead k C').gates.length →
        gateAt (delDead k C') j = shiftGate k (gateAt C' (unshiftG k j)) := by
      intro k C' hk j hj
      have hj_lt : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
      have hj_e : j < (C'.gates.eraseIdx k).length := by rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
      rw [gateAt_eq hj]
      dsimp only [delDead, unshiftG]
      rw [List.getElem_map]
      split_ifs with hjk
      · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (by omega)]
      · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
    have delDead_readsBack : ∀ (k : ℕ) (C' : Circuit), ReadsBack nv C' →
        k < C'.gates.length → (∀ j < C'.gates.length, nv + k ∉ (gateAt C' j).inputs) →
        ReadsBack nv (delDead k C') := by
      intro k C' hRB hk hno j hj w' hw'
      rw [delDead_gateAt k C' hk j hj] at hw'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
      have hj_len : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
      have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
      have hw_lt : w < nv + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
      have hw_ne : w ≠ nv + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
      dsimp only [shiftW]
      dsimp only [unshiftG] at hw_lt
      split_ifs at hw_lt ⊢ <;> omega
    have delDead_ao2 : ∀ (k : ℕ) (C' : Circuit), IsAO2 nv C' →
        k < C'.gates.length → (∀ j < C'.gates.length, nv + k ∉ (gateAt C' j).inputs) →
        IsAO2 nv (delDead k C') := by
      intro k C' h hk hno
      have mapped : ∀ g ∈ (delDead k C').gates,
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have hm := List.mem_of_mem_eraseIdx hg'
        exact ⟨h.1 g' hm, by dsimp only [shiftGate]; rw [List.length_map]; exact h.2.2 g' hm⟩
      exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack k C' h.2.1 hk hno,
        fun g hg => (mapped g hg).2⟩
    have delDead_wires_eq : ∀ (k : ℕ) (C' : Circuit) (l : List Bool), l.length = nv →
        ReadsBack nv C' → k < C'.gates.length → (∀ j < C'.gates.length, nv + k ∉ (gateAt C' j).inputs) →
        ∀ w : ℕ, val (delDead k C') l w = val C' l (unshiftW k w) := by
      intro k C' l hl hRB hk hno w
      have hRB' : ReadsBack nv (delDead k C') := delDead_readsBack k C' hRB hk hno
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hw_oob : nv + (delDead k C').gates.length ≤ w
        · have hdl := delDead_length k C' hk
          have huw : nv + C'.gates.length ≤ unshiftW k w := by dsimp only [unshiftW]; split_ifs <;> omega
          rw [val_ge hl hw_oob, val_ge hl huw]
        · by_cases hwn : w < nv
          · have huw : unshiftW k w = w := by dsimp only [unshiftW]; split_ifs <;> omega
            rw [huw, val_input hl hwn, val_input hl hwn]
          · let j := w - nv
            have hw_eq : w = nv + j := by omega
            have hj_lt : j < (delDead k C').gates.length := by omega
            have hdl := delDead_length k C' hk
            have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
            have huw : unshiftW k (nv + j) = nv + unshiftG k j := by
              dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
            rw [hw_eq, huw, val_gate hl hj_lt, val_gate hl hj0_lt, delDead_gateAt k C' hk j hj_lt]
            dsimp only [shiftGate]
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hu_lt' : shiftW k u < nv + j := by
              have hmem : shiftW k u ∈ (gateAt (delDead k C') j).inputs := by
                rw [delDead_gateAt k C' hk j hj_lt]
                exact List.mem_map.mpr ⟨u, hu, rfl⟩
              exact hRB' j hj_lt (shiftW k u) hmem
            have hu_lt0 : u < nv + unshiftG k j := hRB (unshiftG k j) hj0_lt u hu
            have hu_ne : u ≠ nv + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
            simp only [Function.comp_apply]
            rw [if_pos hu_lt', if_pos hu_lt0, ih (shiftW k u) (by omega), unshiftW_shiftW k u hu_ne]
    have leastReadAny : ∀ {j : ℕ}, j < C.gates.length → C.output ≠ nv + j → (readers nv C j).Nonempty := by
      intro j hj hout
      by_contra hnot
      have hno : ∀ k < C.gates.length, nv + j ∉ (gateAt C k).inputs := by
        intro k hk hin
        exact hnot ⟨k, (readers_mem C j k).mpr ⟨hk, hin⟩⟩
      have heq : circuitFun nv (delDead j C) = circuitFun nv C := by
        funext x
        rw [circuitFun_def, circuitFun_def]
        change val (delDead j C) (List.ofFn x) (shiftW j C.output) = val C (List.ofFn x) C.output
        rw [delDead_wires_eq j C (List.ofFn x) List.length_ofFn hLeast.1.2.1 hj hno,
          unshiftW_shiftW j C.output hout]
      have hle := hLeast.2.2 (delDead j C) (delDead_ao2 j C hLeast.1 hj hno) (heq.trans hLeast.2.1)
      have hlen := delDead_length j C hj
      rw [size_def, size_def] at hle
      omega
    have leastRead : ∀ {j : ℕ}, j < C.gates.length → ¬ BelowF G C j → (readers nv C j).Nonempty := by
      intro j hj hd
      refine leastReadAny hj ?_
      intro heq
      apply hd
      intro x hx
      have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hLeast.2.1 x
      rw [heq] at h
      exact h.symm.trans hx
    have replace_gate_by_wire : ∀ (a w0 : ℕ), a < C.gates.length → w0 < nv + a →
        (∀ x : Fin nv → Bool, val C (List.ofFn x) w0 = gateVal nv C a x) → False := by
      intro a w0 ha hw0 hEq
      let repW : ℕ → ℕ := fun w => if w = nv + a then w0 else if w < nv + a then w else w - 1
      let repGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map repW⟩
      let D : Circuit := ⟨(C.gates.eraseIdx a).map repGate, repW C.output⟩
      have hDlen : D.gates.length = C.gates.length - 1 := by
        dsimp only [D]; rw [List.length_map, List.length_eraseIdx_of_lt ha]
      have hDgate : ∀ j, j < D.gates.length → gateAt D j = repGate (gateAt C (unshiftG a j)) := by
        intro j hj
        have hj_lt : j < C.gates.length - 1 := by omega
        have hj_e : j < (C.gates.eraseIdx a).length := by rw [List.length_eraseIdx_of_lt ha]; exact hj_lt
        rw [gateAt_eq hj]
        dsimp only [D, unshiftG]
        rw [List.getElem_map]
        split_ifs with hja
        · rw [List.getElem_eraseIdx_of_lt hj_e hja, gateAt_eq (by omega)]
        · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
      have hDRB : ReadsBack nv D := by
        intro j hj w' hw'
        rw [hDgate j hj] at hw'
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
        have hj0 : unshiftG a j < C.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
        have hwlt : w < nv + unshiftG a j := hLeast.1.2.1 (unshiftG a j) hj0 w hw
        dsimp only [repW]
        dsimp only [unshiftG] at hwlt
        split_ifs at hwlt ⊢ <;> omega
      have hDAO : IsAO2 nv D := by
        have mapped : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
          intro g hg
          obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
          have hm := List.mem_of_mem_eraseIdx hg'
          exact ⟨hLeast.1.1 g' hm, by dsimp only [repGate]; rw [List.length_map]; exact hLeast.1.2.2 g' hm⟩
        exact ⟨fun g hg => (mapped g hg).1, hDRB, fun g hg => (mapped g hg).2⟩
      have hValEq : ∀ (x : Fin nv → Bool) (w : ℕ), w < nv + C.gates.length →
          val D (List.ofFn x) (repW w) = val C (List.ofFn x) w := by
        intro x w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwlt
          by_cases hwn : w < nv
          · have hrw : repW w = w := by dsimp only [repW]; split_ifs <;> omega
            rw [hrw, val_input List.length_ofFn hwn, val_input List.length_ofFn hwn]
          · by_cases hwa : w = nv + a
            · subst w
              have hrw : repW (nv + a) = w0 := by dsimp only [repW]; rw [if_pos rfl]
              have hrw0 : repW w0 = w0 := by dsimp only [repW]; split_ifs <;> omega
              rw [hrw, ← hrw0, ih w0 hw0 (by omega)]
              exact hEq x
            · let j0 := w - nv
              have hweq : w = nv + j0 := by omega
              have hj0 : j0 < C.gates.length := by omega
              let j := if j0 < a then j0 else j0 - 1
              have hj : j < D.gates.length := by dsimp only [j]; split_ifs <;> omega
              have hrw : repW w = nv + j := by dsimp only [repW, j]; split_ifs <;> omega
              have hun : unshiftG a j = j0 := by dsimp only [unshiftG, j]; split_ifs <;> omega
              rw [hrw, hweq, val_gate List.length_ofFn hj, val_gate List.length_ofFn hj0, hDgate j hj, hun]
              dsimp only [repGate]
              rw [List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hult : u < nv + j0 := hLeast.1.2.1 j0 hj0 u hu
              have hrult : repW u < nv + j :=
                hDRB j hj (repW u) (by rw [hDgate j hj, hun]; exact List.mem_map.mpr ⟨u, hu, rfl⟩)
              simp only [Function.comp_apply]
              rw [if_pos hrult, if_pos hult]
              exact ih u (by omega) (by omega)
      have hDcomp : circuitFun nv D = graphFun G ∅ := by
        funext x
        rw [circuitFun_def]
        change val D (List.ofFn x) (repW C.output) = graphFun G ∅ x
        rw [hValEq x C.output hOutLt]
        exact congrFun hLeast.2.1 x
      have hle := hLeast.2.2 D hDAO hDcomp
      rw [size_def, size_def, hDlen] at hle
      omega
    let OrStep : ℕ → ℕ → Prop := fun w w' =>
      ∃ k, k < C.gates.length ∧ w = nv + k ∧ (gateAt C k).op = GateOp.or ∧
        w' ∈ (gateAt C k).inputs ∧ w' < nv + k
    have orStep_up : ∀ {x : List Bool}, x.length = nv → ∀ {w w' : ℕ},
        Relation.ReflTransGen OrStep w w' → val C x w' = true → val C x w = true := by
      intro x hx w w' h hv
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact hv
      | head hstep _ ih =>
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
    have or_trace : ∀ {x : List Bool}, x.length = nv → ∀ w : ℕ, val C x w = true →
        ∃ w', Relation.ReflTransGen OrStep w w' ∧ val C x w' = true ∧
          (w' < nv ∨ ∃ h, h < C.gates.length ∧ w' = nv + h ∧ (gateAt C h).op ≠ GateOp.or) := by
      intro x hx w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hv
        by_cases hw : w < nv
        · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
        · by_cases hlen : nv + C.gates.length ≤ w
          · rw [val_ge hx hlen] at hv; exact Bool.noConfusion hv
          · obtain ⟨k, rfl⟩ : ∃ k, w = nv + k := ⟨w - nv, by omega⟩
            have hk : k < C.gates.length := by omega
            by_cases hop : (gateAt C k).op = GateOp.or
            · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
              obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
              exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
            · exact ⟨nv + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
    have operand_trace : ∀ (u v : Fin nv) (p : ℕ), val C (List.ofFn (pairInput u v)) p = true →
        (∃ t : Fin nv, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val) ∨
        (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
          Relation.ReflTransGen OrStep p (nv + h) ∧
          val C (List.ofFn (pairInput u v)) (nv + h) = true) := by
      intro u v p hv
      obtain ⟨w', hr, hv', hw'⟩ := or_trace List.length_ofFn p hv
      rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
      · left
        refine ⟨⟨w', hlt⟩, ?_, hr⟩
        have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
        rw [show (⟨w', hlt⟩ : Fin nv).val = w' from rfl, hv'] at h1
        exact (pairInput_true u v _).mp h1.symm
      · right
        exact ⟨h, hh, hop, hr, hv'⟩
    have reach_var_val : ∀ (x : Fin nv → Bool) (p : ℕ) (t : Fin nv),
        Relation.ReflTransGen OrStep p t.val → x t = true → val C (List.ofFn x) p = true :=
      fun x p t hr ht => orStep_up List.length_ofFn hr (by rw [val_ofFn]; exact ht)
    have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (gs.foldl (coneStep nv) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih, coneStep_def]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have cones_char : ∀ (gs : List Gate) (i j : ℕ),
        i ∈ (gs.foldl (coneStep nv) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, nv ≤ w ∧ w < nv + j ∧
            (i = w - nv ∨ i ∈ (gs.foldl (coneStep nv) []).getD (w - nv) []) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, List.length_nil, Nat.not_lt_zero, false_and]
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (coneStep nv) []).length = gs.length := by rw [cones_len, List.length_nil, Nat.zero_add]
        have key : ∀ k, k < gs.length →
            (coneStep nv (gs.foldl (coneStep nv) []) g).getD k [] =
              (gs.foldl (coneStep nv) []).getD k [] := by
          intro k hk
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨by simp only [List.length_append, List.length_singleton]; omega, w, hw, h1, h2, ?_⟩
            rw [key (w - nv) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨h, w, hw, h1, h2, ?_⟩
            rw [key (w - nv) (by omega)] at h3
            exact h3
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          have e2 : (coneStep nv (gs.foldl (coneStep nv) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (nv ≤ w ∧ w < nv + gs.length))).flatMap
                (fun w => (w - nv) :: (gs.foldl (coneStep nv) []).getD (w - nv) []) := by
            rw [coneStep_def]
            simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [e2, e1]
          simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
          constructor
          · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
            refine ⟨by simp only [List.length_append, List.length_singleton]; omega, w, hw, h1, h2, ?_⟩
            rw [key (w - nv) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            rw [key (w - nv) (by omega)] at h3
            exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e0 : (coneStep nv (gs.foldl (coneStep nv) []) g).getD j [] = [] := by
            rw [coneStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; exact False.elim (List.not_mem_nil h0)
          · rintro ⟨h0, _⟩; simp only [List.length_append, List.length_singleton] at h0; omega
    have inCone_iff : ∀ i j : ℕ, InCone nv C i j ↔
        j < C.gates.length ∧ ∃ k, k < j ∧ nv + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone nv C i k) := by
      intro i j
      have h := cones_char C.gates i j
      rw [inCone_def, cones_def, gateAt_def, h]
      constructor
      · rintro ⟨h0, w, hw, h1, h2, h3⟩
        refine ⟨h0, w - nv, by omega, ?_, ?_⟩
        · have he : nv + (w - nv) = w := by omega
          rw [he]; exact hw
        · rcases h3 with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (by rw [inCone_def, cones_def]; exact h3)
      · rintro ⟨h0, k, hk, hw, h3⟩
        refine ⟨h0, nv + k, hw, by omega, by omega, ?_⟩
        have he : nv + k - nv = k := by omega
        rw [he]
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by rw [inCone_def, cones_def] at h3; exact h3)
    have inCone_trans : ∀ {i j k : ℕ}, InCone nv C i j → InCone nv C j k → InCone nv C i k := by
      intro i j k hij
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hjk
        obtain ⟨hklen, r, hr, hrin, rfl | hjr⟩ := (inCone_iff j k).mp hjk
        · exact (inCone_iff i k).mpr ⟨hklen, j, hr, hrin, Or.inr hij⟩
        · exact (inCone_iff i k).mpr ⟨hklen, r, hr, hrin, Or.inr (ih r hr hjr)⟩
    have orStep_le : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' → w' ≤ w := by
      intro w w' h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_refl _
      | head hstep _ ih => obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep; omega
    have orStep_cone : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
        ∀ k h', w = nv + k → w' = nv + h' → h' = k ∨ InCone nv C h' k := by
      intro w w' h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro k h' h1 h2; left; omega
      | @head a c hstep hrest ih =>
        intro k h' h1 h2
        obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
        have hk : k0 = k := by omega
        subst hk
        have hle := orStep_le hrest
        obtain ⟨k1, hk1⟩ : ∃ k1, c = nv + k1 := ⟨c - nv, by omega⟩
        subst hk1
        right
        exact (inCone_iff h' k0).mpr ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
    have operand_cone : ∀ {a p h : ℕ}, a < C.gates.length → p ∈ (gateAt C a).inputs → p < nv + a →
        Relation.ReflTransGen OrStep p (nv + h) → InCone nv C h a := by
      intro a p h ha hin hp hr
      have hle := orStep_le hr
      obtain ⟨k1, rfl⟩ : ∃ k1, p = nv + k1 := ⟨p - nv, by omega⟩
      exact (inCone_iff h a).mpr ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
    have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (gs.foldl (orStep nv) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih, orStep_def]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
        i ∈ (gs.foldl (orStep nv) []).getD j [] ↔
          j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
            ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, nv ≤ w ∧ w < nv + j ∧
              i ∈ (gs.foldl (orStep nv) []).getD (w - nv) [])) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, List.length_nil, Nat.not_lt_zero, false_and]
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (orStep nv) []).length = gs.length := by rw [orSets_len, List.length_nil, Nat.zero_add]
        have key : ∀ k, k < gs.length →
            (orStep nv (gs.foldl (orStep nv) []) g).getD k [] =
              (gs.foldl (orStep nv) []).getD k [] := by
          intro k hk
          rw [orStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, h3⟩
            refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
            · exact Or.inl h3
            · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
              rw [key (w - nv) (by omega)]
              exact h3
          · rintro ⟨_, h3⟩
            refine ⟨h, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
            · exact Or.inl h3
            · rw [key (w - nv) (by omega)] at h3
              exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [e1]
          by_cases hop : g.op = GateOp.or
          · have e2 : (orStep nv (gs.foldl (orStep nv) []) g).getD gs.length [] =
                gs.length :: (g.inputs.filter (fun w => decide (nv ≤ w ∧ w < nv + gs.length))).flatMap
                  (fun w => (gs.foldl (orStep nv) []).getD (w - nv) []) := by
              rw [orStep_def, if_pos hop]
              simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [e2]
            simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
            constructor
            · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
              · exact ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inl h3⟩
              · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
                rw [key (w - nv) (by omega)]
                exact h3
            · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
              · exact Or.inl h3
              · rw [key (w - nv) (by omega)] at h3
                exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
          · have e2 : (orStep nv (gs.foldl (orStep nv) []) g).getD gs.length [] = [gs.length] := by
              rw [orStep_def, if_neg hop]
              simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [e2]
            simp only [List.mem_singleton]
            constructor
            · intro h3; exact ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inl h3⟩
            · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
              · exact h3
              · exact False.elim (hop hop2)
        · have e0 : (orStep nv (gs.foldl (orStep nv) []) g).getD j [] = [] := by
            rw [orStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; exact False.elim (List.not_mem_nil h0)
          · rintro ⟨h0, _⟩; simp only [List.length_append, List.length_singleton] at h0; omega
    have orReaches_iff : ∀ k g : ℕ, OrReaches nv C (nv + k) g ↔
        k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
          ∃ i ∈ (gateAt C k).inputs, i < nv + k ∧ OrReaches nv C i g)) := by
      intro k g
      have h := orSets_char C.gates g k
      rw [orReaches_def, orSets_def, gateAt_def]
      have e : nv + k - nv = k := by omega
      rw [e, h]
      constructor
      · rintro ⟨_, hk, h3⟩
        refine ⟨hk, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · exact Or.inr ⟨hop, w, hw, h2, by rw [orReaches_def, orSets_def]; exact ⟨h1, h3⟩⟩
      · rintro ⟨hk, h3⟩
        refine ⟨by omega, hk, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h2, h1⟩
        · exact Or.inl h3
        · rw [orReaches_def, orSets_def] at h1
          exact Or.inr ⟨hop, w, hw, h1.1, h2, h1.2⟩
    have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStep w w2 →
        ∀ g, w2 = nv + g → g < C.gates.length → OrReaches nv C w g := by
      intro w w2 h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro g h1 hg; subst h1
        exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
      | @head a c hstep hrest ih =>
        intro g h1 hg
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
    have orReaches_reach : ∀ (g w : ℕ), OrReaches nv C w g →
        Relation.ReflTransGen OrStep w (nv + g) ∧ g < C.gates.length := by
      intro g w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro h
        rw [orReaches_def] at h
        have hnw : nv ≤ w := h.1
        obtain ⟨k, rfl⟩ : ∃ k, w = nv + k := ⟨w - nv, by omega⟩
        have h' : OrReaches nv C (nv + k) g := by rw [orReaches_def]; exact h
        obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h'
        rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
        · exact ⟨Relation.ReflTransGen.refl, hk⟩
        · obtain ⟨hr2, hg⟩ := ih i hlt hr
          exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
    have orReaches_le : ∀ {w g : ℕ}, OrReaches nv C w g → nv + g ≤ w :=
      fun hr => orStep_le (orReaches_reach _ _ hr).1
    have orReaches_trans : ∀ {w k g : ℕ}, OrReaches nv C w k → OrReaches nv C (nv + k) g → OrReaches nv C w g := by
      intro w k g h1 h2
      obtain ⟨r1, _⟩ := orReaches_reach k w h1
      obtain ⟨r2, hg⟩ := orReaches_reach g (nv + k) h2
      exact reach_orReaches (r1.trans r2) g rfl hg
    have mem_orIn_reach : ∀ {p : ℕ} (u : Fin nv), u ∈ orIn nv C p → Relation.ReflTransGen OrStep p u.val := by
      intro p u hu
      rcases (orIn_def C p u).mp hu with h | ⟨k, hk, hr, hop, hin⟩
      · rw [h]
      · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
    have reach_mem_orIn : ∀ {p : ℕ} (u : Fin nv), Relation.ReflTransGen OrStep p u.val → u ∈ orIn nv C p := by
      intro p u hr
      apply (orIn_def C p u).mpr
      rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
      · exact Or.inl h
      · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
        exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
    have orIn_mono : ∀ {w g : ℕ}, OrReaches nv C w g → orIn nv C (nv + g) ⊆ orIn nv C w := by
      intro w g hr u hu
      exact reach_mem_orIn u ((orReaches_reach g w hr).1.trans (mem_orIn_reach u hu))
    have orIn_leaf : ∀ (v : Fin nv), orIn nv C v.val = {v} := by
      intro v
      apply Finset.ext
      intro u
      rw [orIn_def, Finset.mem_singleton]
      constructor
      · rintro (h | ⟨k, _, hr, _, _⟩)
        · exact Fin.ext h
        · rw [orReaches_def] at hr; have := v.isLt; omega
      · rintro rfl; exact Or.inl rfl
    have topData : ∀ {a : ℕ}, a ∈ tops G C → a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a :=
      fun ha => (tops_mem C _).mp ha
    have junkData : ∀ {a : ℕ}, a ∈ junk G C →
        a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
          ∃ x : Fin nv → Bool, gateVal nv C a x = true ∧ graphFun G ∅ x = false :=
      fun ha => (junk_mem C _).mp ha
    have junkNotBelow : ∀ {j : ℕ}, j ∈ junk G C → ¬ BelowF G C j := by
      intro j hj h
      obtain ⟨_, _, x, hx, hf⟩ := junkData hj
      exact Bool.false_ne_true (hf.symm.trans (h x hx))
    have fin2_or : ∀ b : Fin 2, b = 0 ∨ b = 1 := by
      intro b
      rcases b with ⟨v, hv⟩
      cases v with
      | zero => exact Or.inl rfl
      | succ m =>
        cases m with
        | zero => exact Or.inr rfl
        | succ _ => omega
    have fin2_ne_eq : ∀ (d idx : Fin 2), idx ≠ d → idx = 1 - d := by decide
    have fin3_or : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
      intro i
      rcases i with ⟨v, hv⟩
      cases v with
      | zero => exact Or.inl rfl
      | succ m =>
        cases m with
        | zero => exact Or.inr (Or.inl rfl)
        | succ k =>
          cases k with
          | zero => exact Or.inr (Or.inr rfl)
          | succ _ => omega
    have binaryInputs : ∀ {a : ℕ}, a < C.gates.length → ∃ p q, (gateAt C a).inputs = [p, q] :=
      fun ha => List.length_eq_two.mp (hLeast.1.2.2 _ (gateAt_mem ha))
    have opndMem : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b ∈ (gateAt C a).inputs := by
      intro a ha b
      obtain ⟨p, q, hpq⟩ := binaryInputs ha
      rw [opnd_def, hpq]
      rcases fin2_or b with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem p List.mem_cons_self
    have opndBound : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b < nv + a :=
      fun ha b => hLeast.1.2.1 _ ha _ (opndMem ha b)
    have inputsAsOpnd : ∀ {k z : ℕ}, k < C.gates.length → z ∈ (gateAt C k).inputs → ∃ b : Fin 2, z = opnd C k b := by
      intro k z hk hz
      obtain ⟨p, q, hpq⟩ := binaryInputs hk
      rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
      · exact ⟨0, by rw [opnd_def, hpq]; rfl⟩
      · have e : z = q := List.mem_singleton.mp hq
        exact ⟨1, by rw [opnd_def, hpq]; exact e⟩
    have andValBoth : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∀ x : Fin nv → Bool, gateVal nv C a x = true ↔
          val C (List.ofFn x) (opnd C a 0) = true ∧ val C (List.ofFn x) (opnd C a 1) = true := by
      intro a ha hop x
      rw [gateVal_eq_val, val_and List.length_ofFn ha hop]
      constructor
      · intro h; exact ⟨(h _ (opndMem ha 0)).2, (h _ (opndMem ha 1)).2⟩
      · intro h i hi
        refine ⟨hLeast.1.2.1 a ha i hi, ?_⟩
        obtain ⟨b, rfl⟩ := inputsAsOpnd ha hi
        rcases fin2_or b with rfl | rfl
        · exact h.1
        · exact h.2
    have andValOperands : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∀ x : Fin nv → Bool, gateVal nv C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
      intro a ha hop x
      rw [andValBoth ha hop]
      constructor
      · intro h b; rcases fin2_or b with rfl | rfl; exact h.1; exact h.2
      · intro h; exact ⟨h 0, h 1⟩
    have orValOperands : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.or →
        ∀ x : Fin nv → Bool, gateVal nv C a x = true ↔ ∃ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
      intro a ha hop x
      rw [gateVal_eq_val, val_or List.length_ofFn ha hop]
      constructor
      · rintro ⟨i, hi, _, hvi⟩
        obtain ⟨b, rfl⟩ := inputsAsOpnd ha hi
        exact ⟨b, hvi⟩
      · rintro ⟨b, hvb⟩
        exact ⟨opnd C a b, opndMem ha b, opndBound ha b, hvb⟩
    have orIn_or_union : ∀ {r : ℕ}, r < C.gates.length → (gateAt C r).op = GateOp.or →
        orIn nv C (nv + r) = orIn nv C (opnd C r 0) ∪ orIn nv C (opnd C r 1) := by
      intro r hr hop
      apply Finset.ext
      intro v
      rw [Finset.mem_union]
      constructor
      · intro hv
        rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with h | ⟨w, hstep, hrest⟩
        · have := v.isLt; omega
        · obtain ⟨k, _, heq, _, hin, _⟩ := hstep
          have hkr : k = r := by omega
          subst hkr
          obtain ⟨b, rfl⟩ := inputsAsOpnd hr hin
          rcases fin2_or b with rfl | rfl
          · exact Or.inl (reach_mem_orIn v hrest)
          · exact Or.inr (reach_mem_orIn v hrest)
      · rintro (h0 | h1)
        · exact reach_mem_orIn v (Relation.ReflTransGen.head ⟨r, hr, rfl, hop, opndMem hr 0, opndBound hr 0⟩ (mem_orIn_reach v h0))
        · exact reach_mem_orIn v (Relation.ReflTransGen.head ⟨r, hr, rfl, hop, opndMem hr 1, opndBound hr 1⟩ (mem_orIn_reach v h1))
    have operandReachCone : ∀ {a h : ℕ}, a < C.gates.length → ∀ {b : Fin 2},
        OrReaches nv C (opnd C a b) h → InCone nv C h a := by
      intro a h ha b hr
      exact operand_cone ha (opndMem ha b) (opndBound ha b) (orReaches_reach h _ hr).1
    have operandOrAndJunk : ∀ {a h : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∀ {b : Fin 2}, OrReaches nv C (opnd C a b) h → (gateAt C h).op = GateOp.and → h ∈ junk G C := by
      intro a h ha hop b hr hh
      have hlen := (orReaches_reach h _ hr).2
      have hnb : ¬ BelowF G C h := fun hb => hTop h hlen a ha hh hb hop (operandReachCone ha hr)
      have hdirty : ∃ x : Fin nv → Bool, gateVal nv C h x = true ∧ graphFun G ∅ x = false := by
        by_contra hne
        apply hnb
        intro x hx
        by_contra hf
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
      exact (junk_mem C h).mpr ⟨hlen, hh, hdirty⟩
    have sideVal : ∀ {a : ℕ} {b : Fin 2} {x : Fin nv → Bool} {t : Fin nv},
        t ∈ side (n := nv) C a b → x t = true → val C (List.ofFn x) (opnd C a b) = true := by
      intro a b x t ht hx
      rw [side_def] at ht
      exact reach_var_val x _ t (mem_orIn_reach t ht) hx
    have topAdj : ∀ {a : ℕ}, a ∈ tops G C → ∀ {u v : Fin nv},
        u ∈ side (n := nv) C a 0 → v ∈ side (n := nv) C a 1 → G.Adj u v := by
      intro a ha u v hu hv
      obtain ⟨hl, ho, hb⟩ := topData ha
      exact (graphFun_pair u v).mp
        (hb _ ((andValBoth hl ho _).mpr ⟨sideVal hu (pairInput_left u v), sideVal hv (pairInput_right u v)⟩))
    have topAdj_side : ∀ {t : ℕ}, t ∈ tops G C → ∀ {d : Fin 2} {u v : Fin nv},
        u ∈ side (n := nv) C t d → v ∈ side (n := nv) C t (1 - d) → G.Adj u v := by
      intro t ht d u v hu hv
      rcases fin2_or d with rfl | rfl
      · exact topAdj ht hu hv
      · exact (topAdj ht hv hu).symm
    have side_mem_starEdges : ∀ {t : ℕ}, t ∈ tops G C → ∀ {d : Fin 2} {u v : Fin nv},
        u ∈ side (n := nv) C t d → v ∈ side (n := nv) C t (1 - d) → s(u, v) ∈ starEdges G C := by
      intro t ht d u v hu hv
      rw [starEdges_def]
      refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
      rcases fin2_or d with rfl | rfl
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hv, hu⟩, Sym2.eq_swap⟩
    have emptySide_mem_centreless : ∀ {t : ℕ}, t ∈ tops G C → ∀ {d : Fin 2},
        side (n := nv) C t d = ∅ → t ∈ centreless G C := by
      intro t ht d h
      refine (centreless_mem C t).mpr ⟨ht, ?_⟩
      rcases fin2_or d with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
    have acceptedTop : ∀ {u v : Fin nv}, G.Adj u v → ∃ a ∈ tops G C, gateVal nv C a (pairInput u v) = true := by
      intro u v hadj'
      have hout : ∀ x : Fin nv → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
        fun x => congrFun hLeast.2.1 x
      have huv : val C (List.ofFn (pairInput u v)) C.output = true := by
        rw [hout]; exact (graphFun_pair u v).mpr hadj'
      rcases operand_trace u v C.output huv with ⟨t, _, hr⟩ | ⟨a, hl, ho, hr, hv⟩
      · exfalso
        have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
        rw [hout] at h1
        exact G.irrefl ((graphFun_pair t t).mp h1)
      · have hand := (hLeast.1.1 _ (gateAt_mem hl)).resolve_right ho
        have hb : BelowF G C a := fun x hx => by
          rw [← hout x]
          exact orStep_up List.length_ofFn hr (gateVal_eq_val C a x ▸ hx)
        exact ⟨a, (tops_mem C a).mpr ⟨hl, hand, hb⟩, hv⟩
    have operandSupport : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∀ {b : Fin 2} {u v : Fin nv}, val C (List.ofFn (pairInput u v)) (opnd C a b) = true →
        (∃ t ∈ side (n := nv) C a b, t = u ∨ t = v) ∨
          ∃ j ∈ junk G C, OrReaches nv C (opnd C a b) j ∧ gateVal nv C j (pairInput u v) = true := by
      intro a ha ho b u v h
      rcases operand_trace u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
      · exact Or.inl ⟨t, by rw [side_def]; exact reach_mem_orIn t hr, ht⟩
      · have hr' := reach_orReaches hr j rfl hj
        exact Or.inr ⟨j, operandOrAndJunk ha ho hr' ((hLeast.1.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
    have andRawEmpty : ∀ {j : ℕ}, (gateAt C j).op = GateOp.and → orIn nv C (nv + j) = ∅ := by
      intro j hj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      rcases (orIn_def C (nv + j) v).mp hv with he | ⟨k, _, hr, ho, _⟩
      · have := v.isLt; omega
      · rcases (orReaches_iff j k).mp hr with ⟨_, rfl | ⟨hof, _⟩⟩
        · rw [hj] at ho; exact GateOp.noConfusion ho
        · rw [hj] at hof; exact GateOp.noConfusion hof
    have residualTrace : ∀ {u v : Fin nv}, s(u, v) ∈ Ustar G C →
        ∃ a ∈ tops G C, gateVal nv C a (pairInput u v) = true ∧ ∃ b : Fin 2, ∃ j ∈ junk G C,
          OrReaches nv C (opnd C a b) j ∧ gateVal nv C j (pairInput u v) = true := by
      intro u v he
      rw [Ustar_def] at he
      obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
      have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
      obtain ⟨a, ha, hv⟩ := acceptedTop adj'
      obtain ⟨hl, ho, _⟩ := topData ha
      have h := (andValOperands hl ho _).mp hv
      rcases operandSupport hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
      · rcases operandSupport hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
        · have hxy : x ≠ y := (topAdj ha hx hy).ne
          apply False.elim (miss ?_)
          rw [starEdges_def]
          refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
            ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
          rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        · exact ⟨a, ha, hv, 1, j, hj, hr, hjv⟩
      · exact ⟨a, ha, hv, 0, j, hj, hr, hjv⟩
    have readData : ∀ {j k : ℕ}, k ∈ readers nv C j → k < C.gates.length ∧ nv + j ∈ (gateAt C k).inputs :=
      fun hk => (readers_mem C _ _).mp hk
    have readLt : ∀ {j k : ℕ}, k ∈ readers nv C j → j < k := by
      intro j k hk
      have hlt := hLeast.1.2.1 k (readData hk).1 _ (readData hk).2
      omega
    have val_allTrue : ∀ w, w < nv + C.gates.length → val C (List.ofFn (fun _ : Fin nv => true)) w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hwn : w < nv
        · exact val_ofFn C (fun _ => true) ⟨w, hwn⟩
        · obtain ⟨j, rfl⟩ : ∃ j, w = nv + j := ⟨w - nv, by omega⟩
          have hj : j < C.gates.length := by omega
          rcases hLeast.1.1 _ (gateAt_mem hj) with hand | hor
          · exact (val_and List.length_ofFn hj hand).mpr (fun i hi => by
              have hilt := hLeast.1.2.1 j hj i hi
              exact ⟨hilt, ih i hilt (by omega)⟩)
          · have hi0 := opndMem hj 0
            have hlt0 := opndBound hj 0
            exact (val_or List.length_ofFn hj hor).mpr ⟨opnd C j 0, hi0, hlt0, ih _ hlt0 (by omega)⟩
    have not_belowF_inCone_and : ∀ {k j : ℕ}, k < C.gates.length → BelowF G C k →
        j < C.gates.length → (gateAt C j).op = GateOp.and → ¬ InCone nv C k j := by
      intro k j hk hbk hj hjo hkj
      have htk := val_allTrue (nv + k) (by omega)
      obtain ⟨w', hstep, _, hw'⟩ := or_trace List.length_ofFn (nv + k) htk
      rcases hw' with hlt | ⟨t, htlen, rfl, htop⟩
      · have hvar := reach_var_val (pairInput ⟨w', hlt⟩ ⟨w', hlt⟩) (nv + k) ⟨w', hlt⟩ hstep (pairInput_left _ _)
        exact G.irrefl ((graphFun_pair _ _).mp (hbk _ hvar))
      · have htand := (hLeast.1.1 _ (gateAt_mem htlen)).resolve_right htop
        have htb : BelowF G C t := fun x hx => hbk x (orStep_up List.length_ofFn hstep (gateVal_eq_val C t x ▸ hx))
        rcases orStep_cone hstep k t rfl rfl with rfl | htkc
        · exact hTop t htlen j hj htand htb hjo hkj
        · exact hTop t htlen j hj htand htb hjo (inCone_trans htkc hkj)
    have no_bothNonempty_R_below_lam : ∀ {m0 h : ℕ}, m0 ∈ orN G C \ lam G C → h ∈ lam G C →
        (orIn nv C (opnd C m0 0)).Nonempty → (orIn nv C (opnd C m0 1)).Nonempty →
        ¬ OrReaches nv C (nv + h) m0 := by
      intro m0 h hm0 hh h0 h1 hreach
      obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
      have hm0N := (Finset.mem_sdiff.mp hm0).1
      have hm0len := ((orN_mem C m0).mp hm0N).1
      have htm0 : OrReaches nv C (opnd C t d) m0 :=
        reach_orReaches ((orReaches_reach h _ hth).1.trans (orReaches_reach m0 _ hreach).1) m0 rfl hm0len
      exact (Finset.mem_sdiff.mp hm0).2 ((lam_mem C m0).mpr ⟨hm0N, h0, h1, t, ht, d, hcard, htm0⟩)
    have noncentreless_witness : ∀ {w j : ℕ}, j ∈ junk G C →
        OrReaches nv C w j → (orIn nv C w).Nonempty →
        ∃ m ∈ orN G C \ lam G C, OrReaches nv C w m ∧ OrReaches nv C (nv + m) j ∧ (orIn nv C (nv + m)).Nonempty := by
      intro w j hj hreach hne
      obtain ⟨hpath, _⟩ := orReaches_reach j w hreach
      obtain ⟨hjlen, hjop, _⟩ := junkData hj
      have hjnb := junkNotBelow hj
      have hwalk : ∀ {u : ℕ}, Relation.ReflTransGen OrStep u (nv + j) → (orIn nv C u).Nonempty →
          ∃ m ∈ orN G C \ lam G C, OrReaches nv C u m ∧ OrReaches nv C (nv + m) j ∧ (orIn nv C (nv + m)).Nonempty := by
        intro u hu
        induction hu using Relation.ReflTransGen.head_induction_on with
        | refl =>
          intro hne'
          rw [andRawEmpty hjop] at hne'
          exact False.elim (Finset.not_nonempty_empty hne')
        | @head a c hstep hrest ih =>
          intro hnea
          obtain ⟨k, hklen, rfl, hkop, hcin, hclt⟩ := hstep
          by_cases hnec : (orIn nv C c).Nonempty
          · obtain ⟨m, hmR, hcm, hmj, hmne⟩ := ih hnec
            have hkm : OrReaches nv C (nv + k) m :=
              (orReaches_iff k m).mpr ⟨hklen, Or.inr ⟨hkop, c, hcin, hclt, hcm⟩⟩
            exact ⟨m, hmR, hkm, hmj, hmne⟩
          · have hce : orIn nv C c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnec
            have hkj : OrReaches nv C (nv + k) j :=
              reach_orReaches (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hcin, hclt⟩ hrest) j rfl hjlen
            have hknb : ¬ BelowF G C k := by
              intro hkb
              apply hjnb
              intro x hx
              exact hkb x (orStep_up List.length_ofFn (orReaches_reach j (nv + k) hkj).1 (gateVal_eq_val C j x ▸ hx))
            have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkop, hknb⟩
            have hkNotLam : k ∉ lam G C := by
              intro hkl
              obtain ⟨_, h0, h1, _⟩ := (lam_mem C k).mp hkl
              obtain ⟨b, hb⟩ := inputsAsOpnd hklen hcin
              have hnb : (orIn nv C (opnd C k b)).Nonempty := by rcases fin2_or b with rfl | rfl; exact h0; exact h1
              rw [← hb, hce] at hnb
              exact Finset.not_nonempty_empty hnb
            exact ⟨k, Finset.mem_sdiff.mpr ⟨hkN, hkNotLam⟩, (orReaches_iff k k).mpr ⟨hklen, Or.inl rfl⟩, hkj, hnea⟩
      exact hwalk hpath hne
    have no_lam_two_Ustar_nbrs : ∀ (c : Fin nv) (T : Finset (Fin nv)),
        (∀ x ∈ T, G.Adj c x) →
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → s(c, x) ∈ Ustar G C ∨ s(c, y) ∈ Ustar G C) →
        ∀ h ∈ lam G C, ∀ x ∈ T, ∀ y ∈ T,
          x ∈ orIn nv C (nv + h) → y ∈ orIn nv C (nv + h) → x = y := by
      intro c T hAdj hU h hh x hx y hy hxh hyh
      by_contra hxy
      obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hxs : x ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono hth hxh
      have hys : y ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono hth hyh
      have hzs : z ∈ side (n := nv) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self z
      have hzx : G.Adj z x := (topAdj_side ht hxs hzs).symm
      have hzy : G.Adj z y := (topAdj_side ht hys hzs).symm
      have hzc : z = c := by
        by_contra hne
        have hc4 := hNo4 z c hne
        have h1 : x ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj c p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx, hAdj x hx⟩
        have h2 : y ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj c p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy, hAdj y hy⟩
        exact hxy (Finset.card_le_one.mp hc4 x h1 y h2)
      subst z
      have hstar : ∀ w : Fin nv, w ∈ side (n := nv) C t d → s(c, w) ∈ starEdges G C :=
        fun w hw => Sym2.eq_swap ▸ side_mem_starEdges ht hw hzs
      rcases hU x hx y hy hxy with hux | huy
      · rw [Ustar_def] at hux; exact (Finset.mem_sdiff.mp hux).2 (hstar x hxs)
      · rw [Ustar_def] at huy; exact (Finset.mem_sdiff.mp huy).2 (hstar y hys)
    have hUstarNe : (Ustar G C).Nonempty := by
      by_contra hne
      have hE : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hlt := hBudgetLtCov ∅ (fun e he => by rw [hE] at he; exact False.elim (Finset.notMem_empty e he))
      rw [hE, Finset.card_empty, Finset.card_empty] at hlt
      omega
    have hJunkGe2 : 2 ≤ (junk G C).card := by
      have hJunkPos : 0 < (junk G C).card := by
        obtain ⟨e, he⟩ := hUstarNe
        induction e using Sym2.ind with
        | _ u v =>
          obtain ⟨_, _, _, _, j, hj, _, _⟩ := residualTrace he
          exact Finset.card_pos.mpr ⟨j, hj⟩
      by_contra hlt2
      have hJ1 : (junk G C).card = 1 := by omega
      obtain ⟨j, hjSet⟩ := Finset.card_eq_one.mp hJ1
      have hjMem : j ∈ junk G C := by rw [hjSet]; exact Finset.mem_singleton_self j
      have hjUniq : ∀ j' ∈ junk G C, j' = j := fun j' hj' => Finset.mem_singleton.mp (hjSet ▸ hj')
      obtain ⟨hjlen, hjop, _⟩ := junkData hjMem
      have hjnb : ¬ BelowF G C j := junkNotBelow hjMem
      let R : Finset ℕ := orN G C \ lam G C
      have hRcard_eq : R.card = (orN G C \ lam G C).card := rfl
      let NoAnd : ℕ → Prop := fun w => ∀ k, OrReaches nv C w k → (gateAt C k).op = GateOp.or
      have noAnd_val : ∀ {w : ℕ}, w < nv + C.gates.length → NoAnd w →
          ∀ x : Fin nv → Bool, val C (List.ofFn x) w = true ↔ ∃ v ∈ orIn nv C w, x v = true := by
        intro w hw hna x
        constructor
        · intro hv
          obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn w hv
          rcases hcase with hlt | ⟨h, hh, rfl, hneOr⟩
          · refine ⟨⟨w', hlt⟩, reach_mem_orIn ⟨w', hlt⟩ hpath, ?_⟩
            rw [← val_ofFn C x ⟨w', hlt⟩]; exact hvw'
          · exact False.elim (hneOr (hna h (reach_orReaches hpath h rfl hh)))
        · rintro ⟨v, hv, hxv⟩
          exact reach_var_val x w v (mem_orIn_reach v hv) hxv
      have noAnd_nonempty : ∀ {w : ℕ}, w < nv + C.gates.length → NoAnd w → (orIn nv C w).Nonempty := by
        intro w hw hna
        obtain ⟨v, hv, _⟩ := (noAnd_val hw hna (fun _ => true)).mp (val_allTrue w hw)
        exact ⟨v, hv⟩
      have noAnd_reach_orN : ∀ {w k : ℕ}, NoAnd w → OrReaches nv C w k → k ∈ orN G C ∧ NoAnd (nv + k) := by
        intro w k hna hr
        have hklen := (orReaches_reach k w hr).2
        have hkop := hna k hr
        have hnak : NoAnd (nv + k) := fun k' hk' => hna k' (orReaches_trans hr hk')
        obtain ⟨v, hv⟩ := noAnd_nonempty (by omega : nv + k < nv + C.gates.length) hnak
        have hknb : ¬ BelowF G C k := by
          intro hkb
          have h1 : gateVal nv C k (pairInput v v) = true :=
            (noAnd_val (by omega) hnak (pairInput v v)).mpr ⟨v, hv, pairInput_left v v⟩
          exact G.irrefl ((graphFun_pair v v).mp (hkb _ h1))
        exact ⟨(orN_mem C k).mpr ⟨hklen, hkop, hknb⟩, hnak⟩
      have noAnd_opnd_or : ∀ {k : ℕ}, k < C.gates.length → NoAnd (nv + k) → ∀ b : Fin 2, NoAnd (opnd C k b) := by
        intro k hk hnak b r hr
        have hkop : (gateAt C k).op = GateOp.or := hnak k ((orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩)
        exact hnak r ((orReaches_iff k r).mpr ⟨hk, Or.inr ⟨hkop, opnd C k b, opndMem hk b, opndBound hk b, hr⟩⟩)
      have noAnd_card_ge2 : ∀ {k : ℕ}, k < C.gates.length → NoAnd (nv + k) → 2 ≤ (orIn nv C (nv + k)).card := by
        intro k hk hnak
        obtain ⟨v0, hv0⟩ := noAnd_nonempty (by omega : nv + k < nv + C.gates.length) hnak
        by_contra hlt
        have hcard1 : (orIn nv C (nv + k)).card = 1 := by
          have hpos : 0 < (orIn nv C (nv + k)).card := Finset.card_pos.mpr ⟨v0, hv0⟩
          omega
        obtain ⟨u0, hu0⟩ := Finset.card_eq_one.mp hcard1
        apply replace_gate_by_wire k u0.val hk (by have := u0.isLt; omega)
        intro x
        cases hxu : val C (List.ofFn x) u0.val
        · cases hgk : gateVal nv C k x
          · rfl
          · obtain ⟨v, hv, hxv⟩ := (noAnd_val (by omega) hnak x).mp hgk
            rw [hu0] at hv
            rw [Finset.mem_singleton.mp hv, ← val_ofFn C x u0] at hxv
            exact Bool.noConfusion (hxu.symm.trans hxv)
        · exact ((noAnd_val (by omega) hnak x).mpr ⟨u0, by rw [hu0]; exact Finset.mem_singleton_self u0, by rw [← val_ofFn C x u0]; exact hxu⟩).symm
      have noAnd_opnd_and : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
          ∀ {b : Fin 2}, ¬ OrReaches nv C (opnd C a b) j → NoAnd (opnd C a b) := by
        intro a ha hop b hnr k hr
        have hklen := (orReaches_reach k _ hr).2
        rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
        · have hkj := hjUniq k (operandOrAndJunk ha hop hr hkand)
          subst k; exact False.elim (hnr hr)
        · exact hkor
      let Rw : ℕ → Finset ℕ := fun w => R.filter (fun r => OrReaches nv C w r)
      let Rabove : Finset ℕ := R.filter (fun r => OrReaches nv C (nv + r) j)
      have noAnd_disj_Rabove : ∀ {w : ℕ}, NoAnd w → Disjoint (Rw w) Rabove := by
        intro w hna
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        have hwr := (Finset.mem_filter.mp hr1).2
        have hrj := (Finset.mem_filter.mp hr2).2
        have hop := hna j (orReaches_trans hwr hrj)
        rw [hjop] at hop; exact GateOp.noConfusion hop
      have noAnd_disj_Rw : ∀ {w1 w2 : ℕ}, NoAnd w1 → NoAnd w2 →
          (orIn nv C w1 ∩ orIn nv C w2).card ≤ 1 → Disjoint (Rw w1) (Rw w2) := by
        intro w1 w2 hna1 _ hcap
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        have h1 := (Finset.mem_filter.mp hr1).2
        have h2 := (Finset.mem_filter.mp hr2).2
        have hrlen := (orReaches_reach r w1 h1).2
        have hnar := (noAnd_reach_orN hna1 h1).2
        have hge2 := noAnd_card_ge2 hrlen hnar
        have hsub : orIn nv C (nv + r) ⊆ orIn nv C w1 ∩ orIn nv C w2 :=
          Finset.subset_inter (orIn_mono h1) (orIn_mono h2)
        have hle := Finset.card_le_card hsub
        omega
      have pure_or_R_count : ∀ (Roots : Finset ℕ),
          (∀ w ∈ Roots, w < nv + C.gates.length ∧ NoAnd w) →
          ∃ L : Finset ℕ,
            L.card ≤ Roots.card + (R.filter (fun r => ∃ w ∈ Roots, OrReaches nv C w r)).card ∧
            (∀ w ∈ L, w < nv ∨ ∃ h ∈ lam G C, w = nv + h) ∧
            (∀ w ∈ Roots, orIn nv C w ⊆ L.biUnion (orIn nv C)) := by
        have hInd : ∀ (k : ℕ) (Roots : Finset ℕ),
            (R.filter (fun r => ∃ w ∈ Roots, OrReaches nv C w r)).card = k →
            (∀ w ∈ Roots, w < nv + C.gates.length ∧ NoAnd w) →
            ∃ L : Finset ℕ,
              L.card ≤ Roots.card + k ∧
              (∀ w ∈ L, w < nv ∨ ∃ h ∈ lam G C, w = nv + h) ∧
              (∀ w ∈ Roots, orIn nv C w ⊆ L.biUnion (orIn nv C)) := by
          intro k
          induction k using Nat.strong_induction_on with
          | ind k ih =>
            intro Roots hcard hRoots
            let X := R.filter (fun r => ∃ w ∈ Roots, OrReaches nv C w r)
            by_cases hXne : X.Nonempty
            · let rMax := X.max' hXne
              have hrMaxMem : rMax ∈ X := Finset.max'_mem X hXne
              have hrMaxR : rMax ∈ R := (Finset.mem_filter.mp hrMaxMem).1
              obtain ⟨w0, hw0R, hw0r⟩ := (Finset.mem_filter.mp hrMaxMem).2
              have hrMaxLen : rMax < C.gates.length := ((orN_mem C rMax).mp (Finset.mem_sdiff.mp hrMaxR).1).1
              have hrMaxOp : (gateAt C rMax).op = GateOp.or := ((orN_mem C rMax).mp (Finset.mem_sdiff.mp hrMaxR).1).2.1
              have hrMaxNoAnd : NoAnd (nv + rMax) := (noAnd_reach_orN (hRoots w0 hw0R).2 hw0r).2
              have hOnlySelf : ∀ w ∈ Roots, OrReaches nv C w rMax → w = nv + rMax := by
                intro w hwR hwr
                by_contra hneW
                have hle := orReaches_le hwr
                have hltW : nv + rMax < w := by omega
                let g0 := w - nv
                have hwEq : w = nv + g0 := by omega
                have hg0len : g0 < C.gates.length := by have := (hRoots w hwR).1; omega
                have hg0Self : OrReaches nv C w g0 := by rw [hwEq]; exact (orReaches_iff g0 g0).mpr ⟨hg0len, Or.inl rfl⟩
                have hg0N : g0 ∈ orN G C := (noAnd_reach_orN (hRoots w hwR).2 hg0Self).1
                have hg0NotR : g0 ∉ R := by
                  intro hg0R
                  have hg0X : g0 ∈ X := Finset.mem_filter.mpr ⟨hg0R, w, hwR, hg0Self⟩
                  have hleM : g0 ≤ rMax := Finset.le_max' X g0 hg0X
                  omega
                have hg0Lam : g0 ∈ lam G C := by
                  by_contra hnl
                  exact hg0NotR (Finset.mem_sdiff.mpr ⟨hg0N, hnl⟩)
                have hne0 := noAnd_nonempty (by have := opndBound hrMaxLen 0; omega) (noAnd_opnd_or hrMaxLen hrMaxNoAnd 0)
                have hne1 := noAnd_nonempty (by have := opndBound hrMaxLen 1; omega) (noAnd_opnd_or hrMaxLen hrMaxNoAnd 1)
                rw [hwEq] at hwr
                exact no_bothNonempty_R_below_lam hrMaxR hg0Lam hne0 hne1 hwr
              have hSelfMem : nv + rMax ∈ Roots := hOnlySelf w0 hw0R hw0r ▸ hw0R
              let Roots' : Finset ℕ := (Roots.erase (nv + rMax)) ∪ {opnd C rMax 0, opnd C rMax 1}
              have hRoots'Ok : ∀ w ∈ Roots', w < nv + C.gates.length ∧ NoAnd w := by
                intro w hw
                rcases Finset.mem_union.mp hw with h1 | h2
                · exact hRoots w (Finset.mem_of_mem_erase h1)
                · rcases Finset.mem_insert.mp h2 with rfl | h2'
                  · exact ⟨by have := opndBound hrMaxLen 0; omega, noAnd_opnd_or hrMaxLen hrMaxNoAnd 0⟩
                  · rw [Finset.mem_singleton.mp h2']
                    exact ⟨by have := opndBound hrMaxLen 1; omega, noAnd_opnd_or hrMaxLen hrMaxNoAnd 1⟩
              let X' := R.filter (fun r => ∃ w ∈ Roots', OrReaches nv C w r)
              have hX'Sub : X' ⊆ X.erase rMax := by
                intro r hr
                have hrR := (Finset.mem_filter.mp hr).1
                obtain ⟨w, hw', hwr⟩ := (Finset.mem_filter.mp hr).2
                have hrNe : r ≠ rMax := by
                  intro heq; subst r
                  rcases Finset.mem_union.mp hw' with h1 | h2
                  · exact (Finset.mem_erase.mp h1).1 (hOnlySelf w (Finset.mem_of_mem_erase h1) hwr)
                  · have hwLt : w < nv + rMax := by
                      rcases Finset.mem_insert.mp h2 with rfl | h2'
                      · exact opndBound hrMaxLen 0
                      · rw [Finset.mem_singleton.mp h2']; exact opndBound hrMaxLen 1
                    have hge := orReaches_le hwr
                    omega
                refine Finset.mem_erase.mpr ⟨hrNe, Finset.mem_filter.mpr ⟨hrR, ?_⟩⟩
                rcases Finset.mem_union.mp hw' with h1 | h2
                · exact ⟨w, Finset.mem_of_mem_erase h1, hwr⟩
                · refine ⟨nv + rMax, hSelfMem, (orReaches_iff rMax r).mpr ⟨hrMaxLen, Or.inr ⟨hrMaxOp, w, ?_, ?_, hwr⟩⟩⟩
                  · rcases Finset.mem_insert.mp h2 with rfl | h2'
                    · exact opndMem hrMaxLen 0
                    · rw [Finset.mem_singleton.mp h2']; exact opndMem hrMaxLen 1
                  · rcases Finset.mem_insert.mp h2 with rfl | h2'
                    · exact opndBound hrMaxLen 0
                    · rw [Finset.mem_singleton.mp h2']; exact opndBound hrMaxLen 1
              have hX'Lt : X'.card < k := by
                have h1 := Finset.card_le_card hX'Sub
                have h2 := Finset.card_erase_of_mem hrMaxMem
                have h3 : 0 < X.card := Finset.card_pos.mpr hXne
                have hXk : X.card = k := hcard
                omega
              obtain ⟨L, hLcard, hLok, hLcov⟩ := ih X'.card hX'Lt Roots' rfl hRoots'Ok
              have hR'Card : Roots'.card ≤ Roots.card + 1 := by
                have h1 : Roots'.card ≤ (Roots.erase (nv + rMax)).card + ({opnd C rMax 0, opnd C rMax 1} : Finset ℕ).card :=
                  Finset.card_union_le _ _
                have h2 : ({opnd C rMax 0, opnd C rMax 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
                have h3 := Finset.card_erase_of_mem hSelfMem
                have h4 : 0 < Roots.card := Finset.card_pos.mpr ⟨nv + rMax, hSelfMem⟩
                omega
              refine ⟨L, by omega, hLok, fun w hw => ?_⟩
              by_cases hweq : w = nv + rMax
              · subst w
                rw [orIn_or_union hrMaxLen hrMaxOp]
                refine Finset.union_subset
                  (hLcov (opnd C rMax 0) (Finset.mem_union_right _ (Finset.mem_insert_self _ _)))
                  (hLcov (opnd C rMax 1) (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
              · exact hLcov w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hweq, hw⟩))
            · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXne
              refine ⟨Roots, by omega, fun w hw => ?_, fun w hw v hv => Finset.mem_biUnion.mpr ⟨w, hw, hv⟩⟩
              by_cases hw10 : w < nv
              · exact Or.inl hw10
              · let h := w - nv
                have hwEq : w = nv + h := by omega
                have hlen : h < C.gates.length := by have := (hRoots w hw).1; omega
                have hSelf : OrReaches nv C w h := by rw [hwEq]; exact (orReaches_iff h h).mpr ⟨hlen, Or.inl rfl⟩
                have hN : h ∈ orN G C := (noAnd_reach_orN (hRoots w hw).2 hSelf).1
                have hLam : h ∈ lam G C := by
                  by_contra hnl
                  have hmX : h ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hN, hnl⟩, w, hw, hSelf⟩
                  rw [hXe] at hmX; exact Finset.notMem_empty h hmX
                exact Or.inr ⟨h, hLam, hwEq⟩
        intro Roots hRoots
        exact hInd _ Roots rfl hRoots
      have pure_or_no_pair_bound : ∀ (Roots : Finset ℕ) (T : Finset (Fin nv)),
          (∀ w ∈ Roots, w < nv + C.gates.length ∧ NoAnd w) →
          T ⊆ Roots.biUnion (orIn nv C) →
          (∀ h ∈ lam G C, ∀ x ∈ T, ∀ y ∈ T, x ∈ orIn nv C (nv + h) → y ∈ orIn nv C (nv + h) → x = y) →
          T.card ≤ Roots.card + (R.filter (fun r => ∃ w ∈ Roots, OrReaches nv C w r)).card := by
        intro Roots T hRoots hTsub hNoPair
        obtain ⟨L, hLcard, hLok, hLcov⟩ := pure_or_R_count Roots hRoots
        have hTL : T ⊆ L.biUnion (fun u => T ∩ orIn nv C u) := by
          intro v hv
          obtain ⟨w, hwR, hvw⟩ := Finset.mem_biUnion.mp (hTsub hv)
          obtain ⟨u, huL, hvu⟩ := Finset.mem_biUnion.mp (hLcov w hwR hvw)
          exact Finset.mem_biUnion.mpr ⟨u, huL, Finset.mem_inter.mpr ⟨hv, hvu⟩⟩
        have hEachLe1 : ∀ u ∈ L, (T ∩ orIn nv C u).card ≤ 1 := by
          intro u hu
          apply Finset.card_le_one.mpr
          intro x hx y hy
          obtain ⟨hxT, hxu⟩ := Finset.mem_inter.mp hx
          obtain ⟨hyT, hyu⟩ := Finset.mem_inter.mp hy
          rcases hLok u hu with hlt | ⟨h, hh, rfl⟩
          · rw [show u = (⟨u, hlt⟩ : Fin nv).val from rfl, orIn_leaf] at hxu hyu
            exact (Finset.mem_singleton.mp hxu).trans (Finset.mem_singleton.mp hyu).symm
          · exact hNoPair h hh x hxT y hyT hxu hyu
        have h1 := Finset.card_le_card hTL
        have h2 := Finset.card_biUnion_le (s := L) (t := fun u => T ∩ orIn nv C u)
        have h3 : L.sum (fun u => (T ∩ orIn nv C u).card) ≤ L.sum (fun _ => 1) := Finset.sum_le_sum hEachLe1
        rw [Finset.sum_const, smul_eq_mul, mul_one] at h3
        omega
      have single_wire_no_pair : ∀ (w : ℕ) (T : Finset (Fin nv)),
          w < nv + C.gates.length → NoAnd w → T ⊆ orIn nv C w →
          (∀ h ∈ lam G C, ∀ x ∈ T, ∀ y ∈ T, x ∈ orIn nv C (nv + h) → y ∈ orIn nv C (nv + h) → x = y) →
          T.card ≤ 1 + (Rw w).card := by
        intro w T hw hna hTsub hNoPair
        have h1 := pure_or_no_pair_bound {w} T
          (fun u hu => by rw [Finset.mem_singleton.mp hu]; exact ⟨hw, hna⟩)
          (by intro v hv; exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_singleton_self w, hTsub hv⟩)
          hNoPair
        have hEqF : R.filter (fun r => ∃ u ∈ ({w} : Finset ℕ), OrReaches nv C u r) = Rw w := by
          apply Finset.ext; intro r; simp only [Rw, Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
        rw [Finset.card_singleton, hEqF] at h1
        exact h1
      let wA := opnd C j 0
      let wB := opnd C j 1
      have hwALt : wA < nv + C.gates.length := by have := opndBound hjlen 0; omega
      have hwBLt : wB < nv + C.gates.length := by have := opndBound hjlen 1; omega
      have hnaA : NoAnd wA := noAnd_opnd_and hjlen hjop (fun hr => by have := orReaches_le hr; have := opndBound hjlen 0; omega)
      have hnaB : NoAnd wB := noAnd_opnd_and hjlen hjop (fun hr => by have := orReaches_le hr; have := opndBound hjlen 1; omega)
      let A : Finset (Fin nv) := orIn nv C wA
      let B : Finset (Fin nv) := orIn nv C wB
      have hjVal : ∀ x : Fin nv → Bool, gateVal nv C j x = true ↔ (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) := by
        intro x
        rw [andValBoth hjlen hjop, noAnd_val hwALt hnaA, noAnd_val hwBLt hnaB]
      have hAne : A.Nonempty := noAnd_nonempty hwALt hnaA
      have hBne : B.Nonempty := noAnd_nonempty hwBLt hnaB
      have hNotAsubB : ¬ A ⊆ B := by
        intro hsub
        apply replace_gate_by_wire j wA hjlen (opndBound hjlen 0)
        intro x
        cases h1 : val C (List.ofFn x) wA
        · cases h2 : gateVal nv C j x
          · rfl
          · have h3 := ((andValBoth hjlen hjop x).mp h2).1
            exact Bool.noConfusion (h1.symm.trans h3)
        · obtain ⟨a, haA, hxa⟩ := (noAnd_val hwALt hnaA x).mp h1
          exact ((hjVal x).mpr ⟨⟨a, haA, hxa⟩, ⟨a, hsub haA, hxa⟩⟩).symm
      have hNotBsubA : ¬ B ⊆ A := by
        intro hsub
        apply replace_gate_by_wire j wB hjlen (opndBound hjlen 1)
        intro x
        cases h1 : val C (List.ofFn x) wB
        · cases h2 : gateVal nv C j x
          · rfl
          · have h3 := ((andValBoth hjlen hjop x).mp h2).2
            exact Bool.noConfusion (h1.symm.trans h3)
        · obtain ⟨b, hbB, hxb⟩ := (noAnd_val hwBLt hnaB x).mp h1
          exact ((hjVal x).mpr ⟨⟨b, hsub hbB, hxb⟩, ⟨b, hbB, hxb⟩⟩).symm
      let validZ : Finset (Fin nv) := Finset.univ.filter (fun z =>
        ∀ x : Fin nv → Bool, x z = true → gateVal nv C j x = true → graphFun G ∅ x = true)
      have hValidNotInter : ∀ z ∈ validZ, ¬ (z ∈ A ∧ z ∈ B) := by
        intro z hz hAB
        have hfire := (Finset.mem_filter.mp hz).2 (pairInput z z) (pairInput_left z z)
          ((hjVal _).mpr ⟨⟨z, hAB.1, pairInput_left z z⟩, ⟨z, hAB.2, pairInput_left z z⟩⟩)
        exact G.irrefl ((graphFun_pair z z).mp hfire)
      have hValidA_adjB : ∀ z ∈ validZ, z ∈ A → ∀ b ∈ B, G.Adj z b := by
        intro z hz hzA b hbB
        exact (graphFun_pair z b).mp ((Finset.mem_filter.mp hz).2 (pairInput z b) (pairInput_left z b)
          ((hjVal _).mpr ⟨⟨z, hzA, pairInput_left z b⟩, ⟨b, hbB, pairInput_right z b⟩⟩))
      have hValidB_adjA : ∀ z ∈ validZ, z ∈ B → ∀ a ∈ A, G.Adj z a := by
        intro z hz hzB a haA
        exact (graphFun_pair z a).mp ((Finset.mem_filter.mp hz).2 (pairInput z a) (pairInput_left z a)
          ((hjVal _).mpr ⟨⟨a, haA, pairInput_right z a⟩, ⟨z, hzB, pairInput_left z a⟩⟩))
      have hValid_adjAB : ∀ z ∈ validZ, ∀ w ∈ A ∩ B, G.Adj z w := by
        intro z hz w hw
        obtain ⟨hwA, hwB⟩ := Finset.mem_inter.mp hw
        exact (graphFun_pair z w).mp ((Finset.mem_filter.mp hz).2 (pairInput z w) (pairInput_left z w)
          ((hjVal _).mpr ⟨⟨w, hwA, pairInput_right z w⟩, ⟨w, hwB, pairInput_right z w⟩⟩))
      let ZU : Finset ℕ := (centreless G C).filter (fun t => ∃ d : Fin 2, OrReaches nv C (opnd C t d) j)
      let covZ : Finset (Fin nv) := ZU.biUnion (fun t => side (n := nv) C t 0 ∪ side (n := nv) C t 1)
      have hZ_other_side : ∀ t ∈ ZU, ∃ d : Fin 2,
          OrReaches nv C (opnd C t d) j ∧ ¬ OrReaches nv C (opnd C t (1 - d)) j ∧
          NoAnd (opnd C t (1 - d)) ∧ side (n := nv) C t d = ∅ ∧
          side (n := nv) C t 0 ∪ side (n := nv) C t 1 = side (n := nv) C t (1 - d) ∧
          side (n := nv) C t (1 - d) ⊆ validZ := by
        intro t ht
        obtain ⟨htZ, d, hd⟩ := Finset.mem_filter.mp ht
        obtain ⟨htT, htEmpty⟩ := (centreless_mem C t).mp htZ
        obtain ⟨htlen, htop, htb⟩ := topData htT
        have hnr : ¬ OrReaches nv C (opnd C t (1 - d)) j := by
          intro h1d
          apply hjnb
          intro x hx
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ hd).1 (gateVal_eq_val C j x ▸ hx)
            · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ h1d).1 (gateVal_eq_val C j x ▸ hx)))
        have hna := noAnd_opnd_and htlen htop hnr
        have hne1d : (side (n := nv) C t (1 - d)).Nonempty := by
          rw [side_def]; exact noAnd_nonempty (by have := opndBound htlen (1 - d); omega) hna
        have hemptyD : side (n := nv) C t d = ∅ := by
          rcases htEmpty with h0 | h1
          · rcases fin2_or d with rfl | rfl
            · exact h0
            · rw [show (1 - (1 : Fin 2)) = 0 from rfl, h0] at hne1d
              exact False.elim (Finset.not_nonempty_empty hne1d)
          · rcases fin2_or d with rfl | rfl
            · rw [show (1 - (0 : Fin 2)) = 1 from rfl, h1] at hne1d
              exact False.elim (Finset.not_nonempty_empty hne1d)
            · exact h1
        have hunion : side (n := nv) C t 0 ∪ side (n := nv) C t 1 = side (n := nv) C t (1 - d) := by
          rcases fin2_or d with rfl | rfl
          · rw [hemptyD, Finset.empty_union]; rfl
          · rw [hemptyD, Finset.union_empty]; rfl
        have hsubV : side (n := nv) C t (1 - d) ⊆ validZ := by
          intro z hz
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hxz hxj => ?_⟩
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ hd).1 (gateVal_eq_val C j x ▸ hxj)
            · rw [fin2_ne_eq d idx hidx]; exact sideVal hz hxz))
        exact ⟨d, hd, hnr, hna, hemptyD, hunion, hsubV⟩
      have hUstar_struct : ∀ {u v : Fin nv}, s(u, v) ∈ Ustar G C →
          gateVal nv C j (pairInput u v) = true ∧
          ∃ t ∈ tops G C, ∃ d : Fin 2, OrReaches nv C (opnd C t d) j ∧
            (u ∈ side (n := nv) C t (1 - d) ∨ v ∈ side (n := nv) C t (1 - d)) ∧
            side (n := nv) C t (1 - d) ⊆ validZ := by
        intro u v he
        obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
        have hj'eq : j' = j := hjUniq j' hj'
        subst j'
        obtain ⟨htlen, htop, htb⟩ := topData ht
        have hnr : ¬ OrReaches nv C (opnd C t (1 - d)) j := by
          intro h1d
          apply hjnb
          intro x hx
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ htd).1 (gateVal_eq_val C j x ▸ hx)
            · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ h1d).1 (gateVal_eq_val C j x ▸ hx)))
        have hna := noAnd_opnd_and htlen htop hnr
        have h1dVal : val C (List.ofFn (pairInput u v)) (opnd C t (1 - d)) = true :=
          ((andValOperands htlen htop _).mp htv) (1 - d)
        obtain ⟨z, hzSide, hzp⟩ := (noAnd_val (by have := opndBound htlen (1 - d); omega) hna _).mp h1dVal
        have hsubV : side (n := nv) C t (1 - d) ⊆ validZ := by
          intro w hw
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hxw hxj => ?_⟩
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ htd).1 (gateVal_eq_val C j x ▸ hxj)
            · rw [fin2_ne_eq d idx hidx]; exact sideVal hw hxw))
        refine ⟨hj'v, t, ht, d, htd, ?_, hsubV⟩
        rcases (pairInput_true u v z).mp hzp with rfl | rfl
        · exact Or.inl hzSide
        · exact Or.inr hzSide
      have hRabove_pos_of_Z0 : (centreless G C).card = 0 → 1 ≤ Rabove.card := by
        intro hZ0
        obtain ⟨e, he⟩ := hUstarNe
        induction e using Sym2.ind with
        | _ u v =>
          obtain ⟨_, t, ht, d, htd, _, _⟩ := hUstar_struct he
          have htNotZ : t ∉ centreless G C := fun h => by
            have := Finset.card_pos.mpr ⟨t, h⟩; omega
          have hneD : (orIn nv C (opnd C t d)).Nonempty := by
            by_contra hne
            exact htNotZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
          obtain ⟨m, hmR, _, hmj, _⟩ := noncentreless_witness hjMem htd hneD
          exact Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨hmR, hmj⟩⟩
      have hStar_Rabove_bound : ∀ (c : Fin nv) (T : Finset (Fin nv)),
          (∀ z ∈ T, s(c, z) ∈ Ustar G C ∧ z ∉ covZ ∧ c ∉ validZ) →
          ∃ f : Fin nv → ℕ,
            (∀ z ∈ T, f z ∈ Rabove ∧ (orIn nv C (nv + f z)).Nonempty ∧
              ∀ q ∈ orIn nv C (nv + f z), G.Adj z q ∧ s(z, q) ∈ starEdges G C) ∧
            Set.InjOn f ↑T := by
        intro c T hT
        have hEx : ∀ z : Fin nv, z ∈ T →
            ∃ m ∈ Rabove, (orIn nv C (nv + m)).Nonempty ∧
              ∀ q ∈ orIn nv C (nv + m), G.Adj z q ∧ s(z, q) ∈ starEdges G C := by
          intro z hz
          obtain ⟨heU, hzNotCov, hcNotV⟩ := hT z hz
          obtain ⟨_, t, ht, d, htd, hSideOr, hSubV⟩ := hUstar_struct heU
          have hzSide : z ∈ side (n := nv) C t (1 - d) := by
            rcases hSideOr with hcS | hzS
            · exact False.elim (hcNotV (hSubV hcS))
            · exact hzS
          have htNotZ : t ∉ centreless G C := by
            intro htZ
            have htZU : t ∈ ZU := Finset.mem_filter.mpr ⟨htZ, d, htd⟩
            apply hzNotCov
            refine Finset.mem_biUnion.mpr ⟨t, htZU, ?_⟩
            rcases fin2_or d with rfl | rfl
            · exact Finset.mem_union_right _ hzSide
            · exact Finset.mem_union_left _ hzSide
          have hneD : (orIn nv C (opnd C t d)).Nonempty := by
            by_contra hne
            exact htNotZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
          obtain ⟨m, hmR, htm, hmj, hmne⟩ := noncentreless_witness hjMem htd hneD
          refine ⟨m, Finset.mem_filter.mpr ⟨hmR, hmj⟩, hmne, fun q hq => ?_⟩
          have hqSide : q ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm hq
          exact ⟨(topAdj_side ht hqSide hzSide).symm, Sym2.eq_swap ▸ side_mem_starEdges ht hqSide hzSide⟩
        let f : Fin nv → ℕ := fun z => if h : z ∈ T then Classical.choose (hEx z h) else 0
        refine ⟨f, fun z hz => ?_, fun z1 hz1 z2 hz2 hfeq => ?_⟩
        · dsimp only [f]; rw [dif_pos hz]; exact Classical.choose_spec (hEx z hz)
        · by_contra hne
          have h1 : f z1 ∈ Rabove ∧ (orIn nv C (nv + f z1)).Nonempty ∧
              ∀ q ∈ orIn nv C (nv + f z1), G.Adj z1 q ∧ s(z1, q) ∈ starEdges G C := by
            dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hz1)]; exact Classical.choose_spec (hEx z1 (Finset.mem_coe.mp hz1))
          have h2 : f z2 ∈ Rabove ∧ (orIn nv C (nv + f z2)).Nonempty ∧
              ∀ q ∈ orIn nv C (nv + f z2), G.Adj z2 q ∧ s(z2, q) ∈ starEdges G C := by
            dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hz2)]; exact Classical.choose_spec (hEx z2 (Finset.mem_coe.mp hz2))
          obtain ⟨q, hq⟩ := h1.2.1
          have hq1 := h1.2.2 q hq
          have hq2 := h2.2.2 q (hfeq ▸ hq)
          have hc1 : G.Adj c z1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (hT z1 hz1).1)).1
          have hc2 : G.Adj c z2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (hT z2 hz2).1)).1
          have hqc : q = c := by
            by_contra hqne
            have hc4 := hNo4 q c hqne
            have hm1 : z1 ∈ Finset.univ.filter (fun p => G.Adj q p ∧ G.Adj c p) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq1.1.symm, hc1⟩
            have hm2 : z2 ∈ Finset.univ.filter (fun p => G.Adj q p ∧ G.Adj c p) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq2.1.symm, hc2⟩
            exact hne (Finset.card_le_one.mp hc4 z1 hm1 z2 hm2)
          subst q
          have hu1 := (hT z1 hz1).1
          rw [Ustar_def] at hu1
          exact (Finset.mem_sdiff.mp hu1).2 (Sym2.eq_swap ▸ hq1.2)
      have hCovZ_bound : ∀ (c : Fin nv) (T : Finset (Fin nv)),
          (∀ z ∈ T, G.Adj c z ∧ s(c, z) ∈ Ustar G C ∧ z ∈ covZ) →
          ∃ RZ : Finset ℕ, RZ ⊆ R ∧
            (∀ r ∈ RZ, ∃ t ∈ ZU, ∃ d : Fin 2, ¬ OrReaches nv C (opnd C t d) j ∧ OrReaches nv C (opnd C t d) r) ∧
            T.card ≤ (centreless G C).card + RZ.card := by
        intro c T hT
        let nonJ : ℕ → ℕ := fun t => if h : t ∈ ZU then opnd C t (1 - Classical.choose (hZ_other_side t h)) else 0
        let Roots : Finset ℕ := ZU.image nonJ
        have hRootsOk : ∀ w ∈ Roots, w < nv + C.gates.length ∧ NoAnd w := by
          intro w hw
          obtain ⟨t, htZU, rfl⟩ := Finset.mem_image.mp hw
          dsimp only [nonJ]; rw [dif_pos htZU]
          have htSpec := Classical.choose_spec (hZ_other_side t htZU)
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          exact ⟨by have := opndBound htlen (1 - Classical.choose (hZ_other_side t htZU)); omega, htSpec.2.2.1⟩
        have hTsub : T ⊆ Roots.biUnion (orIn nv C) := by
          intro z hz
          obtain ⟨t, htZU, hzt⟩ := Finset.mem_biUnion.mp (hT z hz).2.2
          have htSpec := Classical.choose_spec (hZ_other_side t htZU)
          rw [htSpec.2.2.2.2.1, side_def] at hzt
          refine Finset.mem_biUnion.mpr ⟨nonJ t, Finset.mem_image_of_mem nonJ htZU, ?_⟩
          dsimp only [nonJ]; rw [dif_pos htZU]; exact hzt
        have hBnd := pure_or_no_pair_bound Roots T hRootsOk hTsub
          (no_lam_two_Ustar_nbrs c T (fun z hz => (hT z hz).1) (fun z hz _ _ _ => Or.inl (hT z hz).2.1))
        let RZ := R.filter (fun r => ∃ w ∈ Roots, OrReaches nv C w r)
        refine ⟨RZ, Finset.filter_subset _ R, fun r hr => ?_, ?_⟩
        · obtain ⟨w, hwR, hwr⟩ := (Finset.mem_filter.mp hr).2
          obtain ⟨t, htZU, rfl⟩ := Finset.mem_image.mp hwR
          dsimp only [nonJ] at hwr; rw [dif_pos htZU] at hwr
          have htSpec := Classical.choose_spec (hZ_other_side t htZU)
          exact ⟨t, htZU, 1 - Classical.choose (hZ_other_side t htZU), htSpec.2.1, hwr⟩
        · have hBnd' : T.card ≤ Roots.card + RZ.card := hBnd
          have h1 : Roots.card ≤ ZU.card := Finset.card_image_le
          have h2 : ZU.card ≤ (centreless G C).card := Finset.card_le_card (Finset.filter_subset _ _)
          omega
      have hRZ_disj_all : ∀ (RZ : Finset ℕ),
          (∀ r ∈ RZ, ∃ t ∈ ZU, ∃ d : Fin 2, ¬ OrReaches nv C (opnd C t d) j ∧ OrReaches nv C (opnd C t d) r) →
          Disjoint RZ Rabove ∧
          ((validZ ∩ A).card ≤ 1 → Disjoint RZ (Rw wA)) ∧
          ((validZ ∩ B).card ≤ 1 → Disjoint RZ (Rw wB)) := by
        intro RZ hRZ
        refine ⟨?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro r hr1 hr2
          obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
          have hna := noAnd_opnd_and htlen htop hnr
          have hop := hna j (orReaches_trans htr (Finset.mem_filter.mp hr2).2)
          rw [hjop] at hop; exact GateOp.noConfusion hop
        · intro hVA
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
          obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
          have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
          subst d
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
          have hna := noAnd_opnd_and htlen htop hnr
          have hcap : (orIn nv C (opnd C t (1 - d0)) ∩ A).card ≤ 1 := by
            have hsub : orIn nv C (opnd C t (1 - d0)) ∩ A ⊆ validZ ∩ A := by
              intro v hv; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
              exact Finset.mem_inter.mpr ⟨hsubV h1, h2⟩
            exact le_trans (Finset.card_le_card hsub) hVA
          exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hnaA hcap)
            (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
        · intro hVB
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
          obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
          have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
          subst d
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
          have hna := noAnd_opnd_and htlen htop hnr
          have hcap : (orIn nv C (opnd C t (1 - d0)) ∩ B).card ≤ 1 := by
            have hsub : orIn nv C (opnd C t (1 - d0)) ∩ B ⊆ validZ ∩ B := by
              intro v hv; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
              exact Finset.mem_inter.mpr ⟨hsubV h1, h2⟩
            exact le_trans (Finset.card_le_card hsub) hVB
          exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hnaB hcap)
            (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
      have hSingletonStarContra : ∀ (c : Fin nv) (w : ℕ),
          w < nv + C.gates.length → NoAnd w →
          (∀ e ∈ Ustar G C, c ∈ e) →
          (∀ u : Fin nv, s(c, u) ∈ Ustar G C → u ∈ orIn nv C w) → False := by
        intro c w hw hna hCov hInW
        have hBnd := hBudgetLtCov {c} (fun e he => ⟨c, Finset.mem_singleton_self c, hCov e he⟩)
        rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hBnd
        let TU : Finset (Fin nv) := (orIn nv C w).filter (fun u => s(c, u) ∈ Ustar G C)
        have hTUcard : (Ustar G C).card ≤ TU.card := by
          have hsub : Ustar G C ⊆ TU.image (fun u => s(c, u)) := by
            intro e he
            induction e using Sym2.ind with
            | _ p q =>
              rcases Sym2.mem_iff.mp (hCov s(p, q) he) with rfl | rfl
              · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hInW q he, he⟩, rfl⟩
              · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hInW p (Sym2.eq_swap ▸ he), Sym2.eq_swap ▸ he⟩, Sym2.eq_swap⟩
          exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
        have hRw := single_wire_no_pair w TU hw hna (Finset.filter_subset _ _)
          (no_lam_two_Ustar_nbrs c TU
            (fun u hu => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (Finset.mem_filter.mp hu).2)).1)
            (fun u hu _ _ _ => Or.inl (Finset.mem_filter.mp hu).2))
        by_cases hZ0 : (centreless G C).card = 0
        · have hRa := hRabove_pos_of_Z0 hZ0
          have hDisj := noAnd_disj_Rabove hna
          have hUn : (Rw w ∪ Rabove).card ≤ R.card :=
            Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R))
          rw [Finset.card_union_of_disjoint hDisj] at hUn
          omega
        · have hSub : (Rw w).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ R)
          omega
      have hAge2 : 2 ≤ A.card := by
        by_contra hlt
        have hA1 : A.card = 1 := by have := Finset.card_pos.mpr hAne; omega
        obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hA1
        have hw0NotB : w0 ∉ B := fun h => hNotAsubB (fun a ha => by rw [hw0] at ha; rw [Finset.mem_singleton.mp ha]; exact h)
        exact hSingletonStarContra w0 wB hwBLt hnaB
          (fun e he => Sym2.ind (fun u v he' => by
            obtain ⟨a, haA, hpa⟩ := ((hjVal _).mp (hUstar_struct he').1).1
            rw [hw0] at haA; rw [Finset.mem_singleton.mp haA] at hpa
            rcases (pairInput_true u v w0).mp hpa with rfl | rfl
            · exact Sym2.mem_mk_left _ _
            · exact Sym2.mem_mk_right _ _) e he)
          (fun u hu => by
            obtain ⟨b, hbB, hpb⟩ := ((hjVal _).mp (hUstar_struct hu).1).2
            rcases (pairInput_true w0 u b).mp hpb with rfl | rfl
            · exact False.elim (hw0NotB hbB)
            · exact hbB)
      have hBge2 : 2 ≤ B.card := by
        by_contra hlt
        have hB1 : B.card = 1 := by have := Finset.card_pos.mpr hBne; omega
        obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hB1
        have hw0NotA : w0 ∉ A := fun h => hNotBsubA (fun b hb => by rw [hw0] at hb; rw [Finset.mem_singleton.mp hb]; exact h)
        exact hSingletonStarContra w0 wA hwALt hnaA
          (fun e he => Sym2.ind (fun u v he' => by
            obtain ⟨b, hbB, hpb⟩ := ((hjVal _).mp (hUstar_struct he').1).2
            rw [hw0] at hbB; rw [Finset.mem_singleton.mp hbB] at hpb
            rcases (pairInput_true u v w0).mp hpb with rfl | rfl
            · exact Sym2.mem_mk_left _ _
            · exact Sym2.mem_mk_right _ _) e he)
          (fun u hu => by
            obtain ⟨a, haA, hpa⟩ := ((hjVal _).mp (hUstar_struct hu).1).1
            rcases (pairInput_true w0 u a).mp hpa with rfl | rfl
            · exact False.elim (hw0NotA haA)
            · exact haA)
      have hVA_le1 : (validZ ∩ A).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro z1 hz1 z2 hz2
        by_contra hne
        have hc4 := hNo4 z1 z2 hne
        have hsub : B ⊆ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z2 p) := fun b hb =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValidA_adjB z1 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2 b hb,
            hValidA_adjB z2 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2 b hb⟩
        have hle := le_trans (Finset.card_le_card hsub) hc4
        omega
      have hVB_le1 : (validZ ∩ B).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro z1 hz1 z2 hz2
        by_contra hne
        have hc4 := hNo4 z1 z2 hne
        have hsub : A ⊆ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z2 p) := fun a ha =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValidB_adjA z1 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2 a ha,
            hValidB_adjA z2 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2 a ha⟩
        have hle := le_trans (Finset.card_le_card hsub) hc4
        omega
      have hCase2Sym : ∀ (w1 w2 : ℕ), w1 < nv + C.gates.length → w2 < nv + C.gates.length →
          NoAnd w1 → NoAnd w2 →
          (∀ x : Fin nv → Bool, gateVal nv C j x = true ↔ (∃ a ∈ orIn nv C w1, x a = true) ∧ (∃ b ∈ orIn nv C w2, x b = true)) →
          (validZ ∩ orIn nv C w1).Nonempty → (validZ ∩ orIn nv C w2) = ∅ →
          (validZ ∩ orIn nv C w1).card ≤ 1 → False := by
        intro w1 w2 hw1 hw2 hna1 hna2 hjV12 hV1ne hV2e hV1le1
        let S1 := orIn nv C w1
        let S2 := orIn nv C w2
        have hV1card : (validZ ∩ S1).card = 1 := by
          have h1 : (validZ ∩ S1).card ≤ 1 := hV1le1
          have h2 : 0 < (validZ ∩ S1).card := Finset.card_pos.mpr hV1ne
          omega
        obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hV1card
        have hz1V : z1 ∈ validZ := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).1
        have hz1S1 : z1 ∈ S1 := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).2
        have hS2adj : ∀ b ∈ S2, G.Adj z1 b := fun b hb =>
          (graphFun_pair z1 b).mp ((Finset.mem_filter.mp hz1V).2 (pairInput z1 b) (pairInput_left z1 b)
            ((hjV12 _).mpr ⟨⟨z1, hz1S1, pairInput_left z1 b⟩, ⟨b, hb, pairInput_right z1 b⟩⟩))
        have hz1NotS2 : z1 ∉ S2 := fun h => G.irrefl (hS2adj z1 h)
        have hNotInV : ∀ b ∈ S2, b ∉ validZ := fun b hb hbv => by
          have hm : b ∈ validZ ∩ S2 := Finset.mem_inter.mpr ⟨hbv, hb⟩
          rw [hV2e] at hm; exact Finset.notMem_empty b hm
        have hV_adjInter : ∀ z ∈ validZ, ∀ w ∈ S1 ∩ S2, G.Adj z w := fun z hz w hw =>
          (graphFun_pair z w).mp ((Finset.mem_filter.mp hz).2 (pairInput z w) (pairInput_left z w)
            ((hjV12 _).mpr ⟨⟨w, (Finset.mem_inter.mp hw).1, pairInput_right z w⟩, ⟨w, (Finset.mem_inter.mp hw).2, pairInput_right z w⟩⟩))
        by_cases hInter1 : (S1 ∩ S2).card = 1
        · obtain ⟨w0, hw0Set⟩ := Finset.card_eq_one.mp hInter1
          have hw0S1 : w0 ∈ S1 := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).1
          have hw0S2 : w0 ∈ S2 := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).2
          have hadjZW : G.Adj z1 w0 := hS2adj w0 hw0S2
          have hw0NotV : w0 ∉ validZ := hNotInV w0 hw0S2
          have hz1NeW0 : z1 ≠ w0 := hadjZW.ne
          have hRw1Pos : 1 ≤ (Rw w1).card := by
            have hw1NotLt10 : ¬ w1 < nv := by
              intro hlt
              have h1 := orIn_leaf ⟨w1, hlt⟩
              have hz1' : z1 ∈ ({⟨w1, hlt⟩} : Finset (Fin nv)) := h1 ▸ hz1S1
              have hw0' : w0 ∈ ({⟨w1, hlt⟩} : Finset (Fin nv)) := h1 ▸ hw0S1
              exact hz1NeW0 ((Finset.mem_singleton.mp hz1').trans (Finset.mem_singleton.mp hw0').symm)
            let r1 := w1 - nv
            have hw1Eq : w1 = nv + r1 := by omega
            have hr1len : r1 < C.gates.length := by omega
            have hr1Self : OrReaches nv C w1 r1 := by rw [hw1Eq]; exact (orReaches_iff r1 r1).mpr ⟨hr1len, Or.inl rfl⟩
            have hr1N : r1 ∈ orN G C := (noAnd_reach_orN hna1 hr1Self).1
            have hr1NotLam : r1 ∉ lam G C := by
              intro hlam
              obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C r1).mp hlam
              obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
              have hqs : q ∈ side (n := nv) C t (1 - d) := by rw [hq]; exact Finset.mem_singleton_self q
              have hz1s : z1 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono hth (hw1Eq ▸ hz1S1)
              have hw0s : w0 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono hth (hw1Eq ▸ hw0S1)
              have hqz1 : G.Adj q z1 := (topAdj_side ht hz1s hqs).symm
              have hqw0 : G.Adj q w0 := (topAdj_side ht hw0s hqs).symm
              exact hNoTri q z1 w0 hqz1 hadjZW hqw0
            exact Finset.card_pos.mpr ⟨r1, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr1N, hr1NotLam⟩, hr1Self⟩⟩
          let TB : Finset (Fin nv) := (S2.erase w0).filter (fun b => s(z1, b) ∈ Ustar G C)
          let TW : Finset (Fin nv) := (validZ.erase z1).filter (fun z => s(w0, z) ∈ Ustar G C)
          let δ : ℕ := if s(z1, w0) ∈ Ustar G C then 1 else 0
          have hEdgeClass : ∀ e ∈ Ustar G C,
              e = s(z1, w0) ∨ (∃ b ∈ TB, e = s(z1, b)) ∨ (∃ z ∈ TW, e = s(w0, z)) := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              obtain ⟨hjv, t, _, d, _, hSide, hSubV⟩ := hUstar_struct he
              obtain ⟨⟨a, ha1, hpa⟩, ⟨b, hb2, hpb⟩⟩ := (hjV12 _).mp hjv
              have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
              have hCaseUV : ∀ p q : Fin nv, s(p, q) ∈ Ustar G C → p ∈ validZ →
                  gateVal nv C j (pairInput p q) = true →
                  s(p, q) = s(z1, w0) ∨ (∃ b' ∈ TB, s(p, q) = s(z1, b')) ∨ (∃ z' ∈ TW, s(p, q) = s(w0, z')) := by
                intro p q hpqU hpV hjvpq
                obtain ⟨⟨a', ha'1, hpa'⟩, ⟨b', hb'2, hpb'⟩⟩ := (hjV12 _).mp hjvpq
                by_cases hpz1 : p = z1
                · subst p
                  have hqb' : q = b' := by
                    rcases (pairInput_true z1 q b').mp hpb' with rfl | rfl
                    · exact False.elim (hz1NotS2 hb'2)
                    · rfl
                  subst q
                  by_cases hbw : b' = w0
                  · subst b'; exact Or.inl rfl
                  · exact Or.inr (Or.inl ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hbw, hb'2⟩, hpqU⟩, rfl⟩)
                · have hpNotS1 : p ∉ S1 := fun h => hpz1 (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, h⟩))
                  have hpNotS2 : p ∉ S2 := fun h => hNotInV p h hpV
                  have hqa' : q = a' := by
                    rcases (pairInput_true p q a').mp hpa' with rfl | rfl
                    · exact False.elim (hpNotS1 ha'1)
                    · rfl
                  have hqb' : q = b' := by
                    rcases (pairInput_true p q b').mp hpb' with rfl | rfl
                    · exact False.elim (hpNotS2 hb'2)
                    · rfl
                  have hqInter : q ∈ S1 ∩ S2 := Finset.mem_inter.mpr ⟨hqa' ▸ ha'1, hqb' ▸ hb'2⟩
                  have hqw0 : q = w0 := Finset.mem_singleton.mp (hw0Set ▸ hqInter)
                  rw [hqw0] at hpqU ⊢
                  exact Or.inr (Or.inr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpz1, hpV⟩, Sym2.eq_swap ▸ hpqU⟩, Sym2.eq_swap⟩)
              rcases hOneV with huV | hvV
              · exact hCaseUV u v he huV hjv
              · have hres := hCaseUV v u (Sym2.eq_swap ▸ he) hvV (pairInput_symm u v ▸ hjv)
                rcases hres with h | ⟨b', hb', h⟩ | ⟨z', hz', h⟩
                · exact Or.inl (Sym2.eq_swap.trans h)
                · exact Or.inr (Or.inl ⟨b', hb', Sym2.eq_swap.trans h⟩)
                · exact Or.inr (Or.inr ⟨z', hz', Sym2.eq_swap.trans h⟩)
          have hUstarCard : (Ustar G C).card ≤ δ + TB.card + TW.card := by
            let E0 : Finset (Sym2 (Fin nv)) := if s(z1, w0) ∈ Ustar G C then {s(z1, w0)} else ∅
            have hsub : Ustar G C ⊆ E0 ∪ (TB.image (fun b => s(z1, b)) ∪ TW.image (fun z => s(w0, z))) := by
              intro e he
              rcases hEdgeClass e he with rfl | ⟨b, hb, rfl⟩ | ⟨z, hz, rfl⟩
              · exact Finset.mem_union_left _ (by dsimp only [E0]; rw [if_pos he]; exact Finset.mem_singleton_self _)
              · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz))
            have hE0 : E0.card = δ := by
              dsimp only [E0, δ]
              by_cases h : s(z1, w0) ∈ Ustar G C
              · rw [if_pos h, if_pos h, Finset.card_singleton]
              · rw [if_neg h, if_neg h, Finset.card_empty]
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_union_le E0 (TB.image (fun b => s(z1, b)) ∪ TW.image (fun z => s(w0, z)))
            have h3 := Finset.card_union_le (TB.image (fun b => s(z1, b))) (TW.image (fun z => s(w0, z)))
            have h4 : (TB.image (fun b => s(z1, b))).card ≤ TB.card := Finset.card_image_le
            have h5 : (TW.image (fun z => s(w0, z))).card ≤ TW.card := Finset.card_image_le
            omega
          have hTB_Rw2 : TB.card ≤ (Rw w2).card := by
            have hw0NotTB : w0 ∉ TB := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
            have hsub2 : insert w0 TB ⊆ S2 := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hxTB
              · exact hw0S2
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTB).1
            have hBnd := single_wire_no_pair w2 (insert w0 TB) hw2 hna2 hsub2
              (no_lam_two_Ustar_nbrs z1 (insert w0 TB) (fun x hx => hS2adj x (hsub2 hx))
                (fun x hx y hy hxy => by
                  rcases Finset.mem_insert.mp hx with rfl | hxTB
                  · rcases Finset.mem_insert.mp hy with rfl | hyTB
                    · exact False.elim (hxy rfl)
                    · exact Or.inr (Finset.mem_filter.mp hyTB).2
                  · exact Or.inl (Finset.mem_filter.mp hxTB).2))
            rw [Finset.card_insert_of_notMem hw0NotTB] at hBnd
            omega
          let TWZ := TW.filter (fun z => z ∈ covZ)
          let TWN := TW.filter (fun z => z ∉ covZ)
          have hTWsplit : TW.card = TWZ.card + TWN.card := by
            have hDisjZ : Disjoint TWZ TWN := Finset.disjoint_left.mpr (fun z h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2)
            have hUnZ : TWZ ∪ TWN = TW := by
              apply Finset.ext; intro z; simp only [TWZ, TWN, Finset.mem_union, Finset.mem_filter]
              exact ⟨fun h => h.elim And.left And.left, fun h => (em (z ∈ covZ)).elim (fun hc => Or.inl ⟨h, hc⟩) (fun hc => Or.inr ⟨h, hc⟩)⟩
            rw [← hUnZ, Finset.card_union_of_disjoint hDisjZ]
          obtain ⟨RZ, hRZsub, hRZspec, hTWZ_bnd⟩ := hCovZ_bound w0 TWZ (fun z hz => by
            obtain ⟨hzTW, hzCov⟩ := Finset.mem_filter.mp hz
            have hu := (Finset.mem_filter.mp hzTW).2
            exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu)).1, hu, hzCov⟩)
          obtain ⟨fN, hfNspec, hfNinj⟩ := hStar_Rabove_bound w0 TWN (fun z hz => by
            obtain ⟨hzTW, hzNotCov⟩ := Finset.mem_filter.mp hz
            exact ⟨(Finset.mem_filter.mp hzTW).2, hzNotCov, hw0NotV⟩)
          have hTWN_bnd : TWN.card ≤ Rabove.card := by
            have hsub : TWN.image fN ⊆ Rabove := fun m hm => by
              obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1
            rw [← Finset.card_image_of_injOn hfNinj]
            exact Finset.card_le_card hsub
          have hDisj12 : Disjoint (Rw w1) (Rw w2) := noAnd_disj_Rw hna1 hna2 (le_of_eq hInter1)
          have hDisj1A : Disjoint (Rw w1) Rabove := noAnd_disj_Rabove hna1
          have hDisj2A : Disjoint (Rw w2) Rabove := noAnd_disj_Rabove hna2
          have hDisjRZ_A : Disjoint RZ Rabove := (hRZ_disj_all RZ hRZspec).1
          have hDisjRZ_1 : Disjoint RZ (Rw w1) := by
            rw [Finset.disjoint_left]
            intro r hr1 hr2
            obtain ⟨t, htZU, d, hnr, htr⟩ := hRZspec r hr1
            obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
            have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
            subst d
            have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
            have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
            have hna := noAnd_opnd_and htlen htop hnr
            have hcap : (orIn nv C (opnd C t (1 - d0)) ∩ S1).card ≤ 1 :=
              le_trans (Finset.card_le_card (fun v hv => Finset.mem_inter.mpr ⟨hsubV (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩)) hV1le1
            exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hna1 hcap)
              (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
          have hDisjRZ_2 : Disjoint RZ (Rw w2) := by
            rw [Finset.disjoint_left]
            intro r hr1 hr2
            obtain ⟨t, htZU, d, hnr, htr⟩ := hRZspec r hr1
            obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
            have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
            subst d
            have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
            have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
            have hna := noAnd_opnd_and htlen htop hnr
            have hcap : (orIn nv C (opnd C t (1 - d0)) ∩ S2).card ≤ 1 := by
              have hsub : orIn nv C (opnd C t (1 - d0)) ∩ S2 ⊆ validZ ∩ S2 :=
                fun v hv => Finset.mem_inter.mpr ⟨hsubV (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
              rw [hV2e] at hsub
              have := Finset.card_le_card hsub; simp only [Finset.card_empty] at this; omega
            exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hna2 hcap)
              (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
          have hRsum : (Rw w1).card + (Rw w2).card + RZ.card + Rabove.card ≤ R.card := by
            have hsub : ((Rw w1 ∪ Rw w2) ∪ RZ) ∪ Rabove ⊆ R :=
              Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R)) hRZsub)
                (Finset.filter_subset _ R)
            have h1 := Finset.card_le_card hsub
            have hd1 : Disjoint (Rw w1 ∪ Rw w2) RZ := Finset.disjoint_union_left.mpr ⟨hDisjRZ_1.symm, hDisjRZ_2.symm⟩
            have hd2 : Disjoint ((Rw w1 ∪ Rw w2) ∪ RZ) Rabove :=
              Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hDisj1A, hDisj2A⟩, hDisjRZ_A⟩
            rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hDisj12] at h1
            exact h1
          have hDeltaLe1 : δ ≤ 1 := by
            dsimp only [δ]
            by_cases h : s(z1, w0) ∈ Ustar G C
            · rw [if_pos h]
            · rw [if_neg h]; omega
          by_cases hTW0 : TW.card = 0
          · have hCov1 : ∀ e ∈ Ustar G C, ∃ v ∈ ({z1} : Finset (Fin nv)), v ∈ e := by
              intro e he
              rcases hEdgeClass e he with rfl | ⟨_, _, rfl⟩ | ⟨z, hz, _⟩
              · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
              · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
              · have := Finset.card_pos.mpr ⟨z, hz⟩; omega
            have hLt := hBudgetLtCov {z1} hCov1
            rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
            omega
          · by_cases hTB0 : TB.card = 0
            · have hCov1 : ∀ e ∈ Ustar G C, ∃ v ∈ ({w0} : Finset (Fin nv)), v ∈ e := by
                intro e he
                rcases hEdgeClass e he with rfl | ⟨b, hb, _⟩ | ⟨_, _, rfl⟩
                · exact ⟨w0, Finset.mem_singleton_self w0, Sym2.mem_mk_right _ _⟩
                · have := Finset.card_pos.mpr ⟨b, hb⟩; omega
                · exact ⟨w0, Finset.mem_singleton_self w0, Sym2.mem_mk_left _ _⟩
              have hLt := hBudgetLtCov {w0} hCov1
              rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
              omega
            · have hCov2 : ∀ e ∈ Ustar G C, ∃ v ∈ ({z1, w0} : Finset (Fin nv)), v ∈ e := by
                intro e he
                rcases hEdgeClass e he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
                · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
                · exact ⟨w0, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
              have hLt := hBudgetLtCov {z1, w0} hCov2
              rw [Finset.card_pair hz1NeW0, hjSet, Finset.card_singleton] at hLt
              by_cases hZ0 : (centreless G C).card = 0
              · have hTWZ0 : TWZ.card = 0 := by
                  by_contra hpos
                  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < TWZ.card)
                  obtain ⟨t, htZU, _⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hz).2
                  have := Finset.card_pos.mpr ⟨t, (Finset.mem_filter.mp htZU).1⟩
                  omega
                obtain ⟨b1, hb1⟩ := Finset.card_pos.mp (by omega : 0 < TB.card)
                have hb1U : s(z1, b1) ∈ Ustar G C := (Finset.mem_filter.mp hb1).2
                have hb1S2 : b1 ∈ S2 := Finset.mem_of_mem_erase (Finset.mem_filter.mp hb1).1
                have hb1NotV : b1 ∉ validZ := hNotInV b1 hb1S2
                obtain ⟨_, tB, htB, dB, htBd, hSideB, hSubVB⟩ := hUstar_struct hb1U
                have hz1SideB : z1 ∈ side (n := nv) C tB (1 - dB) := by
                  rcases hSideB with hz1S | hb1S
                  · exact hz1S
                  · exact False.elim (hb1NotV (hSubVB hb1S))
                have htBNotZ : tB ∉ centreless G C := fun h => by have := Finset.card_pos.mpr ⟨tB, h⟩; omega
                have hneDB : (orIn nv C (opnd C tB dB)).Nonempty := by
                  by_contra hne
                  exact htBNotZ (emptySide_mem_centreless htB (Finset.not_nonempty_iff_eq_empty.mp hne))
                obtain ⟨mB, hmBR, htBmB, hmBj, hmBne⟩ := noncentreless_witness hjMem htBd hneDB
                have hmBMem : mB ∈ Rabove := Finset.mem_filter.mpr ⟨hmBR, hmBj⟩
                have hmBNotImg : mB ∉ TWN.image fN := by
                  intro hmem
                  obtain ⟨z, hzN, hfz⟩ := Finset.mem_image.mp hmem
                  obtain ⟨q, hq⟩ := hmBne
                  have hqSideB : q ∈ side (n := nv) C tB dB := by rw [side_def]; exact orIn_mono htBmB hq
                  have hqz1 : G.Adj z1 q := (topAdj_side htB hqSideB hz1SideB).symm
                  have hqz : G.Adj z q ∧ s(z, q) ∈ starEdges G C := (hfNspec z hzN).2.2 q (hfz.symm ▸ hq)
                  have hzTW : z ∈ TW := (Finset.mem_filter.mp hzN).1
                  have hzNeZ1 : z ≠ z1 := (Finset.mem_erase.mp (Finset.mem_filter.mp hzTW).1).1
                  have hzw0U : s(w0, z) ∈ Ustar G C := (Finset.mem_filter.mp hzTW).2
                  have hzw0 : G.Adj w0 z := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hzw0U)).1
                  have hqNeW0 : q ≠ w0 := by
                    intro heq; subst q
                    rw [Ustar_def] at hzw0U
                    exact (Finset.mem_sdiff.mp hzw0U).2 (Sym2.eq_swap ▸ hqz.2)
                  have hc4 := hNo4 z1 z hzNeZ1.symm
                  have hm1 : w0 ∈ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z p) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadjZW, hzw0.symm⟩
                  have hm2 : q ∈ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z p) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqz1, hqz.1⟩
                  exact hqNeW0.symm (Finset.card_le_one.mp hc4 w0 hm1 q hm2)
                have hRabovePlus : TWN.card + 1 ≤ Rabove.card := by
                  have hsub : insert mB (TWN.image fN) ⊆ Rabove :=
                    Finset.insert_subset_iff.mpr ⟨hmBMem, fun m hm => by
                      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1⟩
                  have h1 := Finset.card_le_card hsub
                  rw [Finset.card_insert_of_notMem hmBNotImg, Finset.card_image_of_injOn hfNinj] at h1
                  exact h1
                omega
              · omega
        · have hAllZ1 : ∀ e ∈ Ustar G C, z1 ∈ e := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
              obtain ⟨⟨a, ha1, hpa⟩, ⟨b, hb2, hpb⟩⟩ := (hjV12 _).mp hjv
              have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
              have hCheck : ∀ p q : Fin nv, p ∈ validZ → gateVal nv C j (pairInput p q) = true → p = z1 := by
                intro p q hpV hjvpq
                by_contra hpne
                have hpNotS1 : p ∉ S1 := fun h => hpne (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, h⟩))
                have hpNotS2 : p ∉ S2 := fun h => hNotInV p h hpV
                obtain ⟨⟨a', ha'1, hpa'⟩, ⟨b', hb'2, hpb'⟩⟩ := (hjV12 _).mp hjvpq
                have hqa' : q = a' := by rcases (pairInput_true p q a').mp hpa' with rfl | rfl; exact False.elim (hpNotS1 ha'1); rfl
                have hqb' : q = b' := by rcases (pairInput_true p q b').mp hpb' with rfl | rfl; exact False.elim (hpNotS2 hb'2); rfl
                have hqInter : q ∈ S1 ∩ S2 := Finset.mem_inter.mpr ⟨hqa' ▸ ha'1, hqb' ▸ hb'2⟩
                have hge2 : 2 ≤ (S1 ∩ S2).card := by have := Finset.card_pos.mpr ⟨q, hqInter⟩; omega
                obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (S1 ∩ S2).card)
                have hc4 := hNo4 p z1 hpne
                have hm1 : x1 ∈ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj z1 w) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_adjInter p hpV x1 hx1, hV_adjInter z1 hz1V x1 hx1⟩
                have hm2 : x2 ∈ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj z1 w) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_adjInter p hpV x2 hx2, hV_adjInter z1 hz1V x2 hx2⟩
                exact hxne (Finset.card_le_one.mp hc4 x1 hm1 x2 hm2)
              rcases hOneV with huV | hvV
              · rw [hCheck u v huV hjv]; exact Sym2.mem_mk_left _ _
              · rw [hCheck v u hvV (pairInput_symm u v ▸ hjv)]; exact Sym2.mem_mk_right _ _
          exact hSingletonStarContra z1 w2 hw2 hna2 hAllZ1 (fun u hu => by
            obtain ⟨b, hb2, hpb⟩ := ((hjV12 _).mp (hUstar_struct hu).1).2
            rcases (pairInput_true z1 u b).mp hpb with rfl | rfl
            · exact False.elim (hz1NotS2 hb2)
            · exact hb2)
      by_cases hVA : (validZ ∩ A).Nonempty
      · by_cases hVB : (validZ ∩ B).Nonempty
        · have hVA1 : (validZ ∩ A).card = 1 := by have := Finset.card_pos.mpr hVA; omega
          have hVB1 : (validZ ∩ B).card = 1 := by have := Finset.card_pos.mpr hVB; omega
          obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hVA1
          obtain ⟨z2, hz2Set⟩ := Finset.card_eq_one.mp hVB1
          have hz1V : z1 ∈ validZ := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).1
          have hz1A : z1 ∈ A := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).2
          have hz2V : z2 ∈ validZ := (Finset.mem_inter.mp (hz2Set ▸ Finset.mem_singleton_self z2)).1
          have hz2B : z2 ∈ B := (Finset.mem_inter.mp (hz2Set ▸ Finset.mem_singleton_self z2)).2
          have hadj12 : G.Adj z1 z2 := hValidA_adjB z1 hz1V hz1A z2 hz2B
          have hABempty : A ∩ B = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            obtain ⟨hwA, hwB⟩ := Finset.mem_inter.mp hw
            exact hNoTri z1 z2 w hadj12 (hValidB_adjA z2 hz2V hz2B w hwA) (hValidA_adjB z1 hz1V hz1A w hwB)
          let TA : Finset (Fin nv) := (A.erase z1).filter (fun a => s(z2, a) ∈ Ustar G C)
          let TB : Finset (Fin nv) := (B.erase z2).filter (fun b => s(z1, b) ∈ Ustar G C)
          let δ : ℕ := if s(z1, z2) ∈ Ustar G C then 1 else 0
          have hEdge1 : ∀ e ∈ Ustar G C,
              e = s(z1, z2) ∨ (∃ a ∈ TA, e = s(z2, a)) ∨ (∃ b ∈ TB, e = s(z1, b)) := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
              have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
              have hCase : ∀ p q : Fin nv, s(p, q) ∈ Ustar G C → p ∈ validZ → gateVal nv C j (pairInput p q) = true →
                  s(p, q) = s(z1, z2) ∨ (∃ a ∈ TA, s(p, q) = s(z2, a)) ∨ (∃ b ∈ TB, s(p, q) = s(z1, b)) := by
                intro p q hpqU hpV hjvpq
                obtain ⟨⟨a', ha'A, hpa'⟩, ⟨b', hb'B, hpb'⟩⟩ := (hjVal _).mp hjvpq
                by_cases hpA : p ∈ A
                · have hp1 : p = z1 := Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, hpA⟩)
                  subst p
                  have hqb' : q = b' := by
                    rcases (pairInput_true z1 q b').mp hpb' with hb'z1 | rfl
                    · have hm : b' ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb'z1 ▸ hz1A, hb'B⟩
                      rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
                    · rfl
                  subst q
                  by_cases hb2 : b' = z2
                  · subst b'; exact Or.inl rfl
                  · exact Or.inr (Or.inr ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hb2, hb'B⟩, hpqU⟩, rfl⟩)
                · by_cases hpB : p ∈ B
                  · have hp2 : p = z2 := Finset.mem_singleton.mp (hz2Set ▸ Finset.mem_inter.mpr ⟨hpV, hpB⟩)
                    subst p
                    have hqa' : q = a' := by
                      rcases (pairInput_true z2 q a').mp hpa' with ha'z2 | rfl
                      · have hm : a' ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha'A, ha'z2 ▸ hz2B⟩
                        rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
                      · rfl
                    subst q
                    by_cases ha1 : a' = z1
                    · subst a'; exact Or.inl Sym2.eq_swap
                    · exact Or.inr (Or.inl ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ha1, ha'A⟩, hpqU⟩, rfl⟩)
                  · have hqa' : q = a' := by rcases (pairInput_true p q a').mp hpa' with rfl | rfl; exact False.elim (hpA ha'A); rfl
                    have hqb' : q = b' := by rcases (pairInput_true p q b').mp hpb' with rfl | rfl; exact False.elim (hpB hb'B); rfl
                    have hm : q ∈ A ∩ B := Finset.mem_inter.mpr ⟨hqa' ▸ ha'A, hqb' ▸ hb'B⟩
                    rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
              rcases hOneV with huV | hvV
              · exact hCase u v he huV hjv
              · rcases hCase v u (Sym2.eq_swap ▸ he) hvV (pairInput_symm u v ▸ hjv) with h | ⟨a, ha, h⟩ | ⟨b, hb, h⟩
                · exact Or.inl (Sym2.eq_swap.trans h)
                · exact Or.inr (Or.inl ⟨a, ha, Sym2.eq_swap.trans h⟩)
                · exact Or.inr (Or.inr ⟨b, hb, Sym2.eq_swap.trans h⟩)
          have hUcard : (Ustar G C).card ≤ δ + TA.card + TB.card := by
            let E0 : Finset (Sym2 (Fin nv)) := if s(z1, z2) ∈ Ustar G C then {s(z1, z2)} else ∅
            have hsub : Ustar G C ⊆ E0 ∪ (TA.image (fun a => s(z2, a)) ∪ TB.image (fun b => s(z1, b))) := by
              intro e he
              rcases hEdge1 e he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
              · exact Finset.mem_union_left _ (by dsimp only [E0]; rw [if_pos he]; exact Finset.mem_singleton_self _)
              · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
            have hE0 : E0.card = δ := by
              dsimp only [E0, δ]
              by_cases h : s(z1, z2) ∈ Ustar G C
              · rw [if_pos h, if_pos h, Finset.card_singleton]
              · rw [if_neg h, if_neg h, Finset.card_empty]
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_union_le E0 (TA.image (fun a => s(z2, a)) ∪ TB.image (fun b => s(z1, b)))
            have h3 := Finset.card_union_le (TA.image (fun a => s(z2, a))) (TB.image (fun b => s(z1, b)))
            have h4 : (TA.image (fun a => s(z2, a))).card ≤ TA.card := Finset.card_image_le
            have h5 : (TB.image (fun b => s(z1, b))).card ≤ TB.card := Finset.card_image_le
            omega
          have hTA_RwA : TA.card ≤ (Rw wA).card := by
            have hz1NotTA : z1 ∉ TA := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
            have hsub : insert z1 TA ⊆ A := fun x hx => by
              rcases Finset.mem_insert.mp hx with rfl | hxTA
              · exact hz1A
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTA).1
            have hBnd := single_wire_no_pair wA (insert z1 TA) hwALt hnaA hsub
              (no_lam_two_Ustar_nbrs z2 (insert z1 TA) (fun x hx => hValidB_adjA z2 hz2V hz2B x (hsub hx))
                (fun x hx y hy hxy => by
                  rcases Finset.mem_insert.mp hx with rfl | hxTA
                  · rcases Finset.mem_insert.mp hy with rfl | hyTA
                    · exact False.elim (hxy rfl)
                    · exact Or.inr (Finset.mem_filter.mp hyTA).2
                  · exact Or.inl (Finset.mem_filter.mp hxTA).2))
            rw [Finset.card_insert_of_notMem hz1NotTA] at hBnd; omega
          have hTB_RwB : TB.card ≤ (Rw wB).card := by
            have hz2NotTB : z2 ∉ TB := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
            have hsub : insert z2 TB ⊆ B := fun x hx => by
              rcases Finset.mem_insert.mp hx with rfl | hxTB
              · exact hz2B
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTB).1
            have hBnd := single_wire_no_pair wB (insert z2 TB) hwBLt hnaB hsub
              (no_lam_two_Ustar_nbrs z1 (insert z2 TB) (fun x hx => hValidA_adjB z1 hz1V hz1A x (hsub hx))
                (fun x hx y hy hxy => by
                  rcases Finset.mem_insert.mp hx with rfl | hxTB
                  · rcases Finset.mem_insert.mp hy with rfl | hyTB
                    · exact False.elim (hxy rfl)
                    · exact Or.inr (Finset.mem_filter.mp hyTB).2
                  · exact Or.inl (Finset.mem_filter.mp hxTB).2))
            rw [Finset.card_insert_of_notMem hz2NotTB] at hBnd; omega
          have hDisjAB : Disjoint (Rw wA) (Rw wB) := noAnd_disj_Rw hnaA hnaB (by rw [hABempty]; simp only [Finset.card_empty, Nat.zero_le])
          have hDisjA_Ra : Disjoint (Rw wA) Rabove := noAnd_disj_Rabove hnaA
          have hDisjB_Ra : Disjoint (Rw wB) Rabove := noAnd_disj_Rabove hnaB
          have hRsum : (Rw wA).card + (Rw wB).card + Rabove.card ≤ R.card := by
            have hsub : (Rw wA ∪ Rw wB) ∪ Rabove ⊆ R :=
              Finset.union_subset (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R)) (Finset.filter_subset _ R)
            have h1 := Finset.card_le_card hsub
            rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDisjA_Ra, hDisjB_Ra⟩),
              Finset.card_union_of_disjoint hDisjAB] at h1
            exact h1
          have hDeltaLe1 : δ ≤ 1 := by
            dsimp only [δ]
            by_cases h : s(z1, z2) ∈ Ustar G C
            · rw [if_pos h]
            · rw [if_neg h]; omega
          by_cases hTA0 : TA.card = 0
          · have hCov1 : ∀ e ∈ Ustar G C, ∃ v ∈ ({z1} : Finset (Fin nv)), v ∈ e := fun e he => by
              rcases hEdge1 e he with rfl | ⟨a, ha, _⟩ | ⟨_, _, rfl⟩
              · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
              · have := Finset.card_pos.mpr ⟨a, ha⟩; omega
              · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
            have hLt := hBudgetLtCov {z1} hCov1
            rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
            by_cases hZ0 : (centreless G C).card = 0
            · have hRa := hRabove_pos_of_Z0 hZ0; omega
            · omega
          · by_cases hTB0 : TB.card = 0
            · have hCov1 : ∀ e ∈ Ustar G C, ∃ v ∈ ({z2} : Finset (Fin nv)), v ∈ e := fun e he => by
                rcases hEdge1 e he with rfl | ⟨_, _, rfl⟩ | ⟨b, hb, _⟩
                · exact ⟨z2, Finset.mem_singleton_self z2, Sym2.mem_mk_right _ _⟩
                · exact ⟨z2, Finset.mem_singleton_self z2, Sym2.mem_mk_left _ _⟩
                · have := Finset.card_pos.mpr ⟨b, hb⟩; omega
              have hLt := hBudgetLtCov {z2} hCov1
              rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
              by_cases hZ0 : (centreless G C).card = 0
              · have hRa := hRabove_pos_of_Z0 hZ0; omega
              · omega
            · have hCov2 : ∀ e ∈ Ustar G C, ∃ v ∈ ({z1, z2} : Finset (Fin nv)), v ∈ e := fun e he => by
                rcases hEdge1 e he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
                · exact ⟨z2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
                · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
              have hLt := hBudgetLtCov {z1, z2} hCov2
              rw [Finset.card_pair hadj12.ne, hjSet, Finset.card_singleton] at hLt
              by_cases hZ0 : (centreless G C).card = 0
              · obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < TA.card)
                obtain ⟨b1, hb1⟩ := Finset.card_pos.mp (by omega : 0 < TB.card)
                have ha1NotV : a1 ∉ validZ := fun h =>
                  (Finset.mem_erase.mp (Finset.mem_filter.mp ha1).1).1
                    (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨h, Finset.mem_of_mem_erase (Finset.mem_filter.mp ha1).1⟩))
                have hb1NotV : b1 ∉ validZ := fun h =>
                  (Finset.mem_erase.mp (Finset.mem_filter.mp hb1).1).1
                    (Finset.mem_singleton.mp (hz2Set ▸ Finset.mem_inter.mpr ⟨h, Finset.mem_of_mem_erase (Finset.mem_filter.mp hb1).1⟩))
                obtain ⟨_, t2, ht2, d2, ht2d, hSide2, hSubV2⟩ := hUstar_struct (Finset.mem_filter.mp ha1).2
                obtain ⟨_, t1, ht1, d1, ht1d, hSide1, hSubV1⟩ := hUstar_struct (Finset.mem_filter.mp hb1).2
                have hz2Side : z2 ∈ side (n := nv) C t2 (1 - d2) := hSide2.elim id (fun h => False.elim (ha1NotV (hSubV2 h)))
                have hz1Side : z1 ∈ side (n := nv) C t1 (1 - d1) := hSide1.elim id (fun h => False.elim (hb1NotV (hSubV1 h)))
                have hneD2 : (orIn nv C (opnd C t2 d2)).Nonempty := by
                  by_contra hne
                  have ht2Z : t2 ∈ centreless G C := emptySide_mem_centreless ht2 (Finset.not_nonempty_iff_eq_empty.mp hne)
                  have := Finset.card_pos.mpr ⟨t2, ht2Z⟩; omega
                have hneD1 : (orIn nv C (opnd C t1 d1)).Nonempty := by
                  by_contra hne
                  have ht1Z : t1 ∈ centreless G C := emptySide_mem_centreless ht1 (Finset.not_nonempty_iff_eq_empty.mp hne)
                  have := Finset.card_pos.mpr ⟨t1, ht1Z⟩; omega
                obtain ⟨m2, hm2R, ht2m2, hm2j, hm2ne⟩ := noncentreless_witness hjMem ht2d hneD2
                obtain ⟨m1, hm1R, ht1m1, hm1j, _⟩ := noncentreless_witness hjMem ht1d hneD1
                have hmNe : m1 ≠ m2 := by
                  intro heq; subst m1
                  obtain ⟨q, hq⟩ := hm2ne
                  have hq2 : q ∈ side (n := nv) C t2 d2 := by rw [side_def]; exact orIn_mono ht2m2 hq
                  have hq1 : q ∈ side (n := nv) C t1 d1 := by rw [side_def]; exact orIn_mono ht1m1 hq
                  have hadj2q : G.Adj z2 q := (topAdj_side ht2 hq2 hz2Side).symm
                  have hadj1q : G.Adj z1 q := (topAdj_side ht1 hq1 hz1Side).symm
                  exact hNoTri z1 z2 q hadj12 hadj2q hadj1q
                have hRa2 : 2 ≤ Rabove.card := by
                  have hsub : ({m1, m2} : Finset ℕ) ⊆ Rabove := fun m hm => by
                    rcases Finset.mem_insert.mp hm with rfl | hm'
                    · exact Finset.mem_filter.mpr ⟨hm1R, hm1j⟩
                    · rw [Finset.mem_singleton.mp hm']; exact Finset.mem_filter.mpr ⟨hm2R, hm2j⟩
                  have h1 := Finset.card_le_card hsub
                  rw [Finset.card_pair hmNe] at h1; exact h1
                omega
              · omega
        · exact hCase2Sym wA wB hwALt hwBLt hnaA hnaB hjVal hVA (Finset.not_nonempty_iff_eq_empty.mp hVB) hVA_le1
      · by_cases hVB : (validZ ∩ B).Nonempty
        · exact hCase2Sym wB wA hwBLt hwALt hnaB hnaA (fun x => (hjVal x).trans and_comm) hVB (Finset.not_nonempty_iff_eq_empty.mp hVA) hVB_le1
        · have hVAe : validZ ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVA
          have hVBe : validZ ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVB
          have hNotA : ∀ z ∈ validZ, z ∉ A := fun z hz h => by
            have hm : z ∈ validZ ∩ A := Finset.mem_inter.mpr ⟨hz, h⟩
            rw [hVAe] at hm; exact Finset.notMem_empty z hm
          have hNotB : ∀ z ∈ validZ, z ∉ B := fun z hz h => by
            have hm : z ∈ validZ ∩ B := Finset.mem_inter.mpr ⟨hz, h⟩
            rw [hVBe] at hm; exact Finset.notMem_empty z hm
          have hEdge3 : ∀ {u v : Fin nv}, s(u, v) ∈ Ustar G C →
              (u ∈ validZ ∧ v ∈ A ∩ B) ∨ (v ∈ validZ ∧ u ∈ A ∩ B) := by
            intro u v he
            obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
            obtain ⟨⟨a, haA, hpa⟩, ⟨b, hbB, hpb⟩⟩ := (hjVal _).mp hjv
            rcases hSide with huS | hvS
            · have huV := hSubV huS
              have hva : v = a := by rcases (pairInput_true u v a).mp hpa with hau | rfl; exact False.elim (hNotA u huV (hau ▸ haA)); rfl
              have hvb : v = b := by rcases (pairInput_true u v b).mp hpb with hbu | rfl; exact False.elim (hNotB u huV (hbu ▸ hbB)); rfl
              exact Or.inl ⟨huV, Finset.mem_inter.mpr ⟨hva ▸ haA, hvb ▸ hbB⟩⟩
            · have hvV := hSubV hvS
              have hua : u = a := by rcases (pairInput_true u v a).mp hpa with rfl | hav; rfl; exact False.elim (hNotA v hvV (hav ▸ haA))
              have hub : u = b := by rcases (pairInput_true u v b).mp hpb with rfl | hbv; rfl; exact False.elim (hNotB v hvV (hbv ▸ hbB))
              exact Or.inr ⟨hvV, Finset.mem_inter.mpr ⟨hua ▸ haA, hub ▸ hbB⟩⟩
          by_cases hAB0 : (A ∩ B).card = 0
          · obtain ⟨e, he⟩ := hUstarNe
            induction e using Sym2.ind with
            | _ u v =>
              rcases hEdge3 he with ⟨_, hv⟩ | ⟨_, hu⟩
              · have := Finset.card_pos.mpr ⟨v, hv⟩; omega
              · have := Finset.card_pos.mpr ⟨u, hu⟩; omega
          · by_cases hAB1 : (A ∩ B).card = 1
            · obtain ⟨w0, hw0Set⟩ := Finset.card_eq_one.mp hAB1
              have hw0A : w0 ∈ A := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).1
              have hw0NotV : w0 ∉ validZ := fun h => hNotA w0 h hw0A
              have hCov1 : ∀ e ∈ Ustar G C, w0 ∈ e := fun e he => Sym2.ind (fun u v he' => by
                rcases hEdge3 he' with ⟨_, hv⟩ | ⟨_, hu⟩
                · have hvw : v = w0 := Finset.mem_singleton.mp (hw0Set ▸ hv); rw [hvw]; exact Sym2.mem_mk_right _ _
                · have huw : u = w0 := Finset.mem_singleton.mp (hw0Set ▸ hu); rw [huw]; exact Sym2.mem_mk_left _ _) e he
              have hLt := hBudgetLtCov {w0} (fun e he => ⟨w0, Finset.mem_singleton_self w0, hCov1 e he⟩)
              rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
              let TW := validZ.filter (fun z => s(w0, z) ∈ Ustar G C)
              have hTWcard : (Ustar G C).card ≤ TW.card := by
                have hsub : Ustar G C ⊆ TW.image (fun z => s(w0, z)) := fun e he => Sym2.ind (fun u v he' => by
                  rcases hEdge3 he' with ⟨huV, hv⟩ | ⟨hvV, hu⟩
                  · have hvw : v = w0 := Finset.mem_singleton.mp (hw0Set ▸ hv); subst v
                    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huV, Sym2.eq_swap ▸ he'⟩, Sym2.eq_swap⟩
                  · have huw : u = w0 := Finset.mem_singleton.mp (hw0Set ▸ hu); subst u
                    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvV, he'⟩, rfl⟩) e he
                exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
              let TWZ := TW.filter (fun z => z ∈ covZ)
              let TWN := TW.filter (fun z => z ∉ covZ)
              have hSplit : TW.card = TWZ.card + TWN.card := by
                have hDisjZ : Disjoint TWZ TWN := Finset.disjoint_left.mpr (fun z h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2)
                have hUnZ : TWZ ∪ TWN = TW := by
                  apply Finset.ext; intro z; simp only [TWZ, TWN, Finset.mem_union, Finset.mem_filter]
                  exact ⟨fun h => h.elim And.left And.left, fun h => (em (z ∈ covZ)).elim (fun hc => Or.inl ⟨h, hc⟩) (fun hc => Or.inr ⟨h, hc⟩)⟩
                rw [← hUnZ, Finset.card_union_of_disjoint hDisjZ]
              obtain ⟨RZ, hRZsub, hRZspec, hTWZ_bnd⟩ := hCovZ_bound w0 TWZ (fun z hz => by
                obtain ⟨hzTW, hzCov⟩ := Finset.mem_filter.mp hz
                have hu := (Finset.mem_filter.mp hzTW).2
                exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu)).1, hu, hzCov⟩)
              obtain ⟨fN, hfNspec, hfNinj⟩ := hStar_Rabove_bound w0 TWN (fun z hz => by
                obtain ⟨hzTW, hzNotCov⟩ := Finset.mem_filter.mp hz
                exact ⟨(Finset.mem_filter.mp hzTW).2, hzNotCov, hw0NotV⟩)
              have hTWN_bnd : TWN.card ≤ Rabove.card := by
                have hsub : TWN.image fN ⊆ Rabove := fun m hm => by
                  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1
                rw [← Finset.card_image_of_injOn hfNinj]
                exact Finset.card_le_card hsub
              have hDisj := (hRZ_disj_all RZ hRZspec).1
              have hRsum : RZ.card + Rabove.card ≤ R.card := by
                have hsub : RZ ∪ Rabove ⊆ R := Finset.union_subset hRZsub (Finset.filter_subset _ R)
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_union_of_disjoint hDisj] at h1; exact h1
              omega
            · have hABge2 : 1 < (A ∩ B).card := by omega
              obtain ⟨w1, hw1, w2, hw2, hwne⟩ := Finset.one_lt_card.mp hABge2
              have hValidLe1 : validZ.card ≤ 1 := Finset.card_le_one.mpr (fun z1 hz1 z2 hz2 => by
                by_contra hne
                have hc4 := hNo4 z1 z2 hne
                have hm1 : w1 ∈ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z2 p) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValid_adjAB z1 hz1 w1 hw1, hValid_adjAB z2 hz2 w1 hw1⟩
                have hm2 : w2 ∈ Finset.univ.filter (fun p => G.Adj z1 p ∧ G.Adj z2 p) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValid_adjAB z1 hz1 w2 hw2, hValid_adjAB z2 hz2 w2 hw2⟩
                exact hwne (Finset.card_le_one.mp hc4 w1 hm1 w2 hm2))
              have hValidPos : validZ.Nonempty := by
                obtain ⟨e, he⟩ := hUstarNe
                induction e using Sym2.ind with
                | _ u v =>
                  rcases hEdge3 he with ⟨huV, _⟩ | ⟨hvV, _⟩
                  · exact ⟨u, huV⟩
                  · exact ⟨v, hvV⟩
              have hV1 : validZ.card = 1 := by have := Finset.card_pos.mpr hValidPos; omega
              obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hV1
              exact hSingletonStarContra z1 wA hwALt hnaA
                (fun e he => Sym2.ind (fun u v he' => by
                  rcases hEdge3 he' with ⟨huV, _⟩ | ⟨hvV, _⟩
                  · have huz : u = z1 := Finset.mem_singleton.mp (hz1Set ▸ huV); rw [huz]; exact Sym2.mem_mk_left _ _
                  · have hvz : v = z1 := Finset.mem_singleton.mp (hz1Set ▸ hvV); rw [hvz]; exact Sym2.mem_mk_right _ _) e he)
                (fun u hu => by
                  rcases hEdge3 hu with ⟨_, huAB⟩ | ⟨huV, hz1AB⟩
                  · exact (Finset.mem_inter.mp huAB).1
                  · have hz1V : z1 ∈ validZ := hz1Set ▸ Finset.mem_singleton_self z1
                    exact False.elim (hNotA z1 hz1V (Finset.mem_inter.mp hz1AB).1))
    have hZorR : 1 ≤ (centreless G C).card ∨ 1 ≤ (orN G C \ lam G C).card := by
      obtain ⟨e, he⟩ := hUstarNe
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨t, ht, _, d, j, hj, htd, _⟩ := residualTrace he
        by_cases htZ : t ∈ centreless G C
        · exact Or.inl (Finset.card_pos.mpr ⟨t, htZ⟩)
        · have hneD : (orIn nv C (opnd C t d)).Nonempty := by
            by_contra hne
            exact htZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
          obtain ⟨m, hmR, _, _, _⟩ := noncentreless_witness hj htd hneD
          exact Or.inr (Finset.card_pos.mpr ⟨m, hmR⟩)
    have hBool_eq_of_ne : ∀ a b c : Bool, a ≠ b → b ≠ c → a = c := by
      intro a b c hab hbc
      cases a <;> cases b <;> cases c <;>
        first | rfl | exact False.elim (hab rfl) | exact False.elim (hbc rfl)
    let LamOrSing : Finset (Fin nv) → Prop := fun S =>
      (∃ v : Fin nv, S = {v}) ∨ (∃ k ∈ lam G C, S = orIn nv C (nv + k))
    let setsEval : Finset (Finset (Fin nv)) → (Fin nv → Bool) → Prop := fun Fs x =>
      ∀ S ∈ Fs, ∃ w ∈ S, x w = true
    have hLamOrSing_mono : ∀ S : Finset (Fin nv), LamOrSing S →
        ∀ u ∈ S, ∀ v ∈ S, col u = col v := by
      intro S hS u hu v hv
      rcases hS with ⟨w, rfl⟩ | ⟨k, hkLam, rfl⟩
      · rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
      · obtain ⟨_, _, _, t, ht, d, hcard, htk⟩ := (lam_mem C k).mp hkLam
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
        have hcSide : c ∈ side (n := nv) C t (1 - d) := by rw [hc]; exact Finset.mem_singleton_self c
        have huSide : u ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htk hu
        have hvSide : v ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htk hv
        have hcu := hCol c u (topAdj_side ht huSide hcSide).symm
        have hcv := hCol c v (topAdj_side ht hvSide hcSide).symm
        exact hBool_eq_of_ne (col u) (col c) (col v) hcu.symm hcv
    have hLamOrSing_star : ∀ S : Finset (Fin nv), LamOrSing S →
        ∀ c u1 u2 : Fin nv, u1 ∈ S → u2 ∈ S → u1 ≠ u2 →
        G.Adj c u1 → G.Adj c u2 → s(c, u1) ∈ starEdges G C := by
      intro S hS c u1 u2 hu1 hu2 hne hc1 hc2
      rcases hS with ⟨w, rfl⟩ | ⟨k, hkLam, rfl⟩
      · exact False.elim (hne ((Finset.mem_singleton.mp hu1).trans (Finset.mem_singleton.mp hu2).symm))
      · obtain ⟨_, _, _, t, ht, d, hcard, htk⟩ := (lam_mem C k).mp hkLam
        obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard
        have hc'Side : c' ∈ side (n := nv) C t (1 - d) := by rw [hc']; exact Finset.mem_singleton_self c'
        have hu1Side : u1 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htk hu1
        have hu2Side : u2 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htk hu2
        have hcc' : c = c' := by
          by_contra hcc
          have hc4 := hNo4 c c' hcc
          have hm1 : u1 ∈ Finset.univ.filter (fun p => G.Adj c p ∧ G.Adj c' p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1, (topAdj_side ht hu1Side hc'Side).symm⟩
          have hm2 : u2 ∈ Finset.univ.filter (fun p => G.Adj c p ∧ G.Adj c' p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc2, (topAdj_side ht hu2Side hc'Side).symm⟩
          exact hne (Finset.card_le_one.mp hc4 u1 hm1 u2 hm2)
        rw [hcc']
        exact Sym2.eq_swap ▸ side_mem_starEdges ht hu1Side hc'Side
    have hMono_atV_uniq : ∀ (Fs : Finset (Finset (Fin nv))),
        (∀ S ∈ Fs, LamOrSing S) →
        ∀ (v : Fin nv),
        (∀ x : Fin nv → Bool, x v = true → setsEval Fs x → graphFun G ∅ x = true) →
        ∀ u1 u2 : Fin nv, s(u1, v) ∈ Ustar G C → s(u2, v) ∈ Ustar G C →
          setsEval Fs (pairInput u1 v) → setsEval Fs (pairInput u2 v) → u1 = u2 := by
      intro Fs hFsL v hSound u1 u2 hu1U hu2U h1 h2
      by_contra hne
      have hnv : ¬ setsEval Fs (pairInput v v) := fun hfs =>
        G.loopless.irrefl v ((graphFun_pair v v).mp (hSound (pairInput v v) (pairInput_left v v) hfs))
      obtain ⟨S0, hS0, hS0miss⟩ : ∃ S0 ∈ Fs, v ∉ S0 := by
        by_contra hno
        apply hnv
        intro S hS
        by_contra hnone
        exact hno ⟨S, hS, fun hvS => hnone ⟨v, hvS, pairInput_left v v⟩⟩
      have hu1S : u1 ∈ S0 := by
        obtain ⟨w, hwS, hwp⟩ := h1 S0 hS0
        rcases (pairInput_true u1 v w).mp hwp with hw | hw
        · rw [hw] at hwS; exact hwS
        · rw [hw] at hwS; exact False.elim (hS0miss hwS)
      have hu2S : u2 ∈ S0 := by
        obtain ⟨w, hwS, hwp⟩ := h2 S0 hS0
        rcases (pairInput_true u2 v w).mp hwp with hw | hw
        · rw [hw] at hwS; exact hwS
        · rw [hw] at hwS; exact False.elim (hS0miss hwS)
      have hadj1' : G.Adj u1 v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu1U)).1
      have hadj2' : G.Adj u2 v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu2U)).1
      have hstar := hLamOrSing_star S0 (hFsL S0 hS0) v u1 u2 hu1S hu2S hne hadj1'.symm hadj2'.symm
      rw [Ustar_def] at hu1U
      exact (Finset.mem_sdiff.mp hu1U).2 (Sym2.eq_swap ▸ hstar)
    have hMono_cross : ∀ (Fs : Finset (Finset (Fin nv))),
        (∀ S ∈ Fs, LamOrSing S) →
        ∀ u1 v1 u2 v2 : Fin nv,
        col u1 = col u2 → col v1 = col v2 → col u1 ≠ col v1 →
        setsEval Fs (pairInput u1 v1) → setsEval Fs (pairInput u2 v2) →
        setsEval Fs (pairInput u1 v2) := by
      intro Fs hFsL u1 v1 u2 v2 hcu hcv hcuv h1 h2 S hS
      obtain ⟨w1, hw1S, hw1p⟩ := h1 S hS
      obtain ⟨w2, hw2S, hw2p⟩ := h2 S hS
      rcases (pairInput_true u1 v1 w1).mp hw1p with hw1 | hw1
      · rw [hw1] at hw1S; exact ⟨u1, hw1S, pairInput_left u1 v2⟩
      · rw [hw1] at hw1S
        rcases (pairInput_true u2 v2 w2).mp hw2p with hw2 | hw2
        · rw [hw2] at hw2S
          have hcolEq := hLamOrSing_mono S (hFsL S hS) v1 hw1S u2 hw2S
          exact False.elim (hcuv (hcu.trans hcolEq.symm))
        · rw [hw2] at hw2S; exact ⟨v2, hw2S, pairInput_right u1 v2⟩
    have hMono_global_uniq : ∀ (Fs : Finset (Finset (Fin nv))),
        (∀ S ∈ Fs, LamOrSing S) →
        (∀ x : Fin nv → Bool, setsEval Fs x → graphFun G ∅ x = true) →
        ∀ u1 v1 u2 v2 : Fin nv, s(u1, v1) ∈ Ustar G C → s(u2, v2) ∈ Ustar G C →
          setsEval Fs (pairInput u1 v1) → setsEval Fs (pairInput u2 v2) →
          s(u1, v1) = s(u2, v2) := by
      intro Fs hFsL hSound u1 v1 u2 v2 he1 he2 h1 h2
      have hadj1 : G.Adj u1 v1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he1)).1
      have hadj2 : G.Adj u2 v2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he2)).1
      have hc1 := hCol u1 v1 hadj1
      have hc2 := hCol u2 v2 hadj2
      have hSameOrient : ∀ a1 b1 a2 b2 : Fin nv,
          s(a1, b1) ∈ Ustar G C → s(a2, b2) ∈ Ustar G C →
          col a1 = col a2 → col b1 = col b2 → col a1 ≠ col b1 →
          setsEval Fs (pairInput a1 b1) → setsEval Fs (pairInput a2 b2) →
          s(a1, b1) = s(a2, b2) := by
        intro a1 b1 a2 b2 ha1b1 ha2b2 hca hcb hcab hf1 hf2
        have h12 : G.Adj a1 b2 := (graphFun_pair a1 b2).mp (hSound _ (hMono_cross Fs hFsL a1 b1 a2 b2 hca hcb hcab hf1 hf2))
        have h21 : G.Adj a2 b1 := (graphFun_pair a2 b1).mp (hSound _ (hMono_cross Fs hFsL a2 b2 a1 b1 hca.symm hcb.symm (hca ▸ hcb ▸ hcab) hf2 hf1))
        have ha12 : G.Adj a1 b1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ ha1b1)).1
        have ha22 : G.Adj a2 b2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ ha2b2)).1
        by_cases haeq : a1 = a2
        · subst a2
          have hbeq : b1 = b2 := hMono_atV_uniq Fs hFsL a1 (fun x _ hx => hSound x hx) b1 b2
            (Sym2.eq_swap ▸ ha1b1) (Sym2.eq_swap ▸ ha2b2) (pairInput_symm a1 b1 ▸ hf1) (pairInput_symm a1 b2 ▸ hf2)
          rw [hbeq]
        · have hc4 := hNo4 a1 a2 haeq
          have hm1 : b1 ∈ Finset.univ.filter (fun p => G.Adj a1 p ∧ G.Adj a2 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha12, h21⟩
          have hm2 : b2 ∈ Finset.univ.filter (fun p => G.Adj a1 p ∧ G.Adj a2 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12, ha22⟩
          have hbeq : b1 = b2 := Finset.card_le_one.mp hc4 b1 hm1 b2 hm2
          subst b2
          have haeq' : a1 = a2 := hMono_atV_uniq Fs hFsL b1 (fun x _ hx => hSound x hx) a1 a2 ha1b1 ha2b2 hf1 hf2
          exact False.elim (haeq haeq')
      by_cases hcu : col u1 = col u2
      · have hcv : col v1 = col v2 := hBool_eq_of_ne (col v1) (col u1) (col v2) hc1.symm (hcu ▸ hc2)
        exact hSameOrient u1 v1 u2 v2 he1 he2 hcu hcv hc1 h1 h2
      · have hcu' : col u1 = col v2 := hBool_eq_of_ne (col u1) (col u2) (col v2) hcu hc2
        have hcv' : col v1 = col u2 := hBool_eq_of_ne (col v1) (col u1) (col u2) hc1.symm hcu
        exact (hSameOrient u1 v1 v2 u2 he1 (Sym2.eq_swap ▸ he2) hcu' hcv' hc1 h1 (pairInput_symm u2 v2 ▸ h2)).trans Sym2.eq_swap
    have hMono_underZ_uniq : ∀ (Fs : Finset (Finset (Fin nv))),
        (∀ S ∈ Fs, LamOrSing S) →
        ∀ (z0 : Fin nv) (u1 v1 u2 v2 : Fin nv),
        s(u1, v1) ∈ Ustar G C → s(u2, v2) ∈ Ustar G C →
        G.Adj z0 v1 → G.Adj z0 v2 → u1 ≠ z0 →
        setsEval Fs (pairInput u1 v1) → setsEval Fs (pairInput u2 v2) →
        (∀ x : Fin nv → Bool, x v2 = true → setsEval Fs x → graphFun G ∅ x = true) →
        s(u1, v1) = s(u2, v2) := by
      intro Fs hFsL z0 u1 v1 u2 v2 he1 he2 hzv1 hzv2 hu1ne h1 h2 hSound2
      have hadj1 : G.Adj u1 v1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he1)).1
      have hadj2 : G.Adj u2 v2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he2)).1
      have hcv : col v1 = col v2 := hBool_eq_of_ne (col v1) (col z0) (col v2) (hCol z0 v1 hzv1).symm (hCol z0 v2 hzv2)
      have hcu : col u1 = col u2 := hBool_eq_of_ne (col u1) (col v1) (col u2) (hCol u1 v1 hadj1) (hcv ▸ (hCol u2 v2 hadj2).symm)
      have h12 : G.Adj u1 v2 :=
        (graphFun_pair u1 v2).mp (hSound2 (pairInput u1 v2) (pairInput_right u1 v2)
          (hMono_cross Fs hFsL u1 v1 u2 v2 hcu hcv (hCol u1 v1 hadj1) h1 h2))
      have hvEq : v1 = v2 := by
        have hc4 := hNo4 u1 z0 hu1ne
        have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1, hzv1⟩
        have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12, hzv2⟩
        exact Finset.card_le_one.mp hc4 v1 hm1 v2 hm2
      subst v2
      have huEq : u1 = u2 := hMono_atV_uniq Fs hFsL v1 hSound2 u1 u2 he1 he2 h1 h2
      rw [huEq]
    have hPairJunk_uniq : ∀ (j : ℕ) (A B : Finset (Fin nv)),
        j ∈ junk G C → LamOrSing A → LamOrSing B →
        (∀ x : Fin nv → Bool, gateVal nv C j x = true ↔ (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true)) →
        ∀ u1 v1 : Fin nv, s(u1, v1) ∈ Ustar G C →
          gateVal nv C j (pairInput u1 v1) = true →
          (∀ x : Fin nv → Bool, x v1 = true → gateVal nv C j x = true → graphFun G ∅ x = true) →
          ∀ u2 v2 : Fin nv, s(u2, v2) ∈ Ustar G C →
            gateVal nv C j (pairInput u2 v2) = true → s(u1, v1) = s(u2, v2) := by
      intro j A B hj hAL hBL hjVal u1 v1 he1 hj1 hSound1 u2 v2 he2 hj2
      obtain ⟨hjlen, _, _⟩ := junkData hj
      have hadj1 : G.Adj u1 v1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he1)).1
      have hadj2 : G.Adj u2 v2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he2)).1
      obtain ⟨⟨a0, ha0A, ha0p⟩, ⟨b0, hb0B, hb0p⟩⟩ := (hjVal _).mp hj1
      have hColorCase : ∀ (P1 P2 : Finset (Fin nv)), LamOrSing P1 → LamOrSing P2 →
          (∀ x : Fin nv → Bool, gateVal nv C j x = true ↔ (∃ a ∈ P1, x a = true) ∧ (∃ b ∈ P2, x b = true)) →
          u1 ∈ P1 → u1 ∈ P2 → False := by
        intro P1 P2 hP1L hP2L hValP hu1P1 hu1P2
        let xI : Fin nv → Bool := fun w => decide (w = v1 ∨ (col w ≠ col v1 ∧ ¬ G.Adj v1 w))
        have hxI_false : graphFun G ∅ xI = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          obtain ⟨a, b, hab, hxa, hxb⟩ := (hG_hasEdge xI).mp ht
          have ha := decide_eq_true_eq.mp hxa
          have hb := decide_eq_true_eq.mp hxb
          rcases ha with rfl | ⟨hac, hna⟩
          · rcases hb with rfl | ⟨_, hnb⟩
            · exact G.loopless.irrefl _ hab
            · exact hnb hab
          · rcases hb with rfl | ⟨hbc, _⟩
            · exact hna hab.symm
            · exact hCol a b hab (hBool_eq_of_ne (col a) (col v1) (col b) hac hbc.symm)
        have hNotJ : gateVal nv C j xI = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          have h1 := hSound1 xI (decide_eq_true (Or.inl rfl)) ht
          rw [hxI_false] at h1; exact Bool.noConfusion h1
        have hMiss : (∀ w ∈ P1, xI w = false) ∨ (∀ w ∈ P2, xI w = false) := by
          by_contra hno
          have h1 : ∃ w ∈ P1, xI w = true := by
            by_contra h1'; apply hno; left; intro w hw
            exact Bool.eq_false_iff.mpr (fun ht => h1' ⟨w, hw, ht⟩)
          have h2 : ∃ w ∈ P2, xI w = true := by
            by_contra h2'; apply hno; right; intro w hw
            exact Bool.eq_false_iff.mpr (fun ht => h2' ⟨w, hw, ht⟩)
          have ht := (hValP xI).mpr ⟨h1, h2⟩
          rw [hNotJ] at ht; exact Bool.noConfusion ht
        have hSubContra : ∀ (Q Rq : Finset (Fin nv)), LamOrSing Q →
            (∀ x : Fin nv → Bool, gateVal nv C j x = true ↔ (∃ a ∈ Q, x a = true) ∧ (∃ b ∈ Rq, x b = true)) →
            u1 ∈ Q → u1 ∈ Rq → (∀ w ∈ Q, xI w = false) → False := by
          intro Q Rq hQL hVQR huQ huRq hQmiss
          have hQsing : Q = {u1} := by
            apply Finset.ext; intro w
            rw [Finset.mem_singleton]
            constructor
            · intro hwQ
              by_contra hne
              have hwcol : col w = col u1 := hLamOrSing_mono Q hQL w hwQ u1 huQ
              have hwne : col w ≠ col v1 := hwcol ▸ hCol u1 v1 hadj1
              have hwadj : G.Adj v1 w := by
                by_contra hna
                have hxt : xI w = true := decide_eq_true (Or.inr ⟨hwne, hna⟩)
                exact Bool.noConfusion ((hQmiss w hwQ).symm.trans hxt)
              have hst := hLamOrSing_star Q hQL v1 u1 w huQ hwQ (Ne.symm hne) hadj1.symm hwadj
              rw [Ustar_def] at he1
              exact (Finset.mem_sdiff.mp he1).2 (Sym2.eq_swap ▸ hst)
            · intro h; rw [h]; exact huQ
          apply replace_gate_by_wire j u1.val hjlen (by have := u1.isLt; omega)
          intro x
          rw [val_ofFn C x u1]
          apply Bool.eq_iff_iff.mpr
          rw [hVQR x, hQsing]
          constructor
          · intro hxu; exact ⟨⟨u1, Finset.mem_singleton_self u1, hxu⟩, ⟨u1, huRq, hxu⟩⟩
          · rintro ⟨⟨a, ha, hxa⟩, _⟩; rw [Finset.mem_singleton.mp ha] at hxa; exact hxa
        rcases hMiss with h1 | h2
        · exact hSubContra P1 P2 hP1L hValP hu1P1 hu1P2 h1
        · exact hSubContra P2 P1 hP2L (fun x => (hValP x).trans and_comm) hu1P2 hu1P1 h2
      rcases (pairInput_true u1 v1 a0).mp ha0p with ha0Eq | ha0Eq
      · rw [ha0Eq] at ha0A
        rcases (pairInput_true u1 v1 b0).mp hb0p with hb0Eq | hb0Eq
        · rw [hb0Eq] at hb0B; exact False.elim (hColorCase A B hAL hBL hjVal ha0A hb0B)
        · rw [hb0Eq] at hb0B
          have hOpp : ∀ a2 b2 : Fin nv, s(a2, b2) ∈ Ustar G C →
              col a2 = col u1 → col b2 = col v1 → gateVal nv C j (pairInput a2 b2) = true →
              s(u1, v1) = s(a2, b2) := by
            intro a2 b2 ha2b2 hca hcb hj2'
            obtain ⟨⟨a', ha'A, ha'p⟩, ⟨b', hb'B, hb'p⟩⟩ := (hjVal _).mp hj2'
            have ha2A : a2 ∈ A := by
              rcases (pairInput_true a2 b2 a').mp ha'p with ha' | ha'
              · rw [ha'] at ha'A; exact ha'A
              · rw [ha'] at ha'A; exact False.elim ((hCol u1 v1 hadj1) ((hLamOrSing_mono A hAL u1 ha0A b2 ha'A).trans hcb))
            have hb2B : b2 ∈ B := by
              rcases (pairInput_true a2 b2 b').mp hb'p with hb' | hb'
              · rw [hb'] at hb'B; exact False.elim ((hCol u1 v1 hadj1) (hca.symm.trans (hLamOrSing_mono B hBL a2 hb'B v1 hb0B)))
              · rw [hb'] at hb'B; exact hb'B
            have ha2v1 : G.Adj a2 v1 :=
              (graphFun_pair a2 v1).mp (hSound1 (pairInput a2 v1) (pairInput_right a2 v1)
                ((hjVal _).mpr ⟨⟨a2, ha2A, pairInput_left a2 v1⟩, ⟨v1, hb0B, pairInput_right a2 v1⟩⟩))
            have haeq : a2 = u1 := by
              by_contra hne
              have hst := hLamOrSing_star A hAL v1 u1 a2 ha0A ha2A (Ne.symm hne) hadj1.symm ha2v1.symm
              rw [Ustar_def] at he1; exact (Finset.mem_sdiff.mp he1).2 (Sym2.eq_swap ▸ hst)
            subst a2
            have hadj2' : G.Adj u1 b2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ ha2b2)).1
            have hbeq : b2 = v1 := by
              by_contra hne
              have hst := hLamOrSing_star B hBL u1 v1 b2 hb0B hb2B (Ne.symm hne) hadj1 hadj2'
              rw [Ustar_def] at he1; exact (Finset.mem_sdiff.mp he1).2 hst
            rw [hbeq]
          by_cases hcu : col u2 = col u1
          · have hcv : col v2 = col v1 := hBool_eq_of_ne (col v2) (col u2) (col v1) (hCol u2 v2 hadj2).symm (hcu ▸ hCol u1 v1 hadj1)
            exact hOpp u2 v2 he2 hcu hcv hj2
          · have hcu' : col v2 = col u1 := hBool_eq_of_ne (col v2) (col u2) (col u1) (hCol u2 v2 hadj2).symm hcu
            have hcv' : col u2 = col v1 := hBool_eq_of_ne (col u2) (col u1) (col v1) hcu (hCol u1 v1 hadj1)
            exact (hOpp v2 u2 (Sym2.eq_swap ▸ he2) hcu' hcv' (pairInput_symm u2 v2 ▸ hj2)).trans Sym2.eq_swap
      · rw [ha0Eq] at ha0A
        rcases (pairInput_true u1 v1 b0).mp hb0p with hb0Eq | hb0Eq
        · rw [hb0Eq] at hb0B
          have hOpp : ∀ a2 b2 : Fin nv, s(a2, b2) ∈ Ustar G C →
              col a2 = col u1 → col b2 = col v1 → gateVal nv C j (pairInput a2 b2) = true →
              s(u1, v1) = s(a2, b2) := by
            intro a2 b2 ha2b2 hca hcb hj2'
            obtain ⟨⟨a', ha'A, ha'p⟩, ⟨b', hb'B, hb'p⟩⟩ := (hjVal _).mp hj2'
            have hb2A : b2 ∈ A := by
              rcases (pairInput_true a2 b2 a').mp ha'p with ha' | ha'
              · rw [ha'] at ha'A; exact False.elim ((hCol u1 v1 hadj1) (hca.symm.trans (hLamOrSing_mono A hAL a2 ha'A v1 ha0A)))
              · rw [ha'] at ha'A; exact ha'A
            have ha2B : a2 ∈ B := by
              rcases (pairInput_true a2 b2 b').mp hb'p with hb' | hb'
              · rw [hb'] at hb'B; exact hb'B
              · rw [hb'] at hb'B; exact False.elim ((hCol u1 v1 hadj1) ((hLamOrSing_mono B hBL u1 hb0B b2 hb'B).trans hcb))
            have ha2v1 : G.Adj a2 v1 :=
              (graphFun_pair a2 v1).mp (hSound1 (pairInput a2 v1) (pairInput_right a2 v1)
                ((hjVal _).mpr ⟨⟨v1, ha0A, pairInput_right a2 v1⟩, ⟨a2, ha2B, pairInput_left a2 v1⟩⟩))
            have haeq : a2 = u1 := by
              by_contra hne
              have hst := hLamOrSing_star B hBL v1 u1 a2 hb0B ha2B (Ne.symm hne) hadj1.symm ha2v1.symm
              rw [Ustar_def] at he1; exact (Finset.mem_sdiff.mp he1).2 (Sym2.eq_swap ▸ hst)
            subst a2
            have hadj2' : G.Adj u1 b2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ ha2b2)).1
            have hbeq : b2 = v1 := by
              by_contra hne
              have hst := hLamOrSing_star A hAL u1 v1 b2 ha0A hb2A (Ne.symm hne) hadj1 hadj2'
              rw [Ustar_def] at he1; exact (Finset.mem_sdiff.mp he1).2 hst
            rw [hbeq]
          by_cases hcu : col u2 = col u1
          · have hcv : col v2 = col v1 := hBool_eq_of_ne (col v2) (col u2) (col v1) (hCol u2 v2 hadj2).symm (hcu ▸ hCol u1 v1 hadj1)
            exact hOpp u2 v2 he2 hcu hcv hj2
          · have hcu' : col v2 = col u1 := hBool_eq_of_ne (col v2) (col u2) (col u1) (hCol u2 v2 hadj2).symm hcu
            have hcv' : col u2 = col v1 := hBool_eq_of_ne (col u2) (col u1) (col v1) hcu (hCol u1 v1 hadj1)
            exact (hOpp v2 u2 (Sym2.eq_swap ▸ he2) hcu' hcv' (pairInput_symm u2 v2 ▸ hj2)).trans Sym2.eq_swap
        · rw [hb0Eq] at hb0B
          have hjv : gateVal nv C j (pairInput v1 v1) = true :=
            (hjVal _).mpr ⟨⟨v1, ha0A, pairInput_left v1 v1⟩, ⟨v1, hb0B, pairInput_left v1 v1⟩⟩
          exact False.elim (G.loopless.irrefl v1 ((graphFun_pair v1 v1).mp (hSound1 _ (pairInput_left v1 v1) hjv)))
    have hNoLamBelow : ∀ (bound : ℕ), (∀ r ∈ orN G C \ lam G C, bound ≤ r) →
        ∀ k : ℕ, k < bound → k ∈ orN G C → ∀ j' ∈ junk G C, ¬ OrReaches nv C (nv + k) j' := by
      intro bound hBnd k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hkb hkN j' hj' hkj
        have hkLam : k ∈ lam G C := by
          by_contra hnl
          have := hBnd k (Finset.mem_sdiff.mpr ⟨hkN, hnl⟩)
          omega
        obtain ⟨_, hne0, hne1, _⟩ := (lam_mem C k).mp hkLam
        obtain ⟨hklen, hkop, _⟩ := (orN_mem C k).mp hkN
        obtain ⟨_, hj'op, _⟩ := junkData hj'
        have hkj'Ne : k ≠ j' := fun h => by rw [h, hj'op] at hkop; exact GateOp.noConfusion hkop
        rcases ((orReaches_iff k j').mp hkj).2 with hEq | ⟨_, w, hwin, hwlt, hwj⟩
        · exact hkj'Ne hEq.symm
        · obtain ⟨b, rfl⟩ := inputsAsOpnd hklen hwin
          have hneb : (orIn nv C (opnd C k b)).Nonempty := by rcases fin2_or b with rfl | rfl; exact hne0; exact hne1
          have hgeN : nv ≤ opnd C k b := (orReaches_def C _ _ ▸ hwj).1
          let k' := opnd C k b - nv
          have hweq : opnd C k b = nv + k' := by omega
          have hk'lt : k' < k := by omega
          rw [hweq] at hwj hneb
          have hk'len : k' < C.gates.length := by omega
          have hk'op : (gateAt C k').op = GateOp.or := by
            rcases hLeast.1.1 _ (gateAt_mem hk'len) with hand | hor
            · rw [andRawEmpty hand] at hneb; exact False.elim (Finset.not_nonempty_empty hneb)
            · exact hor
          have hk'nb : ¬ BelowF G C k' := by
            intro hkb'
            apply junkNotBelow hj'
            intro x hx
            exact hkb' x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k') hwj).1 (gateVal_eq_val C j' x ▸ hx))
          exact ih k' hk'lt (by omega) ((orN_mem C k').mpr ⟨hk'len, hk'op, hk'nb⟩) j' hj' hwj
    have hBelow_noJunk_of_nonempty : ∀ (bound : ℕ), bound ≤ C.gates.length → (∀ r ∈ orN G C \ lam G C, bound ≤ r) →
        ∀ w : ℕ, w < nv + bound → (orIn nv C w).Nonempty →
        ∀ j' ∈ junk G C, ¬ OrReaches nv C w j' := by
      intro bound hBndLen hBnd w hw hne j' hj' hwj
      have hgeN : nv ≤ w := (orReaches_def C w j' ▸ hwj).1
      let k := w - nv
      have hweq : w = nv + k := by omega
      have hklt : k < bound := by omega
      have hklen : k < C.gates.length := by omega
      rw [hweq] at hwj hne
      have hkop : (gateAt C k).op = GateOp.or := by
        rcases hLeast.1.1 _ (gateAt_mem hklen) with hand | hor
        · rw [andRawEmpty hand] at hne; exact False.elim (Finset.not_nonempty_empty hne)
        · exact hor
      have hknb : ¬ BelowF G C k := by
        intro hkb'
        apply junkNotBelow hj'
        intro x hx
        exact hkb' x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k) hwj).1 (gateVal_eq_val C j' x ▸ hx))
      exact hNoLamBelow bound hBnd k hklt ((orN_mem C k).mpr ⟨hklen, hkop, hknb⟩) j' hj' hwj
    have hWireVal_below : ∀ (bound : ℕ), (∀ r ∈ orN G C \ lam G C, bound ≤ r) →
        ∀ (a : ℕ) (b : Fin 2), a ≤ bound → a < C.gates.length → (gateAt C a).op = GateOp.and →
        (∃ S : Finset (Fin nv), LamOrSing S ∧
          ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C a b) = true ↔ ∃ v ∈ S, x v = true) ∨
        (∃ j' ∈ junk G C, j' < a ∧ opnd C a b = nv + j') := by
      intro bound hBnd a b hab ha haop
      let w := opnd C a b
      have hwlt : w < nv + a := opndBound ha b
      by_cases hwn : w < nv
      · left
        refine ⟨{⟨w, hwn⟩}, Or.inl ⟨⟨w, hwn⟩, rfl⟩, fun x => ?_⟩
        change val C (List.ofFn x) w = true ↔ _
        have hval : val C (List.ofFn x) w = x ⟨w, hwn⟩ := val_ofFn C x ⟨w, hwn⟩
        rw [hval]
        constructor
        · intro h; exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _, h⟩
        · rintro ⟨v, hv, hxv⟩; rw [Finset.mem_singleton.mp hv] at hxv; exact hxv
      · let k := w - nv
        have hweq : w = nv + k := by omega
        have hka : k < a := by omega
        have hklen : k < C.gates.length := by omega
        have hknb : ¬ BelowF G C k := fun hkb =>
          not_belowF_inCone_and hklen hkb ha haop ((inCone_iff k a).mpr ⟨ha, k, hka, hweq ▸ opndMem ha b, Or.inl rfl⟩)
        rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
        · right
          have hdirty : ∃ x : Fin nv → Bool, gateVal nv C k x = true ∧ graphFun G ∅ x = false := by
            by_contra hnone; apply hknb; intro x hx; by_contra hf; exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
          exact ⟨k, (junk_mem C k).mpr ⟨hklen, hkand, hdirty⟩, hka, hweq⟩
        · left
          have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
          have hkLam : k ∈ lam G C := by
            by_contra hnl; have := hBnd k (Finset.mem_sdiff.mpr ⟨hkN, hnl⟩); omega
          refine ⟨orIn nv C (nv + k), Or.inr ⟨k, hkLam, rfl⟩, fun x => ?_⟩
          change val C (List.ofFn x) w = true ↔ _
          rw [hweq]
          constructor
          · intro hv
            obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (nv + k) hv
            rcases hcase with hlt | ⟨h, hh, rfl, hneOr⟩
            · refine ⟨⟨w', hlt⟩, reach_mem_orIn ⟨w', hlt⟩ hpath, ?_⟩
              rw [← val_ofFn C x ⟨w', hlt⟩]; exact hvw'
            · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
              have hkh : OrReaches nv C (nv + k) h := reach_orReaches hpath h rfl hh
              have hhJ : h ∈ junk G C := operandOrAndJunk ha haop (hweq ▸ hkh) hhand
              exact False.elim (hNoLamBelow bound hBnd k (by omega) hkN h hhJ hkh)
          · rintro ⟨v, hv, hxv⟩
            exact reach_var_val x (nv + k) v (mem_orIn_reach v hv) hxv
    have hConjBelow : ∀ (bound : ℕ), (∀ r ∈ orN G C \ lam G C, bound ≤ r) →
        ∀ a : ℕ, a ≤ bound → a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∃ Fs : Finset (Finset (Fin nv)), (∀ S ∈ Fs, LamOrSing S) ∧
          ∀ x : Fin nv → Bool, gateVal nv C a x = true ↔ setsEval Fs x := by
      intro bound hBnd a
      induction a using Nat.strong_induction_on with
      | ind a ih =>
        intro hab ha haop
        have hOpndFs : ∀ b : Fin 2, ∃ Fs : Finset (Finset (Fin nv)), (∀ S ∈ Fs, LamOrSing S) ∧
            ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C a b) = true ↔ setsEval Fs x := by
          intro b
          rcases hWireVal_below bound hBnd a b hab ha haop with ⟨S, hSL, hSv⟩ | ⟨j', hj', hj'lt, heq⟩
          · refine ⟨{S}, fun S' hS' => (Finset.mem_singleton.mp hS') ▸ hSL, fun x => ?_⟩
            rw [hSv x]
            exact ⟨fun h S' hS' => (Finset.mem_singleton.mp hS') ▸ h, fun h => h S (Finset.mem_singleton_self S)⟩
          · obtain ⟨hj'len, hj'op, _⟩ := junkData hj'
            obtain ⟨Fs', hFs'L, hFs'v⟩ := ih j' hj'lt (by omega) hj'len hj'op
            exact ⟨Fs', hFs'L, fun x => by rw [heq, ← gateVal_eq_val]; exact hFs'v x⟩
        obtain ⟨F0, hF0L, hF0v⟩ := hOpndFs 0
        obtain ⟨F1, hF1L, hF1v⟩ := hOpndFs 1
        refine ⟨F0 ∪ F1, fun S hS => (Finset.mem_union.mp hS).elim (hF0L S) (hF1L S), fun x => ?_⟩
        rw [andValBoth ha haop, hF0v x, hF1v x]
        constructor
        · intro h S hS; rcases Finset.mem_union.mp hS with h0 | h1; exact h.1 S h0; exact h.2 S h1
        · intro h; exact ⟨fun S h0 => h S (Finset.mem_union_left F1 h0), fun S h1 => h S (Finset.mem_union_right F0 h1)⟩
    have hNotBothSidesR : ∀ {t r : ℕ}, t ∈ tops G C → r ∈ orN G C →
        OrReaches nv C (opnd C t 0) r → OrReaches nv C (opnd C t 1) r → False := by
      intro t r ht hr h0 h1
      obtain ⟨htlen, htop, htb⟩ := topData ht
      obtain ⟨_, _, hrnb⟩ := (orN_mem C r).mp hr
      apply hrnb
      intro x hxr
      exact htb x ((andValBoth htlen htop x).mpr
        ⟨orStep_up List.length_ofFn (orReaches_reach r _ h0).1 (gateVal_eq_val C r x ▸ hxr),
         orStep_up List.length_ofFn (orReaches_reach r _ h1).1 (gateVal_eq_val C r x ▸ hxr)⟩)
    have hSingleR_contra : (centreless G C).card = 0 → (orN G C \ lam G C).card = 1 → False := by
      intro hZ0 hR1
      obtain ⟨r0, hr0Set⟩ := Finset.card_eq_one.mp hR1
      have hr0R : r0 ∈ orN G C \ lam G C := hr0Set ▸ Finset.mem_singleton_self r0
      have hr0N : r0 ∈ orN G C := (Finset.mem_sdiff.mp hr0R).1
      obtain ⟨hr0len, hr0op, _⟩ := (orN_mem C r0).mp hr0N
      have hBnd : ∀ r ∈ orN G C \ lam G C, r0 ≤ r := fun r hr => by
        have := Finset.mem_singleton.mp (hr0Set ▸ hr); omega
      obtain ⟨e0, he0⟩ := hUstarNe
      have hM_uniq : ∃ j1 ∈ junk G C, ∃ z0 ∈ orIn nv C (nv + r0),
          j1 < r0 ∧ OrReaches nv C (nv + r0) j1 ∧
          ∀ j' ∈ junk G C, OrReaches nv C (nv + r0) j' → j' = j1 := by
        induction e0 using Sym2.ind with
        | _ u0 v0 =>
          obtain ⟨t0, ht0, _, d0, j1, hj1, ht0d, _⟩ := residualTrace he0
          have hneD0 : (orIn nv C (opnd C t0 d0)).Nonempty := by
            by_contra hne
            have ht0Z : t0 ∈ centreless G C := emptySide_mem_centreless ht0 (Finset.not_nonempty_iff_eq_empty.mp hne)
            have := Finset.card_pos.mpr ⟨t0, ht0Z⟩; omega
          obtain ⟨m0, hm0R, _, hm0j1, hm0ne⟩ := noncentreless_witness hj1 ht0d hneD0
          have hm0eq : m0 = r0 := Finset.mem_singleton.mp (hr0Set ▸ hm0R)
          subst m0
          obtain ⟨z0, hz0⟩ := hm0ne
          have hz0U : z0 ∈ orIn nv C (opnd C r0 0) ∨ z0 ∈ orIn nv C (opnd C r0 1) :=
            Finset.mem_union.mp (orIn_or_union hr0len hr0op ▸ hz0)
          obtain ⟨b0, hb0ne⟩ : ∃ b0 : Fin 2, (orIn nv C (opnd C r0 b0)).Nonempty :=
            hz0U.elim (fun h => ⟨0, ⟨z0, h⟩⟩) (fun h => ⟨1, ⟨z0, h⟩⟩)
          have hNoJ_b0 : ∀ j' ∈ junk G C, ¬ OrReaches nv C (opnd C r0 b0) j' :=
            hBelow_noJunk_of_nonempty r0 (le_of_lt hr0len) hBnd (opnd C r0 b0) (opndBound hr0len b0) hb0ne
          have hOtherEmpty : orIn nv C (opnd C r0 (1 - b0)) = ∅ := by
            by_contra hne
            have hneb1 := Finset.nonempty_iff_ne_empty.mpr hne
            have hNoJ_b1 := hBelow_noJunk_of_nonempty r0 (le_of_lt hr0len) hBnd (opnd C r0 (1 - b0)) (opndBound hr0len (1 - b0)) hneb1
            obtain ⟨_, hj1op, _⟩ := junkData hj1
            rcases ((orReaches_iff r0 j1).mp hm0j1).2 with hEq | ⟨_, w, hwin, _, hwj1⟩
            · rw [← hEq, hj1op] at hr0op; exact GateOp.noConfusion hr0op
            · obtain ⟨b, rfl⟩ := inputsAsOpnd hr0len hwin
              by_cases hbb : b = b0
              · rw [hbb] at hwj1; exact hNoJ_b0 j1 hj1 hwj1
              · rw [fin2_ne_eq b0 b hbb] at hwj1; exact hNoJ_b1 j1 hj1 hwj1
          have hOpnd_eq_j1 : ∀ j' ∈ junk G C, OrReaches nv C (nv + r0) j' → opnd C r0 (1 - b0) = nv + j' := by
            intro j' hj' hr0j'
            obtain ⟨_, hj'op, _⟩ := junkData hj'
            rcases ((orReaches_iff r0 j').mp hr0j').2 with hEq | ⟨_, w, hwin, hwlt, hwj'⟩
            · rw [← hEq, hj'op] at hr0op; exact False.elim (GateOp.noConfusion hr0op)
            · obtain ⟨b, rfl⟩ := inputsAsOpnd hr0len hwin
              have hbeq : b = 1 - b0 := fin2_ne_eq b0 b (fun h => hNoJ_b0 j' hj' (h ▸ hwj'))
              rw [hbeq] at hwj' hwlt
              have hgeN : nv ≤ opnd C r0 (1 - b0) := (orReaches_def C _ _ ▸ hwj').1
              let k := opnd C r0 (1 - b0) - nv
              have hweq : opnd C r0 (1 - b0) = nv + k := by omega
              have hkle : k < r0 := by omega
              have hklen : k < C.gates.length := by omega
              rw [hweq] at hwj'
              rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
              · rcases ((orReaches_iff k j').mp hwj').2 with hkeq | ⟨hkop', _, _, _, _⟩
                · rw [hweq, hkeq]
                · rw [hkand] at hkop'; exact False.elim (GateOp.noConfusion hkop')
              · have hknb : ¬ BelowF G C k := fun hkb => junkNotBelow hj' (fun x hx =>
                  hkb x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k) hwj').1 (gateVal_eq_val C j' x ▸ hx)))
                exact False.elim (hNoLamBelow r0 hBnd k hkle ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) j' hj' hwj')
          have h1eq := hOpnd_eq_j1 j1 hj1 hm0j1
          have hj1lt : j1 < r0 := by have := opndBound hr0len (1 - b0); omega
          exact ⟨j1, hj1, z0, hz0, hj1lt, hm0j1, fun j' hj' hr0j' => by
            have := (hOpnd_eq_j1 j' hj' hr0j').symm.trans h1eq; omega⟩
      obtain ⟨j1, hj1, z0, hz0, hj1lt, hr0j1, hR0uniqJ⟩ := hM_uniq
      obtain ⟨hj1len, hj1op, _⟩ := junkData hj1
      obtain ⟨Fs1, hFs1L, hFs1v⟩ := hConjBelow r0 hBnd j1 (le_of_lt hj1lt) hj1len hj1op
      have hEdgeInfo : ∀ e ∈ Ustar G C, ∃ u v : Fin nv,
          e = s(u, v) ∧ G.Adj z0 v ∧ u ≠ z0 ∧ setsEval Fs1 (pairInput u v) ∧
          (∀ x : Fin nv → Bool, x v = true → setsEval Fs1 x → graphFun G ∅ x = true) := by
        intro e he
        induction e using Sym2.ind with
        | _ p q =>
          obtain ⟨t, ht, htv, d, j', hj', htd, _⟩ := residualTrace he
          obtain ⟨htlen, htop, htb⟩ := topData ht
          have hneSide : ∀ b : Fin 2, (orIn nv C (opnd C t b)).Nonempty := fun b => by
            by_contra hne
            have htZ : t ∈ centreless G C := emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne)
            have := Finset.card_pos.mpr ⟨t, htZ⟩; omega
          obtain ⟨m0, hm0R, htm0, hm0j', _⟩ := noncentreless_witness hj' htd (hneSide d)
          have hm0eq : m0 = r0 := Finset.mem_singleton.mp (hr0Set ▸ hm0R)
          subst m0
          have hj'eq : j' = j1 := hR0uniqJ j' hj' hm0j'
          subst j'
          have h1dNoJunk : ∀ j2 ∈ junk G C, ¬ OrReaches nv C (opnd C t (1 - d)) j2 := by
            intro j2 hj2 h1d
            obtain ⟨m2, hm2R, htm2, _, _⟩ := noncentreless_witness hj2 h1d (hneSide (1 - d))
            have hm2eq : m2 = r0 := Finset.mem_singleton.mp (hr0Set ▸ hm2R)
            subst m2
            rcases fin2_or d with rfl | rfl
            · exact hNotBothSidesR ht hr0N htm0 htm2
            · exact hNotBothSidesR ht hr0N htm2 htm0
          have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
            ((andValOperands htlen htop _).mp htv) (1 - d)
          obtain ⟨v, hvSide, hvp⟩ : ∃ v ∈ side (n := nv) C t (1 - d), v = p ∨ v = q := by
            rcases operandSupport htlen htop h1dVal with h1 | ⟨j2, hj2, h1d, _⟩
            · exact h1
            · exact False.elim (h1dNoJunk j2 hj2 h1d)
          have hz0Side : z0 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz0
          have hzv : G.Adj z0 v := topAdj_side ht hz0Side hvSide
          have hStarZ0V : s(z0, v) ∈ starEdges G C := side_mem_starEdges ht hz0Side hvSide
          have hFire : ∀ x : Fin nv → Bool, x v = true → setsEval Fs1 x → graphFun G ∅ x = true := by
            intro x hxv hxFs
            have hxj1 : gateVal nv C j1 x = true := (hFs1v x).mpr hxFs
            exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
              by_cases hidx : idx = d
              · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j1 _ htd).1 (gateVal_eq_val C j1 x ▸ hxj1)
              · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
          have hGetFs : ∀ a b : Fin nv, s(a, b) ∈ Ustar G C → b ∈ side (n := nv) C t (1 - d) →
              gateVal nv C t (pairInput a b) = true → setsEval Fs1 (pairInput a b) := by
            intro a b habU hbS htvab
            have h1 : val C (List.ofFn (pairInput a b)) (opnd C t d) = true := ((andValOperands htlen htop _).mp htvab) d
            rcases operandSupport htlen htop h1 with ⟨w, hwSide, hwp⟩ | ⟨j2, hj2, htd2, hj2v⟩
            · exfalso
              rcases hwp with hw | hw
              · rw [hw] at hwSide; rw [Ustar_def] at habU; exact (Finset.mem_sdiff.mp habU).2 (side_mem_starEdges ht hwSide hbS)
              · rw [hw] at hwSide; exact G.loopless.irrefl b (topAdj_side ht hwSide hbS)
            · obtain ⟨m2, hm2R, _, hm2j2, _⟩ := noncentreless_witness hj2 htd2 (hneSide d)
              have hm2eq : m2 = r0 := Finset.mem_singleton.mp (hr0Set ▸ hm2R)
              have hj2eq : j2 = j1 := hR0uniqJ j2 hj2 (hm2eq ▸ hm2j2)
              rw [hj2eq] at hj2v
              exact (hFs1v _).mp hj2v
          rcases hvp with hvEq | hvEq
          · subst v
            have hqNeZ0 : q ≠ z0 := fun h => by
              subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ0V)
            exact ⟨q, p, Sym2.eq_swap, hzv, hqNeZ0,
              hGetFs q p (Sym2.eq_swap ▸ he) hvSide (pairInput_symm p q ▸ htv), hFire⟩
          · subst v
            have hpNeZ0 : p ≠ z0 := fun h => by
              subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ0V
            exact ⟨p, q, rfl, hzv, hpNeZ0, hGetFs p q he hvSide htv, hFire⟩
      obtain ⟨u1, v1, rfl, hzv1, hu1ne, hFs1_e1, hFire1⟩ := hEdgeInfo e0 he0
      have hUstarLe1 : (Ustar G C).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro eA heA eB heB
        obtain ⟨uA, vA, rfl, hzvA, huAne, hFsA, _⟩ := hEdgeInfo eA heA
        obtain ⟨uB, vB, rfl, hzvB, huBne, hFsB, _⟩ := hEdgeInfo eB heB
        have hA1 := hMono_underZ_uniq Fs1 hFs1L z0 uA vA u1 v1 heA he0 hzvA hzv1 huAne hFsA hFs1_e1 hFire1
        have hB1 := hMono_underZ_uniq Fs1 hFs1L z0 uB vB u1 v1 heB he0 hzvB hzv1 huBne hFsB hFs1_e1 hFire1
        exact hA1.trans hB1.symm
      have hlt := hBudgetLtCov {u1} (fun e he => by
        have heq : e = s(u1, v1) := Finset.card_le_one.mp hUstarLe1 e he s(u1, v1) he0
        rw [heq]; exact ⟨u1, Finset.mem_singleton_self u1, Sym2.mem_mk_left _ _⟩)
      rw [Finset.card_singleton] at hlt
      omega
    have hBudgetGe4 : 4 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
      by_contra hlt4
      have hZ0 : (centreless G C).card = 0 := by omega
      have hR1 : (orN G C \ lam G C).card = 1 := by rcases hZorR with hZ1 | hR1 <;> omega
      exact hSingleR_contra hZ0 hR1
    have hUstarGe3 : 3 ≤ (Ustar G C).card := by
      by_contra hlt3
      have hCovCard : ∃ A : Finset (Fin nv), A.card ≤ (Ustar G C).card ∧
          ∀ e ∈ Ustar G C, ∃ v ∈ A, v ∈ e := by
        have hEx : ∀ e ∈ Ustar G C, ∃ v : Fin nv, v ∈ e := fun e _ =>
          Sym2.ind (fun u _ => ⟨u, Sym2.mem_mk_left _ _⟩) e
        let pick : Sym2 (Fin nv) → Fin nv := fun e => if h : e ∈ Ustar G C then Classical.choose (hEx e h) else ⟨0, by omega⟩
        refine ⟨(Ustar G C).image pick, Finset.card_image_le, fun e he => ?_⟩
        refine ⟨pick e, Finset.mem_image_of_mem pick he, ?_⟩
        dsimp only [pick]; rw [dif_pos he]; exact Classical.choose_spec (hEx e he)
      obtain ⟨A, hAc, hAcov⟩ := hCovCard
      have hlt := hBudgetLtCov A hAcov
      omega
    have hBudgetGe5 : 5 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
      by_contra hlt5
      have hB4 : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card = 4 := by omega
      by_cases hZpos : 1 ≤ (centreless G C).card
      · have hZ1 : (centreless G C).card = 1 := by omega
        have hR0 : (orN G C \ lam G C).card = 0 := by omega
        obtain ⟨tz, htzSet⟩ := Finset.card_eq_one.mp hZ1
        have htzMem : tz ∈ centreless G C := htzSet ▸ Finset.mem_singleton_self tz
        have htzTop : tz ∈ tops G C := ((centreless_mem C tz).mp htzMem).1
        obtain ⟨htzlen, htzop, htzb⟩ := topData htzTop
        have hBndAll : ∀ r ∈ orN G C \ lam G C, C.gates.length ≤ r := fun r hr => by
          have := Finset.card_pos.mpr ⟨r, hr⟩; omega
        obtain ⟨FsZ, hFsZL, hFsZv⟩ := hConjBelow C.gates.length hBndAll tz (le_of_lt htzlen) htzlen htzop
        have hUstarAllTz : ∀ e ∈ Ustar G C, ∀ u v : Fin nv, e = s(u, v) → setsEval FsZ (pairInput u v) := by
          intro e he u v huv
          rw [huv] at he
          obtain ⟨t, ht, htv, d, j', hj', htd, _⟩ := residualTrace he
          have htZ : t ∈ centreless G C := by
            by_contra hnz
            have hneD : (orIn nv C (opnd C t d)).Nonempty := by
              by_contra hne
              exact hnz (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
            obtain ⟨m0, hm0R, _, _, _⟩ := noncentreless_witness hj' htd hneD
            have := Finset.card_pos.mpr ⟨m0, hm0R⟩; omega
          have hteq : t = tz := Finset.mem_singleton.mp (htzSet ▸ htZ)
          rw [hteq] at htv
          exact (hFsZv _).mp htv
        have hUle1 : (Ustar G C).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro e1 he1 e2 he2
          induction e1 using Sym2.ind with
          | _ u1 v1 =>
            induction e2 using Sym2.ind with
            | _ u2 v2 =>
              exact hMono_global_uniq FsZ hFsZL (fun x hx => htzb x ((hFsZv x).mpr hx))
                u1 v1 u2 v2 he1 he2 (hUstarAllTz _ he1 u1 v1 rfl) (hUstarAllTz _ he2 u2 v2 rfl)
        omega
      · have hZ0 : (centreless G C).card = 0 := by omega
        have hRne1 : (orN G C \ lam G C).card ≠ 1 := fun h => hSingleR_contra hZ0 h
        have hRpos : 1 ≤ (orN G C \ lam G C).card := by rcases hZorR with hZ1 | hR1 <;> omega
        have hJ2 : (junk G C).card = 2 := by omega
        have hR2 : (orN G C \ lam G C).card = 2 := by omega
        obtain ⟨rA, hrA, rB, hrB, hrABne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orN G C \ lam G C).card)
        let r1 := min rA rB
        let r2 := max rA rB
        have hr1lt2 : r1 < r2 := by dsimp only [r1, r2]; omega
        have hr1R : r1 ∈ orN G C \ lam G C := by
          dsimp only [r1]
          by_cases h : rA ≤ rB
          · rw [min_eq_left h]; exact hrA
          · rw [min_eq_right (le_of_not_ge h)]; exact hrB
        have hr2R : r2 ∈ orN G C \ lam G C := by
          dsimp only [r2]
          by_cases h : rA ≤ rB
          · rw [max_eq_right h]; exact hrB
          · rw [max_eq_left (le_of_not_ge h)]; exact hrA
        have hRset : orN G C \ lam G C = {r1, r2} := by
          apply Eq.symm
          apply Finset.eq_of_subset_of_card_le
          · intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr'
            · exact hr1R
            · rw [Finset.mem_singleton.mp hr']; exact hr2R
          · rw [Finset.card_pair (ne_of_lt hr1lt2), hR2]
        have hr1N : r1 ∈ orN G C := (Finset.mem_sdiff.mp hr1R).1
        have hr2N : r2 ∈ orN G C := (Finset.mem_sdiff.mp hr2R).1
        obtain ⟨hr1len, hr1op, _⟩ := (orN_mem C r1).mp hr1N
        obtain ⟨hr2len, hr2op, _⟩ := (orN_mem C r2).mp hr2N
        have hBnd1 : ∀ r ∈ orN G C \ lam G C, r1 ≤ r := fun r hr => by
          rw [hRset] at hr
          rcases Finset.mem_insert.mp hr with rfl | hr'
          · exact le_refl r1
          · rw [Finset.mem_singleton.mp hr']; exact le_of_lt hr1lt2
        have hneSideTop : ∀ {t : ℕ}, t ∈ tops G C → ∀ b : Fin 2, (orIn nv C (opnd C t b)).Nonempty := by
          intro t ht b
          by_contra hne
          have htZ : t ∈ centreless G C := emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne)
          have := Finset.card_pos.mpr ⟨t, htZ⟩; omega
        have hNotBelowF_reaches_and : ∀ {r : ℕ}, r < C.gates.length → ¬ BelowF G C r →
            ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ (a = r ∨ InCone nv C r a) := by
          intro r
          induction hrem : C.gates.length - r using Nat.strong_induction_on generalizing r with
          | ind d ih =>
            intro hr hrnb
            rcases hLeast.1.1 _ (gateAt_mem hr) with hand | hor
            · exact ⟨r, hr, hand, Or.inl rfl⟩
            · obtain ⟨k, hk⟩ := leastRead hr hrnb
              obtain ⟨hklen, hkin⟩ := readData hk
              have hrk : r < k := readLt hk
              rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
              · exact ⟨k, hklen, hkand, Or.inr ((inCone_iff r k).mpr ⟨hklen, r, hrk, hkin, Or.inl rfl⟩)⟩
              · have hknb : ¬ BelowF G C k := by
                  intro hkb
                  apply hrnb
                  intro x hrx
                  exact hkb x ((val_or List.length_ofFn hklen hkor).mpr ⟨nv + r, hkin, by omega, gateVal_eq_val C r x ▸ hrx⟩)
                obtain ⟨a, halen, haop, haeq⟩ := ih (C.gates.length - k) (by omega) rfl hklen hknb
                rcases haeq with rfl | hka
                · rw [hkor] at haop; exact False.elim (GateOp.noConfusion haop)
                · exact ⟨a, halen, haop, Or.inr (inCone_trans ((inCone_iff r k).mpr ⟨hklen, r, hrk, hkin, Or.inl rfl⟩) hka)⟩
        have hOpnd_notBelowF : ∀ {r k : ℕ} {b : Fin 2}, r < C.gates.length → ¬ BelowF G C r →
            opnd C r b = nv + k → ¬ BelowF G C k := by
          intro r k b hr hrnb heq hkb
          have hkr : k < r := by have := opndBound hr b; omega
          have hklen : k < C.gates.length := by omega
          obtain ⟨a, halen, haop, haeq⟩ := hNotBelowF_reaches_and hr hrnb
          have hkrCone : InCone nv C k r := (inCone_iff k r).mpr ⟨hr, k, hkr, heq ▸ opndMem hr b, Or.inl rfl⟩
          have hka : InCone nv C k a := by
            rcases haeq with rfl | hra
            · exact hkrCone
            · exact inCone_trans hkrCone hra
          exact not_belowF_inCone_and hklen hkb halen haop hka
        have hOrReach_and_junk : ∀ {k h : ℕ}, k < C.gates.length → ¬ BelowF G C k →
            (gateAt C k).op = GateOp.or → h < C.gates.length → (gateAt C h).op = GateOp.and →
            Relation.ReflTransGen OrStep (nv + k) (nv + h) → h ∈ junk G C := by
          intro k h hklen hknb hkor hhlen hhand hpath
          have hnbh : ¬ BelowF G C h := by
            obtain ⟨a, halen, haop, haeq⟩ := hNotBelowF_reaches_and hklen hknb
            have hhk : InCone nv C h k := by
              rcases orStep_cone hpath k h rfl rfl with heq | hcone
              · rw [heq, hkor] at hhand; exact False.elim (GateOp.noConfusion hhand)
              · exact hcone
            have hha : InCone nv C h a := by
              rcases haeq with rfl | hka
              · exact hhk
              · exact inCone_trans hhk hka
            exact fun hbh => not_belowF_inCone_and hhlen hbh halen haop hha
          have hdirty : ∃ y : Fin nv → Bool, gateVal nv C h y = true ∧ graphFun G ∅ y = false := by
            by_contra hnone
            apply hnbh
            intro y hy
            by_contra hf
            exact hnone ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
          exact (junk_mem C h).mpr ⟨hhlen, hhand, hdirty⟩
        have hCardLe2_contra : ∀ (U0 U1 : Finset (Sym2 (Fin nv))),
            Ustar G C ⊆ U0 ∪ U1 → U0.card ≤ 1 → U1.card ≤ 1 → False := by
          intro U0 U1 hsub h0 h1
          have hle := Finset.card_le_card hsub
          have hun := Finset.card_union_le U0 U1
          omega
        by_cases hr1HasJ : ∃ ja ∈ junk G C, OrReaches nv C (nv + r1) ja
        · by_cases hr1Empty : orIn nv C (nv + r1) = ∅
          · have hr1BothJ : ∀ b : Fin 2, ∃ j ∈ junk G C, j < r1 ∧ opnd C r1 b = nv + j := by
              intro b
              have hbe : orIn nv C (opnd C r1 b) = ∅ := by
                have hsub : orIn nv C (opnd C r1 b) ⊆ orIn nv C (nv + r1) := by
                  rw [orIn_or_union hr1len hr1op]
                  rcases fin2_or b with rfl | rfl; exact Finset.subset_union_left; exact Finset.subset_union_right
                rw [hr1Empty] at hsub; exact Finset.subset_empty.mp hsub
              have hgeN : nv ≤ opnd C r1 b := by
                by_contra hlt
                have hm : (⟨opnd C r1 b, by omega⟩ : Fin nv) ∈ orIn nv C (⟨opnd C r1 b, by omega⟩ : Fin nv).val := by
                  rw [orIn_leaf]; exact Finset.mem_singleton_self _
                dsimp only at hm
                rw [hbe] at hm; exact Finset.notMem_empty _ hm
              let k := opnd C r1 b - nv
              have hweq : opnd C r1 b = nv + k := by omega
              have hkr1 : k < r1 := by have := opndBound hr1len b; omega
              have hklen : k < C.gates.length := by omega
              have hknb : ¬ BelowF G C k := hOpnd_notBelowF hr1len ((orN_mem C r1).mp hr1N).2.2 hweq
              rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
              · have hdirty : ∃ x : Fin nv → Bool, gateVal nv C k x = true ∧ graphFun G ∅ x = false := by
                  by_contra hnone; apply hknb; intro x hx; by_contra hf; exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
                exact ⟨k, (junk_mem C k).mpr ⟨hklen, hkand, hdirty⟩, hkr1, hweq⟩
              · have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
                have hkLam : k ∈ lam G C := by
                  by_contra hnl; have := hBnd1 k (Finset.mem_sdiff.mpr ⟨hkN, hnl⟩); omega
                obtain ⟨_, hne0, _, _⟩ := (lam_mem C k).mp hkLam
                obtain ⟨v0, hv0⟩ := hne0
                have hv0k : v0 ∈ orIn nv C (nv + k) := by
                  rw [orIn_or_union hklen hkor]; exact Finset.mem_union_left _ hv0
                rw [← hweq, hbe] at hv0k; exact False.elim (Finset.notMem_empty v0 hv0k)
            obtain ⟨j0, hj0, hj0lt, hj0eq⟩ := hr1BothJ 0
            obtain ⟨j1, hj1, hj1lt, hj1eq⟩ := hr1BothJ 1
            have hj01ne : j0 ≠ j1 := by
              intro heq; subst j1
              apply replace_gate_by_wire r1 (nv + j0) hr1len (by omega)
              intro x
              apply Bool.eq_iff_iff.mpr
              rw [orValOperands hr1len hr1op]
              constructor
              · intro h; exact ⟨0, by rw [hj0eq]; exact h⟩
              · rintro ⟨b, hb⟩; rcases fin2_or b with rfl | rfl; rw [hj0eq] at hb; exact hb; rw [hj1eq] at hb; exact hb
            have hJset : junk G C = {j0, j1} := by
              apply Eq.symm
              apply Finset.eq_of_subset_of_card_le
              · intro j hj
                rcases Finset.mem_insert.mp hj with rfl | hj'
                · exact hj0
                · rw [Finset.mem_singleton.mp hj']; exact hj1
              · rw [Finset.card_pair hj01ne, hJ2]
            obtain ⟨hj0len, hj0op, _⟩ := junkData hj0
            obtain ⟨hj1len, hj1op, _⟩ := junkData hj1
            obtain ⟨Fs0, hFs0L, hFs0v⟩ := hConjBelow r1 hBnd1 j0 (le_of_lt hj0lt) hj0len hj0op
            obtain ⟨Fs1, hFs1L, hFs1v⟩ := hConjBelow r1 hBnd1 j1 (le_of_lt hj1lt) hj1len hj1op
            have hr2Ne : (orIn nv C (nv + r2)).Nonempty := by
              obtain ⟨e0, he0⟩ := hUstarNe
              induction e0 using Sym2.ind with
              | _ u0 v0 =>
                obtain ⟨t0, ht0, _, d0, j', hj', ht0d, _⟩ := residualTrace he0
                obtain ⟨m0, hm0R, _, _, hm0ne⟩ := noncentreless_witness hj' ht0d (hneSideTop ht0 d0)
                rw [hRset] at hm0R
                rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                · rw [hr1Empty] at hm0ne; exact False.elim (Finset.not_nonempty_empty hm0ne)
                · rw [Finset.mem_singleton.mp hm0'] at hm0ne; exact hm0ne
            obtain ⟨z2, hz2⟩ := hr2Ne
            have hEdge3B : ∀ e ∈ Ustar G C, ∃ u v : Fin nv,
                e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
                ((setsEval Fs0 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fs0 x → graphFun G ∅ x = true) ∨
                 (setsEval Fs1 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fs1 x → graphFun G ∅ x = true)) := by
              intro e he
              induction e using Sym2.ind with
              | _ p q =>
                obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
                obtain ⟨htlen, htop, htb⟩ := topData ht
                obtain ⟨m0, hm0R, htm0, _, hm0ne⟩ := noncentreless_witness hj' htd (hneSideTop ht d)
                have hm0eq : m0 = r2 := by
                  rw [hRset] at hm0R
                  rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                  · rw [hr1Empty] at hm0ne; exact False.elim (Finset.not_nonempty_empty hm0ne)
                  · exact Finset.mem_singleton.mp hm0'
                subst m0
                have h1dNoJ : ∀ j2 ∈ junk G C, ¬ OrReaches nv C (opnd C t (1 - d)) j2 := by
                  intro j2 hj2 h1d
                  obtain ⟨m2, hm2R, htm2, _, hm2ne⟩ := noncentreless_witness hj2 h1d (hneSideTop ht (1 - d))
                  have hm2eq : m2 = r2 := by
                    rw [hRset] at hm2R
                    rcases Finset.mem_insert.mp hm2R with rfl | hm2'
                    · rw [hr1Empty] at hm2ne; exact False.elim (Finset.not_nonempty_empty hm2ne)
                    · exact Finset.mem_singleton.mp hm2'
                  subst m2
                  rcases fin2_or d with rfl | rfl
                  · exact hNotBothSidesR ht hr2N htm0 htm2
                  · exact hNotBothSidesR ht hr2N htm2 htm0
                have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
                  ((andValOperands htlen htop _).mp htv) (1 - d)
                obtain ⟨v, hvSide, hvp⟩ : ∃ v ∈ side (n := nv) C t (1 - d), v = p ∨ v = q := by
                  rcases operandSupport htlen htop h1dVal with h1 | ⟨j2, hj2, h1d, _⟩
                  · exact h1
                  · exact False.elim (h1dNoJ j2 hj2 h1d)
                have hz2Side : z2 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz2
                have hzv : G.Adj z2 v := topAdj_side ht hz2Side hvSide
                have hStarZ : s(z2, v) ∈ starEdges G C := side_mem_starEdges ht hz2Side hvSide
                have hFireJ : ∀ x : Fin nv → Bool, x v = true → gateVal nv C j' x = true → graphFun G ∅ x = true := by
                  intro x hxv hxj
                  exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                    by_cases hidx : idx = d
                    · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j' _ htd).1 (gateVal_eq_val C j' x ▸ hxj)
                    · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
                have hj'Cases : j' = j0 ∨ j' = j1 := by
                  rw [hJset] at hj'
                  rcases Finset.mem_insert.mp hj' with rfl | hj''
                  · exact Or.inl rfl
                  · exact Or.inr (Finset.mem_singleton.mp hj'')
                rcases hvp with hvEq | hvEq
                · subst v
                  have hqNe : q ≠ z2 := fun h => by
                    subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ)
                  refine ⟨q, p, Sym2.eq_swap, hzv, hqNe, ?_⟩
                  rcases hj'Cases with rfl | rfl
                  · exact Or.inl ⟨(hFs0v _).mp (pairInput_symm p q ▸ hj'v), fun x hxv hfs => hFireJ x hxv ((hFs0v x).mpr hfs)⟩
                  · exact Or.inr ⟨(hFs1v _).mp (pairInput_symm p q ▸ hj'v), fun x hxv hfs => hFireJ x hxv ((hFs1v x).mpr hfs)⟩
                · subst v
                  have hpNe : p ≠ z2 := fun h => by
                    subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ
                  refine ⟨p, q, rfl, hzv, hpNe, ?_⟩
                  rcases hj'Cases with rfl | rfl
                  · exact Or.inl ⟨(hFs0v _).mp hj'v, fun x hxv hfs => hFireJ x hxv ((hFs0v x).mpr hfs)⟩
                  · exact Or.inr ⟨(hFs1v _).mp hj'v, fun x hxv hfs => hFireJ x hxv ((hFs1v x).mpr hfs)⟩
            let U0 := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              setsEval Fs0 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fs0 x → graphFun G ∅ x = true)
            let U1 := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              setsEval Fs1 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fs1 x → graphFun G ∅ x = true)
            have hSub : Ustar G C ⊆ U0 ∪ U1 := fun e he => by
              obtain ⟨u, v, huv, hzv, hne, hc⟩ := hEdge3B e he
              rcases hc with h0 | h1
              · exact Finset.mem_union_left U1 (Finset.mem_filter.mpr ⟨he, u, v, huv, hzv, hne, h0⟩)
              · exact Finset.mem_union_right U0 (Finset.mem_filter.mpr ⟨he, u, v, huv, hzv, hne, h1⟩)
            have hU0le1 : U0.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fs0 hFs0L z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            have hU1le1 : U1.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fs1 hFs1L z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            exact hCardLe2_contra U0 U1 hSub hU0le1 hU1le1
          · have hr1Ne : (orIn nv C (nv + r1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hr1Empty
            obtain ⟨ja0, hja0, hr1ja0⟩ := hr1HasJ
            obtain ⟨z1, hz1⟩ := hr1Ne
            have hz1U : z1 ∈ orIn nv C (opnd C r1 0) ∨ z1 ∈ orIn nv C (opnd C r1 1) :=
              Finset.mem_union.mp (orIn_or_union hr1len hr1op ▸ hz1)
            obtain ⟨b1, hb1ne⟩ : ∃ b1 : Fin 2, (orIn nv C (opnd C r1 b1)).Nonempty :=
              hz1U.elim (fun h => ⟨0, ⟨z1, h⟩⟩) (fun h => ⟨1, ⟨z1, h⟩⟩)
            have hNoJ_b1 : ∀ j' ∈ junk G C, ¬ OrReaches nv C (opnd C r1 b1) j' :=
              hBelow_noJunk_of_nonempty r1 (le_of_lt hr1len) hBnd1 (opnd C r1 b1) (opndBound hr1len b1) hb1ne
            have hR1opnd : ∀ j' ∈ junk G C, OrReaches nv C (nv + r1) j' → opnd C r1 (1 - b1) = nv + j' := by
              intro j' hj' hr1j'
              obtain ⟨_, hj'op, _⟩ := junkData hj'
              rcases ((orReaches_iff r1 j').mp hr1j').2 with hEq | ⟨_, w, hwin, hwlt, hwj'⟩
              · rw [← hEq, hj'op] at hr1op; exact False.elim (GateOp.noConfusion hr1op)
              · obtain ⟨b, rfl⟩ := inputsAsOpnd hr1len hwin
                have hbeq : b = 1 - b1 := fin2_ne_eq b1 b (fun h => hNoJ_b1 j' hj' (h ▸ hwj'))
                rw [hbeq] at hwj' hwlt
                have hgeN : nv ≤ opnd C r1 (1 - b1) := (orReaches_def C _ _ ▸ hwj').1
                let k := opnd C r1 (1 - b1) - nv
                have hweq : opnd C r1 (1 - b1) = nv + k := by omega
                have hkle : k < r1 := by omega
                have hklen : k < C.gates.length := by omega
                rw [hweq] at hwj'
                rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
                · rcases ((orReaches_iff k j').mp hwj').2 with hkeq | ⟨hkop', _, _, _, _⟩
                  · rw [hweq, hkeq]
                  · rw [hkand] at hkop'; exact False.elim (GateOp.noConfusion hkop')
                · have hknb : ¬ BelowF G C k := fun hkb => junkNotBelow hj' (fun x hx =>
                    hkb x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k) hwj').1 (gateVal_eq_val C j' x ▸ hx)))
                  exact False.elim (hNoLamBelow r1 hBnd1 k hkle ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) j' hj' hwj')
            have hr1OpndJa : opnd C r1 (1 - b1) = nv + ja0 := hR1opnd ja0 hja0 hr1ja0
            have hja0lt : ja0 < r1 := by have := opndBound hr1len (1 - b1); omega
            have hR1uniqJ : ∀ j' ∈ junk G C, OrReaches nv C (nv + r1) j' → j' = ja0 := fun j' hj' h => by
              have := (hR1opnd j' hj' h).symm.trans hr1OpndJa; omega
            obtain ⟨hjalen, hjaop, _⟩ := junkData hja0
            obtain ⟨Fsa, hFsaL, hFsav⟩ := hConjBelow r1 hBnd1 ja0 (le_of_lt hja0lt) hjalen hjaop
            have hR1_b1_val : LamOrSing (orIn nv C (nv + r1)) ∧
                ∀ x : Fin nv → Bool, val C (List.ofFn x) (nv + r1) = true ↔
                  gateVal nv C ja0 x = true ∨ ∃ v ∈ orIn nv C (nv + r1), x v = true := by
              have horEq : orIn nv C (nv + r1) = orIn nv C (opnd C r1 b1) := by
                rw [orIn_or_union hr1len hr1op]
                rcases fin2_or b1 with rfl | rfl
                · rw [show (1 : Fin 2) - 0 = 1 from rfl] at hr1OpndJa
                  rw [hr1OpndJa, andRawEmpty hjaop, Finset.union_empty]
                · rw [show (1 : Fin 2) - 1 = 0 from rfl] at hr1OpndJa
                  rw [hr1OpndJa, andRawEmpty hjaop, Finset.empty_union]
              have hLosB1 : LamOrSing (orIn nv C (opnd C r1 b1)) ∧
                  ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C r1 b1) = true ↔
                    ∃ v ∈ orIn nv C (opnd C r1 b1), x v = true := by
                by_cases hlt : opnd C r1 b1 < nv
                · refine ⟨Or.inl ⟨⟨opnd C r1 b1, hlt⟩, orIn_leaf ⟨opnd C r1 b1, hlt⟩⟩, fun x => ?_⟩
                  rw [orIn_leaf ⟨opnd C r1 b1, hlt⟩]
                  have hval : val C (List.ofFn x) (opnd C r1 b1) = x ⟨opnd C r1 b1, hlt⟩ := val_ofFn C x ⟨opnd C r1 b1, hlt⟩
                  rw [hval]
                  constructor
                  · intro h; exact ⟨_, Finset.mem_singleton_self _, h⟩
                  · rintro ⟨v, hv, hxv⟩; exact (Finset.mem_singleton.mp hv) ▸ hxv
                · let k := opnd C r1 b1 - nv
                  have hweq : opnd C r1 b1 = nv + k := by omega
                  have hkr1 : k < r1 := by have := opndBound hr1len b1; omega
                  have hklen : k < C.gates.length := by omega
                  have hknb : ¬ BelowF G C k := hOpnd_notBelowF hr1len ((orN_mem C r1).mp hr1N).2.2 hweq
                  have hkor : (gateAt C k).op = GateOp.or := by
                    rcases hLeast.1.1 _ (gateAt_mem hklen) with hand | hor
                    · rw [hweq, andRawEmpty hand] at hb1ne; exact False.elim (Finset.not_nonempty_empty hb1ne)
                    · exact hor
                  have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
                  have hkLam : k ∈ lam G C := by
                    by_contra hnl; have := hBnd1 k (Finset.mem_sdiff.mpr ⟨hkN, hnl⟩); omega
                  refine ⟨Or.inr ⟨k, hkLam, by rw [hweq]⟩, fun x => ?_⟩
                  rw [hweq]
                  constructor
                  · intro hv
                    obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (nv + k) hv
                    rcases hcase with hlt' | ⟨h, hh, rfl, hneOr⟩
                    · refine ⟨⟨w', hlt'⟩, reach_mem_orIn ⟨w', hlt'⟩ hpath, ?_⟩
                      rw [← val_ofFn C x ⟨w', hlt'⟩]; exact hvw'
                    · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
                      have hkh : OrReaches nv C (nv + k) h := reach_orReaches hpath h rfl hh
                      have hhJ : h ∈ junk G C := hOrReach_and_junk hklen hknb hkor hh hhand hpath
                      exact False.elim (hNoLamBelow r1 hBnd1 k hkr1 hkN h hhJ hkh)
                  · rintro ⟨v, hv, hxv⟩
                    exact reach_var_val x (nv + k) v (mem_orIn_reach v hv) hxv
              refine ⟨horEq ▸ hLosB1.1, fun x => ?_⟩
              rw [← gateVal_eq_val, orValOperands hr1len hr1op]
              constructor
              · rintro ⟨b, hb⟩
                by_cases hbb : b = b1
                · rw [hbb] at hb; exact Or.inr (horEq ▸ (hLosB1.2 x).mp hb)
                · rw [fin2_ne_eq b1 b hbb, hr1OpndJa] at hb; exact Or.inl hb
              · rintro (hja | hor)
                · exact ⟨1 - b1, by rw [hr1OpndJa]; exact hja⟩
                · exact ⟨b1, (hLosB1.2 x).mpr (horEq ▸ hor)⟩
            have hJbEx : ∃ jb ∈ junk G C, jb ≠ ja0 := by
              have hne : (junk G C \ {ja0}).Nonempty := by
                apply Finset.card_pos.mp
                have hs : ({ja0} : Finset ℕ) ⊆ junk G C := Finset.singleton_subset_iff.mpr hja0
                rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hs, Finset.card_singleton, hJ2]; omega
              obtain ⟨jb, hjb⟩ := hne
              exact ⟨jb, (Finset.mem_sdiff.mp hjb).1, Finset.mem_singleton.not.mp (Finset.mem_sdiff.mp hjb).2⟩
            obtain ⟨jb0, hjb0, hjbNe⟩ := hJbEx
            obtain ⟨hjb0len, hjb0op, _⟩ := junkData hjb0
            have hJset : junk G C = {ja0, jb0} := by
              apply Eq.symm
              apply Finset.eq_of_subset_of_card_le
              · intro j hj
                rcases Finset.mem_insert.mp hj with rfl | hj'
                · exact hja0
                · rw [Finset.mem_singleton.mp hj']; exact hjb0
              · rw [Finset.card_pair (Ne.symm hjbNe), hJ2]
            have hJ_cases : ∀ j ∈ junk G C, j = ja0 ∨ j = jb0 := fun j hj => by
              rw [hJset] at hj
              rcases Finset.mem_insert.mp hj with rfl | hj'
              · exact Or.inl rfl
              · exact Or.inr (Finset.mem_singleton.mp hj')
            have hOrBelowR2 : ∀ {k : ℕ}, k < r2 → k ∈ orN G C → k ≠ r1 →
                (∀ j' ∈ junk G C, OrReaches nv C (nv + k) j' → j' = ja0 ∧ OrReaches nv C (nv + k) r1) ∧
                LamOrSing (orIn nv C (nv + k)) ∧
                ((∀ x : Fin nv → Bool, val C (List.ofFn x) (nv + k) = true ↔ ∃ v ∈ orIn nv C (nv + k), x v = true) ∨
                 (OrReaches nv C (nv + k) r1 ∧
                  ∀ x : Fin nv → Bool, val C (List.ofFn x) (nv + k) = true ↔
                    gateVal nv C ja0 x = true ∨ ∃ v ∈ orIn nv C (nv + k), x v = true)) := by
              intro k hkr2 hkN hkr1
              obtain ⟨hklen, hkor, hknb⟩ := (orN_mem C k).mp hkN
              have hkLam : k ∈ lam G C := by
                by_contra hnl
                have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkN, hnl⟩
                rw [hRset] at hm
                rcases Finset.mem_insert.mp hm with rfl | hm'
                · exact hkr1 rfl
                · have := Finset.mem_singleton.mp hm'; omega
              have hkne : (orIn nv C (nv + k)).Nonempty := by
                obtain ⟨_, hne0, _, _⟩ := (lam_mem C k).mp hkLam
                obtain ⟨v0, hv0⟩ := hne0
                exact ⟨v0, by rw [orIn_or_union hklen hkor]; exact Finset.mem_union_left _ hv0⟩
              have hFirst : ∀ j' ∈ junk G C, OrReaches nv C (nv + k) j' → j' = ja0 ∧ OrReaches nv C (nv + k) r1 := by
                intro j' hj' hkj'
                obtain ⟨m, hmR, hkm, hmj', _⟩ := noncentreless_witness hj' hkj' hkne
                have hmeq : m = r1 := by
                  have hle := orReaches_le hkm
                  rw [hRset] at hmR
                  rcases Finset.mem_insert.mp hmR with rfl | hm'
                  · rfl
                  · have := Finset.mem_singleton.mp hm'; omega
                subst m
                exact ⟨hR1uniqJ j' hj' hmj', hkm⟩
              refine ⟨hFirst, Or.inr ⟨k, hkLam, rfl⟩, ?_⟩
              by_cases hkr : OrReaches nv C (nv + k) r1
              · right
                refine ⟨hkr, fun x => ?_⟩
                constructor
                · intro hv
                  obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (nv + k) hv
                  rcases hcase with hlt' | ⟨h, hh, rfl, hneOr⟩
                  · right; refine ⟨⟨w', hlt'⟩, reach_mem_orIn ⟨w', hlt'⟩ hpath, ?_⟩
                    rw [← val_ofFn C x ⟨w', hlt'⟩]; exact hvw'
                  · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
                    have hhJ := hOrReach_and_junk hklen hknb hkor hh hhand hpath
                    have hheq := (hFirst h hhJ (reach_orReaches hpath h rfl hh)).1
                    left; rw [← hheq]; exact hvw'
                · rintro (hja | ⟨v, hv, hxv⟩)
                  · have hkj := orReaches_trans hkr hr1ja0
                    exact orStep_up List.length_ofFn (orReaches_reach ja0 (nv + k) hkj).1 (gateVal_eq_val C ja0 x ▸ hja)
                  · exact reach_var_val x (nv + k) v (mem_orIn_reach v hv) hxv
              · left
                intro x
                constructor
                · intro hv
                  obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (nv + k) hv
                  rcases hcase with hlt' | ⟨h, hh, rfl, hneOr⟩
                  · refine ⟨⟨w', hlt'⟩, reach_mem_orIn ⟨w', hlt'⟩ hpath, ?_⟩
                    rw [← val_ofFn C x ⟨w', hlt'⟩]; exact hvw'
                  · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
                    have hhJ := hOrReach_and_junk hklen hknb hkor hh hhand hpath
                    exact False.elim (hkr (hFirst h hhJ (reach_orReaches hpath h rfl hh)).2)
                · rintro ⟨v, hv, hxv⟩
                  exact reach_var_val x (nv + k) v (mem_orIn_reach v hv) hxv
            have hr2Ne : (orIn nv C (nv + r2)).Nonempty := by
              by_contra hne
              have hr2E : orIn nv C (nv + r2) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
              have hAllR1 : ∀ e ∈ Ustar G C, ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z1 v ∧ u ≠ z1 ∧
                  setsEval Fsa (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fsa x → graphFun G ∅ x = true := by
                intro e he
                induction e using Sym2.ind with
                | _ p q =>
                  obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
                  obtain ⟨htlen, htop, htb⟩ := topData ht
                  obtain ⟨m0, hm0R, htm0, hm0j', hm0ne⟩ := noncentreless_witness hj' htd (hneSideTop ht d)
                  have hm0eq : m0 = r1 := by
                    rw [hRset] at hm0R
                    rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                    · rfl
                    · rw [Finset.mem_singleton.mp hm0', hr2E] at hm0ne; exact False.elim (Finset.not_nonempty_empty hm0ne)
                  subst m0
                  have hj'eq : j' = ja0 := hR1uniqJ j' hj' hm0j'
                  subst j'
                  have h1dNoJ : ∀ j2 ∈ junk G C, ¬ OrReaches nv C (opnd C t (1 - d)) j2 := by
                    intro j2 hj2 h1d
                    obtain ⟨m2, hm2R, htm2, _, hm2ne⟩ := noncentreless_witness hj2 h1d (hneSideTop ht (1 - d))
                    have hm2eq : m2 = r1 := by
                      rw [hRset] at hm2R
                      rcases Finset.mem_insert.mp hm2R with rfl | hm2'
                      · rfl
                      · rw [Finset.mem_singleton.mp hm2', hr2E] at hm2ne; exact False.elim (Finset.not_nonempty_empty hm2ne)
                    subst m2
                    rcases fin2_or d with rfl | rfl
                    · exact hNotBothSidesR ht hr1N htm0 htm2
                    · exact hNotBothSidesR ht hr1N htm2 htm0
                  have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
                    ((andValOperands htlen htop _).mp htv) (1 - d)
                  obtain ⟨v, hvSide, hvp⟩ : ∃ v ∈ side (n := nv) C t (1 - d), v = p ∨ v = q := by
                    rcases operandSupport htlen htop h1dVal with h1 | ⟨j2, hj2, h1d, _⟩
                    · exact h1
                    · exact False.elim (h1dNoJ j2 hj2 h1d)
                  have hz1Side : z1 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz1
                  have hzv : G.Adj z1 v := topAdj_side ht hz1Side hvSide
                  have hStarZ : s(z1, v) ∈ starEdges G C := side_mem_starEdges ht hz1Side hvSide
                  have hFire : ∀ x : Fin nv → Bool, x v = true → setsEval Fsa x → graphFun G ∅ x = true := by
                    intro x hxv hfs
                    exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                      by_cases hidx : idx = d
                      · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach ja0 _ htd).1 (gateVal_eq_val C ja0 x ▸ (hFsav x).mpr hfs)
                      · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
                  rcases hvp with hvEq | hvEq
                  · subst v
                    have hqNe : q ≠ z1 := fun h => by
                      subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ)
                    exact ⟨q, p, Sym2.eq_swap, hzv, hqNe, (hFsav _).mp (pairInput_symm p q ▸ hj'v), hFire⟩
                  · subst v
                    have hpNe : p ≠ z1 := fun h => by
                      subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ
                    exact ⟨p, q, rfl, hzv, hpNe, (hFsav _).mp hj'v, hFire⟩
              have hUle1 : (Ustar G C).card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                obtain ⟨uA, vA, rfl, hzvA, huAne, hFA, _⟩ := hAllR1 eA heA
                obtain ⟨uB, vB, rfl, hzvB, _, hFB, hSB⟩ := hAllR1 eB heB
                exact hMono_underZ_uniq Fsa hFsaL z1 uA vA uB vB heA heB hzvA hzvB huAne hFA hFB hSB)
              omega
            obtain ⟨z2, hz2⟩ := hr2Ne
            let Ur1 := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z1 v ∧ u ≠ z1 ∧
              setsEval Fsa (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fsa x → graphFun G ∅ x = true)
            let Ur2a := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              setsEval Fsa (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fsa x → graphFun G ∅ x = true)
            let Ur2b := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              gateVal nv C jb0 (pairInput u v) = true ∧ ∀ x : Fin nv → Bool, x v = true → gateVal nv C jb0 x = true → graphFun G ∅ x = true)
            let Uboth := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧
              gateVal nv C ja0 (pairInput u v) = true ∧ gateVal nv C jb0 (pairInput u v) = true ∧
              ∀ x : Fin nv → Bool, gateVal nv C ja0 x = true → gateVal nv C jb0 x = true → graphFun G ∅ x = true)
            have hUr1_le1 : Ur1.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fsa hFsaL z1 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            have hUr2a_le1 : Ur2a.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fsa hFsaL z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            have hEdgeClass : ∀ e ∈ Ustar G C,
                e ∈ Ur1 ∨
                (OrReaches nv C (nv + r2) ja0 ∧ e ∈ Ur2a ∧
                  (OrReaches nv C (nv + r2) r1 → e ∈ Ur1)) ∨
                (OrReaches nv C (nv + r2) jb0 ∧ e ∈ Ur2b) ∨
                (OrReaches nv C (nv + r2) jb0 ∧ e ∈ Uboth) := by
              intro e he
              induction e using Sym2.ind with
              | _ p q =>
                obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
                obtain ⟨htlen, htop, htb⟩ := topData ht
                obtain ⟨m0, hm0R, htm0, hm0j', _⟩ := noncentreless_witness hj' htd (hneSideTop ht d)
                have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
                  ((andValOperands htlen htop _).mp htv) (1 - d)
                rcases operandSupport htlen htop h1dVal with ⟨v, hvSide, hvp⟩ | ⟨j2, hj2, h1d, hj2v⟩
                · have hFireJ' : ∀ x : Fin nv → Bool, x v = true → gateVal nv C j' x = true → graphFun G ∅ x = true := by
                    intro x hxv hxj
                    exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                      by_cases hidx : idx = d
                      · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j' _ htd).1 (gateVal_eq_val C j' x ▸ hxj)
                      · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
                  rw [hRset] at hm0R
                  rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                  · have hj'eq : j' = ja0 := hR1uniqJ j' hj' hm0j'
                    subst j'
                    have hz1Side : z1 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz1
                    have hzv : G.Adj z1 v := topAdj_side ht hz1Side hvSide
                    have hStarZ : s(z1, v) ∈ starEdges G C := side_mem_starEdges ht hz1Side hvSide
                    left
                    rcases hvp with hvEq | hvEq
                    · subst v
                      have hqNe : q ≠ z1 := fun h => by
                        subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ)
                      exact Finset.mem_filter.mpr ⟨he, q, p, Sym2.eq_swap, hzv, hqNe,
                        (hFsav _).mp (pairInput_symm p q ▸ hj'v), fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                    · subst v
                      have hpNe : p ≠ z1 := fun h => by
                        subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ
                      exact Finset.mem_filter.mpr ⟨he, p, q, rfl, hzv, hpNe,
                        (hFsav _).mp hj'v, fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                  · have hm0eq : m0 = r2 := Finset.mem_singleton.mp hm0'
                    subst m0
                    have hz2Side : z2 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz2
                    have hzv2 : G.Adj z2 v := topAdj_side ht hz2Side hvSide
                    have hStarZ2 : s(z2, v) ∈ starEdges G C := side_mem_starEdges ht hz2Side hvSide
                    rcases hJ_cases j' hj' with rfl | rfl
                    · right; left
                      have hToZ1 : OrReaches nv C (nv + r2) r1 → s(p, q) ∈ Ur1 := by
                        intro hr2r1
                        have hz1Side : z1 ∈ side (n := nv) C t d := by
                          rw [side_def]; exact orIn_mono htm0 (orIn_mono hr2r1 hz1)
                        have hzv1 : G.Adj z1 v := topAdj_side ht hz1Side hvSide
                        have hStarZ1 : s(z1, v) ∈ starEdges G C := side_mem_starEdges ht hz1Side hvSide
                        rcases hvp with hvEq | hvEq
                        · subst v
                          have hqNe : q ≠ z1 := fun h => by
                            subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ1)
                          exact Finset.mem_filter.mpr ⟨he, q, p, Sym2.eq_swap, hzv1, hqNe,
                            (hFsav _).mp (pairInput_symm p q ▸ hj'v), fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                        · subst v
                          have hpNe : p ≠ z1 := fun h => by
                            subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ1
                          exact Finset.mem_filter.mpr ⟨he, p, q, rfl, hzv1, hpNe,
                            (hFsav _).mp hj'v, fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                      refine ⟨hm0j', ?_, hToZ1⟩
                      rcases hvp with hvEq | hvEq
                      · subst v
                        have hqNe : q ≠ z2 := fun h => by
                          subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ2)
                        exact Finset.mem_filter.mpr ⟨he, q, p, Sym2.eq_swap, hzv2, hqNe,
                          (hFsav _).mp (pairInput_symm p q ▸ hj'v), fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                      · subst v
                        have hpNe : p ≠ z2 := fun h => by
                          subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ2
                        exact Finset.mem_filter.mpr ⟨he, p, q, rfl, hzv2, hpNe,
                          (hFsav _).mp hj'v, fun x hxv hfs => hFireJ' x hxv ((hFsav x).mpr hfs)⟩
                    · right; right; left
                      refine ⟨hm0j', ?_⟩
                      rcases hvp with hvEq | hvEq
                      · subst v
                        have hqNe : q ≠ z2 := fun h => by
                          subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ2)
                        exact Finset.mem_filter.mpr ⟨he, q, p, Sym2.eq_swap, hzv2, hqNe,
                          pairInput_symm p q ▸ hj'v, hFireJ'⟩
                      · subst v
                        have hpNe : p ≠ z2 := fun h => by
                          subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ2
                        exact Finset.mem_filter.mpr ⟨he, p, q, rfl, hzv2, hpNe, hj'v, hFireJ'⟩
                · obtain ⟨m2, hm2R, htm2, hm2j2, _⟩ := noncentreless_witness hj2 h1d (hneSideTop ht (1 - d))
                  have hmNe : m0 ≠ m2 := by
                    intro heq; subst m2
                    have hmN : m0 ∈ orN G C := (Finset.mem_sdiff.mp hm0R).1
                    rcases fin2_or d with rfl | rfl
                    · exact hNotBothSidesR ht hmN htm0 htm2
                    · exact hNotBothSidesR ht hmN htm2 htm0
                  have hjNe : j' ≠ j2 := by
                    intro heq; subst j2
                    apply junkNotBelow hj'
                    intro x hxj
                    exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                      by_cases hidx : idx = d
                      · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j' _ htd).1 (gateVal_eq_val C j' x ▸ hxj)
                      · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j' _ h1d).1 (gateVal_eq_val C j' x ▸ hxj)))
                  have hGlob : ∀ x : Fin nv → Bool, gateVal nv C j' x = true → gateVal nv C j2 x = true → graphFun G ∅ x = true := by
                    intro x hx1 hx2
                    exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                      by_cases hidx : idx = d
                      · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j' _ htd).1 (gateVal_eq_val C j' x ▸ hx1)
                      · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j2 _ h1d).1 (gateVal_eq_val C j2 x ▸ hx2)))
                  rw [hRset] at hm0R hm2R
                  rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                  · have hm2eq : m2 = r2 := by
                      rcases Finset.mem_insert.mp hm2R with rfl | hm2'
                      · exact False.elim (hmNe rfl)
                      · exact Finset.mem_singleton.mp hm2'
                    subst m2
                    have hj'eq : j' = ja0 := hR1uniqJ j' hj' hm0j'
                    subst j'
                    have hj2eq : j2 = jb0 := by
                      rcases hJ_cases j2 hj2 with rfl | rfl
                      · exact False.elim (hjNe rfl)
                      · rfl
                    subst j2
                    right; right; right
                    exact ⟨hm2j2, Finset.mem_filter.mpr ⟨he, p, q, rfl, hj'v, hj2v, hGlob⟩⟩
                  · have hm0eq : m0 = r2 := Finset.mem_singleton.mp hm0'
                    subst m0
                    have hm2eq : m2 = r1 := by
                      rcases Finset.mem_insert.mp hm2R with rfl | hm2'
                      · rfl
                      · exact False.elim (hmNe (Finset.mem_singleton.mp hm2').symm)
                    subst m2
                    have hj2eq : j2 = ja0 := hR1uniqJ j2 hj2 hm2j2
                    subst j2
                    have hj'eq : j' = jb0 := by
                      rcases hJ_cases j' hj' with rfl | rfl
                      · exact False.elim (hjNe rfl)
                      · rfl
                    subst j'
                    right; right; right
                    exact ⟨hm0j', Finset.mem_filter.mpr ⟨he, p, q, rfl, hj2v, hj'v, fun x ha hb => hGlob x hb ha⟩⟩
            by_cases hJbLtJa : jb0 < ja0
            · have hJbOpnd : ∀ b : Fin 2, ∃ S : Finset (Fin nv), LamOrSing S ∧
                  ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C jb0 b) = true ↔ ∃ v ∈ S, x v = true := by
                intro b
                rcases hWireVal_below r1 hBnd1 jb0 b (le_of_lt (lt_trans hJbLtJa hja0lt)) hjb0len hjb0op with h1 | ⟨j', hj', hj'lt, _⟩
                · exact h1
                · rcases hJ_cases j' hj' with rfl | rfl <;> omega
              obtain ⟨Ab, hAbL, hAbv⟩ := hJbOpnd 0
              obtain ⟨Bb, hBbL, hBbv⟩ := hJbOpnd 1
              have hJbVal : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true ↔
                  (∃ a ∈ Ab, x a = true) ∧ (∃ b ∈ Bb, x b = true) := fun x => by
                rw [andValBoth hjb0len hjb0op, hAbv x, hBbv x]
              let Fsb : Finset (Finset (Fin nv)) := {Ab, Bb}
              have hFsbL : ∀ S ∈ Fsb, LamOrSing S := fun S hS => by
                rcases Finset.mem_insert.mp hS with rfl | hS'
                · exact hAbL
                · exact (Finset.mem_singleton.mp hS') ▸ hBbL
              have hFsbv : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true ↔ setsEval Fsb x := fun x => by
                rw [hJbVal x]
                constructor
                · rintro ⟨ha, hb⟩ S hS
                  rcases Finset.mem_insert.mp hS with rfl | hS'
                  · exact ha
                  · rw [Finset.mem_singleton.mp hS']; exact hb
                · intro h
                  exact ⟨h Ab (Finset.mem_insert_self Ab {Bb}),
                         h Bb (Finset.mem_insert_of_mem (Finset.mem_singleton_self Bb))⟩
              have hJbUnion_le1 : (Ur2b ∪ Uboth).card ≤ 1 := by
                by_cases hneB : Ur2b.Nonempty
                · obtain ⟨e1, he1⟩ := hneB
                  obtain ⟨he1U, u1, v1, rfl, _, _, hjb1, hSound1⟩ := Finset.mem_filter.mp he1
                  apply Finset.card_le_one.mpr
                  intro eA heA eB heB
                  have hEq1 : ∀ e ∈ Ur2b ∪ Uboth, s(u1, v1) = e := by
                    intro e he
                    rcases Finset.mem_union.mp he with h1 | h2
                    · obtain ⟨heU, u2, v2, rfl, _, _, hjb2, _⟩ := Finset.mem_filter.mp h1
                      exact hPairJunk_uniq jb0 Ab Bb hjb0 hAbL hBbL hJbVal u1 v1 he1U hjb1 hSound1 u2 v2 heU hjb2
                    · obtain ⟨heU, u2, v2, rfl, _, hjb2, _⟩ := Finset.mem_filter.mp h2
                      exact hPairJunk_uniq jb0 Ab Bb hjb0 hAbL hBbL hJbVal u1 v1 he1U hjb1 hSound1 u2 v2 heU hjb2
                  exact (hEq1 eA heA).symm.trans (hEq1 eB heB)
                · have hEmp : Ur2b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneB
                  rw [hEmp, Finset.empty_union]
                  apply Finset.card_le_one.mpr
                  intro eA heA eB heB
                  obtain ⟨heAU, uA, vA, rfl, hjaA, hjbA, hGlob⟩ := Finset.mem_filter.mp heA
                  obtain ⟨heBU, uB, vB, rfl, hjaB, hjbB, _⟩ := Finset.mem_filter.mp heB
                  have hUnL : ∀ S ∈ Fsa ∪ Fsb, LamOrSing S := fun S hS =>
                    (Finset.mem_union.mp hS).elim (hFsaL S) (hFsbL S)
                  have hUnEv : ∀ x : Fin nv → Bool, setsEval (Fsa ∪ Fsb) x ↔
                      gateVal nv C ja0 x = true ∧ gateVal nv C jb0 x = true := fun x => by
                    rw [hFsav x, hFsbv x]
                    constructor
                    · intro h; exact ⟨fun S hS => h S (Finset.mem_union_left Fsb hS),
                        fun S hS => h S (Finset.mem_union_right Fsa hS)⟩
                    · rintro ⟨h1, h2⟩ S hS; exact (Finset.mem_union.mp hS).elim (h1 S) (h2 S)
                  exact hMono_global_uniq (Fsa ∪ Fsb) hUnL
                    (fun x hx => hGlob x ((hUnEv x).mp hx).1 ((hUnEv x).mp hx).2)
                    uA vA uB vB heAU heBU ((hUnEv _).mpr ⟨hjaA, hjbA⟩) ((hUnEv _).mpr ⟨hjaB, hjbB⟩)
              by_cases hr2ja : OrReaches nv C (nv + r2) ja0
              · by_cases hr2r1 : OrReaches nv C (nv + r2) r1
                · refine hCardLe2_contra Ur1 (Ur2b ∪ Uboth) ?_ hUr1_le1 hJbUnion_le1
                  intro e he
                  rcases hEdgeClass e he with h1 | ⟨_, _, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                  · exact Finset.mem_union_left _ h1
                  · exact Finset.mem_union_left _ (h2 hr2r1)
                  · exact Finset.mem_union_right _ (Finset.mem_union_left _ h3)
                  · exact Finset.mem_union_right _ (Finset.mem_union_right _ h4)
                · have hr2NoJb : ¬ OrReaches nv C (nv + r2) jb0 := by
                    intro hr2jb
                    have hReachOpnd : ∀ j' ∈ junk G C, OrReaches nv C (nv + r2) j' →
                        ∃ b : Fin 2, OrReaches nv C (opnd C r2 b) j' := by
                      intro j' hj' hr2j'
                      obtain ⟨_, hj'op, _⟩ := junkData hj'
                      rcases ((orReaches_iff r2 j').mp hr2j').2 with hEq | ⟨_, w, hwin, _, hwj'⟩
                      · rw [← hEq, hj'op] at hr2op; exact False.elim (GateOp.noConfusion hr2op)
                      · obtain ⟨b, rfl⟩ := inputsAsOpnd hr2len hwin
                        exact ⟨b, hwj'⟩
                    obtain ⟨ba, hba⟩ := hReachOpnd ja0 hja0 hr2ja
                    have hbaEmpty : orIn nv C (opnd C r2 ba) = ∅ := by
                      by_contra hne
                      obtain ⟨m, hmR, hbam, _, _⟩ := noncentreless_witness hja0 hba (Finset.nonempty_iff_ne_empty.mpr hne)
                      have hlt : nv + m < nv + r2 := lt_of_le_of_lt (orReaches_le hbam) (opndBound hr2len ba)
                      rw [hRset] at hmR
                      rcases Finset.mem_insert.mp hmR with rfl | hm'
                      · exact hr2r1 ((orReaches_iff r2 r1).mpr ⟨hr2len, Or.inr ⟨hr2op, opnd C r2 ba, opndMem hr2len ba, opndBound hr2len ba, hbam⟩⟩)
                      · have := Finset.mem_singleton.mp hm'; omega
                    have hOtherNe : (orIn nv C (opnd C r2 (1 - ba))).Nonempty := by
                      have hz2U : z2 ∈ orIn nv C (opnd C r2 0) ∨ z2 ∈ orIn nv C (opnd C r2 1) :=
                        Finset.mem_union.mp (orIn_or_union hr2len hr2op ▸ hz2)
                      rcases fin2_or ba with rfl | rfl
                      · rw [hbaEmpty] at hz2U
                        rcases hz2U with h0 | h1
                        · exact False.elim (Finset.notMem_empty z2 h0)
                        · exact ⟨z2, h1⟩
                      · rw [hbaEmpty] at hz2U
                        rcases hz2U with h0 | h1
                        · exact ⟨z2, h0⟩
                        · exact False.elim (Finset.notMem_empty z2 h1)
                    obtain ⟨bb, hbb⟩ := hReachOpnd jb0 hjb0 hr2jb
                    by_cases hbbEq : bb = ba
                    · rw [hbbEq] at hbb
                      have hgeN : nv ≤ opnd C r2 ba := (orReaches_def C _ _ ▸ hba).1
                      let k := opnd C r2 ba - nv
                      have hweq : opnd C r2 ba = nv + k := by omega
                      have hkr2 : k < r2 := by have := opndBound hr2len ba; omega
                      have hklen : k < C.gates.length := by omega
                      rw [hweq] at hba hbb hbaEmpty
                      rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
                      · have hkja : k = ja0 := by
                          rcases ((orReaches_iff k ja0).mp hba).2 with h | ⟨hop, _, _, _, _⟩
                          · exact h.symm
                          · rw [hkand] at hop; exact False.elim (GateOp.noConfusion hop)
                        have hkjb : k = jb0 := by
                          rcases ((orReaches_iff k jb0).mp hbb).2 with h | ⟨hop, _, _, _, _⟩
                          · exact h.symm
                          · rw [hkand] at hop; exact False.elim (GateOp.noConfusion hop)
                        exact hjbNe (hkjb.symm.trans hkja)
                      · have hknb : ¬ BelowF G C k := fun hkb => junkNotBelow hja0 (fun x hx =>
                          hkb x (orStep_up List.length_ofFn (orReaches_reach ja0 (nv + k) hba).1 (gateVal_eq_val C ja0 x ▸ hx)))
                        have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
                        have hkNotLam : k ∉ lam G C := by
                          intro hkl
                          obtain ⟨_, hne0, _, _⟩ := (lam_mem C k).mp hkl
                          obtain ⟨v0, hv0⟩ := hne0
                          have hv0k : v0 ∈ orIn nv C (nv + k) := by rw [orIn_or_union hklen hkor]; exact Finset.mem_union_left _ hv0
                          rw [hbaEmpty] at hv0k; exact Finset.notMem_empty v0 hv0k
                        have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkN, hkNotLam⟩
                        rw [hRset] at hm
                        rcases Finset.mem_insert.mp hm with hkr1 | hm'
                        · rw [hkr1] at hbaEmpty; rw [hbaEmpty] at hz1; exact Finset.notMem_empty z1 hz1
                        · have := Finset.mem_singleton.mp hm'; omega
                    · rw [fin2_ne_eq ba bb hbbEq] at hbb
                      obtain ⟨m, hmR, hbm, hmj, _⟩ := noncentreless_witness hjb0 hbb hOtherNe
                      have hlt : nv + m < nv + r2 := lt_of_le_of_lt (orReaches_le hbm) (opndBound hr2len (1 - ba))
                      rw [hRset] at hmR
                      rcases Finset.mem_insert.mp hmR with rfl | hm'
                      · exact hjbNe (hR1uniqJ jb0 hjb0 hmj)
                      · have := Finset.mem_singleton.mp hm'; omega
                  refine hCardLe2_contra Ur1 Ur2a ?_ hUr1_le1 hUr2a_le1
                  intro e he
                  rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨h3, _⟩ | ⟨h4, _⟩
                  · exact Finset.mem_union_left _ h1
                  · exact Finset.mem_union_right _ h2
                  · exact False.elim (hr2NoJb h3)
                  · exact False.elim (hr2NoJb h4)
              · refine hCardLe2_contra Ur1 (Ur2b ∪ Uboth) ?_ hUr1_le1 hJbUnion_le1
                intro e he
                rcases hEdgeClass e he with h1 | ⟨h2, _, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                · exact Finset.mem_union_left _ h1
                · exact False.elim (hr2ja h2)
                · exact Finset.mem_union_right _ (Finset.mem_union_left _ h3)
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ h4)
            · have hJaLtJb : ja0 < jb0 := by omega
              have hJaOpnd : ∀ b : Fin 2, ∃ S : Finset (Fin nv), LamOrSing S ∧
                  ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C ja0 b) = true ↔ ∃ v ∈ S, x v = true := by
                intro b
                rcases hWireVal_below r1 hBnd1 ja0 b (le_of_lt hja0lt) hjalen hjaop with h1 | ⟨j', hj', hj'lt, _⟩
                · exact h1
                · rcases hJ_cases j' hj' with rfl | rfl <;> omega
              obtain ⟨Aa, hAaL, hAav⟩ := hJaOpnd 0
              obtain ⟨Ba, hBaL, hBav⟩ := hJaOpnd 1
              have hJaVal : ∀ x : Fin nv → Bool, gateVal nv C ja0 x = true ↔
                  (∃ a ∈ Aa, x a = true) ∧ (∃ b ∈ Ba, x b = true) := fun x => by
                rw [andValBoth hjalen hjaop, hAav x, hBav x]
              let UjaAll := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ gateVal nv C ja0 (pairInput u v) = true)
              have hUjaAll_le1_of : (∃ u1 v1 : Fin nv, s(u1, v1) ∈ Ustar G C ∧
                  gateVal nv C ja0 (pairInput u1 v1) = true ∧
                  ∀ x : Fin nv → Bool, x v1 = true → gateVal nv C ja0 x = true → graphFun G ∅ x = true) →
                  UjaAll.card ≤ 1 := by
                rintro ⟨u1, v1, he1U, hja1, hSound1⟩
                apply Finset.card_le_one.mpr
                intro eA heA eB heB
                obtain ⟨heAU, uA, vA, rfl, hjaA⟩ := Finset.mem_filter.mp heA
                obtain ⟨heBU, uB, vB, rfl, hjaB⟩ := Finset.mem_filter.mp heB
                have hA := hPairJunk_uniq ja0 Aa Ba hja0 hAaL hBaL hJaVal u1 v1 he1U hja1 hSound1 uA vA heAU hjaA
                have hB := hPairJunk_uniq ja0 Aa Ba hja0 hAaL hBaL hJaVal u1 v1 he1U hja1 hSound1 uB vB heBU hjaB
                exact hA.symm.trans hB
              by_cases hr2jb : OrReaches nv C (nv + r2) jb0
              · have hjbLtR2 : jb0 < r2 := by
                  have hle := orReaches_le hr2jb
                  have hne : jb0 ≠ r2 := fun h => by rw [h, hr2op] at hjb0op; exact GateOp.noConfusion hjb0op
                  omega
                have hJbOpndClass : ∀ b : Fin 2,
                    opnd C jb0 b = nv + ja0 ∨
                    ∃ (S : Finset (Fin nv)) (u : Bool), LamOrSing S ∧
                      ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C jb0 b) = true ↔
                        (if u then gateVal nv C ja0 x = true else False) ∨ (∃ v ∈ S, x v = true) := by
                  intro b
                  let w := opnd C jb0 b
                  have hwlt : w < nv + jb0 := opndBound hjb0len b
                  by_cases hwn : w < nv
                  · right
                    refine ⟨{⟨w, hwn⟩}, false, Or.inl ⟨⟨w, hwn⟩, rfl⟩, fun x => ?_⟩
                    change val C (List.ofFn x) w = true ↔ False ∨ ∃ v ∈ ({⟨w, hwn⟩} : Finset (Fin nv)), x v = true
                    rw [false_or, val_ofFn C x ⟨w, hwn⟩]
                    constructor
                    · intro h; exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _, h⟩
                    · rintro ⟨v, hv, hxv⟩; exact (Finset.mem_singleton.mp hv) ▸ hxv
                  · let k := w - nv
                    have hweq : w = nv + k := by omega
                    have hklt : k < jb0 := by omega
                    have hklen : k < C.gates.length := by omega
                    have hknb : ¬ BelowF G C k := fun hkb =>
                      not_belowF_inCone_and hklen hkb hjb0len hjb0op ((inCone_iff k jb0).mpr ⟨hjb0len, k, hklt, hweq ▸ opndMem hjb0len b, Or.inl rfl⟩)
                    rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
                    · left
                      have hdirty : ∃ x : Fin nv → Bool, gateVal nv C k x = true ∧ graphFun G ∅ x = false := by
                        by_contra hnone; apply hknb; intro x hx; by_contra hf; exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
                      have hkJ : k ∈ junk G C := (junk_mem C k).mpr ⟨hklen, hkand, hdirty⟩
                      rcases hJ_cases k hkJ with hka | hkb
                      · rw [hka] at hweq; exact hweq
                      · omega
                    · right
                      have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
                      by_cases hkr1 : k = r1
                      · refine ⟨orIn nv C (nv + r1), true, hR1_b1_val.1, fun x => ?_⟩
                        change val C (List.ofFn x) w = true ↔ _
                        rw [hweq, hkr1, if_pos rfl]
                        exact hR1_b1_val.2 x
                      · obtain ⟨_, hLosK, hValK⟩ := hOrBelowR2 (lt_trans hklt hjbLtR2) hkN hkr1
                        rcases hValK with hNoJa | ⟨_, hWithJa⟩
                        · refine ⟨orIn nv C (nv + k), false, hLosK, fun x => ?_⟩
                          change val C (List.ofFn x) w = true ↔ _
                          rw [hweq, if_neg Bool.false_ne_true, false_or]
                          exact hNoJa x
                        · refine ⟨orIn nv C (nv + k), true, hLosK, fun x => ?_⟩
                          change val C (List.ofFn x) w = true ↔ _
                          rw [hweq, if_pos rfl]
                          exact hWithJa x
                by_cases hHasJaOpnd : opnd C jb0 0 = nv + ja0 ∨ opnd C jb0 1 = nv + ja0
                · obtain ⟨b0, hb0eq⟩ : ∃ b0 : Fin 2, opnd C jb0 b0 = nv + ja0 :=
                    hHasJaOpnd.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
                  have hJbImpJa : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true → gateVal nv C ja0 x = true := by
                    intro x hjb
                    have := ((andValOperands hjb0len hjb0op x).mp hjb) b0
                    rw [hb0eq, ← gateVal_eq_val] at this
                    exact this
                  have hOtherS : ∃ S1 : Finset (Fin nv), LamOrSing S1 ∧
                      ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C jb0 (1 - b0)) = true ↔ ∃ v ∈ S1, x v = true := by
                    rcases hJbOpndClass (1 - b0) with hEqJa | ⟨S1, u1, hS1L, hS1v⟩
                    · exfalso
                      apply replace_gate_by_wire jb0 (nv + ja0) hjb0len (by omega)
                      intro x
                      apply Bool.eq_iff_iff.mpr
                      rw [andValOperands hjb0len hjb0op]
                      constructor
                      · intro h idx
                        by_cases hidx : idx = b0
                        · rw [hidx, hb0eq]; exact h
                        · rw [fin2_ne_eq b0 idx hidx, hEqJa]; exact h
                      · intro h; have := h b0; rw [hb0eq] at this; exact this
                    · cases u1 with
                      | false =>
                        exact ⟨S1, hS1L, fun x => by have := hS1v x; rw [if_neg Bool.false_ne_true, false_or] at this; exact this⟩
                      | true =>
                        exfalso
                        apply replace_gate_by_wire jb0 (nv + ja0) hjb0len (by omega)
                        intro x
                        apply Bool.eq_iff_iff.mpr
                        rw [andValOperands hjb0len hjb0op]
                        constructor
                        · intro h idx
                          by_cases hidx : idx = b0
                          · rw [hidx, hb0eq]; exact h
                          · rw [fin2_ne_eq b0 idx hidx]
                            exact (hS1v x).mpr (Or.inl (by rw [if_pos rfl, gateVal_eq_val]; exact h))
                        · intro h; have := h b0; rw [hb0eq] at this; exact this
                  obtain ⟨S1, hS1L, hS1v⟩ := hOtherS
                  let Fsb := insert S1 Fsa
                  have hFsbL : ∀ S ∈ Fsb, LamOrSing S := fun S hS =>
                    (Finset.mem_insert.mp hS).elim (fun h => h ▸ hS1L) (hFsaL S)
                  have hFsbv : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true ↔ setsEval Fsb x := fun x => by
                    rw [andValOperands hjb0len hjb0op]
                    constructor
                    · intro h S hS
                      rcases Finset.mem_insert.mp hS with rfl | hSa
                      · exact (hS1v x).mp (h (1 - b0))
                      · have hja := h b0; rw [hb0eq, ← gateVal_eq_val] at hja; exact (hFsav x).mp hja S hSa
                    · intro h idx
                      by_cases hidx : idx = b0
                      · rw [hidx, hb0eq, ← gateVal_eq_val]
                        exact (hFsav x).mpr (fun S hSa => h S (Finset.mem_insert_of_mem hSa))
                      · rw [fin2_ne_eq b0 idx hidx]
                        exact (hS1v x).mpr (h S1 (Finset.mem_insert_self S1 Fsa))
                  have hAllInUja : Ustar G C ⊆ UjaAll := by
                    intro e he
                    rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                    · obtain ⟨_, u, v, rfl, _, _, hfs, _⟩ := Finset.mem_filter.mp h1
                      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, (hFsav _).mpr hfs⟩
                    · obtain ⟨_, u, v, rfl, _, _, hfs, _⟩ := Finset.mem_filter.mp h2
                      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, (hFsav _).mpr hfs⟩
                    · obtain ⟨_, u, v, rfl, _, _, hjb, _⟩ := Finset.mem_filter.mp h3
                      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, hJbImpJa _ hjb⟩
                    · obtain ⟨_, u, v, rfl, hja, _, _⟩ := Finset.mem_filter.mp h4
                      exact Finset.mem_filter.mpr ⟨he, u, v, rfl, hja⟩
                  by_cases hVSound : ∃ u1 v1 : Fin nv, s(u1, v1) ∈ Ustar G C ∧
                      gateVal nv C ja0 (pairInput u1 v1) = true ∧
                      ∀ x : Fin nv → Bool, x v1 = true → gateVal nv C ja0 x = true → graphFun G ∅ x = true
                  · have hle1 := hUjaAll_le1_of hVSound
                    have := Finset.card_le_card hAllInUja; omega
                  · have hUr1Emp : Ur1 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e he => by
                      obtain ⟨heU, u, v, rfl, _, _, hfs, hS⟩ := Finset.mem_filter.mp he
                      exact hVSound ⟨u, v, heU, (hFsav _).mpr hfs, fun x hxv hja => hS x hxv ((hFsav x).mp hja)⟩)
                    have hUr2aEmp : Ur2a = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e he => by
                      obtain ⟨heU, u, v, rfl, _, _, hfs, hS⟩ := Finset.mem_filter.mp he
                      exact hVSound ⟨u, v, heU, (hFsav _).mpr hfs, fun x hxv hja => hS x hxv ((hFsav x).mp hja)⟩)
                    have hUr2b_le1 : Ur2b.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                      obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hjbA, _⟩ := Finset.mem_filter.mp heA
                      obtain ⟨heBU, uB, vB, rfl, hzvB, _, hjbB, hSB⟩ := Finset.mem_filter.mp heB
                      exact hMono_underZ_uniq Fsb hFsbL z2 uA vA uB vB heAU heBU hzvA hzvB huAne
                        ((hFsbv _).mp hjbA) ((hFsbv _).mp hjbB) (fun x hxv hfs => hSB x hxv ((hFsbv x).mpr hfs)))
                    have hUboth_le1 : Uboth.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                      obtain ⟨heAU, uA, vA, rfl, _, hjbA, hGlob⟩ := Finset.mem_filter.mp heA
                      obtain ⟨heBU, uB, vB, rfl, _, hjbB, _⟩ := Finset.mem_filter.mp heB
                      exact hMono_global_uniq Fsb hFsbL
                        (fun x hfs => hGlob x (hJbImpJa x ((hFsbv x).mpr hfs)) ((hFsbv x).mpr hfs))
                        uA vA uB vB heAU heBU ((hFsbv _).mp hjbA) ((hFsbv _).mp hjbB))
                    refine hCardLe2_contra Ur2b Uboth ?_ hUr2b_le1 hUboth_le1
                    intro e he
                    rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                    · rw [hUr1Emp] at h1; exact False.elim (Finset.notMem_empty e h1)
                    · rw [hUr2aEmp] at h2; exact False.elim (Finset.notMem_empty e h2)
                    · exact Finset.mem_union_left _ h3
                    · exact Finset.mem_union_right _ h4
                · have hOpnd0 : ∃ (S0 : Finset (Fin nv)) (u0 : Bool), LamOrSing S0 ∧
                      ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C jb0 0) = true ↔
                        (if u0 then gateVal nv C ja0 x = true else False) ∨ (∃ v ∈ S0, x v = true) :=
                    (hJbOpndClass 0).resolve_left (fun h => hHasJaOpnd (Or.inl h))
                  have hOpnd1 : ∃ (S1 : Finset (Fin nv)) (u1 : Bool), LamOrSing S1 ∧
                      ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C jb0 1) = true ↔
                        (if u1 then gateVal nv C ja0 x = true else False) ∨ (∃ v ∈ S1, x v = true) :=
                    (hJbOpndClass 1).resolve_left (fun h => hHasJaOpnd (Or.inr h))
                  obtain ⟨S0, u0, hS0L, hS0v⟩ := hOpnd0
                  obtain ⟨S1, u1, hS1L, hS1v⟩ := hOpnd1
                  let Fs01 : Finset (Finset (Fin nv)) := {S0, S1}
                  have hFs01L : ∀ S ∈ Fs01, LamOrSing S := fun S hS => by
                    rcases Finset.mem_insert.mp hS with rfl | hS'
                    · exact hS0L
                    · exact (Finset.mem_singleton.mp hS') ▸ hS1L
                  have hFs01_imp_jb : ∀ x : Fin nv → Bool, setsEval Fs01 x → gateVal nv C jb0 x = true := fun x hx => by
                    rw [andValBoth hjb0len hjb0op]
                    exact ⟨(hS0v x).mpr (Or.inr (hx S0 (Finset.mem_insert_self S0 {S1}))),
                           (hS1v x).mpr (Or.inr (hx S1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self S1))))⟩
                  have hJb_imp_or : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true →
                      setsEval Fs01 x ∨ gateVal nv C ja0 x = true := fun x hjb => by
                    by_cases hja : gateVal nv C ja0 x = true
                    · exact Or.inr hja
                    · left
                      obtain ⟨h0, h1⟩ := (andValBoth hjb0len hjb0op x).mp hjb
                      have hs0 : ∃ v ∈ S0, x v = true := by
                        rcases (hS0v x).mp h0 with h | h
                        · cases u0 with
                          | true => rw [if_pos rfl] at h; exact False.elim (hja h)
                          | false => rw [if_neg Bool.false_ne_true] at h; exact False.elim h
                        · exact h
                      have hs1 : ∃ v ∈ S1, x v = true := by
                        rcases (hS1v x).mp h1 with h | h
                        · cases u1 with
                          | true => rw [if_pos rfl] at h; exact False.elim (hja h)
                          | false => rw [if_neg Bool.false_ne_true] at h; exact False.elim h
                        · exact h
                      intro S hS
                      rcases Finset.mem_insert.mp hS with rfl | hS'
                      · exact hs0
                      · rw [Finset.mem_singleton.mp hS']; exact hs1
                  let Ur2S01 := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
                    setsEval Fs01 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fs01 x → graphFun G ∅ x = true)
                  have hUr2S01_le1 : Ur2S01.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                    obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
                    obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
                    exact hMono_underZ_uniq Fs01 hFs01L z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
                  by_cases hVSound : ∃ u1 v1 : Fin nv, s(u1, v1) ∈ Ustar G C ∧
                      gateVal nv C ja0 (pairInput u1 v1) = true ∧
                      ∀ x : Fin nv → Bool, x v1 = true → gateVal nv C ja0 x = true → graphFun G ∅ x = true
                  · refine hCardLe2_contra Ur2S01 UjaAll ?_ hUr2S01_le1 (hUjaAll_le1_of hVSound)
                    intro e he
                    rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                    · obtain ⟨_, u, v, rfl, _, _, hfs, _⟩ := Finset.mem_filter.mp h1
                      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, (hFsav _).mpr hfs⟩)
                    · obtain ⟨_, u, v, rfl, _, _, hfs, _⟩ := Finset.mem_filter.mp h2
                      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, (hFsav _).mpr hfs⟩)
                    · obtain ⟨_, u, v, rfl, hzv, hne, hjb, hS⟩ := Finset.mem_filter.mp h3
                      rcases hJb_imp_or _ hjb with h01 | hja
                      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, h01,
                          fun x hxv hfs => hS x hxv (hFs01_imp_jb x hfs)⟩)
                      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hja⟩)
                    · obtain ⟨_, u, v, rfl, hja, _, _⟩ := Finset.mem_filter.mp h4
                      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hja⟩)
                  · have hUr1Emp : Ur1 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e he => by
                      obtain ⟨heU, u, v, rfl, _, _, hfs, hS⟩ := Finset.mem_filter.mp he
                      exact hVSound ⟨u, v, heU, (hFsav _).mpr hfs, fun x hxv hja => hS x hxv ((hFsav x).mp hja)⟩)
                    have hUr2aEmp : Ur2a = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e he => by
                      obtain ⟨heU, u, v, rfl, _, _, hfs, hS⟩ := Finset.mem_filter.mp he
                      exact hVSound ⟨u, v, heU, (hFsav _).mpr hfs, fun x hxv hja => hS x hxv ((hFsav x).mp hja)⟩)
                    have hOneTrue : ∀ (Skeep : Finset (Fin nv)), LamOrSing Skeep →
                        (∀ x : Fin nv → Bool, gateVal nv C jb0 x = true → ∃ v ∈ Skeep, x v = true) →
                        (∀ x : Fin nv → Bool, gateVal nv C ja0 x = true → (∃ v ∈ Skeep, x v = true) → gateVal nv C jb0 x = true) →
                        False := by
                      intro Skeep hSkL hJbImpSk hJaSkImpJb
                      let FsAk := insert Skeep Fsa
                      have hFsAkL : ∀ S ∈ FsAk, LamOrSing S := fun S hS =>
                        (Finset.mem_insert.mp hS).elim (fun h => h ▸ hSkL) (hFsaL S)
                      have hFsAk_imp : ∀ x : Fin nv → Bool, setsEval FsAk x →
                          gateVal nv C ja0 x = true ∧ gateVal nv C jb0 x = true := fun x hx => by
                        have hja : gateVal nv C ja0 x = true := (hFsav x).mpr (fun S hS => hx S (Finset.mem_insert_of_mem hS))
                        have hsk : ∃ v ∈ Skeep, x v = true := hx Skeep (Finset.mem_insert_self Skeep Fsa)
                        exact ⟨hja, hJaSkImpJb x hja hsk⟩
                      have hMkFsAk : ∀ x : Fin nv → Bool, gateVal nv C ja0 x = true → gateVal nv C jb0 x = true →
                          setsEval FsAk x := fun x hja hjb S hS => by
                        rcases Finset.mem_insert.mp hS with rfl | hSa
                        · exact hJbImpSk x hjb
                        · exact (hFsav x).mp hja S hSa
                      by_cases hBothNe : Uboth.Nonempty
                      · obtain ⟨eb, heb⟩ := hBothNe
                        obtain ⟨_, _, _, _, _, _, hGlob⟩ := Finset.mem_filter.mp heb
                        let Uak := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ setsEval FsAk (pairInput u v))
                        have hUak_le1 : Uak.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                          obtain ⟨heAU, uA, vA, rfl, hFA⟩ := Finset.mem_filter.mp heA
                          obtain ⟨heBU, uB, vB, rfl, hFB⟩ := Finset.mem_filter.mp heB
                          exact hMono_global_uniq FsAk hFsAkL
                            (fun x hx => hGlob x (hFsAk_imp x hx).1 (hFsAk_imp x hx).2)
                            uA vA uB vB heAU heBU hFA hFB)
                        refine hCardLe2_contra Ur2S01 Uak ?_ hUr2S01_le1 hUak_le1
                        intro e he
                        rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                        · rw [hUr1Emp] at h1; exact False.elim (Finset.notMem_empty e h1)
                        · rw [hUr2aEmp] at h2; exact False.elim (Finset.notMem_empty e h2)
                        · obtain ⟨_, u, v, rfl, hzv, hne, hjb, hS⟩ := Finset.mem_filter.mp h3
                          rcases hJb_imp_or _ hjb with h01 | hja
                          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, h01,
                              fun x hxv hfs => hS x hxv (hFs01_imp_jb x hfs)⟩)
                          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hMkFsAk _ hja hjb⟩)
                        · obtain ⟨_, u, v, rfl, hja, hjb, _⟩ := Finset.mem_filter.mp h4
                          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hMkFsAk _ hja hjb⟩)
                      · have hBothEmp : Uboth = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBothNe
                        let UakZ := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
                          setsEval FsAk (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval FsAk x → graphFun G ∅ x = true)
                        have hUakZ_le1 : UakZ.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                          obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
                          obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
                          exact hMono_underZ_uniq FsAk hFsAkL z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
                        refine hCardLe2_contra Ur2S01 UakZ ?_ hUr2S01_le1 hUakZ_le1
                        intro e he
                        rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                        · rw [hUr1Emp] at h1; exact False.elim (Finset.notMem_empty e h1)
                        · rw [hUr2aEmp] at h2; exact False.elim (Finset.notMem_empty e h2)
                        · obtain ⟨_, u, v, rfl, hzv, hne, hjb, hS⟩ := Finset.mem_filter.mp h3
                          rcases hJb_imp_or _ hjb with h01 | hja
                          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, h01,
                              fun x hxv hfs => hS x hxv (hFs01_imp_jb x hfs)⟩)
                          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, hMkFsAk _ hja hjb,
                              fun x hxv hfs => hS x hxv (hFsAk_imp x hfs).2⟩)
                        · rw [hBothEmp] at h4; exact False.elim (Finset.notMem_empty e h4)
                    cases u0 with
                    | true =>
                      cases u1 with
                      | true =>
                        have hJaImpJb : ∀ x : Fin nv → Bool, gateVal nv C ja0 x = true → gateVal nv C jb0 x = true := fun x hja => by
                          rw [andValBoth hjb0len hjb0op]
                          exact ⟨(hS0v x).mpr (Or.inl (by rw [if_pos rfl]; exact hja)),
                                 (hS1v x).mpr (Or.inl (by rw [if_pos rfl]; exact hja))⟩
                        have hAll01 : Ustar G C ⊆ Ur2S01 := by
                          intro e he
                          rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                          · rw [hUr1Emp] at h1; exact False.elim (Finset.notMem_empty e h1)
                          · rw [hUr2aEmp] at h2; exact False.elim (Finset.notMem_empty e h2)
                          · obtain ⟨_, u, v, rfl, hzv, hne, hjb, hS⟩ := Finset.mem_filter.mp h3
                            rcases hJb_imp_or _ hjb with h01 | hja
                            · exact Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, h01,
                                fun x hxv hfs => hS x hxv (hFs01_imp_jb x hfs)⟩
                            · exact False.elim (hVSound ⟨u, v, he, hja, fun x hxv hja' => hS x hxv (hJaImpJb x hja')⟩)
                          · obtain ⟨_, _, _, _, _, _, hGlob⟩ := Finset.mem_filter.mp h4
                            exact False.elim (junkNotBelow hja0 (fun x hja => hGlob x hja (hJaImpJb x hja)))
                        have := Finset.card_le_card hAll01; omega
                      | false =>
                        exact hOneTrue S1 hS1L
                          (fun x hjb => by
                            have h1 := ((andValBoth hjb0len hjb0op x).mp hjb).2
                            have h1' := (hS1v x).mp h1
                            rw [if_neg Bool.false_ne_true, false_or] at h1'; exact h1')
                          (fun x hja hs1 => by
                            rw [andValBoth hjb0len hjb0op]
                            exact ⟨(hS0v x).mpr (Or.inl (by rw [if_pos rfl]; exact hja)), (hS1v x).mpr (Or.inr hs1)⟩)
                    | false =>
                      cases u1 with
                      | true =>
                        exact hOneTrue S0 hS0L
                          (fun x hjb => by
                            have h0 := ((andValBoth hjb0len hjb0op x).mp hjb).1
                            have h0' := (hS0v x).mp h0
                            rw [if_neg Bool.false_ne_true, false_or] at h0'; exact h0')
                          (fun x hja hs0 => by
                            rw [andValBoth hjb0len hjb0op]
                            exact ⟨(hS0v x).mpr (Or.inr hs0), (hS1v x).mpr (Or.inl (by rw [if_pos rfl]; exact hja))⟩)
                      | false =>
                        have hJbEq01 : ∀ x : Fin nv → Bool, gateVal nv C jb0 x = true ↔ setsEval Fs01 x := fun x => by
                          constructor
                          · intro hjb
                            obtain ⟨h0, h1⟩ := (andValBoth hjb0len hjb0op x).mp hjb
                            have h0' := (hS0v x).mp h0; rw [if_neg Bool.false_ne_true, false_or] at h0'
                            have h1' := (hS1v x).mp h1; rw [if_neg Bool.false_ne_true, false_or] at h1'
                            intro S hS
                            rcases Finset.mem_insert.mp hS with rfl | hS'
                            · exact h0'
                            · rw [Finset.mem_singleton.mp hS']; exact h1'
                          · exact hFs01_imp_jb x
                        have hUboth_le1 : Uboth.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
                          obtain ⟨heAU, uA, vA, rfl, hjaA, hjbA, hGlob⟩ := Finset.mem_filter.mp heA
                          obtain ⟨heBU, uB, vB, rfl, hjaB, hjbB, _⟩ := Finset.mem_filter.mp heB
                          have hUnL : ∀ S ∈ Fsa ∪ Fs01, LamOrSing S := fun S hS =>
                            (Finset.mem_union.mp hS).elim (hFsaL S) (hFs01L S)
                          have hUnEv : ∀ x : Fin nv → Bool, setsEval (Fsa ∪ Fs01) x ↔
                              gateVal nv C ja0 x = true ∧ gateVal nv C jb0 x = true := fun x => by
                            rw [hFsav x, hJbEq01 x]
                            constructor
                            · intro h; exact ⟨fun S hS => h S (Finset.mem_union_left Fs01 hS),
                                fun S hS => h S (Finset.mem_union_right Fsa hS)⟩
                            · rintro ⟨h1, h2⟩ S hS; exact (Finset.mem_union.mp hS).elim (h1 S) (h2 S)
                          exact hMono_global_uniq (Fsa ∪ Fs01) hUnL
                            (fun x hx => hGlob x ((hUnEv x).mp hx).1 ((hUnEv x).mp hx).2)
                            uA vA uB vB heAU heBU ((hUnEv _).mpr ⟨hjaA, hjbA⟩) ((hUnEv _).mpr ⟨hjaB, hjbB⟩))
                        refine hCardLe2_contra Ur2S01 Uboth ?_ hUr2S01_le1 hUboth_le1
                        intro e he
                        rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
                        · rw [hUr1Emp] at h1; exact False.elim (Finset.notMem_empty e h1)
                        · rw [hUr2aEmp] at h2; exact False.elim (Finset.notMem_empty e h2)
                        · obtain ⟨_, u, v, rfl, hzv, hne, hjb, hS⟩ := Finset.mem_filter.mp h3
                          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, (hJbEq01 _).mp hjb,
                            fun x hxv hfs => hS x hxv (hFs01_imp_jb x hfs)⟩)
                        · exact Finset.mem_union_right _ h4
              · refine hCardLe2_contra Ur1 Ur2a ?_ hUr1_le1 hUr2a_le1
                intro e he
                rcases hEdgeClass e he with h1 | ⟨_, h2, _⟩ | ⟨h3, _⟩ | ⟨h4, _⟩
                · exact Finset.mem_union_left _ h1
                · exact Finset.mem_union_right _ h2
                · exact False.elim (hr2jb h3)
                · exact False.elim (hr2jb h4)
        · have hNoJunkBelowR2 : ∀ k : ℕ, k < r2 → k ∈ orN G C → ∀ j' ∈ junk G C, ¬ OrReaches nv C (nv + k) j' := by
            intro k hkr2 hkN j' hj' hkj'
            by_cases hkr1 : k = r1
            · exact hr1HasJ ⟨j', hj', hkr1 ▸ hkj'⟩
            · have hkLam : k ∈ lam G C := by
                by_contra hnl
                have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkN, hnl⟩
                rw [hRset] at hm
                rcases Finset.mem_insert.mp hm with rfl | hm'
                · exact hkr1 rfl
                · have := Finset.mem_singleton.mp hm'; omega
              obtain ⟨hklen, hkor, _⟩ := (orN_mem C k).mp hkN
              have hkne : (orIn nv C (nv + k)).Nonempty := by
                obtain ⟨_, hne0, _, _⟩ := (lam_mem C k).mp hkLam
                obtain ⟨v0, hv0⟩ := hne0
                exact ⟨v0, by rw [orIn_or_union hklen hkor]; exact Finset.mem_union_left _ hv0⟩
              obtain ⟨m, hmR, hkm, hmj', _⟩ := noncentreless_witness hj' hkj' hkne
              have hle := orReaches_le hkm
              rw [hRset] at hmR
              rcases Finset.mem_insert.mp hmR with rfl | hm'
              · exact hr1HasJ ⟨j', hj', hmj'⟩
              · have := Finset.mem_singleton.mp hm'; omega
          have hBelowR2_noJ_ne : ∀ w : ℕ, w < nv + r2 → (orIn nv C w).Nonempty →
              ∀ j' ∈ junk G C, ¬ OrReaches nv C w j' := by
            intro w hw hne j' hj' hwj
            have hgeN : nv ≤ w := (orReaches_def C w j' ▸ hwj).1
            let k := w - nv
            have hweq : w = nv + k := by omega
            have hklt : k < r2 := by omega
            have hklen : k < C.gates.length := by omega
            rw [hweq] at hwj hne
            have hkor : (gateAt C k).op = GateOp.or := by
              rcases hLeast.1.1 _ (gateAt_mem hklen) with hand | hor
              · rw [andRawEmpty hand] at hne; exact False.elim (Finset.not_nonempty_empty hne)
              · exact hor
            have hknb : ¬ BelowF G C k := fun hkb => junkNotBelow hj' (fun x hx =>
              hkb x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k) hwj).1 (gateVal_eq_val C j' x ▸ hx)))
            exact hNoJunkBelowR2 k hklt ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) j' hj' hwj
          have hOrValBelowR2 : ∀ {k : ℕ}, k < r2 → k ∈ orN G C → k ≠ r1 →
              LamOrSing (orIn nv C (nv + k)) ∧
              ∀ x : Fin nv → Bool, val C (List.ofFn x) (nv + k) = true ↔ ∃ v ∈ orIn nv C (nv + k), x v = true := by
            intro k hkr2 hkN hkr1
            obtain ⟨hklen, hkor, hknb⟩ := (orN_mem C k).mp hkN
            have hkLam : k ∈ lam G C := by
              by_contra hnl
              have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkN, hnl⟩
              rw [hRset] at hm
              rcases Finset.mem_insert.mp hm with rfl | hm'
              · exact hkr1 rfl
              · have := Finset.mem_singleton.mp hm'; omega
            refine ⟨Or.inr ⟨k, hkLam, rfl⟩, fun x => ?_⟩
            constructor
            · intro hv
              obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (nv + k) hv
              rcases hcase with hlt' | ⟨h, hh, rfl, hneOr⟩
              · refine ⟨⟨w', hlt'⟩, reach_mem_orIn ⟨w', hlt'⟩ hpath, ?_⟩
                rw [← val_ofFn C x ⟨w', hlt'⟩]; exact hvw'
              · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
                have hhJ := hOrReach_and_junk hklen hknb hkor hh hhand hpath
                exact False.elim (hNoJunkBelowR2 k hkr2 hkN h hhJ (reach_orReaches hpath h rfl hh))
            · rintro ⟨v, hv, hxv⟩
              exact reach_var_val x (nv + k) v (mem_orIn_reach v hv) hxv
          have hR1OpndVal : ∀ b : Fin 2, ∃ S : Finset (Fin nv), LamOrSing S ∧
              ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C r1 b) = true ↔ ∃ v ∈ S, x v = true := by
            intro b
            let w := opnd C r1 b
            have hwlt : w < nv + r1 := opndBound hr1len b
            by_cases hwn : w < nv
            · refine ⟨{⟨w, hwn⟩}, Or.inl ⟨⟨w, hwn⟩, rfl⟩, fun x => ?_⟩
              change val C (List.ofFn x) w = true ↔ _
              rw [val_ofFn C x ⟨w, hwn⟩]
              constructor
              · intro h; exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _, h⟩
              · rintro ⟨v, hv, hxv⟩; exact (Finset.mem_singleton.mp hv) ▸ hxv
            · let k := w - nv
              have hweq : w = nv + k := by omega
              have hkr1 : k < r1 := by omega
              have hklen : k < C.gates.length := by omega
              have hknb : ¬ BelowF G C k := hOpnd_notBelowF hr1len ((orN_mem C r1).mp hr1N).2.2 hweq
              rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
              · exfalso
                have hdirty : ∃ x : Fin nv → Bool, gateVal nv C k x = true ∧ graphFun G ∅ x = false := by
                  by_contra hnone; apply hknb; intro x hx; by_contra hf; exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
                have hkJ : k ∈ junk G C := (junk_mem C k).mpr ⟨hklen, hkand, hdirty⟩
                have hr1k : OrReaches nv C (nv + r1) k :=
                  (orReaches_iff r1 k).mpr ⟨hr1len, Or.inr ⟨hr1op, nv + k, hweq ▸ opndMem hr1len b, by omega,
                    (orReaches_iff k k).mpr ⟨hklen, Or.inl rfl⟩⟩⟩
                exact hr1HasJ ⟨k, hkJ, hr1k⟩
              · obtain ⟨hLos, hVal⟩ := hOrValBelowR2 (lt_trans hkr1 hr1lt2) ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) (ne_of_lt hkr1)
                exact ⟨orIn nv C (nv + k), hLos, fun x => by change val C (List.ofFn x) w = true ↔ _; rw [hweq]; exact hVal x⟩
          obtain ⟨Sa, hSaL, hSav⟩ := hR1OpndVal 0
          obtain ⟨Sb, hSbL, hSbv⟩ := hR1OpndVal 1
          have hR1Val : ∀ x : Fin nv → Bool, val C (List.ofFn x) (nv + r1) = true ↔
              (∃ v ∈ Sa, x v = true) ∨ (∃ v ∈ Sb, x v = true) := fun x => by
            rw [← gateVal_eq_val, orValOperands hr1len hr1op]
            constructor
            · rintro ⟨b, hb⟩
              rcases fin2_or b with rfl | rfl
              · exact Or.inl ((hSav x).mp hb)
              · exact Or.inr ((hSbv x).mp hb)
            · rintro (ha | hb)
              · exact ⟨0, (hSav x).mpr ha⟩
              · exact ⟨1, (hSbv x).mpr hb⟩
          have hAndBelowR2 : ∀ a : ℕ, a < r2 → a < C.gates.length → (gateAt C a).op = GateOp.and →
              ∃ (Fs : Finset (Finset (Fin nv))) (useR1 : Bool), (∀ S ∈ Fs, LamOrSing S) ∧
                ∀ x : Fin nv → Bool, gateVal nv C a x = true ↔
                  setsEval Fs x ∧ (if useR1 then (∃ v ∈ Sa, x v = true) ∨ (∃ v ∈ Sb, x v = true) else True) := by
            intro a
            induction a using Nat.strong_induction_on with
            | ind a ih =>
              intro har2 halen haop
              have hOp : ∀ b : Fin 2, ∃ (Fs : Finset (Finset (Fin nv))) (u : Bool), (∀ S ∈ Fs, LamOrSing S) ∧
                  ∀ x : Fin nv → Bool, val C (List.ofFn x) (opnd C a b) = true ↔
                    setsEval Fs x ∧ (if u then (∃ v ∈ Sa, x v = true) ∨ (∃ v ∈ Sb, x v = true) else True) := by
                intro b
                let w := opnd C a b
                have hwlt : w < nv + a := opndBound halen b
                by_cases hwn : w < nv
                · refine ⟨{{⟨w, hwn⟩}}, false, fun S hS => (Finset.mem_singleton.mp hS) ▸ Or.inl ⟨⟨w, hwn⟩, rfl⟩, fun x => ?_⟩
                  change val C (List.ofFn x) w = true ↔ _
                  rw [if_neg Bool.false_ne_true, and_true, val_ofFn C x ⟨w, hwn⟩]
                  constructor
                  · intro h S hS; rw [Finset.mem_singleton.mp hS]; exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _, h⟩
                  · intro h; obtain ⟨v, hv, hxv⟩ := h {⟨w, hwn⟩} (Finset.mem_singleton_self _); exact (Finset.mem_singleton.mp hv) ▸ hxv
                · let k := w - nv
                  have hweq : w = nv + k := by omega
                  have hka : k < a := by omega
                  have hklen : k < C.gates.length := by omega
                  have hknb : ¬ BelowF G C k := fun hkb =>
                    not_belowF_inCone_and hklen hkb halen haop ((inCone_iff k a).mpr ⟨halen, k, hka, hweq ▸ opndMem halen b, Or.inl rfl⟩)
                  rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
                  · obtain ⟨Fs', u', hFs'L, hFs'v⟩ := ih k hka (lt_trans hka har2) hklen hkand
                    exact ⟨Fs', u', hFs'L, fun x => by change val C (List.ofFn x) w = true ↔ _; rw [hweq, ← gateVal_eq_val]; exact hFs'v x⟩
                  · by_cases hkr1 : k = r1
                    · refine ⟨∅, true, fun S hS => False.elim (Finset.notMem_empty S hS), fun x => ?_⟩
                      change val C (List.ofFn x) w = true ↔ _
                      rw [hweq, hkr1, if_pos rfl, hR1Val x]
                      exact ⟨fun h => ⟨fun S hS => False.elim (Finset.notMem_empty S hS), h⟩, fun h => h.2⟩
                    · obtain ⟨hLosK, hValK⟩ := hOrValBelowR2 (lt_trans hka har2) ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) hkr1
                      refine ⟨{orIn nv C (nv + k)}, false, fun S hS => (Finset.mem_singleton.mp hS) ▸ hLosK, fun x => ?_⟩
                      change val C (List.ofFn x) w = true ↔ _
                      rw [hweq, if_neg Bool.false_ne_true, and_true, hValK x]
                      exact ⟨fun h S hS => (Finset.mem_singleton.mp hS) ▸ h, fun h => h _ (Finset.mem_singleton_self _)⟩
              obtain ⟨F0, u0, hF0L, hF0v⟩ := hOp 0
              obtain ⟨F1, u1, hF1L, hF1v⟩ := hOp 1
              refine ⟨F0 ∪ F1, u0 || u1, fun S hS => (Finset.mem_union.mp hS).elim (hF0L S) (hF1L S), fun x => ?_⟩
              rw [andValBoth halen haop, hF0v x, hF1v x]
              have hSetUn : setsEval (F0 ∪ F1) x ↔ setsEval F0 x ∧ setsEval F1 x :=
                ⟨fun h => ⟨fun S hS => h S (Finset.mem_union_left F1 hS), fun S hS => h S (Finset.mem_union_right F0 hS)⟩,
                 fun h S hS => (Finset.mem_union.mp hS).elim (h.1 S) (h.2 S)⟩
              rw [hSetUn]
              cases u0 with
              | false =>
                cases u1 with
                | false => simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, and_true]
                | true =>
                  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, and_true]
                  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
              | true =>
                cases u1 with
                | false =>
                  simp only [Bool.true_or, Bool.false_eq_true, ↓reduceIte, and_true]
                  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
                | true =>
                  simp only [Bool.true_or, ↓reduceIte]
                  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
          have hR2uniq : ∃ j1 ∈ junk G C, ∃ z2 ∈ orIn nv C (nv + r2),
              j1 < r2 ∧ ∀ j' ∈ junk G C, OrReaches nv C (nv + r2) j' → j' = j1 := by
            obtain ⟨e0, he0⟩ := hUstarNe
            induction e0 using Sym2.ind with
            | _ u0 v0 =>
              obtain ⟨t0, ht0, _, d0, j1, hj1, ht0d, _⟩ := residualTrace he0
              obtain ⟨m0, hm0R, _, hm0j1, hm0ne⟩ := noncentreless_witness hj1 ht0d (hneSideTop ht0 d0)
              have hm0eq : m0 = r2 := by
                rw [hRset] at hm0R
                rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                · exact False.elim (hr1HasJ ⟨j1, hj1, hm0j1⟩)
                · exact Finset.mem_singleton.mp hm0'
              subst m0
              obtain ⟨z2, hz2⟩ := hm0ne
              have hz2U : z2 ∈ orIn nv C (opnd C r2 0) ∨ z2 ∈ orIn nv C (opnd C r2 1) :=
                Finset.mem_union.mp (orIn_or_union hr2len hr2op ▸ hz2)
              obtain ⟨b2, hb2ne⟩ : ∃ b2 : Fin 2, (orIn nv C (opnd C r2 b2)).Nonempty :=
                hz2U.elim (fun h => ⟨0, ⟨z2, h⟩⟩) (fun h => ⟨1, ⟨z2, h⟩⟩)
              have hNoJ_b2 : ∀ j' ∈ junk G C, ¬ OrReaches nv C (opnd C r2 b2) j' :=
                hBelowR2_noJ_ne (opnd C r2 b2) (opndBound hr2len b2) hb2ne
              have hOpnd_eq : ∀ j' ∈ junk G C, OrReaches nv C (nv + r2) j' → opnd C r2 (1 - b2) = nv + j' := by
                intro j' hj' hr2j'
                obtain ⟨_, hj'op, _⟩ := junkData hj'
                rcases ((orReaches_iff r2 j').mp hr2j').2 with hEq | ⟨_, w, hwin, hwlt, hwj'⟩
                · rw [← hEq, hj'op] at hr2op; exact False.elim (GateOp.noConfusion hr2op)
                · obtain ⟨b, rfl⟩ := inputsAsOpnd hr2len hwin
                  have hbeq : b = 1 - b2 := fin2_ne_eq b2 b (fun h => hNoJ_b2 j' hj' (h ▸ hwj'))
                  rw [hbeq] at hwj' hwlt
                  have hgeN : nv ≤ opnd C r2 (1 - b2) := (orReaches_def C _ _ ▸ hwj').1
                  let k := opnd C r2 (1 - b2) - nv
                  have hweq : opnd C r2 (1 - b2) = nv + k := by omega
                  have hkr2 : k < r2 := by omega
                  have hklen : k < C.gates.length := by omega
                  rw [hweq] at hwj'
                  rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
                  · rcases ((orReaches_iff k j').mp hwj').2 with hkeq | ⟨hkop', _, _, _, _⟩
                    · rw [hweq, hkeq]
                    · rw [hkand] at hkop'; exact False.elim (GateOp.noConfusion hkop')
                  · have hknb : ¬ BelowF G C k := fun hkb => junkNotBelow hj' (fun x hx =>
                      hkb x (orStep_up List.length_ofFn (orReaches_reach j' (nv + k) hwj').1 (gateVal_eq_val C j' x ▸ hx)))
                    exact False.elim (hNoJunkBelowR2 k hkr2 ((orN_mem C k).mpr ⟨hklen, hkor, hknb⟩) j' hj' hwj')
              have h1eq := hOpnd_eq j1 hj1 hm0j1
              have hj1lt : j1 < r2 := by have := opndBound hr2len (1 - b2); omega
              exact ⟨j1, hj1, z2, hz2, hj1lt, fun j' hj' hr2j' => by
                have := (hOpnd_eq j' hj' hr2j').symm.trans h1eq; omega⟩
          obtain ⟨j1, hj1, z2, hz2, hj1lt, hR2uniqJ⟩ := hR2uniq
          obtain ⟨hj1len, hj1op, _⟩ := junkData hj1
          obtain ⟨Fs1, useR1, hFs1L, hFs1v⟩ := hAndBelowR2 j1 hj1lt hj1len hj1op
          have hEdge3A : ∀ e ∈ Ustar G C, ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              gateVal nv C j1 (pairInput u v) = true ∧
              ∀ x : Fin nv → Bool, x v = true → gateVal nv C j1 x = true → graphFun G ∅ x = true := by
            intro e he
            induction e using Sym2.ind with
            | _ p q =>
              obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
              obtain ⟨htlen, htop, htb⟩ := topData ht
              obtain ⟨m0, hm0R, htm0, hm0j', _⟩ := noncentreless_witness hj' htd (hneSideTop ht d)
              have hm0eq : m0 = r2 := by
                rw [hRset] at hm0R
                rcases Finset.mem_insert.mp hm0R with rfl | hm0'
                · exact False.elim (hr1HasJ ⟨j', hj', hm0j'⟩)
                · exact Finset.mem_singleton.mp hm0'
              subst m0
              have hj'eq : j' = j1 := hR2uniqJ j' hj' hm0j'
              subst j'
              have h1dNoJ : ∀ j2 ∈ junk G C, ¬ OrReaches nv C (opnd C t (1 - d)) j2 := by
                intro j2 hj2 h1d
                obtain ⟨m2, hm2R, htm2, hm2j2, _⟩ := noncentreless_witness hj2 h1d (hneSideTop ht (1 - d))
                have hm2eq : m2 = r2 := by
                  rw [hRset] at hm2R
                  rcases Finset.mem_insert.mp hm2R with rfl | hm2'
                  · exact False.elim (hr1HasJ ⟨j2, hj2, hm2j2⟩)
                  · exact Finset.mem_singleton.mp hm2'
                subst m2
                rcases fin2_or d with rfl | rfl
                · exact hNotBothSidesR ht hr2N htm0 htm2
                · exact hNotBothSidesR ht hr2N htm2 htm0
              have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
                ((andValOperands htlen htop _).mp htv) (1 - d)
              obtain ⟨v, hvSide, hvp⟩ : ∃ v ∈ side (n := nv) C t (1 - d), v = p ∨ v = q := by
                rcases operandSupport htlen htop h1dVal with h1 | ⟨j2, hj2, h1d, _⟩
                · exact h1
                · exact False.elim (h1dNoJ j2 hj2 h1d)
              have hz2Side : z2 ∈ side (n := nv) C t d := by rw [side_def]; exact orIn_mono htm0 hz2
              have hzv : G.Adj z2 v := topAdj_side ht hz2Side hvSide
              have hStarZ : s(z2, v) ∈ starEdges G C := side_mem_starEdges ht hz2Side hvSide
              have hFire : ∀ x : Fin nv → Bool, x v = true → gateVal nv C j1 x = true → graphFun G ∅ x = true := by
                intro x hxv hxj
                exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
                  by_cases hidx : idx = d
                  · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j1 _ htd).1 (gateVal_eq_val C j1 x ▸ hxj)
                  · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
              rcases hvp with hvEq | hvEq
              · subst v
                have hqNe : q ≠ z2 := fun h => by
                  subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ)
                exact ⟨q, p, Sym2.eq_swap, hzv, hqNe, pairInput_symm p q ▸ hj'v, hFire⟩
              · subst v
                have hpNe : p ≠ z2 := fun h => by
                  subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ
                exact ⟨p, q, rfl, hzv, hpNe, hj'v, hFire⟩
          cases useR1 with
          | false =>
            have hFs1Eq : ∀ x : Fin nv → Bool, gateVal nv C j1 x = true ↔ setsEval Fs1 x := fun x => by
              have := hFs1v x; rw [if_neg Bool.false_ne_true, and_true] at this; exact this
            have hUle1 : (Ustar G C).card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨uA, vA, rfl, hzvA, huAne, hjA, _⟩ := hEdge3A eA heA
              obtain ⟨uB, vB, rfl, hzvB, _, hjB, hSB⟩ := hEdge3A eB heB
              exact hMono_underZ_uniq Fs1 hFs1L z2 uA vA uB vB heA heB hzvA hzvB huAne
                ((hFs1Eq _).mp hjA) ((hFs1Eq _).mp hjB) (fun x hxv hfs => hSB x hxv ((hFs1Eq x).mpr hfs)))
            omega
          | true =>
            let Fsa1 := insert Sa Fs1
            let Fsb1 := insert Sb Fs1
            have hFsa1L : ∀ S ∈ Fsa1, LamOrSing S := fun S hS => (Finset.mem_insert.mp hS).elim (fun h => h ▸ hSaL) (hFs1L S)
            have hFsb1L : ∀ S ∈ Fsb1, LamOrSing S := fun S hS => (Finset.mem_insert.mp hS).elim (fun h => h ▸ hSbL) (hFs1L S)
            have hJ1Split : ∀ x : Fin nv → Bool, gateVal nv C j1 x = true ↔ setsEval Fsa1 x ∨ setsEval Fsb1 x := fun x => by
              have h := hFs1v x; rw [if_pos rfl] at h; rw [h]
              constructor
              · rintro ⟨hfs, ha | hb⟩
                · left; intro S hS; exact (Finset.mem_insert.mp hS).elim (fun e => e ▸ ha) (hfs S)
                · right; intro S hS; exact (Finset.mem_insert.mp hS).elim (fun e => e ▸ hb) (hfs S)
              · rintro (ha | hb)
                · exact ⟨fun S hS => ha S (Finset.mem_insert_of_mem hS), Or.inl (ha Sa (Finset.mem_insert_self Sa Fs1))⟩
                · exact ⟨fun S hS => hb S (Finset.mem_insert_of_mem hS), Or.inr (hb Sb (Finset.mem_insert_self Sb Fs1))⟩
            let Ua := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              setsEval Fsa1 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fsa1 x → graphFun G ∅ x = true)
            let Ub := (Ustar G C).filter (fun e => ∃ u v : Fin nv, e = s(u, v) ∧ G.Adj z2 v ∧ u ≠ z2 ∧
              setsEval Fsb1 (pairInput u v) ∧ ∀ x : Fin nv → Bool, x v = true → setsEval Fsb1 x → graphFun G ∅ x = true)
            have hUa_le1 : Ua.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fsa1 hFsa1L z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            have hUb_le1 : Ub.card ≤ 1 := Finset.card_le_one.mpr (fun eA heA eB heB => by
              obtain ⟨heAU, uA, vA, rfl, hzvA, huAne, hFA, _⟩ := Finset.mem_filter.mp heA
              obtain ⟨heBU, uB, vB, rfl, hzvB, _, hFB, hSB⟩ := Finset.mem_filter.mp heB
              exact hMono_underZ_uniq Fsb1 hFsb1L z2 uA vA uB vB heAU heBU hzvA hzvB huAne hFA hFB hSB)
            refine hCardLe2_contra Ua Ub ?_ hUa_le1 hUb_le1
            intro e he
            obtain ⟨u, v, rfl, hzv, hne, hj1v, hS⟩ := hEdge3A e he
            rcases (hJ1Split _).mp hj1v with ha | hb
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, ha,
                fun x hxv hfs => hS x hxv ((hJ1Split x).mpr (Or.inl hfs))⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, rfl, hzv, hne, hb,
                fun x hxv hfs => hS x hxv ((hJ1Split x).mpr (Or.inr hfs))⟩)
    exact ⟨hJunkGe2, hUstarGe3, hBudgetGe5⟩
  classical
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro n E π C0 hRect hMatch hAO0 hComp0
  by_cases hn0 : n = 0
  · subst n
    have hE0 : E.card = 0 := Finset.card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_notMem.mpr (fun e _ => Fin.elim0 e.1))
    omega
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
  let nv : ℕ := n + n
  let G : SimpleGraph (Fin nv) :=
    { Adj := fun u v => ∃ a b : Fin n, (a, b) ∈ E ∧
        ((u = Fin.castAdd n a ∧ v = Fin.natAdd n b) ∨ (v = Fin.castAdd n a ∧ u = Fin.natAdd n b))
      symm := ⟨by
        intro u v h
        obtain ⟨a, b, hab, hcases⟩ := h
        exact ⟨a, b, hab, hcases.symm⟩⟩
      loopless := ⟨by
        intro u h
        obtain ⟨a, b, _, hcases⟩ := h
        rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hlt : u.val < n := by rw [h1, Fin.val_castAdd]; exact a.isLt
          have hge : n ≤ u.val := by rw [h2, Fin.val_natAdd]; omega
          omega
        · have hlt : u.val < n := by rw [h1, Fin.val_castAdd]; exact a.isLt
          have hge : n ≤ u.val := by rw [h2, Fin.val_natAdd]; omega
          omega⟩ }
  let col : Fin nv → Bool := fun u => decide (n ≤ u.val)
  have hCol : ∀ u v : Fin nv, G.Adj u v → col u ≠ col v := by
    intro u v h
    obtain ⟨a, b, _, hcases⟩ := h
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 : col (Fin.castAdd n a) = false := decide_eq_false (by rw [Fin.val_castAdd]; have := a.isLt; omega)
      have h2 : col (Fin.natAdd n b) = true := decide_eq_true (by rw [Fin.val_natAdd]; omega)
      rw [h1, h2]; exact Bool.false_ne_true
    · have h1 : col (Fin.natAdd n b) = true := decide_eq_true (by rw [Fin.val_natAdd]; omega)
      have h2 : col (Fin.castAdd n a) = false := decide_eq_false (by rw [Fin.val_castAdd]; have := a.isLt; omega)
      rw [h1, h2]; exact Bool.false_ne_true.symm
  have hNoTri : ∀ a b c : Fin nv, G.Adj a b → G.Adj b c → G.Adj a c → False := by
    intro a b c hab hbc hac
    have h1 := hCol a b hab
    have h2 := hCol b c hbc
    have h3 := hCol a c hac
    cases ha : col a <;> cases hb : col b <;> cases hc : col c
    · rw [ha, hb] at h1; exact h1 rfl
    · rw [ha, hb] at h1; exact h1 rfl
    · rw [ha, hc] at h3; exact h3 rfl
    · rw [hb, hc] at h2; exact h2 rfl
    · rw [hb, hc] at h2; exact h2 rfl
    · rw [ha, hc] at h3; exact h3 rfl
    · rw [ha, hb] at h1; exact h1 rfl
    · rw [ha, hb] at h1; exact h1 rfl
  let mate : Fin nv → Fin nv := fun u =>
    if h : u.val < n then Fin.natAdd n (π ⟨u.val, h⟩)
    else Fin.castAdd n (π.symm ⟨u.val - n, by have := u.isLt; omega⟩)
  have hMateInv : Function.Involutive mate := by
    intro u
    dsimp only [mate]
    by_cases h : u.val < n
    · rw [dif_pos h]
      have h2 : ¬ (Fin.natAdd n (π ⟨u.val, h⟩)).val < n := by rw [Fin.val_natAdd]; omega
      rw [dif_neg h2]
      apply Fin.ext
      rw [Fin.val_castAdd]
      have hsub : (⟨(Fin.natAdd n (π ⟨u.val, h⟩)).val - n, by have := (Fin.natAdd n (π ⟨u.val, h⟩)).isLt; omega⟩ : Fin n) = π ⟨u.val, h⟩ := by
        apply Fin.ext; dsimp only; rw [Fin.val_natAdd]; omega
      rw [hsub, Equiv.symm_apply_apply]
    · rw [dif_neg h]
      have h2 : (Fin.castAdd n (π.symm ⟨u.val - n, by have := u.isLt; omega⟩)).val < n := by
        rw [Fin.val_castAdd]; exact (π.symm _).isLt
      rw [dif_pos h2]
      apply Fin.ext
      rw [Fin.val_natAdd]
      have hsub : (⟨(Fin.castAdd n (π.symm ⟨u.val - n, by have := u.isLt; omega⟩)).val, h2⟩ : Fin n) =
          π.symm ⟨u.val - n, by have := u.isLt; omega⟩ := by
        apply Fin.ext; rw [Fin.val_castAdd]
      rw [hsub, Equiv.apply_symm_apply]
      dsimp only
      omega
  have hMateAdj : ∀ u : Fin nv, G.Adj u (mate u) := by
    intro u
    dsimp only [mate]
    by_cases h : u.val < n
    · rw [dif_pos h]
      exact ⟨⟨u.val, h⟩, π ⟨u.val, h⟩, hMatch _, Or.inl ⟨Fin.ext (by rw [Fin.val_castAdd]), rfl⟩⟩
    · rw [dif_neg h]
      let b : Fin n := ⟨u.val - n, by have := u.isLt; omega⟩
      have hm : (π.symm b, b) ∈ E := by
        have h1 := hMatch (π.symm b)
        rw [Equiv.apply_symm_apply] at h1
        exact h1
      exact ⟨π.symm b, b, hm, Or.inr ⟨rfl, Fin.ext (by rw [Fin.val_natAdd]; dsimp only [b]; omega)⟩⟩
  have hGne : G.edgeFinset.Nonempty := by
    let u0 : Fin nv := Fin.castAdd n ⟨0, hnPos⟩
    exact ⟨s(u0, mate u0), SimpleGraph.mem_edgeFinset.mpr (hMateAdj u0)⟩
  have hGcard : G.edgeFinset.card = E.card := by
    let toE : Fin n × Fin n → Sym2 (Fin nv) := fun p => s(Fin.castAdd n p.1, Fin.natAdd n p.2)
    have hInj : Function.Injective toE := by
      intro p1 p2 heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have h1' : p1.1 = p2.1 := Fin.ext (by have := congrArg Fin.val h1; rw [Fin.val_castAdd, Fin.val_castAdd] at this; exact this)
        have h2' : p1.2 = p2.2 := Fin.ext (by have := congrArg Fin.val h2; rw [Fin.val_natAdd, Fin.val_natAdd] at this; omega)
        exact Prod.ext h1' h2'
      · have hv := congrArg Fin.val h1
        rw [Fin.val_castAdd, Fin.val_natAdd] at hv
        have := p1.1.isLt; omega
    have hImg : E.image toE = G.edgeFinset := by
      apply Finset.ext
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        rw [Finset.mem_image, SimpleGraph.mem_edgeFinset]
        constructor
        · rintro ⟨p, hp, heq⟩
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨p.1, p.2, hp, Or.inl ⟨h1.symm, h2.symm⟩⟩
          · exact ⟨p.1, p.2, hp, Or.inr ⟨h1.symm, h2.symm⟩⟩
        · rintro ⟨a, b, hab, hcases⟩
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨(a, b), hab, rfl⟩
          · exact ⟨(a, b), hab, Sym2.eq_swap⟩
    rw [← hImg, Finset.card_image_of_injective E hInj]
  have hNo4 : NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro w1 hw1 w2 hw2
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    by_contra hne
    obtain ⟨a1, b1, he1, hc1⟩ := h1.1
    obtain ⟨a2, b2, he2, hc2⟩ := h1.2
    obtain ⟨a3, b3, he3, hc3⟩ := h2.1
    obtain ⟨a4, b4, he4, hc4⟩ := h2.2
    rcases hc1 with ⟨hu1, hw1r⟩ | ⟨hw1l, hu1⟩
    · have hw1ge : n ≤ w1.val := by rw [hw1r, Fin.val_natAdd]; omega
      have hvlt : v.val < n := by
        rcases hc2 with ⟨hv2, _⟩ | ⟨hw1l2, _⟩
        · rw [hv2, Fin.val_castAdd]; exact a2.isLt
        · have : w1.val < n := by rw [hw1l2, Fin.val_castAdd]; exact a2.isLt
          omega
      have hv_eq : v = Fin.castAdd n a2 ∧ w1 = Fin.natAdd n b2 := by
        rcases hc2 with h | ⟨hw1l2, _⟩
        · exact h
        · have : w1.val < n := by rw [hw1l2, Fin.val_castAdd]; exact a2.isLt
          omega
      have hu_eq3 : u = Fin.castAdd n a3 ∧ w2 = Fin.natAdd n b3 := by
        rcases hc3 with h | ⟨_, hu3⟩
        · exact h
        · have hlt : u.val < n := by rw [hu1, Fin.val_castAdd]; exact a1.isLt
          have hge : n ≤ u.val := by rw [hu3, Fin.val_natAdd]; omega
          omega
      have hv_eq4 : v = Fin.castAdd n a4 ∧ w2 = Fin.natAdd n b4 := by
        rcases hc4 with h | ⟨_, hv4⟩
        · exact h
        · have hge : n ≤ v.val := by rw [hv4, Fin.val_natAdd]; omega
          omega
      have ha13 : a1 = a3 := Fin.ext (by have := congrArg Fin.val (hu1.symm.trans hu_eq3.1); rw [Fin.val_castAdd, Fin.val_castAdd] at this; exact this)
      have ha24 : a2 = a4 := Fin.ext (by have := congrArg Fin.val (hv_eq.1.symm.trans hv_eq4.1); rw [Fin.val_castAdd, Fin.val_castAdd] at this; exact this)
      have hb12 : b1 = b2 := Fin.ext (by have := congrArg Fin.val (hw1r.symm.trans hv_eq.2); rw [Fin.val_natAdd, Fin.val_natAdd] at this; omega)
      have hb34 : b3 = b4 := Fin.ext (by have := congrArg Fin.val (hu_eq3.2.symm.trans hv_eq4.2); rw [Fin.val_natAdd, Fin.val_natAdd] at this; omega)
      have ha12ne : a1 ≠ a2 := fun h => huv (by rw [hu1, hv_eq.1, h])
      have hb13ne : b1 ≠ b3 := fun h => hne (by rw [hw1r, hu_eq3.2, h])
      exact hRect a1 a2 b1 b3 ha12ne hb13ne ⟨he1, ha13 ▸ he3, hb12 ▸ he2, ha24 ▸ hb34 ▸ he4⟩
    · have hw1lt : w1.val < n := by rw [hw1l, Fin.val_castAdd]; exact a1.isLt
      have hvge : n ≤ v.val := by
        rcases hc2 with ⟨_, hw1r2⟩ | ⟨_, hv2⟩
        · have : n ≤ w1.val := by rw [hw1r2, Fin.val_natAdd]; omega
          omega
        · rw [hv2, Fin.val_natAdd]; omega
      have hv_eq : w1 = Fin.castAdd n a2 ∧ v = Fin.natAdd n b2 := by
        rcases hc2 with ⟨_, hw1r2⟩ | h
        · have : n ≤ w1.val := by rw [hw1r2, Fin.val_natAdd]; omega
          omega
        · exact h
      have hu_eq3 : w2 = Fin.castAdd n a3 ∧ u = Fin.natAdd n b3 := by
        rcases hc3 with ⟨hu3, _⟩ | h
        · have hge : n ≤ u.val := by rw [hu1, Fin.val_natAdd]; omega
          have hlt : u.val < n := by rw [hu3, Fin.val_castAdd]; exact a3.isLt
          omega
        · exact h
      have hv_eq4 : w2 = Fin.castAdd n a4 ∧ v = Fin.natAdd n b4 := by
        rcases hc4 with ⟨hv4, _⟩ | h
        · have hlt : v.val < n := by rw [hv4, Fin.val_castAdd]; exact a4.isLt
          omega
        · exact h
      have ha12 : a1 = a2 := Fin.ext (by have := congrArg Fin.val (hw1l.symm.trans hv_eq.1); rw [Fin.val_castAdd, Fin.val_castAdd] at this; exact this)
      have ha34 : a3 = a4 := Fin.ext (by have := congrArg Fin.val (hu_eq3.1.symm.trans hv_eq4.1); rw [Fin.val_castAdd, Fin.val_castAdd] at this; exact this)
      have hb13 : b1 = b3 := Fin.ext (by have := congrArg Fin.val (hu1.symm.trans hu_eq3.2); rw [Fin.val_natAdd, Fin.val_natAdd] at this; omega)
      have hb24 : b2 = b4 := Fin.ext (by have := congrArg Fin.val (hv_eq.2.symm.trans hv_eq4.2); rw [Fin.val_natAdd, Fin.val_natAdd] at this; omega)
      have ha13ne : a1 ≠ a3 := fun h => hne (by rw [hw1l, hu_eq3.1, h])
      have hb12ne : b1 ≠ b2 := fun h => huv (by rw [hu1, hv_eq.2, h])
      exact hRect a1 a3 b1 b2 ha13ne hb12ne ⟨he1, ha12 ▸ he2, hb13 ▸ he3, ha34 ▸ hb24 ▸ he4⟩
  have hMinVC : ∀ K : Finset (Fin nv), (∀ u v : Fin nv, G.Adj u v → u ∈ K ∨ v ∈ K) → n ≤ K.card := by
    intro K hK
    let proj : Fin nv → Fin n := fun u =>
      if h : u.val < n then ⟨u.val, h⟩ else π.symm ⟨u.val - n, by have := u.isLt; omega⟩
    have hSub : (Finset.univ : Finset (Fin n)) ⊆ K.image proj := by
      intro i _
      have hadj : G.Adj (Fin.castAdd n i) (Fin.natAdd n (π i)) := ⟨i, π i, hMatch i, Or.inl ⟨rfl, rfl⟩⟩
      rcases hK _ _ hadj with h1 | h2
      · refine Finset.mem_image.mpr ⟨Fin.castAdd n i, h1, ?_⟩
        dsimp only [proj]
        have hlt : (Fin.castAdd n i).val < n := by rw [Fin.val_castAdd]; exact i.isLt
        rw [dif_pos hlt]; apply Fin.ext; rw [Fin.val_castAdd]
      · refine Finset.mem_image.mpr ⟨Fin.natAdd n (π i), h2, ?_⟩
        dsimp only [proj]
        have hge : ¬ (Fin.natAdd n (π i)).val < n := by rw [Fin.val_natAdd]; omega
        rw [dif_neg hge]
        have hsub : (⟨(Fin.natAdd n (π i)).val - n, by have := (Fin.natAdd n (π i)).isLt; omega⟩ : Fin n) = π i := by
          apply Fin.ext; dsimp only; rw [Fin.val_natAdd]; omega
        rw [hsub, Equiv.symm_apply_apply]
    have h1 := Finset.card_le_card hSub
    rw [Finset.card_fin] at h1
    exact le_trans h1 Finset.card_image_le
  have hG_hasEdge : ∀ x : Fin nv → Bool,
      graphFun G ∅ x = true ↔ ∃ u v : Fin nv, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin nv)), x a = true) ||
      decide (∃ u v : Fin nv, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    have hempty : ¬ ∃ a ∈ (∅ : Finset (Fin nv)), x a = true := fun h => by obtain ⟨a, ha, _⟩ := h; exact Finset.notMem_empty a ha
    rw [decide_eq_false hempty, Bool.false_or, decide_eq_true_eq]
  have hFunEq : circuitFun nv C0 = graphFun G ∅ := by
    funext x
    rw [hComp0 x]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, hG_hasEdge]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨Fin.castAdd n a, Fin.natAdd n b, ⟨a, b, hab, Or.inl ⟨rfl, rfl⟩⟩, ha, hb⟩
    · rintro ⟨u, v, ⟨a, b, hab, hcases⟩, hu, hv⟩
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, b, hab, hu, hv⟩
      · exact ⟨a, b, hab, hv, hu⟩
  obtain ⟨C, hLeast, hTop, hCsizeLe, _⟩ := hTopForm nv G C0 hGne hAO0 hFunEq
  by_contra hltTarget
  have hCsizeLt : C.size + 1 < G.edgeFinset.card + n := by rw [hGcard]; omega
  have hBeat : ∀ K : Finset (Fin nv), (∀ u v : Fin nv, G.Adj u v → u ∈ K ∨ v ∈ K) →
      C.size + 1 < G.edgeFinset.card + K.card := fun K hK => by
    have := hMinVC K hK; omega
  obtain ⟨hLed1, hLed2⟩ := hLedger nv G C hNo4 hGne hLeast hTop
  have hBudgetLtCov : ∀ A : Finset (Fin nv),
      (∀ e ∈ Ustar G C, ∃ v ∈ A, v ∈ e) →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
        A.card + (Ustar G C).card := by
    intro A hAcov
    let H : SimpleGraph (Fin nv) := G.deleteEdges ↑(Ustar G C)
    let covers : Finset (Finset (Fin nv)) :=
      Finset.univ.filter (fun T : Finset (Fin nv) => ∀ u v : Fin nv, H.Adj u v → u ∈ T ∨ v ∈ T)
    have hCoversNe : covers.Nonempty :=
      ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
    obtain ⟨K0, hK0mem, hK0min⟩ := Finset.exists_min_image covers Finset.card hCoversNe
    have hK0cov : ∀ u v : Fin nv, H.Adj u v → u ∈ K0 ∨ v ∈ K0 := (Finset.mem_filter.mp hK0mem).2
    have hIsMin : IsMinCover H K0 :=
      ⟨hK0cov, fun T' hT' => hK0min T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩
    have hK0top := hLed2 K0 hIsMin
    have hAKcov : ∀ u v : Fin nv, G.Adj u v → u ∈ A ∪ K0 ∨ v ∈ A ∪ K0 := by
      intro u v huv
      by_cases hu : s(u, v) ∈ Ustar G C
      · obtain ⟨w, hwA, hwe⟩ := hAcov s(u, v) hu
        rcases Sym2.mem_iff.mp hwe with rfl | rfl
        · exact Or.inl (Finset.mem_union_left K0 hwA)
        · exact Or.inr (Finset.mem_union_left K0 hwA)
      · rcases hK0cov u v (SimpleGraph.deleteEdges_adj.mpr ⟨huv, Finset.mem_coe.not.mpr hu⟩) with h1 | h2
        · exact Or.inl (Finset.mem_union_right A h1)
        · exact Or.inr (Finset.mem_union_right A h2)
    have hAKge : n ≤ (A ∪ K0).card := hMinVC (A ∪ K0) hAKcov
    have hUnLe : (A ∪ K0).card ≤ A.card + K0.card := Finset.card_union_le A K0
    omega
  obtain ⟨hJunkGe2, hUstarGe3, hBudgetGe5⟩ :=
    hCore nv G col C (by omega) hCol hNoTri hNo4 hGne hG_hasEdge hLeast hTop hBudgetLtCov
  exact hResidual nv G col mate C hCol hMateInv hMateAdj hNo4 hLeast hTop hBeat hJunkGe2 hUstarGe3 hBudgetGe5 hBudgetLtCov
