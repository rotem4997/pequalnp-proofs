import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4185_1
    (oneJunk :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Circuit),
        NoFourCycle x2 → x2.edgeFinset.Nonempty → IsLeastAO x2 x4 → TopForm x2 x4 →
        (Ustar x2 x4).Nonempty → (junk x2 x4).card = 1 →
        ∃ (x9 : Finset (Fin x1)), CoverPromise.IsVertexCover x2 x9 ∧
          x9.card + (Ustar x2 x4).card ≤
            (tops x2 x4 \ centreless x2 x4).card + 2 * (centreless x2 x4).card +
              (junk x2 x4).card + (orN x2 x4 \ lam x2 x4).card)
    (manyJunk :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Circuit),
        NoFourCycle x2 → x2.edgeFinset.Nonempty → IsLeastAO x2 x4 → TopForm x2 x4 →
        (Ustar x2 x4).Nonempty → 2 ≤ (junk x2 x4).card →
        ∃ (x9 : Finset (Fin x1)), CoverPromise.IsVertexCover x2 x9 ∧
          x9.card + (Ustar x2 x4).card ≤
            (tops x2 x4 \ centreless x2 x4).card + 2 * (centreless x2 x4).card +
              (junk x2 x4).card + (orN x2 x4 \ lam x2 x4).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  intro n G _ C hFour hEdgeNe hLeast hTop
  have hAO : IsAO2 n C := hLeast.1
  have hEval : circuitFun n C = graphFun G ∅ := hLeast.2.1
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len (gs : List Gate) (w : List Bool) :
      (gs.foldl stepW w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega
  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepW w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length (by simp [stepW])]
        simp only [List.getElem_cons_zero]
        have h2 : (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          have hge : w.length ≤ i := Nat.le_of_not_lt hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
      | succ j =>
        have key := ih (stepW w g) j (by simpa using hj)
        have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]; exact key
  let wval (w : ℕ) (x : Fin n → Bool) : Bool := (C.wires (List.ofFn x)).getD w false
  have wval_input (i : Fin n) (x : Fin n → Bool) : wval i.val x = x i := by
    change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
    rw [foldl_getD_lt C.gates (List.ofFn x) i.val (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have wval_ge (w : ℕ) (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) : wval w x = false := by
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [foldl_len, List.length_ofFn]; omega)]
    rfl
  have gateAt_eq {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]
  have gateAt_mem {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj
  have gate_inputs_two {j : ℕ} (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hl := hAO.2.2 (gateAt C j) (gateAt_mem hj)
    rcases heq : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [heq] at hl
    · simp [heq] at hl
    · unfold opnd; rw [heq]; rfl
    · simp [heq] at hl
  have opnd_lt {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) : opnd C j b < n + j := by
    apply hAO.2.1 j hj
    rw [gate_inputs_two hj]
    fin_cases b <;> simp
  have wval_gate {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
      wval (n + j) x =
        if (gateAt C j).op = GateOp.and then wval (opnd C j 0) x && wval (opnd C j 1) x
        else wval (opnd C j 0) x || wval (opnd C j 1) x := by
    have hfg := foldl_getD_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hfg
    change (C.gates.foldl stepW (List.ofFn x)).getD (n + j) false = _
    rw [hfg, ← gateAt_eq hj, gate_inputs_two hj]
    have h0 : opnd C j 0 < n + j := opnd_lt hj 0
    have h1 : opnd C j 1 < n + j := opnd_lt hj 1
    simp only [List.map_cons, List.map_nil, ite_eq_left h0, ite_eq_left h1]
    rcases hAO.1 (gateAt C j) (gateAt_mem hj) with hop | hop
    · rw [hop, ite_eq_left rfl]
      change ([wval (opnd C j 0) x, wval (opnd C j 1) x].all id) = _
      simp
    · rw [hop, ite_eq_right (by intro h; cases h)]
      change ([wval (opnd C j 0) x, wval (opnd C j 1) x].any id) = _
      simp
  have orSets_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]; omega
  have orSets_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ k < gs.length, (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        change ((gs.foldl (orStep n) []) ++ [_]).getD k [] = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨by simp; omega, Or.inl rfl⟩
          · refine ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]; exact h3
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨h, Or.inl rfl⟩
          · rw [key (w - n) (by omega)] at h3
            exact ⟨h, Or.inr ⟨hop, w, hw, h1, h2, h3⟩⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            generalize gs.foldl (orStep n) [] = cs at hlen ⊢
            unfold orStep
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            simp [hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (rfl | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl rfl⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]; exact h3
          · rintro ⟨_, rfl | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl rfl
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            generalize gs.foldl (orStep n) [] = cs at hlen ⊢
            unfold orStep
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            simp [hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          change ((gs.foldl (orStep n) []) ++ [_]).getD j [] = []
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hlen]; omega)]
          rfl
        rw [e0]; simp; omega
  have orReaches_iff (w i : ℕ) :
      OrReaches n C w i ↔
        n ≤ w ∧ w < n + C.gates.length ∧
          (i = w - n ∨ ((gateAt C (w - n)).op = GateOp.or ∧
            ∃ b : Fin 2, OrReaches n C (opnd C (w - n) b) i)) := by
    unfold OrReaches orSets
    constructor
    · rintro ⟨hge, hm⟩
      rw [orSets_char C.gates i (w - n)] at hm
      obtain ⟨hlt, h3⟩ := hm
      refine ⟨hge, by omega, ?_⟩
      rcases h3 with rfl | ⟨hop, u, hu, h1, h2, h3⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hop, ?_⟩
        change u ∈ (gateAt C (w - n)).inputs at hu
        rw [gate_inputs_two hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨0, h1, h3⟩
        · exact ⟨1, h1, h3⟩
    · rintro ⟨hge, hlt, h3⟩
      refine ⟨hge, ?_⟩
      rw [orSets_char C.gates i (w - n)]
      refine ⟨by omega, ?_⟩
      rcases h3 with rfl | ⟨hop, b, hb1, hb2⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hop, opnd C (w - n) b, ?_, hb1, opnd_lt (by omega) b, hb2⟩
        change opnd C (w - n) b ∈ (gateAt C (w - n)).inputs
        rw [gate_inputs_two (by omega)]; fin_cases b <;> simp
  have orReaches_val {w i : ℕ} (h : OrReaches n C w i) (x : Fin n → Bool) :
      wval (n + i) x = true → wval w x = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      rw [orReaches_iff] at h
      obtain ⟨hge, hlt, rfl | ⟨hop, b, hb⟩⟩ := h
      · have heq : n + (w - n) = w := by omega
        rw [heq]; exact id
      · intro hi
        have hblt := opnd_lt (j := w - n) (by omega) b
        have hbv := ih (opnd C (w - n) b) (by omega) hb hi
        have heq : n + (w - n) = w := by omega
        rw [← heq, wval_gate (by omega) x, ite_eq_right (by intro h; rw [hop] at h; cases h), Bool.or_eq_true]
        fin_cases b
        · exact Or.inl hbv
        · exact Or.inr hbv
  have orIn_val {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (x : Fin n → Bool) (hxu : x u = true) :
      wval w x = true := by
    unfold orIn at hu
    obtain ⟨_, heq | ⟨k, hk, hr, hop, hmem⟩⟩ := Finset.mem_filter.mp hu
    · rw [← heq, wval_input u x]; exact hxu
    · apply orReaches_val hr x
      rw [wval_gate hk x, ite_eq_right (by intro h; rw [hop] at h; cases h), Bool.or_eq_true]
      rw [gate_inputs_two hk] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1
      · left; rw [← h0, wval_input u x]; exact hxu
      · right; rw [← h1, wval_input u x]; exact hxu
  -- Cone characterization (for TopForm)
  have cones_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]; omega
  have cones_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k < gs.length, (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        change ((gs.foldl (coneStep n) []) ++ [_]).getD k [] = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - n) (by omega)]; exact Or.inr h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - n) (by omega)] at h3; exact Or.inr h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          change ((gs.foldl (coneStep n) []) ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (gs.foldl (coneStep n) []).length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) [])]).getD gs.length [] = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [e1, e2]
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - n) (by omega)]; exact Or.inr h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - n) (by omega)] at h3; exact Or.inr h3
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          change ((gs.foldl (coneStep n) []) ++ [_]).getD j [] = []
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hlen]; omega)]
          rfl
        rw [e0]; simp; omega
  have inCone_step {i j : ℕ} (hj : j < C.gates.length) (b : Fin 2)
      (hw : n ≤ opnd C j b) (h : i = opnd C j b - n ∨ InCone n C i (opnd C j b - n)) :
      InCone n C i j := by
    unfold InCone cones
    rw [cones_char C.gates i j]
    refine ⟨hj, opnd C j b, ?_, hw, opnd_lt hj b, h⟩
    change opnd C j b ∈ (gateAt C j).inputs
    rw [gate_inputs_two hj]; fin_cases b <;> simp
  have orReaches_inCone {j b i} (hj : j < C.gates.length) (h : OrReaches n C (opnd C j b) i) :
      InCone n C i j := by
    have hrec : ∀ w, OrReaches n C w i → ∀ k < C.gates.length, w = n + k → i = k ∨ InCone n C i k := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hr k hk heq
        rw [orReaches_iff] at hr
        obtain ⟨hge, hlt, rfl | ⟨_, c, hc⟩⟩ := hr
        · exact Or.inl (by omega)
        · have heq2 : w - n = k := by omega
          rw [heq2] at hc
          have hltc := opnd_lt hk c
          have hgec : n ≤ opnd C k c := (orReaches_iff _ _).mp hc |>.1
          have hsub := ih (opnd C k c) (by omega) hc (opnd C k c - n) (by omega) (by omega)
          exact Or.inr (inCone_step hk c hgec hsub)
    have hge : n ≤ opnd C j b := (orReaches_iff _ _).mp h |>.1
    have hlt := opnd_lt hj b
    exact inCone_step hj b hge (hrec (opnd C j b) h (opnd C j b - n) (by omega) (by omega))
  -- Split on whether Ustar is nonempty
  by_cases hU : (Ustar G C).Nonempty
  · -- Prove junk is nonempty when Ustar is nonempty
    have hJunkNe : (junk G C).Nonempty := by
      by_contra hJunkEmpty
      rw [Finset.not_nonempty_iff_eq_empty] at hJunkEmpty
      have hClean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
        intro j hj hop x hx
        cases hfx : graphFun G ∅ x with
        | true => rfl
        | false =>
          have hjmem : j ∈ junk G C := by
            unfold junk gatesWhere IsDirtyAnd IsDirty
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, x, hx, hfx⟩
          rw [hJunkEmpty] at hjmem
          exact (Finset.notMem_empty j hjmem).elim
      obtain ⟨e, heU⟩ := hU
      unfold Ustar at heU
      obtain ⟨heG, heNotStar⟩ := Finset.mem_sdiff.mp heU
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp heG
        have hf_single (w : Fin n) : graphFun G ∅ (fun k => decide (k = w)) = false := by
          change (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a = w) = true) ||
            decide (∃ a b, G.Adj a b ∧ decide (a = w) = true ∧ decide (b = w) = true)) = false
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_false_iff_not]
          rintro ⟨a, b, hab, ha, hb⟩
          rw [decide_eq_true_eq] at ha hb
          subst ha; subst hb
          exact G.ne_of_adj hab rfl
        have hOutTrue : wval C.output (pairInput u v) = true := by
          change circuitFun n C (pairInput u v) = true
          rw [hEval]
          change (decide (∃ a ∈ (∅ : Finset (Fin n)), _) ||
            decide (∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true
          rw [Bool.or_eq_true]
          right
          rw [decide_eq_true_eq]
          refine ⟨u, v, huv, ?_, ?_⟩
          · change decide (u = u ∨ u = v) = true; simp
          · change decide (v = u ∨ v = v) = true; simp
        have hFindAnd : ∀ w, (∀ z : Fin n, wval w (fun k => decide (k = z)) = false) →
            wval w (pairInput u v) = true →
            ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ wval (n + a) (pairInput u v) = true := by
          intro w
          induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hBel ht
            by_cases hw : w < n
            · have h1 := hBel ⟨w, hw⟩
              rw [wval_input ⟨w, hw⟩ _] at h1; simp at h1
            · by_cases hw2 : w < n + C.gates.length
              · have hj : w - n < C.gates.length := by omega
                have heq : n + (w - n) = w := by omega
                rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
                · exact ⟨w - n, hj, hop, by rwa [heq]⟩
                · rw [← heq, wval_gate hj _, ite_eq_right (by intro h; rw [hop] at h; cases h), Bool.or_eq_true] at ht
                  have hSub (b : Fin 2) : ∀ z : Fin n, wval (opnd C (w - n) b) (fun k => decide (k = z)) = false := by
                    intro z
                    have h0 := hBel z
                    rw [← heq, wval_gate hj _, ite_eq_right (by intro h; rw [hop] at h; cases h), Bool.or_eq_false_iff] at h0
                    fin_cases b
                    · exact h0.1
                    · exact h0.2
                  rcases ht with h0 | h1
                  · exact ih (opnd C (w - n) 0) (by have := opnd_lt hj 0; omega) (hSub 0) h0
                  · exact ih (opnd C (w - n) 1) (by have := opnd_lt hj 1; omega) (hSub 1) h1
              · rw [wval_ge w (by omega) _] at ht; cases ht
        obtain ⟨a, ha, hopa, hva⟩ := hFindAnd C.output (fun z => by
          change circuitFun n C (fun k => decide (k = z)) = false
          rw [hEval]; exact hf_single z) hOutTrue
        have haTop : a ∈ tops G C := by
          unfold tops gatesWhere
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hopa, hClean a ha hopa⟩
        have hHit : ∀ w, (∀ i < C.gates.length, OrReaches n C w i → (gateAt C i).op ≠ GateOp.and) →
            wval w (pairInput u v) = true → ∃ z ∈ orIn n C w, pairInput u v z = true := by
          intro w
          induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hno ht
            by_cases hw : w < n
            · rw [wval_input ⟨w, hw⟩ _] at ht
              refine ⟨⟨w, hw⟩, ?_, ht⟩
              unfold orIn
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
            · by_cases hw2 : w < n + C.gates.length
              · have hj : w - n < C.gates.length := by omega
                have heq : n + (w - n) = w := by omega
                have hnotand : (gateAt C (w - n)).op ≠ GateOp.and :=
                  hno (w - n) hj ((orReaches_iff w (w - n)).mpr ⟨by omega, hw2, Or.inl rfl⟩)
                have hop : (gateAt C (w - n)).op = GateOp.or :=
                  (hAO.1 (gateAt C (w - n)) (gateAt_mem hj)).resolve_left hnotand
                rw [← heq, wval_gate hj _, ite_eq_right hnotand, Bool.or_eq_true] at ht
                have hLift (b : Fin 2) (z : Fin n) (hz : z ∈ orIn n C (opnd C (w - n) b)) : z ∈ orIn n C w := by
                  unfold orIn at hz ⊢
                  obtain ⟨_, heqb | ⟨k, hk, hrk, hopk, hmemk⟩⟩ := Finset.mem_filter.mp hz
                  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨w - n, hj,
                      (orReaches_iff w (w - n)).mpr ⟨by omega, hw2, Or.inl rfl⟩, hop, ?_⟩⟩
                    rw [gate_inputs_two hj, heqb]
                    fin_cases b <;> simp
                  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨k, hk,
                      (orReaches_iff w k).mpr ⟨by omega, hw2, Or.inr ⟨hop, b, hrk⟩⟩, hopk, hmemk⟩⟩
                rcases ht with h0 | h1
                · obtain ⟨z, hz, hxz⟩ := ih (opnd C (w - n) 0) (by have := opnd_lt hj 0; omega)
                    (fun i hi hr => hno i hi ((orReaches_iff w i).mpr ⟨by omega, hw2, Or.inr ⟨hop, 0, hr⟩⟩)) h0
                  exact ⟨z, hLift 0 z hz, hxz⟩
                · obtain ⟨z, hz, hxz⟩ := ih (opnd C (w - n) 1) (by have := opnd_lt hj 1; omega)
                    (fun i hi hr => hno i hi ((orReaches_iff w i).mpr ⟨by omega, hw2, Or.inr ⟨hop, 1, hr⟩⟩)) h1
                  exact ⟨z, hLift 1 z hz, hxz⟩
              · rw [wval_ge w (by omega) _] at ht; cases ht
        rw [wval_gate ha _, ite_eq_left hopa, Bool.and_eq_true] at hva
        obtain ⟨z0, hz0, hxz0⟩ := hHit (opnd C a 0) (fun i hi hr hopi =>
          hTop i hi a ha hopi (hClean i hi hopi) hopa (orReaches_inCone ha hr)) hva.1
        obtain ⟨z1, hz1, hxz1⟩ := hHit (opnd C a 1) (fun i hi hr hopi =>
          hTop i hi a ha hopi (hClean i hi hopi) hopa (orReaches_inCone ha hr)) hva.2
        have hne : z0 ≠ z1 := by
          intro eq
          subst eq
          have h0 := orIn_val hz0 (fun k => decide (k = z0)) (by simp)
          have h1 := orIn_val hz1 (fun k => decide (k = z0)) (by simp)
          have hga : gateVal n C a (fun k => decide (k = z0)) = true := by
            change wval (n + a) _ = true
            rw [wval_gate ha _, ite_eq_left hopa, h0, h1]; rfl
          have hf := hClean a ha hopa (fun k => decide (k = z0)) hga
          rw [hf_single z0] at hf; cases hf
        change decide (z0 = u ∨ z0 = v) = true at hxz0
        change decide (z1 = u ∨ z1 = v) = true at hxz1
        rw [decide_eq_true_eq] at hxz0 hxz1
        have hStar : s(u, v) ∈ starEdges G C := by
          unfold starEdges
          refine Finset.mem_biUnion.mpr ⟨a, haTop, Finset.mem_image.mpr ⟨(z0, z1), Finset.mem_product.mpr ⟨hz0, hz1⟩, ?_⟩⟩
          rcases hxz0 with rfl | rfl <;> rcases hxz1 with rfl | rfl
          · exact (hne rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hne rfl).elim
        exact heNotStar hStar
    have hPos : 1 ≤ (junk G C).card := Finset.card_pos.mpr hJunkNe
    by_cases h1 : (junk G C).card = 1
    · exact oneJunk n G C hFour hEdgeNe hLeast hTop hU h1
    · exact manyJunk n G C hFour hEdgeNe hLeast hTop hU (by omega)
  · -- Base case: Ustar G C = ∅, prove directly via star centers of tops \ centreless
    rw [Finset.not_nonempty_iff_eq_empty] at hU
    have side_adj {a : ℕ} (ha : a ∈ tops G C) {u v : Fin n}
        (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) : G.Adj u v := by
      unfold tops gatesWhere at ha
      obtain ⟨haLt, hopa, hBel⟩ := Finset.mem_filter.mp ha
      rw [Finset.mem_range] at haLt
      have h0 := orIn_val hu (pairInput u v) (by change decide (u = u ∨ u = v) = true; simp)
      have h1 := orIn_val hv (pairInput u v) (by change decide (v = u ∨ v = v) = true; simp)
      have hga : gateVal n C a (pairInput u v) = true := by
        change wval (n + a) (pairInput u v) = true
        rw [wval_gate haLt _, ite_eq_left hopa, h0, h1]; rfl
      have hf := hBel (pairInput u v) hga
      change (decide (∃ x ∈ (∅ : Finset (Fin n)), _) ||
        decide (∃ p q, G.Adj p q ∧ pairInput u v p = true ∧ pairInput u v q = true)) = true at hf
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq] at hf
      obtain ⟨p, q, hpq, hp, hq⟩ := hf
      change decide (p = u ∨ p = v) = true at hp
      change decide (q = u ∨ q = v) = true at hq
      rw [decide_eq_true_eq] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact (G.ne_of_adj hpq rfl).elim
      · exact hpq
      · exact hpq.symm
      · exact (G.ne_of_adj hpq rfl).elim
    have hCtrEx (a : ℕ) (ha : a ∈ tops G C \ centreless G C) :
        ∃ c : Fin n, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, u = c ∨ v = c := by
      obtain ⟨haT, haNotC⟩ := Finset.mem_sdiff.mp ha
      have hne0 : (side (n := n) C a 0).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        apply haNotC
        unfold centreless
        exact Finset.mem_filter.mpr ⟨haT, Or.inl h0⟩
      have hne1 : (side (n := n) C a 1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h1
        apply haNotC
        unfold centreless
        exact Finset.mem_filter.mpr ⟨haT, Or.inr h1⟩
      by_cases h0 : (side (n := n) C a 0).card ≤ 1
      · obtain ⟨c, hc⟩ := hne0
        exact ⟨c, fun u hu _ _ => Or.inl (Finset.card_le_one.mp h0 u hu c hc)⟩
      · have h1 : (side (n := n) C a 1).card ≤ 1 := by
          by_contra h1gt
          obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (side (n := n) C a 0).card)
          obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < (side (n := n) C a 1).card)
          have hle := hFour u1 u2 hu12
          have hm1 : v1 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, side_adj haT hu1 hv1, side_adj haT hu2 hv1⟩
          have hm2 : v2 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, side_adj haT hu1 hv2, side_adj haT hu2 hv2⟩
          exact hv12 (Finset.card_le_one.mp hle v1 hm1 v2 hm2)
        obtain ⟨c, hc⟩ := hne1
        exact ⟨c, fun _ _ v hv => Or.inr (Finset.card_le_one.mp h1 v hv c hc)⟩
    have hnPos : 0 < n := by
      obtain ⟨e, he⟩ := hEdgeNe
      induction e using Sym2.ind with
      | _ u _ => exact Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
    let ctr (a : ℕ) : Fin n := if ha : a ∈ tops G C \ centreless G C then Classical.choose (hCtrEx a ha) else ⟨0, hnPos⟩
    let K : Finset (Fin n) := (tops G C \ centreless G C).image ctr
    refine ⟨K, ?_, ?_⟩
    · intro u v huv
      have heG : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      have heStar : s(u, v) ∈ starEdges G C := by
        by_contra hnot
        have hm : s(u, v) ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨heG, hnot⟩
        rw [hU] at hm
        exact (Finset.notMem_empty _ hm).elim
      unfold starEdges at heStar
      obtain ⟨a, haT, hp⟩ := Finset.mem_biUnion.mp heStar
      obtain ⟨pq, hpq, heq⟩ := Finset.mem_image.mp hp
      obtain ⟨hp0, hq1⟩ := Finset.mem_product.mp hpq
      have haTC : a ∈ tops G C \ centreless G C := by
        refine Finset.mem_sdiff.mpr ⟨haT, fun hc => ?_⟩
        unfold centreless at hc
        rcases (Finset.mem_filter.mp hc).2 with h0 | h1
        · rw [h0] at hp0; exact Finset.notMem_empty _ hp0
        · rw [h1] at hq1; exact Finset.notMem_empty _ hq1
      have hspec := Classical.choose_spec (hCtrEx a haTC) pq.1 hp0 pq.2 hq1
      have hctreq : ctr a = Classical.choose (hCtrEx a haTC) := by
        change (if ha : a ∈ tops G C \ centreless G C then Classical.choose (hCtrEx a ha) else ⟨0, hnPos⟩) = _
        rw [dite_eq_left haTC]
      have hmemK : ctr a ∈ K := Finset.mem_image.mpr ⟨a, haTC, rfl⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hspec with h1 | h2
        · exact Or.inl (h1 ▸ hctreq ▸ hmemK)
        · exact Or.inr (h2 ▸ hctreq ▸ hmemK)
      · rcases hspec with h1 | h2
        · exact Or.inr (h1 ▸ hctreq ▸ hmemK)
        · exact Or.inl (h2 ▸ hctreq ▸ hmemK)
    · rw [hU, Finset.card_empty, Nat.add_zero]
      have hK : K.card ≤ (tops G C \ centreless G C).card := Finset.card_image_le
      omega
