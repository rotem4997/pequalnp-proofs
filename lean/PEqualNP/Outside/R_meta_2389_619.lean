import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2389_619
    (hClean : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 26 C →
      C.size ≤ 63 →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true →
          C.eval (List.ofFn x) = true) →
      False)
    (hSameSide : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 26 C →
      C.size ≤ 63 →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn (fun i : Fin 26 => decide (i = (0 : Fin 26) ∨ i = (1 : Fin 26))))).getD (26 + j) false = true) →
      False)
    (hCross : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 26 C →
      C.size ≤ 63 →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn (fun i : Fin 26 => decide (i = (0 : Fin 26) ∨ i = (14 : Fin 26))))).getD (26 + j) false = true) →
      False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  classical
  intro C hAO2 hspec
  by_contra hlt64
  have hsz63 : C.size ≤ 63 := by omega
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := hAO2.1
  have hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C := hAO2.2.1
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := hAO2.2.2
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]; rfl
  have hrun_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool), (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]; omega
  have hgetD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b; simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ), i < x.length + gs.length →
      (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ), i < x.length →
      (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1; exact h1
  have hrun_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map fun i =>
            if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := hrun_len gs x
      have hsame : ∀ k ≤ gs.length, ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hrun_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · have hgd : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd, hsame j (Nat.le_of_lt hlt), hrun_prefix gs [g] x _ (by omega)]
        exact ih j hlt
      · have hjeq : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
        subst hjeq
        have hgd : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hgd, hsame gs.length le_rfl, hrun_snoc, ← hlen, hgetD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hrun_mono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ w, (run gs x).getD w false = true → (run gs y).getD w false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => intro w hw; exact hle w hw
    | append_singleton gs g ih =>
      intro w hw
      have ih' := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
      have l1 := hrun_len gs x
      have l2 := hrun_len gs y
      rw [hrun_snoc] at hw ⊢
      rcases Nat.lt_trichotomy w (x.length + gs.length) with hlt | heq | hgt
      · rw [hgetD_lt _ _ _ (by omega)] at hw
        rw [hgetD_lt _ _ _ (by omega)]
        exact ih' w hw
      · have e1 : w = (run gs x).length := by omega
        have e2 : w = (run gs y).length := by omega
        rw [e1, hgetD_at] at hw
        rw [e2, hgetD_at]
        rcases hgs g (List.mem_append_right _ (List.mem_singleton_self g)) with hop | hop
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).all id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).all id = true
          rw [List.all_map, List.all_eq_true] at hw ⊢
          intro q hq; exact ih' q (hw q hq)
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).any id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).any id = true
          rw [List.any_map, List.any_eq_true] at hw ⊢
          rcases hw with ⟨q, hq1, hq2⟩
          exact ⟨q, hq1, ih' q hq2⟩
      · exfalso
        have hdef : (run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)]).getD w false = false :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        rw [hdef] at hw
        exact Bool.false_ne_true hw
  by_cases hclean : ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true →
        C.eval (List.ofFn x) = true
  · exact hClean C hAO2 hsz63 hspec hclean
  · have hdirty_ex : ∃ j : ℕ, j < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true ∧ C.eval (List.ofFn x) = false := by
      push_neg at hclean
      rcases hclean with ⟨j, hj, hand, x, hval, hne⟩
      have hfalse : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x)
        · rfl
        · exact (hne h).elim
      exact ⟨j, hj, hand, x, hval, hfalse⟩
    let j0 : ℕ := Nat.find hdirty_ex
    have hj0_spec := Nat.find_spec hdirty_ex
    have hj0_lt : j0 < C.gates.length := hj0_spec.1
    have hj0_and : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and := hj0_spec.2.1
    rcases hj0_spec.2.2 with ⟨x, hx_val, hx_false⟩
    have hearlier_and : ∀ i < j0,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn x)).getD (26 + i) false = false := by
      intro i hilt hiand
      by_contra hne
      have htrue : (C.wires (List.ofFn x)).getD (26 + i) false = true := by
        cases h : (C.wires (List.ofFn x)).getD (26 + i) false
        · exact (hne h).elim
        · rfl
      exact Nat.find_min hdirty_ex hilt ⟨Nat.lt_trans hilt hj0_lt, hiand, x, htrue, hx_false⟩
    have hsingle_witness : ∀ w : ℕ, w < 26 + j0 → (run C.gates (List.ofFn x)).getD w false = true →
        ∃ u : Fin 26, x u = true ∧ (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u)))).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hwtrue
        by_cases hw26 : w < 26
        · refine ⟨⟨w, hw26⟩, ?_, ?_⟩
          · rw [hrun_input C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw26)] at hwtrue
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw26] at hwtrue
            exact hwtrue
          · rw [hrun_input C.gates _ w (by rw [List.length_ofFn]; exact hw26)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw26]
            exact decide_eq_true rfl
        · let i : ℕ := w - 26
          have hiw : w = 26 + i := by omega
          have hilt : i < j0 := by omega
          have hiC : i < C.gates.length := Nat.lt_trans hilt hj0_lt
          have hgi_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C i ∈ C.gates := by
            change C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
            rw [List.getD_eq_getElem _ _ hiC]
            exact List.getElem_mem hiC
          rcases hAO (PEqualNP.MetaComplexity.NestedCover.gateAt C i) hgi_mem with hiand | hior
          · exfalso
            have hf := hearlier_and i hilt hiand
            change (run C.gates (List.ofFn x)).getD (26 + i) false = false at hf
            rw [hiw, hf] at hwtrue
            exact Bool.false_ne_true hwtrue
          · rw [hiw] at hwtrue
            have hrg := hrun_gate C.gates (List.ofFn x) i hiC
            rw [List.length_ofFn] at hrg
            rw [hrg] at hwtrue
            change (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op.eval
              ((PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs.map fun k =>
                if k < 26 + i then (run C.gates (List.ofFn x)).getD k false else false) = true at hwtrue
            rw [hior] at hwtrue
            change ((PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs.map fun k =>
              if k < 26 + i then (run C.gates (List.ofFn x)).getD k false else false).any id = true at hwtrue
            rw [List.any_map, List.any_eq_true] at hwtrue
            rcases hwtrue with ⟨k, hk_in, hk_true⟩
            have hk_lt : k < 26 + i := hRB i hiC k hk_in
            dsimp only [Function.comp, id] at hk_true
            rw [if_pos hk_lt] at hk_true
            rcases ih k (by omega) (by omega) hk_true with ⟨u, hxu, hku⟩
            refine ⟨u, hxu, ?_⟩
            rw [hiw]
            have hrg2 := hrun_gate C.gates (List.ofFn (fun t : Fin 26 => decide (t = u))) i hiC
            rw [List.length_ofFn] at hrg2
            rw [hrg2]
            change (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op.eval
              ((PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs.map fun m =>
                if m < 26 + i then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u)))).getD m false else false) = true
            rw [hior]
            change ((PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs.map fun m =>
              if m < 26 + i then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u)))).getD m false else false).any id = true
            rw [List.any_map, List.any_eq_true]
            exact ⟨k, hk_in, by dsimp only [Function.comp, id]; rw [if_pos hk_lt]; exact hku⟩
    have hgj0_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C j0 ∈ C.gates := by
      change C.gates.getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hj0_lt]
      exact List.getElem_mem hj0_lt
    have hj0_len2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.length = 2 := hLen2 _ hgj0_mem
    rcases hinputs : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩
    · rw [hinputs] at hj0_len2; cases hj0_len2
    · rw [hinputs] at hj0_len2; cases hj0_len2
    · have hw1_in : w1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs := by rw [hinputs]; exact List.mem_cons_self
      have hw2_in : w2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs := by rw [hinputs]; exact List.mem_cons_of_mem _ List.mem_cons_self
      have hw1_lt : w1 < 26 + j0 := hRB j0 hj0_lt w1 hw1_in
      have hw2_lt : w2 < 26 + j0 := hRB j0 hj0_lt w2 hw2_in
      have hrg0 := hrun_gate C.gates (List.ofFn x) j0 hj0_lt
      rw [List.length_ofFn] at hrg0
      change (run C.gates (List.ofFn x)).getD (26 + j0) false = true at hx_val
      rw [hrg0] at hx_val
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.map fun k =>
          if k < 26 + j0 then (run C.gates (List.ofFn x)).getD k false else false) = true at hx_val
      rw [hj0_and, hinputs] at hx_val
      change (if w1 < 26 + j0 then (run C.gates (List.ofFn x)).getD w1 false else false) &&
        ((if w2 < 26 + j0 then (run C.gates (List.ofFn x)).getD w2 false else false) && true) = true at hx_val
      rw [if_pos hw1_lt, if_pos hw2_lt, Bool.and_true, Bool.and_eq_true] at hx_val
      rcases hsingle_witness w1 hw1_lt hx_val.1 with ⟨u, hxu, hwu⟩
      rcases hsingle_witness w2 hw2_lt hx_val.2 with ⟨v, hxv, hwv⟩
      let rel0 : Fin 26 → Fin 26 → Prop := fun a b =>
        a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let G0 : SimpleGraph (Fin 26) := SimpleGraph.fromRel rel0
      have hrel_iff : ∀ a b : Fin 26, G0.Adj a b ↔
          ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l) := by
        dsimp only [G0, rel0, SimpleGraph.fromRel]
        decide +kernel
      have hnot_adj : ¬ G0.Adj u v := by
        intro hadj
        rcases (hrel_iff u v).mp hadj with ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · have htr := (hspec x).mpr ⟨p, l, hpl, hxu, hxv⟩
          rw [hx_false] at htr; cases htr
        · have htr := (hspec x).mpr ⟨p, l, hpl, hxv, hxu⟩
          rw [hx_false] at htr; cases htr
      have hw1_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD w1 false = true := by
        refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 26 => decide (t = u)))
          (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v))) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w1 hwu
        intro k hk
        by_cases hk26 : k < 26
        · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk26] at hk ⊢
          change decide (⟨k, hk26⟩ = u) = true at hk
          change decide (⟨k, hk26⟩ = u ∨ ⟨k, hk26⟩ = v) = true
          rw [decide_eq_true_eq] at hk ⊢; exact Or.inl hk
        · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
      have hw2_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD w2 false = true := by
        refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 26 => decide (t = v)))
          (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v))) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w2 hwv
        intro k hk
        by_cases hk26 : k < 26
        · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk26] at hk ⊢
          change decide (⟨k, hk26⟩ = v) = true at hk
          change decide (⟨k, hk26⟩ = u ∨ ⟨k, hk26⟩ = v) = true
          rw [decide_eq_true_eq] at hk ⊢; exact Or.inr hk
        · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
      have hj0_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD (26 + j0) false = true := by
        have hrgp := hrun_gate C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v))) j0 hj0_lt
        rw [List.length_ofFn] at hrgp
        rw [hrgp]
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op.eval
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.map fun k =>
            if k < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD k false else false) = true
        rw [hj0_and, hinputs]
        change (if w1 < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD w1 false else false) &&
          ((if w2 < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v)))).getD w2 false else false) && true) = true
        rw [if_pos hw1_lt, if_pos hw2_lt, hw1_uv, hw2_uv]; rfl
      have hrelabel : ∀ (e eInv : Fin 26 → Fin 26),
          (∀ a : Fin 26, eInv (e a) = a) →
          (∀ a : Fin 26, e (eInv a) = a) →
          (∀ a b : Fin 26, G0.Adj (e a) (e b) ↔ G0.Adj a b) →
          (e u = 0 ∧ (e v = 0 ∨ e v = 1 ∨ e v = 14)) → False := by
        intro e eInv hli hri haut heuv
        let mw : ℕ → ℕ := fun w => if h : w < 26 then (e ⟨w, h⟩).val else w
        let mg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g => ⟨g.op, g.inputs.map mw⟩
        let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map mg, mw C.output⟩
        have hmw_lt : ∀ w k : ℕ, w < 26 + k → mw w < 26 + k := by
          intro w k hw; dsimp only [mw]; split_ifs with h26
          · have := (e ⟨w, h26⟩).isLt; omega
          · exact hw
        have hD_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (y : Fin 26 → Bool) (w : ℕ),
            (run (gs.map mg) (List.ofFn y)).getD (mw w) false =
              (run gs (List.ofFn (fun a : Fin 26 => y (e a)))).getD w false := by
          intro gs y
          induction gs using List.reverseRecOn with
          | nil =>
            intro w
            change (List.ofFn y).getD (mw w) false = (List.ofFn (fun a : Fin 26 => y (e a))).getD w false
            dsimp only [mw]
            split_ifs with h26
            · have hlt := (e ⟨w, h26⟩).isLt
              rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt]
              rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h26]
            · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
              rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
          | append_singleton gs g ih =>
            intro w
            rw [List.map_append, List.map_singleton, hrun_snoc, hrun_snoc]
            have hlen1 : (run (gs.map mg) (List.ofFn y)).length = 26 + gs.length := by
              rw [hrun_len, List.length_ofFn, List.length_map]
            have hlen2 : (run gs (List.ofFn (fun a : Fin 26 => y (e a)))).length = 26 + gs.length := by
              rw [hrun_len, List.length_ofFn]
            rcases Nat.lt_trichotomy w (26 + gs.length) with hlt | heq | hgt
            · have hmlt : mw w < 26 + gs.length := hmw_lt w gs.length hlt
              rw [hgetD_lt _ _ _ (by omega), hgetD_lt _ _ _ (by omega)]
              exact ih w
            · subst heq
              have hmw_eq : mw (26 + gs.length) = 26 + gs.length := by dsimp only [mw]; rw [dif_neg (by omega)]
              rw [hmw_eq]
              have h1 : (run (gs.map mg) (List.ofFn y) ++
                  [(mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false)]).getD
                  (26 + gs.length) false =
                  (mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false) := by
                rw [← hlen1]; exact hgetD_at _ _
              have h2 : (run gs (List.ofFn (fun a : Fin 26 => y (e a))) ++
                  [g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun a : Fin 26 => y (e a)))).getD i false)]).getD
                  (26 + gs.length) false =
                  g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun a : Fin 26 => y (e a)))).getD i false) := by
                rw [← hlen2]; exact hgetD_at _ _
              rw [h1, h2]; dsimp only [mg]; rw [List.map_map]
              congr 1; refine List.map_congr_left fun i _ => ih i
            · have hmw_eq : mw w = w := by dsimp only [mw]; rw [dif_neg (by omega)]
              rw [hmw_eq]
              rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
              rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
        have hD_AO : PEqualNP.EdgeOwnership.AndOrOnly D := by
          intro g hg; rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩; exact hAO g0 hg0
        have hD_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D := by
          intro j hj k hk
          rw [List.length_map] at hj
          have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt D j = mg (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
            change (C.gates.map mg).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
              mg (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
            rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getD_eq_getElem _ _ hj, List.getElem_map]
          rw [hgd] at hk
          rcases List.mem_map.mp hk with ⟨i, hi, rfl⟩
          exact hmw_lt i j (hRB j hj i hi)
        have hD_Len2 : ∀ g ∈ D.gates, g.inputs.length = 2 := by
          intro g hg; rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
          dsimp only [mg]; rw [List.length_map]; exact hLen2 g0 hg0
        have hD_sz : D.size ≤ 63 := by change (C.gates.map mg).length ≤ 63; rw [List.length_map]; exact hsz63
        have hD_spec : ∀ y : Fin 26 → Bool, D.eval (List.ofFn y) = true ↔
            ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
              y (Fin.castAdd 13 p) = true ∧ y (Fin.natAdd 13 l) = true := by
          intro y
          have h1 : D.eval (List.ofFn y) = C.eval (List.ofFn (fun a => y (e a))) := hD_run C.gates y C.output
          rw [h1, hspec]
          constructor
          · rintro ⟨p, l, hpl, hp, hl⟩
            have hadj : G0.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) :=
              (hrel_iff _ _).mpr ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
            have hadj' : G0.Adj (e (Fin.castAdd 13 p)) (e (Fin.natAdd 13 l)) := (haut _ _).mpr hadj
            rcases (hrel_iff _ _).mp hadj' with ⟨p', l', hpl', ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
            · exact ⟨p', l', hpl', h1' ▸ hp, h2' ▸ hl⟩
            · exact ⟨p', l', hpl', h1' ▸ hl, h2' ▸ hp⟩
          · rintro ⟨p, l, hpl, hp, hl⟩
            have hadj : G0.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) :=
              (hrel_iff _ _).mpr ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
            have hadj' : G0.Adj (eInv (Fin.castAdd 13 p)) (eInv (Fin.natAdd 13 l)) :=
              (haut _ _).mp (by rw [hri, hri]; exact hadj)
            rcases (hrel_iff _ _).mp hadj' with ⟨p', l', hpl', ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
            · refine ⟨p', l', hpl', ?_, ?_⟩
              · rw [← h1', hri]; exact hp
              · rw [← h2', hri]; exact hl
            · refine ⟨p', l', hpl', ?_, ?_⟩
              · rw [← h1', hri]; exact hl
              · rw [← h2', hri]; exact hp
        have hj0_D_lt : j0 < D.gates.length := by change j0 < (C.gates.map mg).length; rw [List.length_map]; exact hj0_lt
        have hj0_D_and : (PEqualNP.MetaComplexity.NestedCover.gateAt D j0).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt D j0 = mg (PEqualNP.MetaComplexity.NestedCover.gateAt C j0) := by
            change (C.gates.map mg).getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
              mg (C.gates.getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
            rw [List.getD_eq_getElem _ _ hj0_D_lt, List.getD_eq_getElem _ _ hj0_lt, List.getElem_map]
          rw [hgd]; exact hj0_and
        have hj0_D_val : (D.wires (List.ofFn (fun t : Fin 26 => decide (t = e u ∨ t = e v)))).getD (26 + j0) false = true := by
          have hmw_j0 : mw (26 + j0) = 26 + j0 := by dsimp only [mw]; rw [dif_neg (by omega)]
          have hstep := hD_run C.gates (fun t : Fin 26 => decide (t = e u ∨ t = e v)) (26 + j0)
          rw [hmw_j0] at hstep
          change (run (C.gates.map mg) (List.ofFn (fun t : Fin 26 => decide (t = e u ∨ t = e v)))).getD (26 + j0) false = true
          rw [hstep]
          have hpeq : (fun a : Fin 26 => decide (e a = e u ∨ e a = e v)) = (fun a : Fin 26 => decide (a = u ∨ a = v)) := by
            funext a
            apply Bool.eq_iff_iff.mpr
            rw [decide_eq_true_eq, decide_eq_true_eq]
            constructor
            · rintro (h | h)
              · exact Or.inl (by have := congrArg eInv h; rw [hli, hli] at this; exact this)
              · exact Or.inr (by have := congrArg eInv h; rw [hli, hli] at this; exact this)
            · rintro (rfl | rfl)
              · exact Or.inl rfl
              · exact Or.inr rfl
          rw [hpeq]; exact hj0_uv
        rcases heuv with ⟨heu0, hev0 | hev1 | hev14⟩
        · rw [heu0, hev0] at hj0_D_val
          have hmono01 : (D.wires (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (1 : Fin 26))))).getD (26 + j0) false = true := by
            refine hrun_mono D.gates hD_AO
              (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (0 : Fin 26))))
              (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (1 : Fin 26))))
              (by rw [List.length_ofFn, List.length_ofFn]) ?_ (26 + j0) hj0_D_val
            intro k hk
            by_cases hk26 : k < 26
            · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk26] at hk ⊢
              change decide (⟨k, hk26⟩ = (0 : Fin 26) ∨ ⟨k, hk26⟩ = (0 : Fin 26)) = true at hk
              change decide (⟨k, hk26⟩ = (0 : Fin 26) ∨ ⟨k, hk26⟩ = (1 : Fin 26)) = true
              rw [decide_eq_true_eq] at hk ⊢
              rcases hk with h | h <;> exact Or.inl h
            · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
          exact hSameSide D ⟨hD_AO, hD_RB, hD_Len2⟩ hD_sz hD_spec ⟨j0, hj0_D_lt, hj0_D_and, hmono01⟩
        · rw [heu0, hev1] at hj0_D_val
          exact hSameSide D ⟨hD_AO, hD_RB, hD_Len2⟩ hD_sz hD_spec ⟨j0, hj0_D_lt, hj0_D_and, hj0_D_val⟩
        · rw [heu0, hev14] at hj0_D_val
          exact hCross D ⟨hD_AO, hD_RB, hD_Len2⟩ hD_sz hD_spec ⟨j0, hj0_D_lt, hj0_D_and, hj0_D_val⟩
      let tblFun : List ℕ → Fin 26 → Fin 26 := fun L a => Fin.ofNat 26 (L.getD a.val 0)
      let dual : Fin 26 → Fin 26 := fun a =>
        if a.val < 13 then Fin.natAdd 13 (-Fin.ofNat 13 a.val)
        else Fin.castAdd 13 (-Fin.ofNat 13 (a.val - 13))
      let shift : Fin 13 → Fin 26 → Fin 26 := fun c a =>
        if a.val < 13 then Fin.castAdd 13 (Fin.ofNat 13 a.val - c)
        else Fin.natAdd 13 (Fin.ofNat 13 (a.val - 13) - c)
      let frob : Fin 26 → Fin 26 := fun a =>
        if a.val < 13 then Fin.castAdd 13 (3 * Fin.ofNat 13 a.val)
        else Fin.natAdd 13 (3 * Fin.ofNat 13 (a.val - 13))
      let frob2 : Fin 26 → Fin 26 := fun a =>
        if a.val < 13 then Fin.castAdd 13 (9 * Fin.ofNat 13 a.val)
        else Fin.natAdd 13 (9 * Fin.ofNat 13 (a.val - 13))
      let p2L : List ℕ := [0, 4, 1, 7, 2, 12, 6, 8, 3, 5, 10, 11, 9, 17, 14, 24, 19, 25, 16, 18, 20, 15, 22, 23, 21, 13]
      let p4L : List ℕ := [0, 2, 4, 8, 1, 9, 6, 3, 7, 12, 10, 11, 5, 25, 14, 21, 18, 13, 19, 16, 20, 24, 22, 23, 15, 17]
      let p7L : List ℕ := [0, 12, 5, 2, 9, 3, 6, 1, 4, 8, 10, 11, 7, 25, 22, 15, 19, 13, 16, 18, 14, 21, 20, 23, 24, 17]
      let p7iL : List ℕ := [0, 7, 3, 5, 8, 2, 6, 12, 9, 4, 10, 11, 1, 17, 20, 15, 18, 25, 19, 16, 22, 21, 14, 23, 24, 13]
      let l2L : List ℕ := [0, 11, 4, 10, 8, 2, 3, 12, 5, 6, 9, 1, 7, 23, 21, 14, 20, 25, 15, 16, 22, 18, 19, 13, 24, 17]
      let l2iL : List ℕ := [0, 11, 5, 6, 2, 8, 9, 12, 4, 10, 3, 1, 7, 23, 15, 18, 19, 25, 21, 22, 16, 14, 20, 13, 24, 17]
      let cP2 := tblFun p2L
      let cP4 := tblFun p4L
      let cP7 := tblFun p7L
      let cP7i := tblFun p7iL
      let cL2 := tblFun l2L
      let cL2i := tblFun l2iL
      let isAut : (Fin 26 → Fin 26) → (Fin 26 → Fin 26) → Prop := fun f g =>
        (∀ a : Fin 26, g (f a) = a) ∧ (∀ a : Fin 26, f (g a) = a) ∧ (∀ a b : Fin 26, G0.Adj (f a) (f b) ↔ G0.Adj a b)
      have hcomp : ∀ f1 g1 f2 g2, isAut f1 g1 → isAut f2 g2 → isAut (fun a => f2 (f1 a)) (fun a => g1 (g2 a)) := by
        intro f1 g1 f2 g2 h1 h2
        exact ⟨fun a => by dsimp only; rw [h2.1, h1.1], fun a => by dsimp only; rw [h1.2.1, h2.2.1],
          fun a b => (h2.2.2 _ _).trans (h1.2.2 a b)⟩
      have hid_aut : isAut id id := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩
      have hdual_aut : isAut dual dual := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, dual]; decide +kernel
      have hshift_aut : ∀ c : Fin 13, isAut (shift c) (shift (-c)) := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, shift]; decide +kernel
      have hfrob_aut : isAut frob frob2 := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, frob, frob2]; decide +kernel
      have hfrob2_aut : isAut frob2 frob := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, frob, frob2]; decide +kernel
      have hcP2_aut : isAut cP2 cP4 := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, cP2, cP4, tblFun, p2L, p4L]; decide +kernel
      have hcP4_aut : isAut cP4 cP2 := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, cP2, cP4, tblFun, p2L, p4L]; decide +kernel
      have hcP7_aut : isAut cP7 cP7i := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, cP7, cP7i, tblFun, p7L, p7iL]; decide +kernel
      have hcL2_aut : isAut cL2 cL2i := by dsimp only [isAut, G0, rel0, SimpleGraph.fromRel, cL2, cL2i, tblFun, l2L, l2iL]; decide +kernel
      have hstep1 : ∃ f1 g1, isAut f1 g1 ∧ f1 u = 0 := by
        by_cases hu13 : u.val < 13
        · refine ⟨shift (Fin.ofNat 13 u.val), shift (-Fin.ofNat 13 u.val), hshift_aut _, ?_⟩
          dsimp only [shift]; rw [if_pos hu13, sub_self]; rfl
        · let c : Fin 13 := -Fin.ofNat 13 (u.val - 13)
          refine ⟨fun a => shift c (dual a), fun a => dual (shift (-c) a), hcomp _ _ _ _ hdual_aut (hshift_aut c), ?_⟩
          dsimp only [dual, shift]; rw [if_neg hu13]
          have hc13 : (Fin.castAdd 13 c).val < 13 := by rw [Fin.val_castAdd]; exact c.isLt
          rw [if_pos hc13]
          have hceq : Fin.ofNat 13 (Fin.castAdd 13 c).val = c := by rw [Fin.val_castAdd]; exact Fin.ext (Nat.mod_eq_of_lt c.isLt)
          rw [hceq, sub_self]; rfl
      rcases hstep1 with ⟨f1, g1, hf1, hfu0⟩
      have hnot_adj0w : ¬ G0.Adj 0 (f1 v) := by
        intro h0w; apply hnot_adj; rw [← hfu0] at h0w; exact (hf1.2.2 u v).mp h0w
      have hcases_all : ∀ w : Fin 26, ¬ G0.Adj 0 w →
          (w = 0) ∨ (w = 1) ∨ (w = 3) ∨ (w = 9) ∨ (w = 2) ∨ (w = 6) ∨ (w = 5) ∨
          (w = 4) ∨ (w = 12) ∨ (w = 10) ∨ (w = 7) ∨ (w = 8) ∨ (w = 11) ∨
          (w = 14) ∨ (w = 16) ∨ (w = 22) ∨ (w = 15) ∨ (w = 19) ∨ (w = 18) ∨ (w = 20) ∨ (w = 21) ∨ (w = 24) := by
        dsimp only [G0, rel0, SimpleGraph.fromRel]; decide +kernel
      have horb : ∀ w : Fin 26, ¬ G0.Adj 0 w →
          ∃ f2 g2, isAut f2 g2 ∧ f2 0 = 0 ∧ (f2 w = 0 ∨ f2 w = 1 ∨ f2 w = 14) := by
        intro w hnw
        rcases hcases_all w hnw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨id, id, hid_aut, rfl, Or.inl rfl⟩
        · exact ⟨id, id, hid_aut, rfl, Or.inr (Or.inl rfl)⟩
        · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨cP2, cP4, hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP2 (frob2 a), fun a => frob (cP4 a), hcomp _ _ _ _ hfrob2_aut hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP2 (frob a), fun a => frob2 (cP4 a), hcomp _ _ _ _ hfrob_aut hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨cP4, cP2, hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP4 (frob2 a), fun a => frob (cP2 a), hcomp _ _ _ _ hfrob2_aut hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP4 (frob a), fun a => frob2 (cP2 a), hcomp _ _ _ _ hfrob_aut hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨cP7, cP7i, hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP7 (frob2 a), fun a => frob (cP7i a), hcomp _ _ _ _ hfrob2_aut hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨fun a => cP7 (frob a), fun a => frob2 (cP7i a), hcomp _ _ _ _ hfrob_aut hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
        · exact ⟨id, id, hid_aut, rfl, Or.inr (Or.inr rfl)⟩
        · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨cL2, cL2i, hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨fun a => cL2 (frob2 a), fun a => frob (cL2i a), hcomp _ _ _ _ hfrob2_aut hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨fun a => cL2 (frob a), fun a => frob2 (cL2i a), hcomp _ _ _ _ hfrob_aut hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨cP7, cP7i, hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨fun a => cP7 (frob2 a), fun a => frob (cP7i a), hcomp _ _ _ _ hfrob2_aut hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
        · exact ⟨fun a => cP7 (frob a), fun a => frob2 (cP7i a), hcomp _ _ _ _ hfrob_aut hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
      rcases horb (f1 v) hnot_adj0w with ⟨f2, g2, hf2, hf20, hf2w⟩
      have htot := hcomp _ _ _ _ hf1 hf2
      exact hrelabel (fun a => f2 (f1 a)) (fun a => g1 (g2 a)) htot.1 htot.2.1 htot.2.2 ⟨by rw [hfu0, hf20], hf2w⟩
    · rw [hinputs] at hj0_len2; cases hj0_len2
