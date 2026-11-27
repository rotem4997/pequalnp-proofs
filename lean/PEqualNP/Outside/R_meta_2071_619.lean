import PEqualNP.Defs

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2071_619
    (hSameSide :
      let Dset : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (v w : ℕ → Bool),
        let trace : Fin 26 → ℕ → (ℕ → Bool) → Prop := fun a b f =>
          (∀ i < 26, f i = decide (i = b)) ∧
          let ws : List Bool := C.wires (List.ofFn fun i : Fin 26 => decide (i = a))
          ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x y : ℕ),
            C.gates[j]? = some g → g.inputs = [x, y] →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              f (26 + j) = (ws.getD x false && f y || f x && ws.getD y false)) ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → f (26 + j) = (f x || f y))
        C.size ≤ 64 →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ (u t : Fin 13), u - t ∈ Dset ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (C.wires (List.ofFn (fun i : Fin 26 => decide (i = (0 : Fin 26) ∨ i = (1 : Fin 26))))).getD (26 + j) false = true) →
        p - l ∈ Dset →
        trace (Fin.castAdd 13 p) (13 + l.val) v →
        trace (Fin.natAdd 13 l) p.val w →
        v C.output = true ∨ w C.output = true)
    (hCross :
      let Dset : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (v w : ℕ → Bool),
        let trace : Fin 26 → ℕ → (ℕ → Bool) → Prop := fun a b f =>
          (∀ i < 26, f i = decide (i = b)) ∧
          let ws : List Bool := C.wires (List.ofFn fun i : Fin 26 => decide (i = a))
          ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x y : ℕ),
            C.gates[j]? = some g → g.inputs = [x, y] →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              f (26 + j) = (ws.getD x false && f y || f x && ws.getD y false)) ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → f (26 + j) = (f x || f y))
        C.size ≤ 64 →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ (u t : Fin 13), u - t ∈ Dset ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (C.wires (List.ofFn (fun i : Fin 26 => decide (i = (0 : Fin 26) ∨ i = (14 : Fin 26))))).getD (26 + j) false = true) →
        p - l ∈ Dset →
        trace (Fin.castAdd 13 p) (13 + l.val) v →
        trace (Fin.natAdd 13 l) p.val w →
        v C.output = true ∨ w C.output = true)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  classical
  dsimp only
  intro C p l v w hsz64 hsyn hspec handPairs hdirty_ex hinc hv hw
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact (hsyn j C.gates[j] (List.getElem?_eq_getElem hj)).1
  have hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C := by
    intro j hj k hk
    have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = C.gates[j]
      exact List.getD_eq_getElem _ _ hj
    rw [hgd] at hk
    obtain ⟨a, b, hab, _, ha, hb⟩ := (hsyn j C.gates[j] (List.getElem?_eq_getElem hj)).2
    rw [hab] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ha
    · exact hb
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a, b, hab, _⟩ := (hsyn j C.gates[j] (List.getElem?_eq_getElem hj)).2
    rw [hab]; rfl
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
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw26] at hwtrue
          exact hwtrue
        · rw [hrun_input C.gates _ w (by rw [List.length_ofFn]; exact hw26)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw26]
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
          rw [ite_eq_left hk_lt] at hk_true
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
          exact ⟨k, hk_in, by dsimp only [Function.comp, id]; rw [ite_eq_left hk_lt]; exact hku⟩
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
    rw [ite_eq_left hw1_lt, ite_eq_left hw2_lt, Bool.and_true, Bool.and_eq_true] at hx_val
    rcases hsingle_witness w1 hw1_lt hx_val.1 with ⟨u, hxu, hwu⟩
    rcases hsingle_witness w2 hw2_lt hx_val.2 with ⟨v0, hxv0, hwv0⟩
    let rel0 : Fin 26 → Fin 26 → Prop := fun a b =>
      a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
    let G0 : SimpleGraph (Fin 26) := SimpleGraph.fromRel rel0
    have hrel_iff : ∀ a b : Fin 26, G0.Adj a b ↔
        ∃ (p' l' : Fin 13), p' - l' ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          (a = Fin.castAdd 13 p' ∧ b = Fin.natAdd 13 l' ∨ b = Fin.castAdd 13 p' ∧ a = Fin.natAdd 13 l') := by
      dsimp only [G0, rel0, SimpleGraph.fromRel]
      decide +kernel
    have hnot_adj : ¬ G0.Adj u v0 := by
      intro hadj
      rcases (hrel_iff u v0).mp hadj with ⟨p', l', hpl', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · have htr := (hspec x).mpr ⟨p', l', hpl', hxu, hxv0⟩
        rw [hx_false] at htr; cases htr
      · have htr := (hspec x).mpr ⟨p', l', hpl', hxv0, hxu⟩
        rw [hx_false] at htr; cases htr
    have hw1_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD w1 false = true := by
      refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 26 => decide (t = u)))
        (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0))) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w1 hwu
      intro k hk
      by_cases hk26 : k < 26
      · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hk26] at hk ⊢
        change decide (⟨k, hk26⟩ = u) = true at hk
        change decide (⟨k, hk26⟩ = u ∨ ⟨k, hk26⟩ = v0) = true
        rw [decide_eq_true_eq] at hk ⊢; exact Or.inl hk
      · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
    have hw2_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD w2 false = true := by
      refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 26 => decide (t = v0)))
        (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0))) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w2 hwv0
      intro k hk
      by_cases hk26 : k < 26
      · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hk26] at hk ⊢
        change decide (⟨k, hk26⟩ = v0) = true at hk
        change decide (⟨k, hk26⟩ = u ∨ ⟨k, hk26⟩ = v0) = true
        rw [decide_eq_true_eq] at hk ⊢; exact Or.inr hk
      · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
    have hj0_uv : (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD (26 + j0) false = true := by
      have hrgp := hrun_gate C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0))) j0 hj0_lt
      rw [List.length_ofFn] at hrgp
      rw [hrgp]
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.map fun k =>
          if k < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD k false else false) = true
      rw [hj0_and, hinputs]
      change (if w1 < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD w1 false else false) &&
        ((if w2 < 26 + j0 then (run C.gates (List.ofFn (fun t : Fin 26 => decide (t = u ∨ t = v0)))).getD w2 false else false) && true) = true
      rw [ite_eq_left hw1_lt, ite_eq_left hw2_lt, hw1_uv, hw2_uv]; rfl
    have hrelabel : ∀ (e eInv : Fin 26 → Fin 26),
        (∀ a : Fin 26, eInv (e a) = a) →
        (∀ a : Fin 26, e (eInv a) = a) →
        (∀ a b : Fin 26, G0.Adj (e a) (e b) ↔ G0.Adj a b) →
        (e u = 0 ∧ (e v0 = 0 ∨ e v0 = 1 ∨ e v0 = 14)) →
        v C.output = true ∨ w C.output = true := by
      intro e eInv hli hri haut heuv
      let mw : ℕ → ℕ := fun a => if h : a < 26 then (e ⟨a, h⟩).val else a
      let mwInv : ℕ → ℕ := fun a => if h : a < 26 then (eInv ⟨a, h⟩).val else a
      let mg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g => ⟨g.op, g.inputs.map mw⟩
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map mg, mw C.output⟩
      have hmw_lt : ∀ a k : ℕ, a < 26 + k → mw a < 26 + k := by
        intro a k ha; dsimp only [mw]; split_ifs with h26
        · have := (e ⟨a, h26⟩).isLt; omega
        · exact ha
      have hmw_inv_l : ∀ a : ℕ, mwInv (mw a) = a := by
        intro a; dsimp only [mw, mwInv]
        by_cases ha : a < 26
        · rw [dite_eq_left ha, dite_eq_left (e ⟨a, ha⟩).isLt]
          exact congrArg Fin.val (hli ⟨a, ha⟩)
        · rw [dite_eq_right ha, dite_eq_right ha]
      have hmw_inv_r : ∀ a : ℕ, mw (mwInv a) = a := by
        intro a; dsimp only [mw, mwInv]
        by_cases ha : a < 26
        · rw [dite_eq_left ha, dite_eq_left (eInv ⟨a, ha⟩).isLt]
          exact congrArg Fin.val (hri ⟨a, ha⟩)
        · rw [dite_eq_right ha, dite_eq_right ha]
      have hmw_inj : Function.Injective mw := fun a b h => by
        have := congrArg mwInv h; rw [hmw_inv_l, hmw_inv_l] at this; exact this
      have hD_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (y : Fin 26 → Bool) (a : ℕ),
          (run (gs.map mg) (List.ofFn y)).getD (mw a) false =
            (run gs (List.ofFn (fun t : Fin 26 => y (e t)))).getD a false := by
        intro gs y
        induction gs using List.reverseRecOn with
        | nil =>
          intro a
          change (List.ofFn y).getD (mw a) false = (List.ofFn (fun t : Fin 26 => y (e t))).getD a false
          dsimp only [mw]
          split_ifs with h26
          · have hlt := (e ⟨a, h26⟩).isLt
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hlt]
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h26]
          · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
            rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        | append_singleton gs g ih =>
          intro a
          rw [List.map_append, List.map_singleton, hrun_snoc, hrun_snoc]
          have hlen1 : (run (gs.map mg) (List.ofFn y)).length = 26 + gs.length := by
            rw [hrun_len, List.length_ofFn, List.length_map]
          have hlen2 : (run gs (List.ofFn (fun t : Fin 26 => y (e t)))).length = 26 + gs.length := by
            rw [hrun_len, List.length_ofFn]
          rcases Nat.lt_trichotomy a (26 + gs.length) with hlt | heq | hgt
          · have hmlt : mw a < 26 + gs.length := hmw_lt a gs.length hlt
            rw [hgetD_lt _ _ _ (by omega), hgetD_lt _ _ _ (by omega)]
            exact ih a
          · subst heq
            have hmw_eq : mw (26 + gs.length) = 26 + gs.length := by dsimp only [mw]; rw [dite_eq_right (by omega)]
            rw [hmw_eq]
            have h1 : (run (gs.map mg) (List.ofFn y) ++
                [(mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false)]).getD
                (26 + gs.length) false =
                (mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false) := by
              rw [← hlen1]; exact hgetD_at _ _
            have h2 : (run gs (List.ofFn (fun t : Fin 26 => y (e t))) ++
                [g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun t : Fin 26 => y (e t)))).getD i false)]).getD
                (26 + gs.length) false =
                g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun t : Fin 26 => y (e t)))).getD i false) := by
              rw [← hlen2]; exact hgetD_at _ _
            rw [h1, h2]; dsimp only [mg]; rw [List.map_map]
            congr 1; refine List.map_congr_left fun i _ => ih i
          · have hmw_eq : mw a = a := by dsimp only [mw]; rw [dite_eq_right (by omega)]
            rw [hmw_eq]
            rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
            rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
      have hD_sz : D.size ≤ 64 := by change (C.gates.map mg).length ≤ 64; rw [List.length_map]; exact hsz64
      have hD_syn : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
        intro j g hj
        change (C.gates.map mg)[j]? = some g at hj
        rw [List.getElem?_map] at hj
        cases hc : C.gates[j]? with
        | none => rw [hc] at hj; cases hj
        | some g0 =>
          rw [hc] at hj
          simp only [Option.map_some, Option.some.injEq] at hj
          subst hj
          obtain ⟨hop, a, b, hab, hne, ha, hb⟩ := hsyn j g0 hc
          refine ⟨hop, mw a, mw b, ?_, fun h => hne (hmw_inj h), hmw_lt a j ha, hmw_lt b j hb⟩
          simp [mg, hab]
      have hD_spec : ∀ y : Fin 26 → Bool, D.eval (List.ofFn y) = true ↔
          ∃ (u' t' : Fin 13), u' - t' ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
            y (Fin.castAdd 13 u') = true ∧ y (Fin.natAdd 13 t') = true := by
        intro y
        have h1 : D.eval (List.ofFn y) = C.eval (List.ofFn (fun a => y (e a))) := hD_run C.gates y C.output
        rw [h1, hspec]
        constructor
        · rintro ⟨p', l', hpl', hp', hl'⟩
          have hadj : G0.Adj (Fin.castAdd 13 p') (Fin.natAdd 13 l') :=
            (hrel_iff _ _).mpr ⟨p', l', hpl', Or.inl ⟨rfl, rfl⟩⟩
          have hadj' : G0.Adj (e (Fin.castAdd 13 p')) (e (Fin.natAdd 13 l')) := (haut _ _).mpr hadj
          rcases (hrel_iff _ _).mp hadj' with ⟨p'', l'', hpl'', ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
          · exact ⟨p'', l'', hpl'', h1' ▸ hp', h2' ▸ hl'⟩
          · exact ⟨p'', l'', hpl'', h1' ▸ hl', h2' ▸ hp'⟩
        · rintro ⟨p', l', hpl', hp', hl'⟩
          have hadj : G0.Adj (Fin.castAdd 13 p') (Fin.natAdd 13 l') :=
            (hrel_iff _ _).mpr ⟨p', l', hpl', Or.inl ⟨rfl, rfl⟩⟩
          have hadj' : G0.Adj (eInv (Fin.castAdd 13 p')) (eInv (Fin.natAdd 13 l')) :=
            (haut _ _).mp (by rw [hri, hri]; exact hadj)
          rcases (hrel_iff _ _).mp hadj' with ⟨p'', l'', hpl'', ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
          · refine ⟨p'', l'', hpl'', ?_, ?_⟩
            · rw [← h1', hri]; exact hp'
            · rw [← h2', hri]; exact hl'
          · refine ⟨p'', l'', hpl'', ?_, ?_⟩
            · rw [← h1', hri]; exact hl'
            · rw [← h2', hri]; exact hp'
      have hD_cones : PEqualNP.EdgeOwnership.cones 26 D = PEqualNP.EdgeOwnership.cones 26 C := by
        change (C.gates.map mg).foldl (PEqualNP.EdgeOwnership.coneStep 26) [] =
          C.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []
        rw [List.foldl_map]
        have hstep : ∀ (cs : List (List ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate),
            PEqualNP.EdgeOwnership.coneStep 26 cs (mg g) = PEqualNP.EdgeOwnership.coneStep 26 cs g := by
          intro cs g
          unfold PEqualNP.EdgeOwnership.coneStep
          congr 2
          dsimp only [mg]
          have hfilt : ∀ l : List ℕ,
              (l.map mw).filter (fun a => decide (26 ≤ a ∧ a < 26 + cs.length)) =
              l.filter (fun a => decide (26 ≤ a ∧ a < 26 + cs.length)) := by
            intro l
            induction l with
            | nil => rfl
            | cons a rest ih =>
              simp only [List.map_cons, List.filter_cons]
              by_cases ha : a < 26
              · have hma : mw a < 26 := by dsimp only [mw]; rw [dite_eq_left ha]; exact (e ⟨a, ha⟩).isLt
                have h1 : decide (26 ≤ mw a ∧ mw a < 26 + cs.length) = false := decide_eq_false (by omega)
                have h2 : decide (26 ≤ a ∧ a < 26 + cs.length) = false := decide_eq_false (by omega)
                rw [h1, h2]; exact ih
              · have hma : mw a = a := by dsimp only [mw]; rw [dite_eq_right ha]
                rw [hma]
                cases decide (26 ≤ a ∧ a < 26 + cs.length)
                · exact ih
                · exact congrArg (List.cons a) ih
          rw [hfilt]
        have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List (List ℕ)),
            gs.foldl (fun cs g => PEqualNP.EdgeOwnership.coneStep 26 cs (mg g)) init =
            gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) init := by
          intro gs
          induction gs with
          | nil => intro init; rfl
          | cons g rest ih => intro init; simp only [List.foldl_cons, hstep, ih]
        exact hfold C.gates []
      have hD_andPairs : 0 < PEqualNP.TopForm.andPairs 26 D := by
        have heq : PEqualNP.TopForm.andPairs 26 D = PEqualNP.TopForm.andPairs 26 C := by
          unfold PEqualNP.TopForm.andPairs
          have hlen : D.gates.length = C.gates.length := List.length_map _
          rw [hlen]
          congr 1
          ext q
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          refine and_congr_right fun hq => ?_
          have hgD : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op =
              (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op := by
            intro k hk
            change ((C.gates.map mg).getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
              (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op
            rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getD_eq_getElem _ _ hk, List.getElem_map]
          have hic : PEqualNP.EdgeOwnership.InCone 26 D q.1 q.2 ↔ PEqualNP.EdgeOwnership.InCone 26 C q.1 q.2 := by
            unfold PEqualNP.EdgeOwnership.InCone; rw [hD_cones]
          rw [hgD q.1 hq.1, hgD q.2 hq.2, hic]
        rw [heq]; exact handPairs
      have hD_AO : PEqualNP.EdgeOwnership.AndOrOnly D := by
        intro g hg; rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩; exact hAO g0 hg0
      have hj0_D_lt : j0 < D.gates.length := by change j0 < (C.gates.map mg).length; rw [List.length_map]; exact hj0_lt
      have hj0_D_and : (PEqualNP.MetaComplexity.NestedCover.gateAt D j0).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
        have hgd : PEqualNP.MetaComplexity.NestedCover.gateAt D j0 = mg (PEqualNP.MetaComplexity.NestedCover.gateAt C j0) := by
          change (C.gates.map mg).getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            mg (C.gates.getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          rw [List.getD_eq_getElem _ _ hj0_D_lt, List.getD_eq_getElem _ _ hj0_lt, List.getElem_map]
        rw [hgd]; exact hj0_and
      have hj0_D_val : (D.wires (List.ofFn (fun t : Fin 26 => decide (t = e u ∨ t = e v0)))).getD (26 + j0) false = true := by
        have hmw_j0 : mw (26 + j0) = 26 + j0 := by dsimp only [mw]; rw [dite_eq_right (by omega)]
        have hstep := hD_run C.gates (fun t : Fin 26 => decide (t = e u ∨ t = e v0)) (26 + j0)
        rw [hmw_j0] at hstep
        change (run (C.gates.map mg) (List.ofFn (fun t : Fin 26 => decide (t = e u ∨ t = e v0)))).getD (26 + j0) false = true
        rw [hstep]
        have hpeq : (fun a : Fin 26 => decide (e a = e u ∨ e a = e v0)) = (fun a : Fin 26 => decide (a = u ∨ a = v0)) := by
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
      have htrace_map : ∀ (a0 b0 : Fin 26) (f : ℕ → Bool),
          ((∀ k < 26, f k = decide (k = b0.val)) ∧
            ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x1 x2 : ℕ),
              C.gates[j]? = some g → g.inputs = [x1, x2] →
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
                f (26 + j) = ((C.wires (List.ofFn fun t : Fin 26 => decide (t = a0))).getD x1 false && f x2 ||
                  f x1 && (C.wires (List.ofFn fun t : Fin 26 => decide (t = a0))).getD x2 false)) ∧
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → f (26 + j) = (f x1 || f x2))) →
          ((∀ k < 26, f (mwInv k) = decide (k = (e b0).val)) ∧
            ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x1 x2 : ℕ),
              D.gates[j]? = some g → g.inputs = [x1, x2] →
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
                f (mwInv (26 + j)) = ((D.wires (List.ofFn fun t : Fin 26 => decide (t = e a0))).getD x1 false && f (mwInv x2) ||
                  f (mwInv x1) && (D.wires (List.ofFn fun t : Fin 26 => decide (t = e a0))).getD x2 false)) ∧
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → f (mwInv (26 + j)) = (f (mwInv x1) || f (mwInv x2)))) := by
        intro a0 b0 f hf
        constructor
        · intro k hk
          have hlt : mwInv k < 26 := by dsimp only [mwInv]; rw [dite_eq_left hk]; exact (eInv ⟨k, hk⟩).isLt
          rw [hf.1 (mwInv k) hlt]
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_eq, decide_eq_true_eq]
          dsimp only [mwInv]
          rw [dite_eq_left hk]
          constructor
          · intro h
            have h1 : eInv ⟨k, hk⟩ = b0 := Fin.ext h
            have h2 := congrArg e h1
            rw [hri] at h2
            exact congrArg Fin.val h2
          · intro h
            have h1 : (⟨k, hk⟩ : Fin 26) = e b0 := Fin.ext h
            have h2 := congrArg eInv h1
            rw [hli] at h2
            exact congrArg Fin.val h2
        · intro j g x1 x2 hj hg
          change (C.gates.map mg)[j]? = some g at hj
          rw [List.getElem?_map] at hj
          cases hc : C.gates[j]? with
          | none => rw [hc] at hj; cases hj
          | some g0 =>
            rw [hc] at hj
            simp only [Option.map_some, Option.some.injEq] at hj
            subst hj
            have hmw26 : mwInv (26 + j) = 26 + j := by dsimp only [mwInv]; rw [dite_eq_right (by omega)]
            rw [hmw26]
            have hg0_in : g0.inputs = [mwInv x1, mwInv x2] := by
              have hlen : g0.inputs.length = 2 := hLen2 g0 (List.mem_of_getElem? hc)
              rcases hgl : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
              · rw [hgl] at hlen; cases hlen
              · rw [hgl] at hlen; cases hlen
              · dsimp only [mg] at hg
                rw [hgl, List.map_cons, List.map_cons, List.map_nil] at hg
                simp only [List.cons.injEq, and_true] at hg
                rw [← hg.1, ← hg.2, hmw_inv_l, hmw_inv_l]
              · rw [hgl] at hlen; cases hlen
            have hw_eq : ∀ z : ℕ,
                (D.wires (List.ofFn fun t : Fin 26 => decide (t = e a0))).getD z false =
                (C.wires (List.ofFn fun t : Fin 26 => decide (t = a0))).getD (mwInv z) false := by
              intro z
              have hstep := hD_run C.gates (fun t : Fin 26 => decide (t = e a0)) (mwInv z)
              rw [hmw_inv_r z] at hstep
              change (run (C.gates.map mg) (List.ofFn fun t : Fin 26 => decide (t = e a0))).getD z false = _
              rw [hstep]
              have hfeq : (fun t : Fin 26 => decide (e t = e a0)) = (fun t : Fin 26 => decide (t = a0)) := by
                funext t
                apply Bool.eq_iff_iff.mpr
                rw [decide_eq_true_eq, decide_eq_true_eq]
                exact ⟨fun h => by have := congrArg eInv h; rw [hli, hli] at this; exact this, fun h => by rw [h]⟩
              rw [hfeq]; rfl
            have hrec := hf.2 j g0 (mwInv x1) (mwInv x2) hc hg0_in
            rw [hw_eq x1, hw_eq x2]
            exact hrec
      have hadj_pl : G0.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) :=
        (hrel_iff _ _).mpr ⟨p, l, hinc, Or.inl ⟨rfl, rfl⟩⟩
      have hadj_epl : G0.Adj (e (Fin.castAdd 13 p)) (e (Fin.natAdd 13 l)) := (haut _ _).mpr hadj_pl
      have hv_mapped := htrace_map (Fin.castAdd 13 p) (Fin.natAdd 13 l) v hv
      have hw_mapped := htrace_map (Fin.natAdd 13 l) (Fin.castAdd 13 p) w hw
      have hdispatch : ∀ (p' l' : Fin 13) (v' w' : ℕ → Bool),
          p' - l' ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
          ((∀ k < 26, v' k = decide (k = 13 + l'.val)) ∧
            ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x1 x2 : ℕ),
              D.gates[j]? = some g → g.inputs = [x1, x2] →
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
                v' (26 + j) = ((D.wires (List.ofFn fun t : Fin 26 => decide (t = Fin.castAdd 13 p'))).getD x1 false && v' x2 ||
                  v' x1 && (D.wires (List.ofFn fun t : Fin 26 => decide (t = Fin.castAdd 13 p'))).getD x2 false)) ∧
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → v' (26 + j) = (v' x1 || v' x2))) →
          ((∀ k < 26, w' k = decide (k = p'.val)) ∧
            ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (x1 x2 : ℕ),
              D.gates[j]? = some g → g.inputs = [x1, x2] →
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
                w' (26 + j) = ((D.wires (List.ofFn fun t : Fin 26 => decide (t = Fin.natAdd 13 l'))).getD x1 false && w' x2 ||
                  w' x1 && (D.wires (List.ofFn fun t : Fin 26 => decide (t = Fin.natAdd 13 l'))).getD x2 false)) ∧
              (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → w' (26 + j) = (w' x1 || w' x2))) →
          v' D.output = true ∨ w' D.output = true := by
        intro p' l' v' w' hinc' hv' hw'
        rcases heuv with ⟨heu0, hev0 | hev1 | hev14⟩
        · rw [heu0, hev0] at hj0_D_val
          have hmono01 : (D.wires (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (1 : Fin 26))))).getD (26 + j0) false = true := by
            refine hrun_mono D.gates hD_AO
              (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (0 : Fin 26))))
              (List.ofFn (fun t : Fin 26 => decide (t = (0 : Fin 26) ∨ t = (1 : Fin 26))))
              (by rw [List.length_ofFn, List.length_ofFn]) ?_ (26 + j0) hj0_D_val
            intro k hk
            by_cases hk26 : k < 26
            · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hk26] at hk ⊢
              change decide (⟨k, hk26⟩ = (0 : Fin 26) ∨ ⟨k, hk26⟩ = (0 : Fin 26)) = true at hk
              change decide (⟨k, hk26⟩ = (0 : Fin 26) ∨ ⟨k, hk26⟩ = (1 : Fin 26)) = true
              rw [decide_eq_true_eq] at hk ⊢
              rcases hk with h | h <;> exact Or.inl h
            · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
          exact hSameSide D p' l' v' w' hD_sz hD_syn hD_spec hD_andPairs ⟨j0, hj0_D_lt, hj0_D_and, hmono01⟩ hinc' hv' hw'
        · rw [heu0, hev1] at hj0_D_val
          exact hSameSide D p' l' v' w' hD_sz hD_syn hD_spec hD_andPairs ⟨j0, hj0_D_lt, hj0_D_and, hj0_D_val⟩ hinc' hv' hw'
        · rw [heu0, hev14] at hj0_D_val
          exact hCross D p' l' v' w' hD_sz hD_syn hD_spec hD_andPairs ⟨j0, hj0_D_lt, hj0_D_and, hj0_D_val⟩ hinc' hv' hw'
      rcases (hrel_iff _ _).mp hadj_epl with ⟨p', l', hpl', ⟨hp', hl'⟩ | ⟨hl', hp'⟩⟩
      · rw [hp', hl'] at hv_mapped hw_mapped
        have hres := hdispatch p' l' (fun k => v (mwInv k)) (fun k => w (mwInv k)) hpl' hv_mapped hw_mapped
        change v (mwInv (mw C.output)) = true ∨ w (mwInv (mw C.output)) = true at hres
        rw [hmw_inv_l] at hres
        exact hres
      · rw [hp', hl'] at hv_mapped hw_mapped
        have hres := hdispatch p' l' (fun k => w (mwInv k)) (fun k => v (mwInv k)) hpl' hw_mapped hv_mapped
        change w (mwInv (mw C.output)) = true ∨ v (mwInv (mw C.output)) = true at hres
        rw [hmw_inv_l] at hres
        exact hres.elim Or.inr Or.inl
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
        dsimp only [shift]; rw [ite_eq_left hu13, sub_self]; rfl
      · let c : Fin 13 := -Fin.ofNat 13 (u.val - 13)
        refine ⟨fun a => shift c (dual a), fun a => dual (shift (-c) a), hcomp _ _ _ _ hdual_aut (hshift_aut c), ?_⟩
        dsimp only [dual, shift]; rw [ite_eq_right hu13]
        have hc13 : (Fin.castAdd 13 c).val < 13 := by rw [Fin.val_castAdd]; exact c.isLt
        rw [ite_eq_left hc13]
        have hceq : Fin.ofNat 13 (Fin.castAdd 13 c).val = c := by rw [Fin.val_castAdd]; exact Fin.ext (Nat.mod_eq_of_lt c.isLt)
        rw [hceq, sub_self]; rfl
    rcases hstep1 with ⟨f1, g1, hf1, hfu0⟩
    have hnot_adj0w : ¬ G0.Adj 0 (f1 v0) := by
      intro h0w; apply hnot_adj; rw [← hfu0] at h0w; exact (hf1.2.2 u v0).mp h0w
    have hcases_all : ∀ a : Fin 26, ¬ G0.Adj 0 a →
        (a = 0) ∨ (a = 1) ∨ (a = 3) ∨ (a = 9) ∨ (a = 2) ∨ (a = 6) ∨ (a = 5) ∨
        (a = 4) ∨ (a = 12) ∨ (a = 10) ∨ (a = 7) ∨ (a = 8) ∨ (a = 11) ∨
        (a = 14) ∨ (a = 16) ∨ (a = 22) ∨ (a = 15) ∨ (a = 19) ∨ (a = 18) ∨ (a = 20) ∨ (a = 21) ∨ (a = 24) := by
      dsimp only [G0, rel0, SimpleGraph.fromRel]; decide +kernel
    have horb : ∀ a : Fin 26, ¬ G0.Adj 0 a →
        ∃ f2 g2, isAut f2 g2 ∧ f2 0 = 0 ∧ (f2 a = 0 ∨ f2 a = 1 ∨ f2 a = 14) := by
      intro a hnw
      rcases hcases_all a hnw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨id, id, hid_aut, rfl, Or.inl rfl⟩
      · exact ⟨id, id, hid_aut, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨cP2, cP4, hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP2 (frob2 t), fun t => frob (cP4 t), hcomp _ _ _ _ hfrob2_aut hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP2 (frob t), fun t => frob2 (cP4 t), hcomp _ _ _ _ hfrob_aut hcP2_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨cP4, cP2, hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP4 (frob2 t), fun t => frob (cP2 t), hcomp _ _ _ _ hfrob2_aut hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP4 (frob t), fun t => frob2 (cP2 t), hcomp _ _ _ _ hfrob_aut hcP4_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨cP7, cP7i, hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP7 (frob2 t), fun t => frob (cP7i t), hcomp _ _ _ _ hfrob2_aut hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨fun t => cP7 (frob t), fun t => frob2 (cP7i t), hcomp _ _ _ _ hfrob_aut hcP7_aut, by decide, Or.inr (Or.inl (by decide))⟩
      · exact ⟨id, id, hid_aut, rfl, Or.inr (Or.inr rfl)⟩
      · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨cL2, cL2i, hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨fun t => cL2 (frob2 t), fun t => frob (cL2i t), hcomp _ _ _ _ hfrob2_aut hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨fun t => cL2 (frob t), fun t => frob2 (cL2i t), hcomp _ _ _ _ hfrob_aut hcL2_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨cP7, cP7i, hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨fun t => cP7 (frob2 t), fun t => frob (cP7i t), hcomp _ _ _ _ hfrob2_aut hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
      · exact ⟨fun t => cP7 (frob t), fun t => frob2 (cP7i t), hcomp _ _ _ _ hfrob_aut hcP7_aut, by decide, Or.inr (Or.inr (by decide))⟩
    rcases horb (f1 v0) hnot_adj0w with ⟨f2, g2, hf2, hf20, hf2w⟩
    have htot := hcomp _ _ _ _ hf1 hf2
    exact hrelabel (fun a => f2 (f1 a)) (fun a => g1 (g2 a)) htot.1 htot.2.1 htot.2.2 ⟨by rw [hfu0, hf20], hf2w⟩
  · rw [hinputs] at hj0_len2; cases hj0_len2
