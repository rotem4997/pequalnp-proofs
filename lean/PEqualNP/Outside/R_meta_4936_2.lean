import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.SharedOr

-- By strong induction on circuit size, sanitize out-of-bounds reads and extra NOT inputs,
-- eliminate dead gates, wire aliases, and constant gates, then strip the output gate (leaving
-- at most 17 gates for top OR / top AND, or stripping both the final NOT and its input gate
-- to leave at most 16 gates for top NAND / top NOR).
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4936_2
    (topOr :
      ∀ (C : Circuit) (b : Bool) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) =>
          (C.wires (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1])).getD w false
        ReadsBack 11 C → C.size ≤ 17 → u < 11 + C.size → v < 11 + C.size →
        (∀ k < C.size,
          let g := gateAt C k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 11 C (11 + k) u ∨ InOutCone 11 C (11 + k) v) ∧
          (∀ p < 11 + k, ∃ x : Fin 10 → Bool, W x (11 + k) ≠ W x p) ∧
          ∀ c : Bool, ∃ x : Fin 10 → Bool, W x (11 + k) = c) →
        (∀ c : Bool, ∃ x : Fin 10 → Bool, W x u = c ∧ W x v = !c) →
        (∀ x, (W x u || W x v) = G x) → False)
    (topAnd :
      ∀ (C : Circuit) (b : Bool) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) =>
          (C.wires (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1])).getD w false
        ReadsBack 11 C → C.size ≤ 17 → u < 11 + C.size → v < 11 + C.size →
        (∀ k < C.size,
          let g := gateAt C k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 11 C (11 + k) u ∨ InOutCone 11 C (11 + k) v) ∧
          (∀ p < 11 + k, ∃ x : Fin 10 → Bool, W x (11 + k) ≠ W x p) ∧
          ∀ c : Bool, ∃ x : Fin 10 → Bool, W x (11 + k) = c) →
        (∀ c : Bool, ∃ x : Fin 10 → Bool, W x u = c ∧ W x v = !c) →
        (∀ x, (W x u && W x v) = G x) → False)
    (topNand :
      ∀ (C : Circuit) (b : Bool) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) =>
          (C.wires (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1])).getD w false
        ReadsBack 11 C → C.size ≤ 16 → u < 11 + C.size → v < 11 + C.size →
        (∀ k < C.size,
          let g := gateAt C k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 11 C (11 + k) u ∨ InOutCone 11 C (11 + k) v) ∧
          (∀ p < 11 + k, ∃ x : Fin 10 → Bool, W x (11 + k) ≠ W x p) ∧
          ∀ c : Bool, ∃ x : Fin 10 → Bool, W x (11 + k) = c) →
        (∀ c : Bool, ∃ x : Fin 10 → Bool, W x u = c ∧ W x v = !c) →
        (∀ x, (!(W x u && W x v)) = G x) → False)
    (topNor :
      ∀ (C : Circuit) (b : Bool) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) =>
          (C.wires (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1])).getD w false
        ReadsBack 11 C → C.size ≤ 16 → u < 11 + C.size → v < 11 + C.size →
        (∀ k < C.size,
          let g := gateAt C k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 11 C (11 + k) u ∨ InOutCone 11 C (11 + k) v) ∧
          (∀ p < 11 + k, ∃ x : Fin 10 → Bool, W x (11 + k) ≠ W x p) ∧
          ∀ c : Bool, ∃ x : Fin 10 → Bool, W x (11 + k) = c) →
        (∀ c : Bool, ∃ x : Fin 10 → Bool, W x u = c ∧ W x v = !c) →
        (∀ x, (!(W x u || W x v)) = G x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  let F := fun x : Fin 10 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  have hZeroF : F (fun _ => false) = false := by decide
  have hOneF : F (fun _ => true) = true := by decide
  have hUnitF : ∀ i : Fin 10, F (fun j => decide (j = i)) = false := by decide
  have hEdge23 : F (fun j => decide (j = 2 ∨ j = 3)) = true := by decide
  classical
  have hGF (x : Fin 10 → Bool) : G x = F x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false]
    ac_rfl
  intro C0 b hf0 hsz0 _ _
  by_contra hNoDiff
  push Not at hNoDiff
  let inp (x : Fin 10 → Bool) : List Bool :=
    List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]
  have inp_len (x : Fin 10 → Bool) : (inp x).length = 11 := by simp [inp]
  let stepWire (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let wf (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl stepWire ws
  let val (D : Circuit) (w : ℕ) (x : Fin 10 → Bool) : Bool := (D.wires (inp x)).getD w false
  have wf_len : ∀ (gs : List Gate) (ws : List Bool), (wf gs ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp [wf]
    | cons g gs ih =>
      intro ws
      change (wf gs (stepWire ws g)).length = ws.length + (gs.length + 1)
      rw [ih]; simp [stepWire]; omega
  have wf_getD_lt : ∀ (gs : List Gate) (ws : List Bool), ∀ w < ws.length,
      (wf gs ws).getD w false = ws.getD w false := by
    intro gs
    induction gs with
    | nil => intro ws w _; rfl
    | cons g gs ih =>
      intro ws w hw
      change (wf gs (stepWire ws g)).getD w false = ws.getD w false
      rw [ih _ w (by simp [stepWire]; omega)]
      simp only [stepWire, List.getD_append _ _ _ _ hw]
  have wf_append (gs1 gs2 : List Gate) (ws : List Bool) :
      wf (gs1 ++ gs2) ws = wf gs2 (wf gs1 ws) := List.foldl_append
  have gateAt_mem (D : Circuit) (k : ℕ) (hk : k < D.gates.length) : gateAt D k ∈ D.gates := by
    change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have gateAt_eq_getElem (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt D k = D.gates[k] := by
    change D.gates.getD k ⟨GateOp.or, []⟩ = D.gates[k]
    exact List.getD_eq_getElem _ _ hk
  have val_gate (D : Circuit) (k : ℕ) (hk : k < D.gates.length) (x : Fin 10 → Bool) :
      val D (11 + k) x =
        (gateAt D k).op.eval ((gateAt D k).inputs.map fun w =>
          if w < 11 + k then val D w x else false) := by
    have hsplit : D.gates = D.gates.take k ++ [D.gates[k]] ++ D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 : D.gates[k] :: D.gates.drop (k + 1) = D.gates.drop k := List.cons_getElem_drop_succ
      rw [← h2] at h1
      simp only [List.append_assoc, List.singleton_append]
      exact h1.symm
    let ws := wf (D.gates.take k) (inp x)
    have hwsLen : ws.length = 11 + k := by
      simp only [ws, wf_len, inp_len, List.length_take]; omega
    have hD : D.wires (inp x) = wf (D.gates.drop (k + 1)) (stepWire ws D.gates[k]) := by
      change wf D.gates (inp x) = _
      conv_lhs => rw [hsplit]
      rw [wf_append, wf_append]
      rfl
    have hget : val D (11 + k) x = (stepWire ws D.gates[k]).getD (11 + k) false := by
      change (D.wires (inp x)).getD (11 + k) false = _
      rw [hD, wf_getD_lt _ _ (11 + k) (by simp [stepWire, hwsLen])]
    rw [hget]
    have hlast : (stepWire ws D.gates[k]).getD (11 + k) false =
        D.gates[k].op.eval (D.gates[k].inputs.map fun w => ws.getD w false) := by
      simp only [stepWire, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hwsLen, Nat.sub_self]
      rfl
    rw [hlast, gateAt_eq_getElem D k hk]
    congr 1
    apply List.map_congr_left
    intro w _
    by_cases hwk : w < 11 + k
    · simp only [hwk, ↓reduceIte]
      change ws.getD w false = (D.wires (inp x)).getD w false
      have hwsLen1 : (stepWire ws D.gates[k]).length = 11 + k + 1 := by
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil, hwsLen]
      rw [hD, wf_getD_lt (D.gates.drop (k + 1)) (stepWire ws D.gates[k]) w (by omega)]
      exact (List.getD_append _ _ _ _ (by rw [hwsLen]; omega)).symm
    · simp only [hwk, ↓reduceIte]
      exact List.getD_eq_default _ _ (by rw [hwsLen]; omega)
  have val_gate_rb (D : Circuit) (hb : ReadsBack 11 D) (k : ℕ) (hk : k < D.gates.length)
      (x : Fin 10 → Bool) :
      val D (11 + k) x = (gateAt D k).op.eval ((gateAt D k).inputs.map fun w => val D w x) := by
    rw [val_gate D k hk x]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hlt : w < 11 + k := hb k hk w hw
    simp [hlt]
  have val_in (D : Circuit) (x : Fin 10 → Bool) (w : ℕ) (hw : w < 11) :
      val D w x = (inp x).getD w false := by
    change (wf D.gates (inp x)).getD w false = (inp x).getD w false
    rw [wf_getD_lt D.gates (inp x) w (by rw [inp_len]; exact hw)]
  have val_oob (D : Circuit) (x : Fin 10 → Bool) (w : ℕ) (hw : 11 + D.gates.length ≤ w) :
      val D w x = false := by
    change (wf D.gates (inp x)).getD w false = false
    apply List.getD_eq_default
    rw [wf_len, inp_len]
    exact hw
  have val_take (D : Circuit) (m : ℕ) (hm : m ≤ D.gates.length) (x : Fin 10 → Bool)
      (w : ℕ) (hw : w < 11 + m) :
      val ⟨D.gates.take m, 0⟩ w x = val D w x := by
    change (wf (D.gates.take m) (inp x)).getD w false = (wf D.gates (inp x)).getD w false
    have hsp : D.gates = D.gates.take m ++ D.gates.drop m := (List.take_append_drop m D.gates).symm
    conv_rhs => rw [hsp, wf_append]
    rw [wf_getD_lt (D.gates.drop m) (wf (D.gates.take m) (inp x)) w
      (by rw [wf_len, inp_len, List.length_take]; omega)]
  -- Cone helpers for n = 11
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      change (gs.foldl (coneStep 11) (coneStep 11 cs g)).length = cs.length + (gs.length + 1)
      rw [ih]; change (cs ++ _).length + gs.length = _; simp; omega
  have cones_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)), ∀ k < cs.length,
      (gs.foldl (coneStep 11) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      change (gs.foldl (coneStep 11) (coneStep 11 cs g)).getD k [] = cs.getD k []
      rw [ih _ k (by change k < (cs ++ _).length; simp; omega)]
      change (cs ++ _).getD k [] = cs.getD k []
      exact List.getD_append _ _ _ _ hk
  have inCone_lt_len (D : Circuit) (i k : ℕ) (h : InCone 11 D i k) : k < D.gates.length := by
    by_contra hge
    have hlen : (cones 11 D).length = D.gates.length := by
      change (D.gates.foldl (coneStep 11) []).length = D.gates.length
      rw [cones_len]; simp
    have hnil : (cones 11 D).getD k [] = [] := List.getD_eq_default _ _ (by omega)
    change i ∈ (cones 11 D).getD k [] at h
    rw [hnil] at h
    exact List.not_mem_nil h
  have inCone_iff (D : Circuit) (i k : ℕ) (hk : k < D.gates.length) :
      InCone 11 D i k ↔ ∃ w ∈ (gateAt D k).inputs, 11 ≤ w ∧ w < 11 + k ∧
        (i = w - 11 ∨ InCone 11 D i (w - 11)) := by
    have hsplit : D.gates = D.gates.take k ++ [D.gates[k]] ++ D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 : D.gates[k] :: D.gates.drop (k + 1) = D.gates.drop k := List.cons_getElem_drop_succ
      rw [← h2] at h1
      simp only [List.append_assoc, List.singleton_append]
      exact h1.symm
    let cs := (D.gates.take k).foldl (coneStep 11) []
    have hcsLen : cs.length = k := by
      simp only [cs, cones_len, List.length_nil, zero_add, List.length_take]; omega
    have hC : cones 11 D = (D.gates.drop (k + 1)).foldl (coneStep 11) (coneStep 11 cs D.gates[k]) := by
      change D.gates.foldl (coneStep 11) [] = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append]
      rfl
    have hget : (cones 11 D).getD k [] = (coneStep 11 cs D.gates[k]).getD k [] := by
      rw [hC, cones_getD_lt _ _ k (by change k < (cs ++ _).length; simp [hcsLen])]
    have hlast : (coneStep 11 cs D.gates[k]).getD k [] =
        (D.gates[k].inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + k))).flatMap
          (fun w => (w - 11) :: cs.getD (w - 11) []) := by
      change (cs ++ [_]).getD k [] = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hcsLen, Nat.sub_self]
      simp
    change i ∈ (cones 11 D).getD k [] ↔ _
    rw [hget, hlast, gateAt_eq_getElem D k hk, List.mem_flatMap]
    constructor
    · rintro ⟨w, hwF, hi⟩
      obtain ⟨hw, hcondB⟩ := List.mem_filter.mp hwF
      obtain ⟨h11, hlt⟩ := of_decide_eq_true hcondB
      rw [List.mem_cons] at hi
      refine ⟨w, hw, h11, hlt, ?_⟩
      rcases hi with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 11 D).getD (w - 11) []
        rw [hC, cones_getD_lt _ _ (w - 11) (by change w - 11 < (cs ++ _).length; simp [hcsLen]; omega)]
        change i ∈ (cs ++ _).getD (w - 11) []
        rw [List.getD_append _ _ _ _ (by omega : w - 11 < cs.length)]
        exact hmem
    · rintro ⟨w, hw, h11, hlt, hcase⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h11, hlt⟩⟩, ?_⟩
      rw [List.mem_cons]
      rcases hcase with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 11 D).getD (w - 11) [] at hmem
        rw [hC, cones_getD_lt _ _ (w - 11) (by change w - 11 < (cs ++ _).length; simp [hcsLen]; omega)] at hmem
        change i ∈ (cs ++ _).getD (w - 11) [] at hmem
        rw [List.getD_append _ _ _ _ (by omega : w - 11 < cs.length)] at hmem
        exact hmem
  have inCone_lt (D : Circuit) : ∀ k i, InCone 11 D i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i h
      have hk := inCone_lt_len D i k h
      obtain ⟨w, _, h11, hlt, hcase⟩ := (inCone_iff D i k hk).mp h
      rcases hcase with rfl | hsub
      · omega
      · have := ih (w - 11) (by omega) i hsub; omega
  have inCone_trans (D : Circuit) : ∀ k i j, InCone 11 D i j → InCone 11 D j k → InCone 11 D i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i j hij hjk
      have hk := inCone_lt_len D j k hjk
      obtain ⟨w, hw, h11, hlt, hcase⟩ := (inCone_iff D j k hk).mp hjk
      refine (inCone_iff D i k hk).mpr ⟨w, hw, h11, hlt, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 11) (by omega) i j hij hsub
  have inCone_take (D : Circuit) (m : ℕ) (hm : m ≤ D.gates.length) (i k : ℕ) (hk : k < m) :
      InCone 11 ⟨D.gates.take m, 0⟩ i k ↔ InCone 11 D i k := by
    have hsp : D.gates = D.gates.take m ++ D.gates.drop m := (List.take_append_drop m D.gates).symm
    change i ∈ (cones 11 ⟨D.gates.take m, 0⟩).getD k [] ↔ i ∈ (cones 11 D).getD k []
    have hC : cones 11 D = (D.gates.drop m).foldl (coneStep 11) (cones 11 ⟨D.gates.take m, 0⟩) := by
      change D.gates.foldl (coneStep 11) [] = _
      conv_lhs => rw [hsp]
      exact List.foldl_append
    have hLen : (cones 11 ⟨D.gates.take m, 0⟩).length = m := by
      change ((D.gates.take m).foldl (coneStep 11) []).length = m
      rw [cones_len, List.length_nil, zero_add, List.length_take]; omega
    rw [hC, cones_getD_lt _ _ k (by omega)]
  have inOutCone_step (D : Circuit) (hb : ReadsBack 11 D) (k u a : ℕ) (hk : k < D.gates.length)
      (hu : u ∈ (gateAt D k).inputs) (h11 : 11 ≤ u) (hka : InOutCone 11 D (11 + k) a) :
      InOutCone 11 D u a := by
    have huLt : u < 11 + k := hb k hk u hu
    have huk : InCone 11 D (u - 11) k :=
      (inCone_iff D (u - 11) k hk).mpr ⟨u, hu, h11, huLt, Or.inl rfl⟩
    rcases hka with hEq | ⟨_, ha11, hka'⟩
    · refine Or.inr ⟨h11, by omega, ?_⟩
      have : a - 11 = k := by omega
      rw [this]; exact huk
    · refine Or.inr ⟨h11, ha11, ?_⟩
      have hEq : (11 + k) - 11 = k := by omega
      rw [hEq] at hka'
      exact inCone_trans D (a - 11) (u - 11) k huk hka'
  -- Sanitize pass for n = 11
  let sanitizeGate (k : ℕ) (g : Gate) : Gate :=
    if g.op = .and then
      if g.inputs.all (fun w => decide (w < 11 + k)) then g else ⟨.or, []⟩
    else if g.op = .or then
      ⟨.or, g.inputs.filter (fun w => decide (w < 11 + k))⟩
    else
      if g.inputs.length = 0 then ⟨.and, []⟩
      else if g.inputs.headD 0 < 11 + k then ⟨.not, [g.inputs.headD 0]⟩ else ⟨.and, []⟩
  let sanitize (D : Circuit) : Circuit :=
    ⟨(List.range D.gates.length).map (fun k => sanitizeGate k (gateAt D k)), D.output⟩
  have sanitize_len (D : Circuit) : (sanitize D).gates.length = D.gates.length := by
    change ((List.range D.gates.length).map _).length = D.gates.length
    simp
  have sanitize_gateAt (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt (sanitize D) k = sanitizeGate k (gateAt D k) := by
    have hkS : k < (sanitize D).gates.length := by rw [sanitize_len]; exact hk
    rw [gateAt_eq_getElem (sanitize D) k hkS]
    change ((List.range D.gates.length).map (fun k => sanitizeGate k (gateAt D k)))[k]'(by simp [hk]) = _
    simp
  have sanitize_meta (D : Circuit) (hf : FanInTwo D) :
      FanInTwo (sanitize D) ∧ ReadsBack 11 (sanitize D) ∧
      (∀ k < (sanitize D).gates.length, (gateAt (sanitize D) k).op = .not →
        (gateAt (sanitize D) k).inputs.length = 1) := by
    have hmem_iff (g : Gate) (hg : g ∈ (sanitize D).gates) :
        ∃ k < D.gates.length, g = sanitizeGate k (gateAt D k) := by
      change g ∈ (List.range D.gates.length).map _ at hg
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      exact ⟨k, List.mem_range.mp hk, rfl⟩
    have hgate_ok (k : ℕ) (hk : k < D.gates.length) :
        ((sanitizeGate k (gateAt D k)).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          (sanitizeGate k (gateAt D k)).inputs.length ≤ 2) ∧
        (∀ w ∈ (sanitizeGate k (gateAt D k)).inputs, w < 11 + k) ∧
        ((sanitizeGate k (gateAt D k)).op = .not → (sanitizeGate k (gateAt D k)).inputs.length = 1) := by
      obtain ⟨hop, hlen⟩ := hf (gateAt D k) (gateAt_mem D k hk)
      dsimp only [sanitizeGate]
      split_ifs with h1 h2 h3 h4 h5
      · refine ⟨⟨hop, hlen⟩, ?_, fun hn => by rw [h1] at hn; cases hn⟩
        intro w hw
        exact of_decide_eq_true (List.all_eq_true.mp h2 w hw)
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
      · refine ⟨⟨by simp, (List.length_filter_le _ _).trans hlen⟩, ?_, fun hn => by cases hn⟩
        intro w hw
        exact of_decide_eq_true (List.mem_filter.mp hw).2
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
      · refine ⟨⟨by simp, by simp⟩, ?_, fun _ => rfl⟩
        intro w hw
        simp only [List.mem_singleton] at hw
        rw [hw]; exact h5
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := hmem_iff g hg
      exact (hgate_ok k hk).1
    · intro k hk w hw
      have hkD : k < D.gates.length := by rw [← sanitize_len D]; exact hk
      rw [sanitize_gateAt D k hkD] at hw
      exact (hgate_ok k hkD).2.1 w hw
    · intro k hk hn
      have hkD : k < D.gates.length := by rw [← sanitize_len D]; exact hk
      rw [sanitize_gateAt D k hkD] at hn ⊢
      exact (hgate_ok k hkD).2.2 hn
  have sanitize_val (D : Circuit) (hf : FanInTwo D) (x : Fin 10 → Bool) :
      ∀ w, val (sanitize D) w x = val D w x := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw11 : w < 11
      · rw [val_in _ x w hw11, val_in _ x w hw11]
      · by_cases hwLt : w < 11 + D.gates.length
        · let k := w - 11
          have hk : k < D.gates.length := by omega
          have hwEq : w = 11 + k := by omega
          rw [hwEq, val_gate (sanitize D) k (by rw [sanitize_len]; exact hk) x,
              val_gate D k hk x, sanitize_gateAt D k hk]
          have hIH : ∀ u < 11 + k, val (sanitize D) u x = val D u x :=
            fun u hu => ih u (by omega)
          have hmap : ∀ (l : List ℕ),
              (l.map fun u => if u < 11 + k then val (sanitize D) u x else false) =
              (l.map fun u => if u < 11 + k then val D u x else false) := by
            intro l
            apply List.map_congr_left
            intro u _
            by_cases hu : u < 11 + k
            · simp [hu, hIH u hu]
            · simp [hu]
          obtain ⟨hop, _⟩ := hf (gateAt D k) (gateAt_mem D k hk)
          dsimp only [sanitizeGate]
          rcases hop with hAnd | hOr | hNot
          · rw [hAnd]; simp only [↓reduceIte]
            split_ifs with hall
            · rw [hAnd, hmap]
            · change false = ((gateAt D k).inputs.map fun u =>
                  if u < 11 + k then val D u x else false).all id
              symm
              rw [List.all_eq_false]
              have hnotAll : ¬ ∀ u ∈ (gateAt D k).inputs, decide (u < 11 + k) = true := by
                intro ha; exact hall (List.all_eq_true.mpr ha)
              push Not at hnotAll
              obtain ⟨u, huMem, huGe⟩ := hnotAll
              have huNotLt : ¬ u < 11 + k := fun hlt => huGe (decide_eq_true hlt)
              refine ⟨false, List.mem_map.mpr ⟨u, huMem, by simp [huNotLt]⟩, by decide⟩
          · rw [hOr]; simp only [reduceCtorEq, ↓reduceIte]
            change (((gateAt D k).inputs.filter fun u => decide (u < 11 + k)).map fun u =>
                if u < 11 + k then val (sanitize D) u x else false).any id =
              ((gateAt D k).inputs.map fun u => if u < 11 + k then val D u x else false).any id
            rw [hmap]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, List.mem_filter, id_eq]
            constructor
            · rintro ⟨_, ⟨u, ⟨huMem, _⟩, rfl⟩, hb⟩
              exact ⟨_, ⟨u, huMem, rfl⟩, hb⟩
            · rintro ⟨_, ⟨u, huMem, rfl⟩, hb⟩
              by_cases huLt : u < 11 + k
              · exact ⟨true, ⟨u, ⟨huMem, decide_eq_true huLt⟩, by simpa [huLt] using hb⟩, rfl⟩
              · simp [huLt] at hb
          · rw [hNot]; simp only [reduceCtorEq, ↓reduceIte]
            cases hIns : (gateAt D k).inputs with
            | nil =>
              simp only [List.length_nil, ↓reduceIte]; rfl
            | cons a rest =>
              simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.headD_cons]
              by_cases haLt : a < 11 + k
              · simp only [haLt, ↓reduceIte]
                change (!(if a < 11 + k then val (sanitize D) a x else false)) =
                  (!(if a < 11 + k then val D a x else false))
                simp [haLt, hIH a haLt]
              · simp only [haLt, ↓reduceIte]
                change true = (!(if a < 11 + k then val D a x else false))
                simp [haLt]
        · rw [val_oob (sanitize D) x w (by rw [sanitize_len]; omega),
              val_oob D x w (by omega)]
  -- eraseGate helpers for n = 11
  have erase_meta (D : Circuit) (hf : FanInTwo D) (hb : ReadsBack 11 D)
      (hnot1 : ∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1)
      (m p : ℕ) (hm : m < D.gates.length) (hp : p < 11 + m) :
      FanInTwo (eraseGate 11 D m p) ∧ ReadsBack 11 (eraseGate 11 D m p) ∧
      (∀ k < (eraseGate 11 D m p).gates.length,
        (gateAt (eraseGate 11 D m p) k).op = .not → (gateAt (eraseGate 11 D m p) k).inputs.length = 1) ∧
      (eraseGate 11 D m p).gates.length + 1 = D.gates.length := by
    have hgs : (eraseGate 11 D m p).gates =
        D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 11 m p)⟩) := by
      dsimp only [eraseGate]; simp only [hm, ↓reduceIte]
    have hsz : (eraseGate 11 D m p).gates.length + 1 = D.gates.length := by
      rw [hgs, List.length_append, List.length_take, List.length_map, List.length_drop]; omega
    have hgateAt (k : ℕ) (hk : k < (eraseGate 11 D m p).gates.length) :
        (k < m ∧ gateAt (eraseGate 11 D m p) k = gateAt D k) ∨
        (m ≤ k ∧ gateAt (eraseGate 11 D m p) k =
          ⟨(gateAt D (k + 1)).op, (gateAt D (k + 1)).inputs.map (eraseRedirect 11 m p)⟩) := by
      rw [gateAt_eq_getElem _ k hk]
      have htakeLen : (D.gates.take m).length = m := by rw [List.length_take]; omega
      by_cases hkm : k < m
      · left; refine ⟨hkm, ?_⟩
        simp only [hgs, List.getElem_append_left (by omega : k < (D.gates.take m).length),
          List.getElem_take, gateAt_eq_getElem D k (by omega)]
      · right; refine ⟨by omega, ?_⟩
        simp only [hgs, List.getElem_append_right (by omega : (D.gates.take m).length ≤ k),
          htakeLen, List.getElem_map, List.getElem_drop]
        have hIdx : m + 1 + (k - m) = k + 1 := by omega
        simp only [hIdx, gateAt_eq_getElem D (k + 1) (by omega)]
    have hfE : FanInTwo (eraseGate 11 D m p) := by
      intro g hg
      rw [hgs, List.mem_append] at hg
      rcases hg with h1 | h2
      · exact hf g (List.mem_of_mem_take h1)
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp h2
        obtain ⟨hop, hlen⟩ := hf g' (List.mem_of_mem_drop hg')
        exact ⟨hop, by simp [hlen]⟩
    have hbE : ReadsBack 11 (eraseGate 11 D m p) := by
      intro k hk u hu
      rcases hgateAt k hk with ⟨hkm, heq⟩ | ⟨hmk, heq⟩
      · rw [heq] at hu; exact hb k (by omega) u hu
      · rw [heq] at hu
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
        have hvLt : v < 11 + (k + 1) := hb (k + 1) (by omega) v hv
        dsimp only [eraseRedirect]; split_ifs <;> omega
    have hnotE : ∀ k < (eraseGate 11 D m p).gates.length,
        (gateAt (eraseGate 11 D m p) k).op = .not → (gateAt (eraseGate 11 D m p) k).inputs.length = 1 := by
      intro k hk hn
      rcases hgateAt k hk with ⟨hkm, heq⟩ | ⟨hmk, heq⟩
      · rw [heq] at hn ⊢; exact hnot1 k (by omega) hn
      · rw [heq] at hn ⊢
        simp only [List.length_map]
        exact hnot1 (k + 1) (by omega) hn
    exact ⟨hfE, hbE, hnotE, hsz⟩
  have erase_eval (D : Circuit) (hf : FanInTwo D) (hb : ReadsBack 11 D)
      (hnot1 : ∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1)
      (m p : ℕ) (hm : m < D.gates.length) (hp : p < 11 + m)
      (P : ℕ → Prop)
      (hDown : ∀ k < D.gates.length, P (11 + k) → ∀ u ∈ (gateAt D k).inputs, P u)
      (hMode : ¬ P (11 + m) ∨ ((∀ x : Fin 10 → Bool, val D (11 + m) x = val D p x) ∧ P p)) :
      ∀ x : Fin 10 → Bool, ∀ w, P w → val (eraseGate 11 D m p) (eraseRedirect 11 m p w) x = val D w x := by
    obtain ⟨_, hbE, _, hszE⟩ := erase_meta D hf hb hnot1 m p hm hp
    have hgs : (eraseGate 11 D m p).gates =
        D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 11 m p)⟩) := by
      dsimp only [eraseGate]; simp only [hm, ↓reduceIte]
    have htakeLen : (D.gates.take m).length = m := by rw [List.length_take]; omega
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hPw
      by_cases hw11 : w < 11
      · have hr : eraseRedirect 11 m p w = w := by dsimp only [eraseRedirect]; split_ifs <;> omega
        rw [hr, val_in _ x w hw11, val_in _ x w hw11]
      · by_cases hwLt : w < 11 + D.gates.length
        · let k := w - 11
          have hk : k < D.gates.length := by omega
          have hwEq : w = 11 + k := by omega
          rw [hwEq] at hPw ⊢
          by_cases hkm : k < m
          · have hr : eraseRedirect 11 m p (11 + k) = 11 + k := by
              dsimp only [eraseRedirect]; split_ifs <;> omega
            rw [hr, val_gate_rb (eraseGate 11 D m p) hbE k (by omega) x, val_gate_rb D hb k hk x]
            have hgk : gateAt (eraseGate 11 D m p) k = gateAt D k := by
              rw [gateAt_eq_getElem _ k (by omega), gateAt_eq_getElem D k hk]
              simp only [hgs, List.getElem_append_left (by omega : k < (D.gates.take m).length), List.getElem_take]
            rw [hgk]
            congr 1
            apply List.map_congr_left
            intro u hu
            have huLt : u < 11 + k := hb k hk u hu
            have hru : eraseRedirect 11 m p u = u := by dsimp only [eraseRedirect]; split_ifs <;> omega
            conv_lhs => rw [← hru]
            exact ih u (by omega) (hDown k hk hPw u hu)
          · by_cases hkeq : k = m
            · rw [hkeq] at hPw ⊢
              rcases hMode with hnot | ⟨heq, hPp⟩
              · exact False.elim (hnot hPw)
              · have hr : eraseRedirect 11 m p (11 + m) = p := by dsimp only [eraseRedirect]; simp
                have hrp : eraseRedirect 11 m p p = p := by dsimp only [eraseRedirect]; split_ifs <;> omega
                rw [hr]
                have hih := ih p (by omega) hPp
                rw [hrp] at hih
                exact hih.trans (heq x).symm
            · have hmk : m < k := by omega
              have hr : eraseRedirect 11 m p (11 + k) = 11 + (k - 1) := by
                dsimp only [eraseRedirect]; split_ifs <;> omega
              rw [hr, val_gate_rb (eraseGate 11 D m p) hbE (k - 1) (by omega) x, val_gate_rb D hb k hk x]
              have hgk : gateAt (eraseGate 11 D m p) (k - 1) =
                  ⟨(gateAt D k).op, (gateAt D k).inputs.map (eraseRedirect 11 m p)⟩ := by
                rw [gateAt_eq_getElem _ (k - 1) (by omega), gateAt_eq_getElem D k hk]
                simp only [hgs, List.getElem_append_right (by omega : (D.gates.take m).length ≤ k - 1),
                  htakeLen, List.getElem_map, List.getElem_drop]
                have hIdx : m + 1 + (k - 1 - m) = k := by omega
                simp only [hIdx]
              rw [hgk, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have huLt : u < 11 + k := hb k hk u hu
              exact ih u (by omega) (hDown k hk hPw u hu)
        · have hr : eraseRedirect 11 m p w = w - 1 := by
            dsimp only [eraseRedirect]; split_ifs <;> omega
          rw [hr, val_oob (eraseGate 11 D m p) x (w - 1) (by omega), val_oob D x w (by omega)]
  have redirect_lt (sz sz' m r w : ℕ) (hsz : sz' + 1 = sz) (hm : m < sz) (hr : r < 11 + m)
      (hw : w < 11 + sz) : eraseRedirect 11 m r w < 11 + sz' := by
    dsimp only [eraseRedirect]; split_ifs <;> omega
  -- Helper: no input wire 0..10 equals F or !F
  have inp_zero (w : ℕ) (hw : w < 11) : (inp (fun _ => false)).getD w false = false := by
    dsimp only [inp]
    by_cases hw10 : w < 10
    · rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    · have hwEq : w = 10 := by omega
      rw [hwEq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn]
      cases b <;> rfl
  have inp_ne_F (w : ℕ) (hw : w < 11) : ∃ x : Fin 10 → Bool, (inp x).getD w false ≠ F x := by
    by_cases hw10 : w < 10
    · let i : Fin 10 := ⟨w, hw10⟩
      refine ⟨fun j => decide (j = i), ?_⟩
      rw [hUnitF i]
      dsimp only [inp]
      rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      simp [i]
    · have hwEq : w = 10 := by omega
      refine ⟨fun j => decide (j = 2 ∨ j = 3), ?_⟩
      rw [hEdge23, hwEq]
      dsimp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn]
      cases b <;> decide
  -- Main strong induction on circuit size
  have main_ind : ∀ s : ℕ, ∀ D : Circuit, ∀ out : ℕ,
      D.gates.length = s → s ≤ 18 →
      FanInTwo D → ReadsBack 11 D →
      (∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1) →
      out < 11 + D.gates.length →
      (∀ x : Fin 10 → Bool, val D out x = F x) → False := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro D out hDs hSmall hfD hbD hnotD houtLt hComp
      have shrink_of_eq (E : Circuit) (out' : ℕ)
          (hfE : FanInTwo E) (hbE : ReadsBack 11 E)
          (hnotE : ∀ k < E.gates.length, (gateAt E k).op = .not → (gateAt E k).inputs.length = 1)
          (hszE : E.gates.length < D.gates.length) (hout' : out' < 11 + E.gates.length)
          (heq : ∀ x : Fin 10 → Bool, val E out' x = val D out x) : False :=
        ih E.gates.length (by omega) E out' rfl (by omega) hfE hbE hnotE hout'
          (fun x => (heq x).trans (hComp x))
      -- Step 1: eliminate dead gates
      by_cases hDead : ∃ k < D.gates.length, ¬ InOutCone 11 D (11 + k) out
      · obtain ⟨k, hk, hno⟩ := hDead
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD k 0 hk (by omega)
        let P' (w : ℕ) : Prop := w < 11 ∨ InOutCone 11 D w out
        have hDown' : ∀ m < D.gates.length, P' (11 + m) → ∀ w ∈ (gateAt D m).inputs, P' w := by
          intro m hm hPm w hw
          by_cases hw11 : 11 ≤ w
          · rcases hPm with hlt | h1
            · omega
            · exact Or.inr (inOutCone_step D hbD m w out hm hw hw11 h1)
          · exact Or.inl (by omega)
        have hNotP : ¬ P' (11 + k) := by
          rintro (hlt | h1)
          · omega
          · exact hno h1
        have hEv := erase_eval D hfD hbD hnotD k 0 hk (by omega) P' hDown' (Or.inl hNotP)
        exact shrink_of_eq (eraseGate 11 D k 0) (eraseRedirect 11 k 0 out)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ k 0 out hszE hk (by omega) houtLt)
          (fun x => hEv x out (Or.inr (Or.inl rfl)))
      have hNoDead : ∀ k < D.gates.length, InOutCone 11 D (11 + k) out := by
        intro k hk; by_contra h; exact hDead ⟨k, hk, h⟩
      -- Step 2: eliminate wire aliases
      by_cases hSameWire : ∃ k < D.gates.length, ∃ p < 11 + k, ∀ x : Fin 10 → Bool, val D (11 + k) x = val D p x
      · obtain ⟨k, hk, p, hp, heq⟩ := hSameWire
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD k p hk hp
        have hEv := erase_eval D hfD hbD hnotD k p hk hp (fun _ => True)
          (fun _ _ _ _ _ => trivial) (Or.inr ⟨heq, trivial⟩)
        exact shrink_of_eq (eraseGate 11 D k p) (eraseRedirect 11 k p out)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ k p out hszE hk hp houtLt)
          (fun x => hEv x out trivial)
      have hNoSame : ∀ k < D.gates.length, ∀ p < 11 + k, ∃ x : Fin 10 → Bool, val D (11 + k) x ≠ val D p x := by
        intro k hk p hp; by_contra h; push Not at h; exact hSameWire ⟨k, hk, p, hp, h⟩
      have hNotLen1 (k : ℕ) (hk : k < D.gates.length) (hAO : (gateAt D k).op = .and ∨ (gateAt D k).op = .or) :
          (gateAt D k).inputs.length ≠ 1 := by
        intro hlen
        obtain ⟨p, hp_eq⟩ := List.length_eq_one_iff.mp hlen
        have hp_lt : p < 11 + k := hbD k hk p (by rw [hp_eq]; simp)
        obtain ⟨x, hne⟩ := hNoSame k hk p hp_lt
        apply hne
        rw [val_gate_rb D hbD k hk x, hp_eq]
        rcases hAO with h | h
        · rw [h]; change ([val D p x]).all id = val D p x; simp
        · rw [h]; change ([val D p x]).any id = val D p x; simp
      have hDistinctOfLen2 (k : ℕ) (hk : k < D.gates.length)
          (hAO : (gateAt D k).op = .and ∨ (gateAt D k).op = .or)
          (hlen : (gateAt D k).inputs.length = 2) : (gateAt D k).inputs.Nodup := by
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
        rw [hpq]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          not_false_eq_true, and_true]
        intro heq; subst heq
        have hp_lt : p < 11 + k := hbD k hk p (by rw [hpq]; simp)
        obtain ⟨x, hne⟩ := hNoSame k hk p hp_lt
        apply hne
        rw [val_gate_rb D hbD k hk x, hpq]
        rcases hAO with h | h
        · rw [h]; change ([val D p x, val D p x]).all id = val D p x; simp
        · rw [h]; change ([val D p x, val D p x]).any id = val D p x; simp
      -- Step 3: eliminate any constant gate
      by_cases hConst : ∃ k < D.gates.length, ∃ c : Bool, ∀ x : Fin 10 → Bool, val D (11 + k) x = c
      · let Cs := (Finset.range D.gates.length).filter fun k =>
          ∃ c : Bool, ∀ x : Fin 10 → Bool, val D (11 + k) x = c
        have hCsNE : Cs.Nonempty := by
          obtain ⟨k, hk, hc⟩ := hConst
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hc⟩⟩
        let m := Cs.max' hCsNE
        have hmMem := Finset.mem_filter.mp (Finset.max'_mem Cs hCsNE)
        have hmLt : m < D.gates.length := Finset.mem_range.mp hmMem.1
        obtain ⟨c, hmC⟩ := hmMem.2
        have hmOut : out ≠ 11 + m := by
          intro h
          cases c with
          | false =>
            have h1 := hComp (fun _ => true)
            rw [h, hmC _, hOneF] at h1; cases h1
          | true =>
            have h0 := hComp (fun _ => false)
            rw [h, hmC _, hZeroF] at h0; cases h0
        have hNoRead : ∀ k < D.gates.length, 11 + m ∉ (gateAt D k).inputs := by
          intro k hk hmem
          have hmk : m < k := by have := hbD k hk (11 + m) hmem; omega
          obtain ⟨hop, hlenLe⟩ := hfD (gateAt D k) (gateAt_mem D k hk)
          rcases hop with hand | hor | hnot
          · have hlenNe0 : (gateAt D k).inputs.length ≠ 0 := by
              intro h0; rw [List.length_eq_zero_iff.mp h0] at hmem; exact List.not_mem_nil hmem
            have hlen2 : (gateAt D k).inputs.length = 2 := by
              have := hNotLen1 k hk (Or.inl hand); omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
            rw [hpq] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            cases c with
            | false =>
              have hkF : ∀ x : Fin 10 → Bool, val D (11 + k) x = false := by
                intro x
                rw [val_gate_rb D hbD k hk x, hand, hpq]
                rcases hmem with rfl | rfl
                · change (val D (11 + m) x && (val D q x && true)) = false; rw [hmC x]; rfl
                · change (val D p x && (val D (11 + m) x && true)) = false; rw [hmC x]; simp
              have hle := Finset.le_max' Cs k
                (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, false, hkF⟩)
              omega
            | true =>
              rcases hmem with rfl | rfl
              · obtain ⟨x, hne⟩ := hNoSame k hk q (hbD k hk q (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hand, hpq]
                change (val D (11 + m) x && (val D q x && true)) = val D q x; rw [hmC x]; simp
              · obtain ⟨x, hne⟩ := hNoSame k hk p (hbD k hk p (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hand, hpq]
                change (val D p x && (val D (11 + m) x && true)) = val D p x; rw [hmC x]; simp
          · have hlenNe0 : (gateAt D k).inputs.length ≠ 0 := by
              intro h0; rw [List.length_eq_zero_iff.mp h0] at hmem; exact List.not_mem_nil hmem
            have hlen2 : (gateAt D k).inputs.length = 2 := by
              have := hNotLen1 k hk (Or.inr hor); omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
            rw [hpq] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            cases c with
            | true =>
              have hkT : ∀ x : Fin 10 → Bool, val D (11 + k) x = true := by
                intro x
                rw [val_gate_rb D hbD k hk x, hor, hpq]
                rcases hmem with rfl | rfl
                · change (val D (11 + m) x || (val D q x || false)) = true; rw [hmC x]; rfl
                · change (val D p x || (val D (11 + m) x || false)) = true; rw [hmC x]; simp
              have hle := Finset.le_max' Cs k
                (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, true, hkT⟩)
              omega
            | false =>
              rcases hmem with rfl | rfl
              · obtain ⟨x, hne⟩ := hNoSame k hk q (hbD k hk q (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hor, hpq]
                change (val D (11 + m) x || (val D q x || false)) = val D q x; rw [hmC x]; simp
              · obtain ⟨x, hne⟩ := hNoSame k hk p (hbD k hk p (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hor, hpq]
                change (val D p x || (val D (11 + m) x || false)) = val D p x; rw [hmC x]; simp
          · have hlen1 := hnotD k hk hnot
            obtain ⟨p, hp_eq⟩ := List.length_eq_one_iff.mp hlen1
            rw [hp_eq] at hmem
            have hpEq : 11 + m = p := List.mem_singleton.mp hmem
            have hkC : ∀ x : Fin 10 → Bool, val D (11 + k) x = !c := by
              intro x
              rw [val_gate_rb D hbD k hk x, hnot, hp_eq, ← hpEq]
              change (!(val D (11 + m) x)) = !c
              rw [hmC x]
            have hle := Finset.le_max' Cs k
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, !c, hkC⟩)
            omega
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD m 0 hmLt (by omega)
        have hEv := erase_eval D hfD hbD hnotD m 0 hmLt (by omega) (fun w => w ≠ 11 + m)
          (fun k hk _ w hw hEq => hNoRead k hk (hEq ▸ hw)) (Or.inl (fun h => h rfl))
        exact shrink_of_eq (eraseGate 11 D m 0) (eraseRedirect 11 m 0 out)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ m 0 out hszE hmLt (by omega) houtLt)
          (fun x => hEv x out hmOut)
      have hNonConst (k : ℕ) (hk : k < D.gates.length) (c : Bool) :
          ∃ x : Fin 10 → Bool, val D (11 + k) x = c := by
        by_contra h
        push Not at h
        refine hConst ⟨k, hk, !c, fun x => ?_⟩
        have hx := h x
        cases hv : val D (11 + k) x <;> cases c <;> (try rfl) <;> exact False.elim (hx hv)
      have hShape (k : ℕ) (hk : k < D.gates.length) :
          (((gateAt D k).op = .and ∨ (gateAt D k).op = .or) ∧
            (gateAt D k).inputs.length = 2 ∧ (gateAt D k).inputs.Nodup) ∨
          ((gateAt D k).op = .not ∧ (gateAt D k).inputs.length = 1) := by
        obtain ⟨hop, hle⟩ := hfD (gateAt D k) (gateAt_mem D k hk)
        rcases hop with hand | hor | hnot
        · have hne0 : (gateAt D k).inputs.length ≠ 0 := by
            intro h0
            have hnil := List.length_eq_zero_iff.mp h0
            exact hConst ⟨k, hk, true, fun x => by rw [val_gate_rb D hbD k hk x, hand, hnil]; rfl⟩
          have hne1 := hNotLen1 k hk (Or.inl hand)
          have hlen2 : (gateAt D k).inputs.length = 2 := by omega
          exact Or.inl ⟨Or.inl hand, hlen2, hDistinctOfLen2 k hk (Or.inl hand) hlen2⟩
        · have hne0 : (gateAt D k).inputs.length ≠ 0 := by
            intro h0
            have hnil := List.length_eq_zero_iff.mp h0
            exact hConst ⟨k, hk, false, fun x => by rw [val_gate_rb D hbD k hk x, hor, hnil]; rfl⟩
          have hne1 := hNotLen1 k hk (Or.inr hor)
          have hlen2 : (gateAt D k).inputs.length = 2 := by omega
          exact Or.inl ⟨Or.inr hor, hlen2, hDistinctOfLen2 k hk (Or.inr hor) hlen2⟩
        · exact Or.inr ⟨hnot, hnotD k hk hnot⟩
      -- Step 4: out is the last gate 11 + (s - 1), and s ≥ 1!
      have houtGe11 : 11 ≤ out := by
        by_contra hlt
        obtain ⟨x, hx⟩ := inp_ne_F out (by omega)
        apply hx
        rw [← val_in D x out (by omega)]
        exact hComp x
      have hsPos : 1 ≤ D.gates.length := by omega
      have houtLast : out = 11 + (D.gates.length - 1) := by
        have hlive := hNoDead (D.gates.length - 1) (by omega)
        rcases hlive with hEq | ⟨_, _, hcone⟩
        · exact hEq.symm
        · have := inCone_lt D (out - 11) (11 + (D.gates.length - 1) - 11) hcone
          omega
      -- Helper: take first m gates of D, transferring all cleanliness to (p, q)
      have mkHead (m : ℕ) (hm : m < D.gates.length) (p q : ℕ)
          (hp : p < 11 + m) (hq : q < 11 + m)
          (hIns : (gateAt D m).inputs = [p, q])
          (hAO : (gateAt D m).op = .and ∨ (gateAt D m).op = .or)
          (hLiveM : ∀ k < m, InOutCone 11 D (11 + k) (11 + m)) :
          let E : Circuit := ⟨D.gates.take m, 0⟩
          ReadsBack 11 E ∧ E.size = m ∧ p < 11 + E.size ∧ q < 11 + E.size ∧
          (∀ k < E.size,
            let g := gateAt E k
            (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
              (g.op = .not ∧ g.inputs.length = 1)) ∧
            (InOutCone 11 E (11 + k) p ∨ InOutCone 11 E (11 + k) q) ∧
            (∀ r < 11 + k, ∃ x : Fin 10 → Bool, val E (11 + k) x ≠ val E r x) ∧
            ∀ c : Bool, ∃ x : Fin 10 → Bool, val E (11 + k) x = c) ∧
          (∀ c : Bool, ∃ x : Fin 10 → Bool, val E p x = c ∧ val E q x = !c) ∧
          (∀ x : Fin 10 → Bool, val E p x = val D p x ∧ val E q x = val D q x) := by
        let E : Circuit := ⟨D.gates.take m, 0⟩
        have hLenE : E.gates.length = m := by
          change (D.gates.take m).length = m; rw [List.length_take]; omega
        have hGateE (k : ℕ) (hk : k < m) : gateAt E k = gateAt D k := by
          rw [gateAt_eq_getElem E k (by omega), gateAt_eq_getElem D k (by omega)]
          exact List.getElem_take
        have hbE : ReadsBack 11 E := by
          intro k hk w hw
          have hkM : k < m := by omega
          rw [hGateE k hkM] at hw
          exact hbD k (by omega) w hw
        have hCleanE : ∀ k < E.size,
            let g := gateAt E k
            (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
              (g.op = .not ∧ g.inputs.length = 1)) ∧
            (InOutCone 11 E (11 + k) p ∨ InOutCone 11 E (11 + k) q) ∧
            (∀ r < 11 + k, ∃ x : Fin 10 → Bool, val E (11 + k) x ≠ val E r x) ∧
            ∀ c : Bool, ∃ x : Fin 10 → Bool, val E (11 + k) x = c := by
          intro k hk
          change k < E.gates.length at hk
          have hkM : k < m := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hGateE k hkM]; exact hShape k (by omega)
          · have hkm := hLiveM k hkM
            rcases hkm with hEq | ⟨_, _, hcone⟩
            · omega
            · have hSubEq : (11 + m) - 11 = m := by omega
              have hSubK : (11 + k) - 11 = k := by omega
              rw [hSubEq, hSubK] at hcone
              obtain ⟨w, hw, h11, hlt, hcase⟩ := (inCone_iff D k m hm).mp hcone
              rw [hIns] at hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl
              · left
                rcases hcase with hEqK | hSub
                · exact Or.inl (by omega)
                · exact Or.inr ⟨by omega, h11, by rw [hSubK]; exact (inCone_take D m (by omega) k (w - 11) (by omega)).mpr hSub⟩
              · right
                rcases hcase with hEqK | hSub
                · exact Or.inl (by omega)
                · exact Or.inr ⟨by omega, h11, by rw [hSubK]; exact (inCone_take D m (by omega) k (w - 11) (by omega)).mpr hSub⟩
          · intro r hr
            obtain ⟨x, hne⟩ := hNoSame k (by omega) r hr
            refine ⟨x, ?_⟩
            rw [val_take D m (by omega) x (11 + k) (by omega), val_take D m (by omega) x r (by omega)]
            exact hne
          · intro c
            obtain ⟨x, hx⟩ := hNonConst k (by omega) c
            refine ⟨x, ?_⟩
            rw [val_take D m (by omega) x (11 + k) (by omega)]
            exact hx
        have hIncomp : ∀ c : Bool, ∃ x : Fin 10 → Bool, val E p x = c ∧ val E q x = !c := by
          intro c
          by_contra h
          push Not at h
          have hDep : ∀ x : Fin 10 → Bool, val D p x = c → val D q x = c := by
            intro x hx
            have h1 := h x (by rw [val_take D m (by omega) x p hp]; exact hx)
            rw [val_take D m (by omega) x q hq] at h1
            cases hqV : val D q x <;> cases c <;> (try rfl) <;> exact False.elim (h1 hqV)
          rcases hAO with hand | hor
          · cases c with
            | false =>
              obtain ⟨x, hne⟩ := hNoSame m hm q hq
              apply hne
              rw [val_gate_rb D hbD m hm x, hand, hIns]
              change (val D p x && (val D q x && true)) = val D q x
              cases hpV : val D p x
              · rw [hDep x hpV]; rfl
              · simp
            | true =>
              obtain ⟨x, hne⟩ := hNoSame m hm p hp
              apply hne
              rw [val_gate_rb D hbD m hm x, hand, hIns]
              change (val D p x && (val D q x && true)) = val D p x
              cases hpV : val D p x
              · rfl
              · rw [hDep x hpV]; rfl
          · cases c with
            | false =>
              obtain ⟨x, hne⟩ := hNoSame m hm p hp
              apply hne
              rw [val_gate_rb D hbD m hm x, hor, hIns]
              change (val D p x || (val D q x || false)) = val D p x
              cases hpV : val D p x
              · rw [hDep x hpV]; rfl
              · rfl
            | true =>
              obtain ⟨x, hne⟩ := hNoSame m hm q hq
              apply hne
              rw [val_gate_rb D hbD m hm x, hor, hIns]
              change (val D p x || (val D q x || false)) = val D q x
              cases hpV : val D p x
              · simp
              · rw [hDep x hpV]; rfl
        refine ⟨hbE, hLenE, by change p < 11 + E.gates.length; omega,
          by change q < 11 + E.gates.length; omega, hCleanE, hIncomp,
          fun x => ⟨val_take D m (by omega) x p hp, val_take D m (by omega) x q hq⟩⟩
      -- Dispatch on the output gate D.gates.length - 1
      let last := D.gates.length - 1
      have hLastLt : last < D.gates.length := by omega
      rcases hShape last hLastLt with ⟨hAO, hlen2, _⟩ | ⟨hNot, hlen1⟩
      · obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
        have hpLt : p < 11 + last := hbD last hLastLt p (by rw [hpq]; simp)
        have hqLt : q < 11 + last := hbD last hLastLt q (by rw [hpq]; simp)
        obtain ⟨hbE, hSzE, hpE, hqE, hClE, hIncE, hValE⟩ :=
          mkHead last hLastLt p q hpLt hqLt hpq hAO (fun k hk => by rw [← houtLast]; exact hNoDead k (by omega))
        rcases hAO with hand | hor
        · refine topAnd ⟨D.gates.take last, 0⟩ b p q hbE (by omega) hpE hqE hClE hIncE (fun x => ?_)
          change (val ⟨D.gates.take last, 0⟩ p x && val ⟨D.gates.take last, 0⟩ q x) = G x
          rw [(hValE x).1, (hValE x).2, hGF, ← hComp x, houtLast, val_gate_rb D hbD last hLastLt x, hand, hpq]
          change (val D p x && val D q x) = (val D p x && (val D q x && true))
          simp
        · refine topOr ⟨D.gates.take last, 0⟩ b p q hbE (by omega) hpE hqE hClE hIncE (fun x => ?_)
          change (val ⟨D.gates.take last, 0⟩ p x || val ⟨D.gates.take last, 0⟩ q x) = G x
          rw [(hValE x).1, (hValE x).2, hGF, ← hComp x, houtLast, val_gate_rb D hbD last hLastLt x, hor, hpq]
          change (val D p x || val D q x) = (val D p x || (val D q x || false))
          simp
      · -- Output gate is NOT(u): u must be the second-to-last gate (11 + (last - 1)) and AND/OR!
        obtain ⟨u, huEq⟩ := List.length_eq_one_iff.mp hlen1
        have huLt : u < 11 + last := hbD last hLastLt u (by rw [huEq]; simp)
        have hNotU (x : Fin 10 → Bool) : (!(val D u x)) = F x := by
          have h1 := hComp x
          rw [houtLast, val_gate_rb D hbD last hLastLt x, hNot, huEq] at h1
          exact h1
        have huGe11 : 11 ≤ u := by
          by_contra hlt
          have h0 := hNotU (fun _ => false)
          rw [val_in D _ u (by omega), inp_zero u (by omega), hZeroF] at h0
          cases h0
        have hLiveU : ∀ k < last, InOutCone 11 D (11 + k) u := by
          intro k hk
          have hlive := hNoDead k (by omega)
          rw [houtLast] at hlive
          rcases hlive with hEq | ⟨_, _, hcone⟩
          · omega
          · have hSubL : (11 + last) - 11 = last := by omega
            have hSubK : (11 + k) - 11 = k := by omega
            rw [hSubL, hSubK] at hcone
            obtain ⟨w, hw, h11, _, hcase⟩ := (inCone_iff D k last hLastLt).mp hcone
            rw [huEq] at hw
            have hwu : w = u := List.mem_singleton.mp hw
            subst hwu
            rcases hcase with hEqK | hSub
            · exact Or.inl (by omega)
            · exact Or.inr ⟨by omega, h11, by simpa using hSub⟩
        have hLastPos : 1 ≤ last := by omega
        let prev := last - 1
        have hPrevLt : prev < D.gates.length := by omega
        have huPrev : u = 11 + prev := by
          have hlive := hLiveU prev (by omega)
          rcases hlive with hEq | ⟨_, _, hcone⟩
          · exact hEq.symm
          · have := inCone_lt D (u - 11) (11 + prev - 11) hcone; omega
        rcases hShape prev hPrevLt with ⟨hAO, hlen2, _⟩ | ⟨hNot2, hlen1'⟩
        · obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
          have hpLt : p < 11 + prev := hbD prev hPrevLt p (by rw [hpq]; simp)
          have hqLt : q < 11 + prev := hbD prev hPrevLt q (by rw [hpq]; simp)
          obtain ⟨hbE, hSzE, hpE, hqE, hClE, hIncE, hValE⟩ :=
            mkHead prev hPrevLt p q hpLt hqLt hpq hAO (fun k hk => by rw [← huPrev]; exact hLiveU k (by omega))
          rcases hAO with hand | hor
          · refine topNand ⟨D.gates.take prev, 0⟩ b p q hbE (by omega) hpE hqE hClE hIncE (fun x => ?_)
            change (!(val ⟨D.gates.take prev, 0⟩ p x && val ⟨D.gates.take prev, 0⟩ q x)) = G x
            rw [(hValE x).1, (hValE x).2, hGF, ← hNotU x, huPrev, val_gate_rb D hbD prev hPrevLt x, hand, hpq]
            change (!(val D p x && val D q x)) = (!(val D p x && (val D q x && true)))
            simp
          · refine topNor ⟨D.gates.take prev, 0⟩ b p q hbE (by omega) hpE hqE hClE hIncE (fun x => ?_)
            change (!(val ⟨D.gates.take prev, 0⟩ p x || val ⟨D.gates.take prev, 0⟩ q x)) = G x
            rw [(hValE x).1, (hValE x).2, hGF, ← hNotU x, huPrev, val_gate_rb D hbD prev hPrevLt x, hor, hpq]
            change (!(val D p x || val D q x)) = (!(val D p x || (val D q x || false)))
            simp
        · -- NOT(NOT(w)) = w is a wire alias, contradicting hNoSame!
          obtain ⟨w, hwEq⟩ := List.length_eq_one_iff.mp hlen1'
          have hwLt : w < 11 + prev := hbD prev hPrevLt w (by rw [hwEq]; simp)
          obtain ⟨x, hne⟩ := hNoSame last hLastLt w (by omega)
          apply hne
          rw [val_gate_rb D hbD last hLastLt x, hNot, huEq]
          change (!(val D u x)) = val D w x
          rw [huPrev, val_gate_rb D hbD prev hPrevLt x, hNot2, hwEq]
          change (!(!(val D w x))) = val D w x
          exact Bool.not_not _
  -- Entry point: sanitize C0 and call main_ind
  let Cs := sanitize C0
  obtain ⟨hfS, hbS, hnotS⟩ := sanitize_meta C0 hf0
  have hSzS : Cs.gates.length = C0.gates.length := sanitize_len C0
  have hValS (x : Fin 10 → Bool) (w : ℕ) : val Cs w x = val C0 w x := sanitize_val C0 hf0 x w
  have houtLt : C0.output < 11 + Cs.gates.length := by
    by_contra hge
    have h1 : val Cs C0.output (fun _ => true) = F (fun _ => true) := by
      rw [hValS]; exact hNoDiff (fun _ => true)
    rw [val_oob Cs _ C0.output (by omega), hOneF] at h1
    cases h1
  exact main_ind Cs.gates.length Cs C0.output rfl (by change C0.gates.length ≤ 18 at hsz0; omega)
    hfS hbS hnotS houtLt (fun x => by rw [hValS]; exact hNoDiff x)
