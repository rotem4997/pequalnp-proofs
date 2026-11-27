import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_7999_413
    (noFano26 :
      ∀ D : Circuit, D.size ≤ 26 → IsAO2 14 D →
        (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        False)
    (noMinusEdge25 :
      ∀ D : Circuit, D.size = 25 → IsAO2 14 D →
        (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        (∀ x : Fin 14 → Bool,
          (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ ¬(p = 0 ∧ l = 0) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
          D.eval (List.ofFn x) = true) →
        D.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∃ x5 ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (11 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (8 : ℕ))], PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5.1, x5.2] : PEqualNP.CircuitLowerBounds.Gate }) → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → False := by
  intro C hSize hAO hDist hFirst hFano _
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
  have hCsize_pos : 0 < C.size := by
    by_contra h0
    have h0' : ¬ 0 < C.gates.length := h0
    have he : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨u, _, hgu⟩ := hFirst
    have hop : (gateAt C 0).op = GateOp.or := by unfold gateAt; rw [he]; rfl
    rw [hgu] at hop
    exact GateOp.noConfusion hop
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
  obtain ⟨⟨a0, b0⟩, hmem0, hgate0⟩ := hFirst
  let perms : List ((ℕ × ℕ) × List ℕ × List ℕ) := [
    ((0, 7),  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
    ((0, 11), [0, 2, 4, 6, 1, 3, 5, 13, 8, 10, 12, 7, 9, 11], [0, 4, 1, 5, 2, 6, 3, 11, 8, 12, 9, 13, 10, 7]),
    ((1, 8),  [6, 0, 1, 2, 3, 4, 5, 13, 7, 8, 9, 10, 11, 12], [1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 7]),
    ((2, 8),  [2, 1, 0, 4, 3, 5, 6, 8, 7, 11, 10, 9, 12, 13], [2, 1, 0, 4, 3, 5, 6, 8, 7, 11, 10, 9, 12, 13])
  ]
  have hPermsValid : ∀ entry ∈ perms,
      let f := entry.2.1
      let g := entry.2.2
      (∀ i : Fin 14, f.getD i.val 0 < 14 ∧ g.getD i.val 0 < 14 ∧
        g.getD (f.getD i.val 0) 0 = i.val ∧ f.getD (g.getD i.val 0) 0 = i.val) ∧
      (∀ p : Fin 7, f.getD p.val 0 < 7 ∧ g.getD p.val 0 < 7) ∧
      (∀ l : Fin 7, 7 ≤ f.getD (7 + l.val) 0 ∧ 7 ≤ g.getD (7 + l.val) 0) ∧
      f.getD entry.1.1 0 = 0 ∧ f.getD entry.1.2 0 = 7 ∧
      entry.1.1 < 14 ∧ entry.1.2 < 14 ∧
      (∀ p l : Fin 7,
        let fp := f.getD p.val 0
        let fl := f.getD (7 + l.val) 0 - 7
        (fp = fl ∨ fp = (fl + 1) % 7 ∨ fp = (fl + 3) % 7) ↔
        (p = l ∨ p = l + 1 ∨ p = l + 3)) := by
    decide +kernel
  have hFindPerm : ∀ e ∈ ([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)),
      ∃ entry ∈ perms, entry.1 = e := by
    decide +kernel
  obtain ⟨⟨ePair, fL, gL⟩, hentry, heqPair⟩ := hFindPerm (a0, b0) hmem0
  obtain ⟨hbij, hpts, hlines, hfa, hfb, ha0lt, hb0lt, hincPres⟩ := hPermsValid (ePair, fL, gL) hentry
  have ha0eq : ePair.1 = a0 := congrArg Prod.fst heqPair
  have hb0eq : ePair.2 = b0 := congrArg Prod.snd heqPair
  rw [ha0eq] at hfa ha0lt
  rw [hb0eq] at hfb hb0lt
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
  have hmapW_bound : ∀ w j, w < 14 + j → mapW w < 14 + j := by
    intro w j hw
    by_cases h14 : w < 14
    · have := (hmapW_lt14 w).2 h14; omega
    · simpa [mapW, h14] using hw
  have hmapW_inj : ∀ u v, mapW u = mapW v → u = v := by
    intro u v h
    have := congrArg invW h
    rwa [hinvW_mapW, hinvW_mapW] at this
  let C1 : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩, mapW C.output⟩
  have hC1size : C1.size = C.size := List.length_map _
  have hC1gate : ∀ j < C.size,
      gateAt C1 j = ⟨(gateAt C j).op, (gateAt C j).inputs.map mapW⟩ := by
    intro j hj
    have hj' : j < C.gates.length := hj
    unfold gateAt
    change (C.gates.map fun g => (⟨g.op, g.inputs.map mapW⟩ : Gate)).getD j _ = _
    rw [List.getD_eq_getElem _ _ (by simp [hj']), List.getD_eq_getElem _ _ hj', List.getElem_map]
  have hC1g0 : gateAt C1 0 = ⟨GateOp.and, [0, 7]⟩ := by
    rw [hC1gate 0 hCsize_pos, hgate0]
    simp only [List.map_cons, List.map_nil, mapW, ha0lt, hb0lt, ↓reduceIte, hfa, hfb]
  have hC1AO : IsAO2 14 C1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hAO.1 g0 hg0
    · intro j hj i hi
      have hjC : j < C.size := hC1size ▸ hj
      rw [hC1gate j hjC] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      exact hmapW_bound i0 j (hAO.2.1 j hjC i0 hi0)
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simpa using hAO.2.2 g0 hg0
  have hC1dist : ∀ j < C1.size, opnd C1 j 0 ≠ opnd C1 j 1 := by
    intro j hj
    have hjC : j < C.size := hC1size ▸ hj
    obtain ⟨hinp, _, _, _⟩ := gate_inputs2 C hAO j hjC
    have h0 : opnd C1 j 0 = mapW (opnd C j 0) ∧ opnd C1 j 1 = mapW (opnd C j 1) := by
      unfold opnd; rw [hC1gate j hjC, hinp]; exact ⟨rfl, rfl⟩
    rw [h0.1, h0.2]
    intro he
    exact hDist j hjC (hmapW_inj _ _ he)
  let finPerm : Fin 14 → Fin 14 := fun i => ⟨fL.getD i.val 0, (hbij i).1⟩
  let finInv : Fin 14 → Fin 14 := fun i => ⟨gL.getD i.val 0, (hbij i).2.1⟩
  have hC1wire : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.size →
      (C1.wires (List.ofFn x)).getD (mapW r) false =
        (C.wires (List.ofFn (fun i => x (finPerm i)))).getD r false := by
    intro x r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr
      by_cases h14 : r < 14
      · have hmr : mapW r < 14 := (hmapW_lt14 r).2 h14
        rw [wire_input C1 x (mapW r) hmr, wire_input C _ r h14]
        congr 1; ext; simp [mapW, finPerm, h14]
      · let j := r - 14
        have hj : j < C.size := by omega
        have hrj : r = 14 + j := by omega
        have hmr : mapW r = 14 + j := by simp [mapW, hrj]
        rw [hmr, hrj]
        rw [wire_gate C1 hC1AO x j (hC1size.symm ▸ hj), wire_gate C hAO _ j hj]
        obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 C hAO j hj
        have hg := hC1gate j hj
        have h0 : opnd C1 j 0 = mapW (opnd C j 0) ∧ opnd C1 j 1 = mapW (opnd C j 1) := by
          unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
        rw [hg, h0.1, h0.2, ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
  have hC1Fano : ∀ x : Fin 14 → Bool, C1.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x
    have hev : C1.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (finPerm i))) :=
      hC1wire x C.output hCout
    rw [hev, hFano]
    have hmod_iff : ∀ a b : Fin 7,
        (a.val = b.val ∨ a.val = (b.val + 1) % 7 ∨ a.val = (b.val + 3) % 7) ↔
        (a = b ∨ a = b + 1 ∨ a = b + 3) := by
      decide +kernel
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hfp : fL.getD p.val 0 < 7 := (hpts p).1
      have hfl_ge : 7 ≤ fL.getD (7 + l.val) 0 := (hlines l).1
      have hfl_lt : fL.getD (7 + l.val) 0 < 14 := (hbij (Fin.natAdd 7 l)).1
      let p' : Fin 7 := ⟨fL.getD p.val 0, hfp⟩
      let l' : Fin 7 := ⟨fL.getD (7 + l.val) 0 - 7, by omega⟩
      have ep : Fin.castAdd 7 p' = finPerm (Fin.castAdd 7 p) := Fin.ext rfl
      have el : Fin.natAdd 7 l' = finPerm (Fin.natAdd 7 l) := by
        apply Fin.ext
        change 7 + (fL.getD (7 + l.val) 0 - 7) = fL.getD (7 + l.val) 0
        omega
      refine ⟨p', l', ?_, by rwa [ep], by rwa [el]⟩
      exact (hmod_iff p' l').1 ((hincPres p l).2 hpl)
    · rintro ⟨p', l', hpl', hp', hl'⟩
      have hgp : gL.getD p'.val 0 < 7 := (hpts p').2
      have hgl_ge : 7 ≤ gL.getD (7 + l'.val) 0 := (hlines l').2
      have hgl_lt : gL.getD (7 + l'.val) 0 < 14 := (hbij (Fin.natAdd 7 l')).2.1
      let p : Fin 7 := ⟨gL.getD p'.val 0, hgp⟩
      let l : Fin 7 := ⟨gL.getD (7 + l'.val) 0 - 7, by omega⟩
      have hfp_eq : fL.getD p.val 0 = p'.val := (hbij (Fin.castAdd 7 p')).2.2.2
      have hfl_eq : fL.getD (7 + l.val) 0 = 7 + l'.val := by
        have h1 : 7 + l.val = gL.getD (7 + l'.val) 0 := by
          change 7 + (gL.getD (7 + l'.val) 0 - 7) = gL.getD (7 + l'.val) 0; omega
        rw [h1]
        exact (hbij (Fin.natAdd 7 l')).2.2.2
      have ep : finPerm (Fin.castAdd 7 p) = Fin.castAdd 7 p' := Fin.ext hfp_eq
      have el : finPerm (Fin.natAdd 7 l) = Fin.natAdd 7 l' := Fin.ext hfl_eq
      refine ⟨p, l, ?_, by rwa [ep], by rwa [el]⟩
      have hmod := (hmod_iff p' l').2 hpl'
      apply (hincPres p l).1
      simpa only [hfp_eq, hfl_eq, Nat.add_sub_cancel_left] using hmod
  have hC1size_pos : 0 < C1.size := hC1size.symm ▸ hCsize_pos
  have hC1out : C1.output < 14 + C1.size := by
    rw [hC1size]; exact hmapW_bound C.output C.size hCout
  have hC1_14_false : ∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
      (C1.wires (List.ofFn x)).getD 14 false = false := by
    intro x hx
    have hw := wire_gate C1 hC1AO x 0 hC1size_pos
    have hop0 : (gateAt C1 0).op = GateOp.and := by rw [hC1g0]
    have ha0 : opnd C1 0 0 = 0 := by unfold opnd; rw [hC1g0]; rfl
    have hb0 : opnd C1 0 1 = 7 := by unfold opnd; rw [hC1g0]; rfl
    rw [hop0, ha0, hb0, eval_and, wire_input C1 x 0 (by omega), wire_input C1 x 7 (by omega)] at hw
    rw [hw]
    rcases hx with h0 | h7
    · simp [h0]
    · simp [h7]
  let optW (gs : List Gate) (x : Fin 14 → Bool) (o : Option ℕ) : Bool :=
    Option.casesOn o false (fun w => ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false)
  have optW_snoc : ∀ (gs : List Gate) (g : Gate) (x : Fin 14 → Bool) (o : Option ℕ),
      (∀ w', o = some w' → w' < 14 + gs.length) →
      optW (gs ++ [g]) x o = optW gs x o := by
    intro gs g x o ho
    cases o with
    | none => rfl
    | some w' =>
      have hw' : w' < 14 + gs.length := ho w' rfl
      dsimp only [optW]
      change ((gs ++ [g]).foldl wstep (List.ofFn x)).getD w' false =
        (gs.foldl wstep (List.ofFn x)).getD w' false
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl wstep (List.ofFn x)).length = 14 + gs.length := by
        rw [wfold_len, List.length_ofFn]
      have hlt : w' < (gs.foldl wstep (List.ofFn x)).length := by omega
      change ((gs.foldl wstep (List.ofFn x)) ++ [_]).getD w' false = _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  have hBuild : ∀ j, 1 ≤ j → j ≤ C1.size →
      ∃ (gs : List Gate) (rep : ℕ → Option ℕ),
        IsAO2 14 ⟨gs, 0⟩ ∧
        (∀ k < gs.length, opnd ⟨gs, 0⟩ k 0 ≠ opnd ⟨gs, 0⟩ k 1) ∧
        gs.length + 1 ≤ j ∧
        rep 14 = none ∧
        (∀ w < 14 + j, ∀ w', rep w = some w' → w' < 14 + gs.length) ∧
        (∀ x : Fin 14 → Bool, ∀ w < 14 + j,
          optW gs x (rep w) = true → (C1.wires (List.ofFn x)).getD w false = true) ∧
        (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
          ∀ w < 14 + j, optW gs x (rep w) = (C1.wires (List.ofFn x)).getD w false) ∧
        (gs.length + 1 = j → ∀ w < 14 + j, w ≠ 14 →
          rep w ≠ none ∧ ∀ x : Fin 14 → Bool,
            optW gs x (rep w) = (C1.wires (List.ofFn x)).getD w false) := by
    intro j hj1
    induction j with
    | zero => omega
    | succ j ih =>
      intro hjle
      by_cases hj0 : j = 0
      · subst hj0
        refine ⟨[], fun w => if w < 14 then some w else none, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨(by intro g hg; cases hg), (by intro k hk; cases hk), (by intro g hg; cases hg)⟩
        · intro k hk; cases hk
        · simp
        · simp
        · intro w _ w' hw'
          by_cases hw14 : w < 14
          · simp only [hw14, ↓reduceIte, Option.some.injEq] at hw'; subst hw'; simp [hw14]
          · simp only [hw14, ↓reduceIte] at hw'; cases hw'
        · intro x w hw hopt
          by_cases hw14 : w < 14
          · simp only [hw14, ↓reduceIte] at hopt
            have hi1 := wire_input ⟨[], 0⟩ x w hw14
            have hi2 := wire_input C1 x w hw14
            rw [hi2]; rwa [← hi1]
          · simp only [hw14, ↓reduceIte] at hopt; cases hopt
        · intro x hx w hw
          by_cases hw14 : w < 14
          · simp only [hw14, ↓reduceIte]
            dsimp only [optW]
            rw [wire_input ⟨[], 0⟩ x w hw14, wire_input C1 x w hw14]
          · have hw14eq : w = 14 := by omega
            subst hw14eq
            simp only [lt_self_iff_false, ↓reduceIte]
            exact (hC1_14_false x hx).symm
        · intro _ w hw hwne
          have hw14 : w < 14 := by omega
          simp only [hw14, ↓reduceIte]
          refine ⟨Option.some_ne_none _, fun x => ?_⟩
          dsimp only [optW]
          rw [wire_input ⟨[], 0⟩ x w hw14, wire_input C1 x w hw14]
      · have hj1' : 1 ≤ j := by omega
        have hjlt : j < C1.size := by omega
        obtain ⟨gs, rep, hgsAO, hgsDist, hgsLen, hrep14, hrepBnd, hSound, hAgree, hFull⟩ :=
          ih hj1' (by omega)
        obtain ⟨hinp, hop, ha, hb⟩ := gate_inputs2 C1 hC1AO j hjlt
        let u := opnd C1 j 0
        let v := opnd C1 j 1
        have hu_lt : u < 14 + j := ha
        have hv_lt : v < 14 + j := hb
        have hstep_same : ∀ (oNew : Option ℕ),
            (∀ w', oNew = some w' → w' < 14 + gs.length) →
            (∀ x : Fin 14 → Bool, optW gs x oNew = true →
              (C1.wires (List.ofFn x)).getD (14 + j) false = true) →
            (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
              optW gs x oNew = (C1.wires (List.ofFn x)).getD (14 + j) false) →
            ∃ (gs' : List Gate) (rep' : ℕ → Option ℕ),
              IsAO2 14 ⟨gs', 0⟩ ∧
              (∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1) ∧
              gs'.length + 1 ≤ j + 1 ∧
              rep' 14 = none ∧
              (∀ w < 14 + (j + 1), ∀ w', rep' w = some w' → w' < 14 + gs'.length) ∧
              (∀ x : Fin 14 → Bool, ∀ w < 14 + (j + 1),
                optW gs' x (rep' w) = true → (C1.wires (List.ofFn x)).getD w false = true) ∧
              (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
                ∀ w < 14 + (j + 1), optW gs' x (rep' w) = (C1.wires (List.ofFn x)).getD w false) ∧
              (gs'.length + 1 = j + 1 → ∀ w < 14 + (j + 1), w ≠ 14 →
                rep' w ≠ none ∧ ∀ x : Fin 14 → Bool,
                  optW gs' x (rep' w) = (C1.wires (List.ofFn x)).getD w false) := by
          intro oNew hoBnd hoSound hoAgree
          let rep' : ℕ → Option ℕ := fun w => if w = 14 + j then oNew else rep w
          refine ⟨gs, rep', hgsAO, hgsDist, by omega, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only [rep']; rw [if_neg (by omega)]; exact hrep14
          · intro w hw w' hw'
            by_cases heq : w = 14 + j
            · subst heq; dsimp only [rep'] at hw'; rw [if_pos rfl] at hw'; exact hoBnd w' hw'
            · dsimp only [rep'] at hw'; rw [if_neg heq] at hw'; exact hrepBnd w (by omega) w' hw'
          · intro x w hw hopt
            by_cases heq : w = 14 + j
            · subst heq; dsimp only [rep'] at hopt; rw [if_pos rfl] at hopt; exact hoSound x hopt
            · dsimp only [rep'] at hopt; rw [if_neg heq] at hopt; exact hSound x w (by omega) hopt
          · intro x hx w hw
            by_cases heq : w = 14 + j
            · subst heq; dsimp only [rep']; rw [if_pos rfl]; exact hoAgree x hx
            · dsimp only [rep']; rw [if_neg heq]; exact hAgree x hx w (by omega)
          · intro heq; omega
        rcases hop with hand | hor
        · have hC1j : ∀ x : Fin 14 → Bool,
              (C1.wires (List.ofFn x)).getD (14 + j) false =
                ((C1.wires (List.ofFn x)).getD u false && (C1.wires (List.ofFn x)).getD v false) := by
            intro x; rw [wire_gate C1 hC1AO x j hjlt, hand, eval_and]
          cases hru : rep u with
          | none =>
            apply hstep_same none (fun _ h => by cases h) (fun _ h => by cases h)
            intro x hx
            have huF : (C1.wires (List.ofFn x)).getD u false = false := by
              have h1 := hAgree x hx u hu_lt; rw [hru] at h1; exact h1.symm
            rw [hC1j x, huF]; rfl
          | some u' =>
            cases hrv : rep v with
            | none =>
              apply hstep_same none (fun _ h => by cases h) (fun _ h => by cases h)
              intro x hx
              have hvF : (C1.wires (List.ofFn x)).getD v false = false := by
                have h1 := hAgree x hx v hv_lt; rw [hrv] at h1; exact h1.symm
              rw [hC1j x, hvF]; simp [optW]
            | some v' =>
              by_cases huv : u' = v'
              · apply hstep_same (some u')
                  (fun w' hw' => by cases hw'; exact hrepBnd u hu_lt u' hru)
                · intro x hx
                  rw [hC1j x, Bool.and_eq_true]
                  have huT := hSound x u hu_lt (by rw [hru]; exact hx)
                  have hvT := hSound x v hv_lt (by rw [hrv, ← huv]; exact hx)
                  exact ⟨huT, hvT⟩
                · intro x hx
                  have huE := hAgree x hx u hu_lt
                  have hvE := hAgree x hx v hv_lt
                  rw [hru] at huE; rw [hrv, ← huv] at hvE
                  rw [hC1j x, ← huE, ← hvE, Bool.and_self]
              · let newG : Gate := ⟨GateOp.and, [u', v']⟩
                let gs' : List Gate := gs ++ [newG]
                let rep' : ℕ → Option ℕ := fun w => if w = 14 + j then some (14 + gs.length) else rep w
                have hu'lt : u' < 14 + gs.length := hrepBnd u hu_lt u' hru
                have hv'lt : v' < 14 + gs.length := hrepBnd v hv_lt v' hrv
                have hgs'len : gs'.length = gs.length + 1 := by simp [gs']
                have hgs'AO : IsAO2 14 ⟨gs', 0⟩ := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro g hg
                    rw [List.mem_append, List.mem_singleton] at hg
                    rcases hg with h1 | rfl
                    · exact hgsAO.1 g h1
                    · exact Or.inl rfl
                  · intro k hk i hi
                    have hk' : k < gs.length + 1 := by simpa [gs'] using hk
                    by_cases hkl : k < gs.length
                    · have hgk : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                        unfold gateAt; change (gs ++ [newG]).getD k _ = gs.getD k _
                        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
                      rw [hgk] at hi; exact hgsAO.2.1 k hkl i hi
                    · have hke : k = gs.length := by omega
                      subst hke
                      have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                        unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                      rw [hgk] at hi
                      simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl <;> omega
                  · intro g hg
                    rw [List.mem_append, List.mem_singleton] at hg
                    rcases hg with h1 | rfl
                    · exact hgsAO.2.2 g h1
                    · rfl
                have hgs'Dist : ∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1 := by
                  intro k hk
                  have hk' : k < gs.length + 1 := by simpa [gs'] using hk
                  by_cases hkl : k < gs.length
                  · have hgk : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                      unfold gateAt; change (gs ++ [newG]).getD k _ = gs.getD k _
                      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
                    unfold opnd; rw [hgk]; exact hgsDist k hkl
                  · have hke : k = gs.length := by omega
                    subst hke
                    have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                      unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                    unfold opnd; rw [hgk]; exact huv
                have hnewVal : ∀ x : Fin 14 → Bool,
                    optW gs' x (some (14 + gs.length)) =
                      (optW gs x (some u') && optW gs x (some v')) := by
                  intro x
                  dsimp only [optW]
                  have hwg := wire_gate ⟨gs', 0⟩ hgs'AO x gs.length (by change gs.length < gs'.length; omega)
                  have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                    unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                  have ho0 : opnd ⟨gs', 0⟩ gs.length 0 = u' := by unfold opnd; rw [hgk]; rfl
                  have ho1 : opnd ⟨gs', 0⟩ gs.length 1 = v' := by unfold opnd; rw [hgk]; rfl
                  rw [hwg, hgk, ho0, ho1, eval_and]
                  have hsu := optW_snoc gs newG x (some u') (fun _ h => by cases h; exact hu'lt)
                  have hsv := optW_snoc gs newG x (some v') (fun _ h => by cases h; exact hv'lt)
                  exact congrArg₂ (· && ·) hsu hsv
                refine ⟨gs', rep', hgs'AO, hgs'Dist, by omega, ?_, ?_, ?_, ?_, ?_⟩
                · dsimp only [rep']; rw [if_neg (by omega)]; exact hrep14
                · intro w hw w' hw'
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep'] at hw'; rw [if_pos rfl] at hw'; cases hw'; omega
                  · dsimp only [rep'] at hw'; rw [if_neg heq] at hw'
                    have := hrepBnd w (by omega) w' hw'; omega
                · intro x w hw hopt
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep'] at hopt; rw [if_pos rfl] at hopt
                    rw [hnewVal x, Bool.and_eq_true] at hopt
                    rw [hC1j x, Bool.and_eq_true]
                    exact ⟨hSound x u hu_lt (by rw [hru]; exact hopt.1),
                           hSound x v hv_lt (by rw [hrv]; exact hopt.2)⟩
                  · dsimp only [rep'] at hopt; rw [if_neg heq] at hopt
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))] at hopt
                    exact hSound x w (by omega) hopt
                · intro x hx w hw
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep']; rw [if_pos rfl, hnewVal x, hC1j x]
                    have huE := hAgree x hx u hu_lt; rw [hru] at huE
                    have hvE := hAgree x hx v hv_lt; rw [hrv] at hvE
                    rw [huE, hvE]
                  · dsimp only [rep']; rw [if_neg heq]
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))]
                    exact hAgree x hx w (by omega)
                · intro hfull' w hw hwne
                  have hfull : gs.length + 1 = j := by omega
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep']; rw [if_pos rfl]
                    refine ⟨Option.some_ne_none _, fun x => ?_⟩
                    rw [hnewVal x, hC1j x]
                    have hu14 : u ≠ 14 := by intro h; rw [h, hrep14] at hru; cases hru
                    have hv14 : v ≠ 14 := by intro h; rw [h, hrep14] at hrv; cases hrv
                    have huE := (hFull hfull u hu_lt hu14).2 x; rw [hru] at huE
                    have hvE := (hFull hfull v hv_lt hv14).2 x; rw [hrv] at hvE
                    rw [huE, hvE]
                  · dsimp only [rep']; rw [if_neg heq]
                    obtain ⟨hne, hval⟩ := hFull hfull w (by omega) hwne
                    refine ⟨hne, fun x => ?_⟩
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))]
                    exact hval x
        · have hC1j : ∀ x : Fin 14 → Bool,
              (C1.wires (List.ofFn x)).getD (14 + j) false =
                ((C1.wires (List.ofFn x)).getD u false || (C1.wires (List.ofFn x)).getD v false) := by
            intro x; rw [wire_gate C1 hC1AO x j hjlt, hor, eval_or]
          cases hru : rep u with
          | none =>
            cases hrv : rep v with
            | none =>
              apply hstep_same none (fun _ h => by cases h) (fun _ h => by cases h)
              intro x hx
              have huF : (C1.wires (List.ofFn x)).getD u false = false := by
                have h1 := hAgree x hx u hu_lt; rw [hru] at h1; exact h1.symm
              have hvF : (C1.wires (List.ofFn x)).getD v false = false := by
                have h1 := hAgree x hx v hv_lt; rw [hrv] at h1; exact h1.symm
              rw [hC1j x, huF, hvF]; rfl
            | some v' =>
              apply hstep_same (some v')
                (fun w' hw' => by cases hw'; exact hrepBnd v hv_lt v' hrv)
              · intro x hx
                rw [hC1j x, Bool.or_eq_true]
                exact Or.inr (hSound x v hv_lt (by rw [hrv]; exact hx))
              · intro x hx
                have huF : (C1.wires (List.ofFn x)).getD u false = false := by
                  have h1 := hAgree x hx u hu_lt; rw [hru] at h1; exact h1.symm
                have hvE := hAgree x hx v hv_lt; rw [hrv] at hvE
                rw [hC1j x, huF, Bool.false_or, hvE]
          | some u' =>
            cases hrv : rep v with
            | none =>
              apply hstep_same (some u')
                (fun w' hw' => by cases hw'; exact hrepBnd u hu_lt u' hru)
              · intro x hx
                rw [hC1j x, Bool.or_eq_true]
                exact Or.inl (hSound x u hu_lt (by rw [hru]; exact hx))
              · intro x hx
                have hvF : (C1.wires (List.ofFn x)).getD v false = false := by
                  have h1 := hAgree x hx v hv_lt; rw [hrv] at h1; exact h1.symm
                have huE := hAgree x hx u hu_lt; rw [hru] at huE
                rw [hC1j x, hvF, Bool.or_false, huE]
            | some v' =>
              by_cases huv : u' = v'
              · apply hstep_same (some u')
                  (fun w' hw' => by cases hw'; exact hrepBnd u hu_lt u' hru)
                · intro x hx
                  rw [hC1j x, Bool.or_eq_true]
                  exact Or.inl (hSound x u hu_lt (by rw [hru]; exact hx))
                · intro x hx
                  have huE := hAgree x hx u hu_lt; rw [hru] at huE
                  have hvE := hAgree x hx v hv_lt; rw [hrv, ← huv] at hvE
                  rw [hC1j x, ← huE, ← hvE, Bool.or_self]
              · let newG : Gate := ⟨GateOp.or, [u', v']⟩
                let gs' : List Gate := gs ++ [newG]
                let rep' : ℕ → Option ℕ := fun w => if w = 14 + j then some (14 + gs.length) else rep w
                have hu'lt : u' < 14 + gs.length := hrepBnd u hu_lt u' hru
                have hv'lt : v' < 14 + gs.length := hrepBnd v hv_lt v' hrv
                have hgs'len : gs'.length = gs.length + 1 := by simp [gs']
                have hgs'AO : IsAO2 14 ⟨gs', 0⟩ := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro g hg
                    rw [List.mem_append, List.mem_singleton] at hg
                    rcases hg with h1 | rfl
                    · exact hgsAO.1 g h1
                    · exact Or.inr rfl
                  · intro k hk i hi
                    have hk' : k < gs.length + 1 := by simpa [gs'] using hk
                    by_cases hkl : k < gs.length
                    · have hgk : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                        unfold gateAt; change (gs ++ [newG]).getD k _ = gs.getD k _
                        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
                      rw [hgk] at hi; exact hgsAO.2.1 k hkl i hi
                    · have hke : k = gs.length := by omega
                      subst hke
                      have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                        unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                      rw [hgk] at hi
                      simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl <;> omega
                  · intro g hg
                    rw [List.mem_append, List.mem_singleton] at hg
                    rcases hg with h1 | rfl
                    · exact hgsAO.2.2 g h1
                    · rfl
                have hgs'Dist : ∀ k < gs'.length, opnd ⟨gs', 0⟩ k 0 ≠ opnd ⟨gs', 0⟩ k 1 := by
                  intro k hk
                  have hk' : k < gs.length + 1 := by simpa [gs'] using hk
                  by_cases hkl : k < gs.length
                  · have hgk : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                      unfold gateAt; change (gs ++ [newG]).getD k _ = gs.getD k _
                      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
                    unfold opnd; rw [hgk]; exact hgsDist k hkl
                  · have hke : k = gs.length := by omega
                    subst hke
                    have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                      unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                    unfold opnd; rw [hgk]; exact huv
                have hnewVal : ∀ x : Fin 14 → Bool,
                    optW gs' x (some (14 + gs.length)) =
                      (optW gs x (some u') || optW gs x (some v')) := by
                  intro x
                  dsimp only [optW]
                  have hwg := wire_gate ⟨gs', 0⟩ hgs'AO x gs.length (by change gs.length < gs'.length; omega)
                  have hgk : gateAt ⟨gs', 0⟩ gs.length = newG := by
                    unfold gateAt; change (gs ++ [newG]).getD gs.length _ = newG
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                  have ho0 : opnd ⟨gs', 0⟩ gs.length 0 = u' := by unfold opnd; rw [hgk]; rfl
                  have ho1 : opnd ⟨gs', 0⟩ gs.length 1 = v' := by unfold opnd; rw [hgk]; rfl
                  rw [hwg, hgk, ho0, ho1, eval_or]
                  have hsu := optW_snoc gs newG x (some u') (fun _ h => by cases h; exact hu'lt)
                  have hsv := optW_snoc gs newG x (some v') (fun _ h => by cases h; exact hv'lt)
                  exact congrArg₂ (· || ·) hsu hsv
                refine ⟨gs', rep', hgs'AO, hgs'Dist, by omega, ?_, ?_, ?_, ?_, ?_⟩
                · dsimp only [rep']; rw [if_neg (by omega)]; exact hrep14
                · intro w hw w' hw'
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep'] at hw'; rw [if_pos rfl] at hw'; cases hw'; omega
                  · dsimp only [rep'] at hw'; rw [if_neg heq] at hw'
                    have := hrepBnd w (by omega) w' hw'; omega
                · intro x w hw hopt
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep'] at hopt; rw [if_pos rfl] at hopt
                    rw [hnewVal x, Bool.or_eq_true] at hopt
                    rw [hC1j x, Bool.or_eq_true]
                    rcases hopt with h1 | h2
                    · exact Or.inl (hSound x u hu_lt (by rw [hru]; exact h1))
                    · exact Or.inr (hSound x v hv_lt (by rw [hrv]; exact h2))
                  · dsimp only [rep'] at hopt; rw [if_neg heq] at hopt
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))] at hopt
                    exact hSound x w (by omega) hopt
                · intro x hx w hw
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep']; rw [if_pos rfl, hnewVal x, hC1j x]
                    have huE := hAgree x hx u hu_lt; rw [hru] at huE
                    have hvE := hAgree x hx v hv_lt; rw [hrv] at hvE
                    rw [huE, hvE]
                  · dsimp only [rep']; rw [if_neg heq]
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))]
                    exact hAgree x hx w (by omega)
                · intro hfull' w hw hwne
                  have hfull : gs.length + 1 = j := by omega
                  by_cases heq : w = 14 + j
                  · subst heq; dsimp only [rep']; rw [if_pos rfl]
                    refine ⟨Option.some_ne_none _, fun x => ?_⟩
                    rw [hnewVal x, hC1j x]
                    have hu14 : u ≠ 14 := by intro h; rw [h, hrep14] at hru; cases hru
                    have hv14 : v ≠ 14 := by intro h; rw [h, hrep14] at hrv; cases hrv
                    have huE := (hFull hfull u hu_lt hu14).2 x; rw [hru] at huE
                    have hvE := (hFull hfull v hv_lt hv14).2 x; rw [hrv] at hvE
                    rw [huE, hvE]
                  · dsimp only [rep']; rw [if_neg heq]
                    obtain ⟨hne, hval⟩ := hFull hfull w (by omega) hwne
                    refine ⟨hne, fun x => ?_⟩
                    rw [optW_snoc gs newG x (rep w) (hrepBnd w (by omega))]
                    exact hval x
  obtain ⟨gs, rep, hgsAO, hgsDist, hgsLen, hrep14, hrepBnd, hSound, hAgree, hFull⟩ :=
    hBuild C1.size hC1size_pos (le_refl _)
  cases hrout : rep C1.output with
  | none =>
    let x18 : Fin 14 → Bool := fun i => decide (i = 1 ∨ i = 8)
    have hx18_0 : x18 0 = false := by decide
    have h1 := hAgree x18 (Or.inl hx18_0) C1.output hC1out
    rw [hrout] at h1
    have hC1_18 : C1.eval (List.ofFn x18) = true :=
      (hC1Fano x18).mpr ⟨1, 1, Or.inl rfl, by decide, by decide⟩
    change false = C1.eval (List.ofFn x18) at h1
    rw [hC1_18] at h1
    exact Bool.noConfusion h1
  | some outD =>
    let D : Circuit := ⟨gs, outD⟩
    have hDAO : IsAO2 14 D := hgsAO
    have hDdist : ∀ k < D.size, opnd D k 0 ≠ opnd D k 1 := hgsDist
    have houtD_lt : outD < 14 + D.size := hrepBnd C1.output hC1out outD hrout
    have hDsize_le26 : D.size ≤ 26 := by
      have : C1.size ≤ 27 := hC1size.symm ▸ hSize
      change gs.length ≤ 26
      omega
    have hDsound : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      intro x hx
      apply (hC1Fano x).mp
      exact hSound x C1.output hC1out (by rw [hrout]; exact hx)
    have hDminus : ∀ x : Fin 14 → Bool,
        (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ ¬(p = 0 ∧ l = 0) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        D.eval (List.ofFn x) = true := by
      rintro x ⟨p, l, hpl, hne00, hp, hl⟩
      let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
      have he07 : e 0 = false ∨ e 7 = false := by
        by_cases hp0 : p = 0
        · right
          have hl0 : l ≠ 0 := fun h => hne00 ⟨hp0, h⟩
          dsimp only [e]
          simp only [decide_eq_false_iff_not, not_or]
          exact ⟨fun h => by have := congrArg Fin.val h; change 7 = p.val at this; omega,
            fun h => hl0 (Fin.ext (by have := congrArg Fin.val h; change 7 = 7 + l.val at this; omega))⟩
        · left
          dsimp only [e]
          simp only [decide_eq_false_iff_not, not_or]
          exact ⟨fun h => hp0 (Fin.ext (by have := congrArg Fin.val h; change 0 = p.val at this; omega)),
            fun h => by have := congrArg Fin.val h; change 0 = 7 + l.val at this; omega⟩
      have hCe : C1.eval (List.ofFn e) = true :=
        (hC1Fano e).mpr ⟨p, l, hpl, by simp [e], by simp [e]⟩
      have hDe : D.eval (List.ofFn e) = true := by
        have h1 := hAgree e he07 C1.output hC1out
        rw [hrout] at h1
        exact h1.trans hCe
      have hle : ∀ i : Fin 14, e i = true → x i = true := by
        intro i hi
        simp only [e, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact hp
        · exact hl
      exact eval_mono D hDAO e x hle outD houtD_lt hDe
    by_cases hFullEq : gs.length + 1 = C1.size
    · have hOutNe14 : C1.output ≠ 14 := by
        intro h; rw [h, hrep14] at hrout; cases hrout
      have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
        intro x
        have h1 := (hFull hFullEq C1.output hC1out hOutNe14).2 x
        rw [hrout] at h1
        change D.eval (List.ofFn x) = C1.eval (List.ofFn x) at h1
        rw [h1]
        exact hC1Fano x
      exact noFano26 D hDsize_le26 hDAO hDdist hDFano
    · by_cases hle24 : D.size ≤ 24
      · let gA : Gate := ⟨GateOp.and, [0, 7]⟩
        let gO : Gate := ⟨GateOp.or, [outD, 14 + D.size]⟩
        let E : Circuit := ⟨gs ++ [gA, gO], 14 + D.size + 1⟩
        have hEsize : E.size ≤ 26 := by
          change (gs ++ [gA, gO]).length ≤ 26
          simp only [List.length_append, List.length_cons, List.length_nil]
          change gs.length ≤ 24 at hle24
          omega
        have hEAO : IsAO2 14 E := by
          refine ⟨?_, ?_, ?_⟩
          · intro g hg
            rw [List.mem_append, List.mem_cons, List.mem_singleton] at hg
            rcases hg with h1 | rfl | rfl
            · exact hgsAO.1 g h1
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro k hk i hi
            have hk' : k < gs.length + 2 := by simpa [E] using hk
            by_cases hkl : k < gs.length
            · have hgk : gateAt E k = gateAt D k := by
                unfold gateAt; change (gs ++ [gA, gO]).getD k _ = gs.getD k _
                rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
              rw [hgk] at hi; exact hgsAO.2.1 k hkl i hi
            · by_cases hk1 : k = gs.length
              · subst hk1
                have hgk : gateAt E gs.length = gA := by
                  unfold gateAt; change (gs ++ [gA, gO]).getD gs.length _ = gA
                  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
                rw [hgk] at hi
                simp only [gA, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl <;> omega
              · have hk2 : k = gs.length + 1 := by omega
                subst hk2
                have hgk : gateAt E (gs.length + 1) = gO := by
                  unfold gateAt; change (gs ++ [gA, gO]).getD (gs.length + 1) _ = gO
                  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
                  have hsub : gs.length + 1 - gs.length = 1 := by omega
                  rw [hsub]; rfl
                rw [hgk] at hi
                simp only [gO, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with hi | hi
                · rw [hi]; change outD < 14 + gs.length at houtD_lt; omega
                · rw [hi]; change 14 + gs.length < 14 + (gs.length + 1); omega
          · intro g hg
            rw [List.mem_append, List.mem_cons, List.mem_singleton] at hg
            rcases hg with h1 | rfl | rfl
            · exact hgsAO.2.2 g h1
            · rfl
            · rfl
        have hEdist : ∀ k < E.size, opnd E k 0 ≠ opnd E k 1 := by
          intro k hk
          have hk' : k < gs.length + 2 := by
            change k < (gs ++ [gA, gO]).length at hk
            simp only [List.length_append, List.length_cons, List.length_nil] at hk
            exact hk
          by_cases hkl : k < gs.length
          · have hgk : gateAt E k = gateAt D k := by
              unfold gateAt; change (gs ++ [gA, gO]).getD k _ = gs.getD k _
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hkl]
            unfold opnd; rw [hgk]; exact hgsDist k hkl
          · by_cases hk1 : k = gs.length
            · subst hk1
              have hgk : gateAt E gs.length = gA := by
                unfold gateAt; change (gs ++ [gA, gO]).getD gs.length _ = gA
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
              unfold opnd; rw [hgk]; decide
            · have hk2 : k = gs.length + 1 := by omega
              subst hk2
              have hgk : gateAt E (gs.length + 1) = gO := by
                unfold gateAt; change (gs ++ [gA, gO]).getD (gs.length + 1) _ = gO
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
                have hsub : gs.length + 1 - gs.length = 1 := by omega
                rw [hsub]; rfl
              unfold opnd; rw [hgk]
              change outD ≠ 14 + D.size; omega
        have hEeval : ∀ x : Fin 14 → Bool,
            E.eval (List.ofFn x) = (D.eval (List.ofFn x) || (x 0 && x 7)) := by
          intro x
          have hgA : gateAt E D.size = gA := by
            unfold gateAt; change (gs ++ [gA, gO]).getD gs.length _ = gA
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
          have hgO : gateAt E (D.size + 1) = gO := by
            unfold gateAt; change (gs ++ [gA, gO]).getD (gs.length + 1) _ = gO
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
            have hsub : gs.length + 1 - gs.length = 1 := by omega
            rw [hsub]; rfl
          have hwO := wire_gate E hEAO x (D.size + 1) (by change gs.length + 1 < (gs ++ [gA, gO]).length; simp)
          have hwA := wire_gate E hEAO x D.size (by change gs.length < (gs ++ [gA, gO]).length; simp)
          have hEout : E.eval (List.ofFn x) = (E.wires (List.ofFn x)).getD (14 + (D.size + 1)) false := rfl
          have hoO0 : opnd E (D.size + 1) 0 = outD := by unfold opnd; rw [hgO]; rfl
          have hoO1 : opnd E (D.size + 1) 1 = 14 + D.size := by unfold opnd; rw [hgO]; rfl
          have hoA0 : opnd E D.size 0 = 0 := by unfold opnd; rw [hgA]; rfl
          have hoA1 : opnd E D.size 1 = 7 := by unfold opnd; rw [hgA]; rfl
          have hEpref : (E.wires (List.ofFn x)).getD outD false = D.eval (List.ofFn x) := by
            change ((gs ++ [gA, gO]).foldl wstep (List.ofFn x)).getD outD false =
              (gs.foldl wstep (List.ofFn x)).getD outD false
            rw [List.foldl_append]
            exact wfold_getD_lt [gA, gO] (gs.foldl wstep (List.ofFn x)) outD
              (by rw [wfold_len, List.length_ofFn]; exact houtD_lt)
          rw [hEout, hwO, hgO, hoO0, hoO1, eval_or, hEpref, hwA, hgA, hoA0, hoA1, eval_and,
              wire_input E x 0 (by omega), wire_input E x 7 (by omega)]
          rfl
        have hEFano : ∀ x : Fin 14 → Bool, E.eval (List.ofFn x) = true ↔
            ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
              x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
          intro x
          rw [hEeval x, Bool.or_eq_true, Bool.and_eq_true]
          constructor
          · rintro (hD | ⟨h0, h7⟩)
            · exact hDsound x hD
            · exact ⟨0, 0, Or.inl rfl, h0, h7⟩
          · rintro ⟨p, l, hpl, hp, hl⟩
            by_cases h00 : p = 0 ∧ l = 0
            · rcases h00 with ⟨rfl, rfl⟩
              exact Or.inr ⟨hp, hl⟩
            · exact Or.inl (hDminus x ⟨p, l, hpl, h00, hp, hl⟩)
        exact noFano26 E hEsize hEAO hEdist hEFano
      · have hD25 : D.size = 25 := by
          have : C1.size ≤ 27 := hC1size.symm ▸ hSize
          change gs.length = 25
          change ¬ gs.length ≤ 24 at hle24
          omega
        cases h07 : D.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) with
        | false =>
          exact noMinusEdge25 D hD25 hDAO hDdist hDsound hDminus h07
        | true =>
          have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
              ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
                x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
            intro x
            constructor
            · exact hDsound x
            · rintro ⟨p, l, hpl, hp, hl⟩
              by_cases h00 : p = 0 ∧ l = 0
              · rcases h00 with ⟨rfl, rfl⟩
                exact eval_mono D hDAO (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) x
                  (fun i hi => by
                    simp only [decide_eq_true_eq] at hi
                    rcases hi with rfl | rfl
                    · exact hp
                    · exact hl)
                  outD houtD_lt h07
              · exact hDminus x ⟨p, l, hpl, h00, hp, hl⟩
          exact noFano26 D hDsize_le26 hDAO hDdist hDFano
