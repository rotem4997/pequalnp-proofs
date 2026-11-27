import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MinimumComplex PEqualNP.NotBracket in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7391_1
    (hMono18 :
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
      ∀ D : Circuit, Strict 10 D → D.size ≤ 18 → D.output + 1 = 10 + D.size →
        notCount D = 0 →
        D.gates.head? ∈ ([some ⟨.and, [0, 1]⟩, some ⟨.and, [0, 2]⟩,
          some ⟨.or, [0, 1]⟩, some ⟨.or, [0, 2]⟩] : List (Option Gate)) →
        ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x)
    (hNotFirst :
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
      ∀ D : Circuit, Strict 10 D → D.size ≤ 19 → D.output + 1 = 10 + D.size →
        1 ≤ notCount D → 10 + notCount D ≤ D.size →
        (∀ j < D.size - 1, ∃ g ∈ D.gates, 10 + j ∈ g.inputs) →
        (∀ k (hk : k < D.gates.length), D.gates[k].op = .not →
          ∀ g ∈ D.gates, g.op = .not → 10 + k ∉ g.inputs) →
        D.gates.head? = some ⟨.not, [0]⟩ →
        ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x)
    (hBinFirst :
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
      ∀ D : Circuit, Strict 10 D → D.size ≤ 19 → D.output + 1 = 10 + D.size →
        1 ≤ notCount D → 10 + notCount D ≤ D.size →
        (∀ j < D.size - 1, ∃ g ∈ D.gates, 10 + j ∈ g.inputs) →
        (∀ k (hk : k < D.gates.length), D.gates[k].op = .not →
          ∀ g ∈ D.gates, g.op = .not → 10 + k ∉ g.inputs) →
        D.gates.head? ∈ ([some ⟨.and, [0, 1]⟩, some ⟨.and, [0, 2]⟩,
          some ⟨.or, [0, 1]⟩, some ⟨.or, [0, 2]⟩] : List (Option Gate)) →
        ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (10 : ℕ)) && x2 (1 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (2 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (3 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (4 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (0 : Fin (10 : ℕ)) || x2 (0 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (5 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (7 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (9 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (6 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (8 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x3 : ℕ),     have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.getD x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };     (∀ x5 ∈ x4.inputs, x5 < (10 : ℕ) + x3) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length ≤ (1 : ℕ)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (19 : ℕ) → x3.output + (1 : ℕ) = (10 : ℕ) + x3.size → x2 x3 → (x3.size < (19 : ℕ) ∨ ∃ x8 ∈ x3.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬x1 x3) := by
  classical
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro x1 x2 C0 hFan0 hSz0 _ hLeg0 hBud0 hComp0
  let edges : List ℕ := [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85]
  let f : (Fin 10 → Bool) → Bool := fun x =>
    edges.any fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
  have sameF : ∀ x : Fin 10 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) = f x := by
    intro x
    simp only [f, edges, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hEvalDef : ∀ (E : Circuit) (x : List Bool), E.eval x = (E.wires x).getD E.output false :=
    fun _ _ => rfl
  have hWiresDef : ∀ (E : Circuit) (x : List Bool), E.wires x = E.gates.foldl step x :=
    fun _ _ => rfl
  have hOpAnd : ∀ l : List Bool, GateOp.eval .and l = l.all id := fun _ => rfl
  have hOpOr : ∀ l : List Bool, GateOp.eval .or l = l.any id := fun _ => rfl
  have hOpNot : ∀ l : List Bool, GateOp.eval .not l = !(l.headD false) := fun _ => rfl
  have fold_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have fold_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  let Legal : Circuit → Prop := fun D =>
    ∀ j : ℕ,
      (∀ i ∈ (D.gates.getD j ⟨.or, []⟩).inputs, i < 10 + j) ∧
      ((D.gates.getD j ⟨.or, []⟩).op = .not → (D.gates.getD j ⟨.or, []⟩).inputs.length ≤ 1)
  have hGood : ∃ s : ℕ, ∃ D : Circuit, FanInTwo D ∧ Legal D ∧ D.size = s ∧
      s ≤ 19 ∧ (s < 19 ∨ ∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x :=
    ⟨C0.size, C0, hFan0, hLeg0, rfl, hSz0, hBud0, fun x => (hComp0 x).trans (sameF x)⟩
  let sMin := Nat.find hGood
  have hsMinSpec := Nat.find_spec hGood
  have hsMinLe : ∀ s < sMin, ¬ ∃ D : Circuit, FanInTwo D ∧ Legal D ∧ D.size = s ∧
      s ≤ 19 ∧ (s < 19 ∨ ∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x :=
    fun s hs => Nat.find_min hGood hs
  obtain ⟨D, hFan, hLeg, hSzEq, hSz19, hBud, hComp⟩ := hsMinSpec
  have noSmaller : ∀ D' : Circuit, FanInTwo D' → Legal D' → D'.size < D.size →
      (∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = f x) → False := by
    intro D' hF' hL' hlt hC'
    exact hsMinLe D'.size (by omega) ⟨D', hF', hL', rfl, by omega, Or.inl (by omega), hC'⟩
  have legal_at : ∀ (E : Circuit) (j : ℕ) (hj : j < E.gates.length), Legal E →
      (∀ i ∈ E.gates[j].inputs, i < 10 + j) ∧
      (E.gates[j].op = .not → E.gates[j].inputs.length ≤ 1) := by
    intro E j hj hL
    have h := hL j
    rwa [List.getD_eq_getElem _ _ hj] at h
  have mkLegal : ∀ (E : Circuit),
      (∀ j (hj : j < E.gates.length),
        (∀ i ∈ E.gates[j].inputs, i < 10 + j) ∧
        (E.gates[j].op = .not → E.gates[j].inputs.length ≤ 1)) →
      Legal E := by
    intro E h j
    by_cases hj : j < E.gates.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact h j hj
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
      simp
  have f_allFalse : f (fun _ => false) = false := by decide
  have f_pair01 : f (fun i => decide (i = (0 : Fin 10) ∨ i = (1 : Fin 10))) = true := by decide
  have f_oneHot : ∀ i : Fin 10, f (fun k => decide (k = i)) = false := by decide
  have f_not_const : ∀ b : Bool, ∃ x : Fin 10 → Bool, f x ≠ b := by
    intro b
    cases b with
    | false => exact ⟨fun i => decide (i = (0 : Fin 10) ∨ i = (1 : Fin 10)), by rw [f_pair01]; simp⟩
    | true => exact ⟨fun _ => false, by rw [f_allFalse]; simp⟩
  have hOutLt : D.output < 10 + D.size := by
    by_contra hge
    have hge' : 10 + D.size ≤ D.output := Nat.le_of_not_lt hge
    have h1 := hComp (fun i => decide (i = (0 : Fin 10) ∨ i = (1 : Fin 10)))
    rw [f_pair01] at h1
    have hl : (D.wires (List.ofFn (fun i : Fin 10 => decide (i = (0 : Fin 10) ∨ i = (1 : Fin 10))))).length = 10 + D.size := by
      show (D.gates.foldl step _).length = _
      rw [fold_len, List.length_ofFn]; rfl
    rw [hEvalDef] at h1
    rw [List.getD_eq_default _ _ (by omega)] at h1
    exact Bool.false_ne_true h1
  have hSizePos : 1 ≤ D.size := by
    by_contra h0
    have hlen0 : D.gates.length = 0 := by unfold Circuit.size at h0; omega
    have hnil : D.gates = [] := List.length_eq_zero_iff.mp hlen0
    have hlt10 : D.output < 10 := by unfold Circuit.size at hOutLt; omega
    let i0 : Fin 10 := ⟨D.output, hlt10⟩
    have h1 := hComp (fun k => decide (k = i0))
    rw [f_oneHot i0] at h1
    rw [hEvalDef, hWiresDef, hnil, List.foldl_nil] at h1
    rw [List.getD_eq_getElem _ _ (by simp [hlt10]), List.getElem_ofFn] at h1
    have h2 : decide (i0 = i0) = true := by simp
    exact Bool.noConfusion (h2.symm.trans h1)
  have hOutLast : D.output + 1 = 10 + D.size := by
    by_contra hne
    have hlt : D.output < 10 + (D.size - 1) := by omega
    let gs := D.gates.take (D.size - 1)
    let D' : Circuit := ⟨gs, D.output⟩
    have hgsLen : gs.length = D.size - 1 := by
      simp only [gs, List.length_take]
      unfold Circuit.size
      omega
    have hD'sz : D'.size < D.size := by
      unfold Circuit.size at hSizePos ⊢
      change gs.length < D.gates.length
      rw [hgsLen]
      unfold Circuit.size
      omega
    have hD'Fan : FanInTwo D' := fun g hg => hFan g (List.mem_of_mem_take hg)
    have hD'Leg : Legal D' := by
      apply mkLegal
      intro j hj
      have hjD : j < D.gates.length := by
        change j < gs.length at hj
        rw [hgsLen] at hj
        unfold Circuit.size at hj
        omega
      have heq : gs[j] = D.gates[j] := List.getElem_take
      rw [heq]
      exact legal_at D j hjD hLeg
    have hD'Comp : ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = f x := by
      intro x
      rw [← hComp x]
      show (gs.foldl step (List.ofFn x)).getD D.output false =
        (D.gates.foldl step (List.ofFn x)).getD D.output false
      have hsp : D.gates = gs ++ D.gates.drop (D.size - 1) := (List.take_append_drop _ _).symm
      conv_rhs => rw [hsp, List.foldl_append]
      symm
      apply fold_lt
      rw [fold_len, List.length_ofFn, hgsLen]
      exact hlt
    exact noSmaller D' hD'Fan hD'Leg hD'sz hD'Comp
  let redir : ℕ → ℕ → ℕ → ℕ := fun m p i =>
    if i = 10 + m then p else if 10 + m < i then i - 1 else i
  have eraseRedir : ∀ (m : ℕ), m < D.gates.length → ∀ (p : ℕ), p < 10 + m →
      (∀ x : Fin 10 → Bool,
        (D.wires (List.ofFn x)).getD (10 + m) false = (D.wires (List.ofFn x)).getD p false) →
      False := by
    intro m hm p hp hEq
    let A := D.gates.take m
    let B := D.gates.drop (m + 1)
    let fR := redir m p
    let B' : List Gate := B.map fun g => ⟨g.op, g.inputs.map fR⟩
    let D' : Circuit := ⟨A ++ B', fR D.output⟩
    have hAlen : A.length = m := by simp only [A, List.length_take]; omega
    have hBlen : B.length = D.gates.length - (m + 1) := by simp only [B, List.length_drop]
    have hD'len : D'.gates.length = D.gates.length - 1 := by
      simp only [D', B', List.length_append, List.length_map, hAlen, hBlen]
      omega
    have hD'Fan : FanInTwo D' := by
      intro g hg
      rcases List.mem_append.mp hg with hA | hB
      · exact hFan g (List.mem_of_mem_take hA)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hB
        have h0 := hFan g0 (List.mem_of_mem_drop hg0)
        exact ⟨h0.1, by simp [h0.2]⟩
    have hD'Leg : Legal D' := by
      apply mkLegal
      intro j hj
      by_cases hjm : j < m
      · have h1 : D'.gates[j] = D.gates[j] := by
          simp only [D', List.getElem_append_left (by omega : j < A.length), A, List.getElem_take]
        rw [h1]
        exact legal_at D j (by omega) hLeg
      · have h2 : D'.gates[j] = ⟨(D.gates[j + 1]'(by omega)).op,
            (D.gates[j + 1]'(by omega)).inputs.map fR⟩ := by
          have hidx : m + 1 + (j - m) = j + 1 := by omega
          simp only [D', List.getElem_append_right (by omega : A.length ≤ j), B', List.getElem_map,
            B, List.getElem_drop, hAlen, hidx]
        rw [h2]
        have h0 := legal_at D (j + 1) (by omega) hLeg
        refine ⟨?_, ?_⟩
        · intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          have hi0lt := h0.1 i0 hi0
          dsimp only [fR, redir]
          split_ifs <;> omega
        · intro hnot
          simpa using h0.2 hnot
    have hD'Comp : ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = f x := by
      intro x
      rw [← hComp x]
      have hsp : D.gates = A ++ D.gates[m] :: B := by
        have h1 := List.take_append_drop m D.gates
        rw [List.drop_eq_getElem_cons hm] at h1
        exact h1.symm
      let w0 := A.foldl step (List.ofFn x)
      have hw0len : w0.length = 10 + m := by
        rw [fold_len, List.length_ofFn, hAlen]
      have hstepInv : ∀ (gs : List Gate) (w w' : List Bool),
          10 + m < w.length → w.length = w'.length + 1 →
          (∀ i : ℕ, w'.getD (fR i) false = w.getD i false) →
          ∀ i : ℕ,
            ((gs.map fun g => ⟨g.op, g.inputs.map fR⟩).foldl step w').getD (fR i) false =
            (gs.foldl step w).getD i false := by
        intro gs
        induction gs with
        | nil => intro w w' _ _ inv i; exact inv i
        | cons g gs ih =>
          intro w w' hwm hwl inv i
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have hgeval : (⟨g.op, g.inputs.map fR⟩ : Gate).op.eval
              ((⟨g.op, g.inputs.map fR⟩ : Gate).inputs.map fun k => w'.getD k false) =
              g.op.eval (g.inputs.map fun k => w.getD k false) := by
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro k _
            exact inv k
          apply ih (step w g) (step w' ⟨g.op, g.inputs.map fR⟩)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
          intro k
          simp only [step, hgeval]
          dsimp only [fR, redir]
          by_cases hk1 : k = 10 + m
          · subst hk1
            simp only [if_true]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            simpa only [fR, redir, if_true] using inv (10 + m)
          · by_cases hk2 : 10 + m < k
            · simp only [hk1, hk2, if_false, if_true]
              rcases lt_trichotomy k w.length with hlt | heq | hgt
              · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
                simpa only [fR, redir, hk1, hk2, if_false, if_true] using inv k
              · subst heq
                have hsub : w.length - 1 = w'.length := by omega
                rw [hsub, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
                simp
              · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
            · simp only [hk1, hk2, if_false]
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              simpa only [fR, redir, hk1, hk2, if_false] using inv k
      have hBase : ∀ i : ℕ, w0.getD (fR i) false = (step w0 D.gates[m]).getD i false := by
        intro i
        have hEqx := hEq x
        have h1 : (D.wires (List.ofFn x)).getD (10 + m) false =
            (step w0 D.gates[m]).getD (10 + m) false := by
          rw [hWiresDef]
          conv_lhs => rw [hsp, List.foldl_append, List.foldl_cons]
          exact fold_lt B (step w0 D.gates[m]) (10 + m)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)
        have h2 : (D.wires (List.ofFn x)).getD p false = w0.getD p false := by
          rw [hWiresDef]
          rw [hsp, List.foldl_append, List.foldl_cons]
          rw [fold_lt B (step w0 D.gates[m]) p
            (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
          exact List.getD_append _ _ _ _ (by omega)
        rw [h1, h2] at hEqx
        dsimp only [fR, redir]
        by_cases hi1 : i = 10 + m
        · subst hi1; simp only [if_true]; exact hEqx.symm
        · by_cases hi2 : 10 + m < i
          · simp only [hi1, hi2, if_false, if_true]
            rw [List.getD_eq_default _ _ (by omega),
              List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
          · simp only [hi1, hi2, if_false]
            exact (List.getD_append _ _ _ _ (by omega)).symm
      show (D'.gates.foldl step (List.ofFn x)).getD (fR D.output) false =
        (D.gates.foldl step (List.ofFn x)).getD D.output false
      conv_rhs => rw [hsp, List.foldl_append, List.foldl_cons]
      simp only [D', List.foldl_append]
      exact hstepInv B (step w0 D.gates[m]) w0
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)
        (by simp only [step, List.length_append, List.length_cons, List.length_nil])
        hBase D.output
    exact noSmaller D' hD'Fan hD'Leg (by change D'.gates.length < D.gates.length; omega) hD'Comp
  have eraseDead : ∀ (m : ℕ), m < D.gates.length → D.output ≠ 10 + m →
      (∀ g ∈ D.gates, 10 + m ∉ g.inputs) → False := by
    intro m hm hOutNe hNoRead
    let A := D.gates.take m
    let B := D.gates.drop (m + 1)
    let sh : ℕ → ℕ := fun i => if 10 + m < i then i - 1 else i
    let B' : List Gate := B.map fun g => ⟨g.op, g.inputs.map sh⟩
    let D' : Circuit := ⟨A ++ B', sh D.output⟩
    have hAlen : A.length = m := by simp only [A, List.length_take]; omega
    have hBlen : B.length = D.gates.length - (m + 1) := by simp only [B, List.length_drop]
    have hD'len : D'.gates.length = D.gates.length - 1 := by
      simp only [D', B', List.length_append, List.length_map, hAlen, hBlen]
      omega
    have hD'Fan : FanInTwo D' := by
      intro g hg
      rcases List.mem_append.mp hg with hA | hB
      · exact hFan g (List.mem_of_mem_take hA)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hB
        have h0 := hFan g0 (List.mem_of_mem_drop hg0)
        exact ⟨h0.1, by simp [h0.2]⟩
    have hD'Leg : Legal D' := by
      apply mkLegal
      intro j hj
      by_cases hjm : j < m
      · have h1 : D'.gates[j] = D.gates[j] := by
          simp only [D', List.getElem_append_left (by omega : j < A.length), A, List.getElem_take]
        rw [h1]
        exact legal_at D j (by omega) hLeg
      · have h2 : D'.gates[j] = ⟨(D.gates[j + 1]'(by omega)).op,
            (D.gates[j + 1]'(by omega)).inputs.map sh⟩ := by
          have hidx : m + 1 + (j - m) = j + 1 := by omega
          simp only [D', List.getElem_append_right (by omega : A.length ≤ j), B', List.getElem_map,
            B, List.getElem_drop, hAlen, hidx]
        rw [h2]
        have h0 := legal_at D (j + 1) (by omega) hLeg
        have hnr := hNoRead (D.gates[j + 1]'(by omega)) (List.getElem_mem (by omega))
        refine ⟨?_, ?_⟩
        · intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          have hi0lt := h0.1 i0 hi0
          have hi0ne : i0 ≠ 10 + m := fun heq => hnr (heq ▸ hi0)
          dsimp only [sh]
          split_ifs <;> omega
        · intro hnot
          simpa using h0.2 hnot
    have hD'Comp : ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = f x := by
      intro x
      rw [← hComp x]
      have hsp : D.gates = A ++ D.gates[m] :: B := by
        have h1 := List.take_append_drop m D.gates
        rw [List.drop_eq_getElem_cons hm] at h1
        exact h1.symm
      let w0 := A.foldl step (List.ofFn x)
      have hw0len : w0.length = 10 + m := by
        rw [fold_len, List.length_ofFn, hAlen]
      have hstepInv : ∀ (gs : List Gate), (∀ g ∈ gs, 10 + m ∉ g.inputs) →
          ∀ (w w' : List Bool), 10 + m < w.length → w.length = w'.length + 1 →
          (∀ i : ℕ, i ≠ 10 + m → w'.getD (sh i) false = w.getD i false) →
          ∀ i : ℕ, i ≠ 10 + m →
            ((gs.map fun g => ⟨g.op, g.inputs.map sh⟩).foldl step w').getD (sh i) false =
            (gs.foldl step w).getD i false := by
        intro gs
        induction gs with
        | nil => intro _ w w' _ _ inv i hi; exact inv i hi
        | cons g gs ih =>
          intro hnr w w' hwm hwl inv i hi
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have hgne : 10 + m ∉ g.inputs := hnr g List.mem_cons_self
          have hgeval : (⟨g.op, g.inputs.map sh⟩ : Gate).op.eval
              ((⟨g.op, g.inputs.map sh⟩ : Gate).inputs.map fun k => w'.getD k false) =
              g.op.eval (g.inputs.map fun k => w.getD k false) := by
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro k hk
            exact inv k (fun heq => hgne (heq ▸ hk))
          apply ih (fun g1 hg1 => hnr g1 (List.mem_cons_of_mem _ hg1))
            (step w g) (step w' ⟨g.op, g.inputs.map sh⟩)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            _ i hi
          intro k hk
          simp only [step, hgeval]
          dsimp only [sh]
          by_cases hk2 : 10 + m < k
          · simp only [hk2, if_true]
            rcases lt_trichotomy k w.length with hlt | heq | hgt
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
              simpa only [sh, hk2, if_true] using inv k hk
            · subst heq
              have hsub : w.length - 1 = w'.length := by omega
              rw [hsub, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
              simp
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · simp only [hk2, if_false]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            simpa only [sh, hk2, if_false] using inv k hk
      have hBase : ∀ i : ℕ, i ≠ 10 + m →
          w0.getD (sh i) false = (step w0 D.gates[m]).getD i false := by
        intro i hi
        dsimp only [sh]
        by_cases hi2 : 10 + m < i
        · simp only [hi2, if_true]
          rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
        · simp only [hi2, if_false]
          exact (List.getD_append _ _ _ _ (by omega)).symm
      show (D'.gates.foldl step (List.ofFn x)).getD (sh D.output) false =
        (D.gates.foldl step (List.ofFn x)).getD D.output false
      conv_rhs => rw [hsp, List.foldl_append, List.foldl_cons]
      simp only [D', List.foldl_append]
      exact hstepInv B (fun g hg => hNoRead g (List.mem_of_mem_drop hg)) (step w0 D.gates[m]) w0
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)
        (by simp only [step, List.length_append, List.length_cons, List.length_nil])
        hBase D.output hOutNe
    exact noSmaller D' hD'Fan hD'Leg (by change D'.gates.length < D.gates.length; omega) hD'Comp
  have eraseConst : ∀ (m : ℕ), m < D.gates.length → ∀ (c : Bool),
      (∀ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD (10 + m) false = c) → False := by
    intro m hm c hConst
    have hOutNe : D.output ≠ 10 + m := by
      intro heq
      obtain ⟨x, hx⟩ := f_not_const c
      have h1 := hComp x
      rw [hEvalDef, heq] at h1
      rw [hConst x] at h1
      exact hx h1.symm
    let A := D.gates.take m
    let B := D.gates.drop (m + 1)
    let sh : ℕ → ℕ := fun i => if 10 + m < i then i - 1 else i
    let sg : Gate → Gate := fun g =>
      if g.op = .not then
        if g.inputs = [10 + m] then (if c then ⟨.or, []⟩ else ⟨.and, []⟩)
        else ⟨.not, g.inputs.map sh⟩
      else if g.op = .and then
        if 10 + m ∈ g.inputs then
          if c then ⟨.and, (g.inputs.filter fun i => decide (i ≠ 10 + m)).map sh⟩
          else ⟨.or, []⟩
        else ⟨.and, g.inputs.map sh⟩
      else if g.op = .or then
        if 10 + m ∈ g.inputs then
          if c then ⟨.and, []⟩
          else ⟨.or, (g.inputs.filter fun i => decide (i ≠ 10 + m)).map sh⟩
        else ⟨.or, g.inputs.map sh⟩
      else g
    let B' := B.map sg
    let D' : Circuit := ⟨A ++ B', sh D.output⟩
    have hAlen : A.length = m := by simp only [A, List.length_take]; omega
    have hBlen : B.length = D.gates.length - (m + 1) := by simp only [B, List.length_drop]
    have hD'len : D'.gates.length = D.gates.length - 1 := by
      simp only [D', B', List.length_append, List.length_map, hAlen, hBlen]
      omega
    have hsgFan : ∀ g, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
        g.inputs.length ≤ 2 →
        (sg g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (sg g).inputs.length ≤ 2 := by
      intro g hop hl
      rcases g with ⟨op, ins⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · dsimp only [sg]
        simp only [reduceCtorEq, if_false, if_true]
        split_ifs
        · exact ⟨by simp, by simp [le_trans (List.length_filter_le _ _) hl]⟩
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp, by simp [hl]⟩
      · dsimp only [sg]
        simp only [reduceCtorEq, if_false, if_true]
        split_ifs
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp, by simp [le_trans (List.length_filter_le _ _) hl]⟩
        · exact ⟨by simp, by simp [hl]⟩
      · dsimp only [sg]
        simp only [if_true]
        split_ifs
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp, by simp [hl]⟩
    have hD'Fan : FanInTwo D' := by
      intro g hg
      rcases List.mem_append.mp hg with hA | hB
      · exact hFan g (List.mem_of_mem_take hA)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hB
        have h0 := hFan g0 (List.mem_of_mem_drop hg0)
        exact hsgFan g0 h0.1 h0.2
    have hD'Leg : Legal D' := by
      apply mkLegal
      intro j hj
      by_cases hjm : j < m
      · have h1 : D'.gates[j] = D.gates[j] := by
          simp only [D', List.getElem_append_left (by omega : j < A.length), A, List.getElem_take]
        rw [h1]
        exact legal_at D j (by omega) hLeg
      · have h2 : D'.gates[j] = sg (D.gates[j + 1]'(by omega)) := by
          simp only [D', List.getElem_append_right (by omega : A.length ≤ j), B', List.getElem_map,
            B, List.getElem_drop, hAlen]
          congr 2; omega
        rw [h2]
        have h0 := legal_at D (j + 1) (by omega) hLeg
        have hF0 := hFan (D.gates[j + 1]'(by omega)) (List.getElem_mem (by omega))
        rcases hF0.1 with hop | hop | hop
        · dsimp only [sg]; rw [hop]; simp only [reduceCtorEq, if_false, if_true]
          by_cases hmem : 10 + m ∈ (D.gates[j + 1]'(by omega)).inputs
          · simp only [hmem, if_true]
            cases c with
            | true =>
              simp only [if_true]
              refine ⟨?_, by simp⟩
              intro i hi
              obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
              simp only [List.mem_filter, decide_eq_true_eq] at hi0
              have := h0.1 i0 hi0.1
              dsimp only [sh]; split_ifs <;> omega
            | false => simp
          · simp only [hmem, if_false]
            refine ⟨?_, by simp⟩
            intro i hi
            obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
            have := h0.1 i0 hi0
            have hne : i0 ≠ 10 + m := fun heq => hmem (heq ▸ hi0)
            dsimp only [sh]; split_ifs <;> omega
        · dsimp only [sg]; rw [hop]; simp only [reduceCtorEq, if_false, if_true]
          by_cases hmem : 10 + m ∈ (D.gates[j + 1]'(by omega)).inputs
          · simp only [hmem, if_true]
            cases c with
            | true => simp
            | false =>
              simp only [Bool.false_eq_true, if_false]
              refine ⟨?_, by simp⟩
              intro i hi
              obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
              simp only [List.mem_filter, decide_eq_true_eq] at hi0
              have := h0.1 i0 hi0.1
              dsimp only [sh]; split_ifs <;> omega
          · simp only [hmem, if_false]
            refine ⟨?_, by simp⟩
            intro i hi
            obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
            have := h0.1 i0 hi0
            have hne : i0 ≠ 10 + m := fun heq => hmem (heq ▸ hi0)
            dsimp only [sh]; split_ifs <;> omega
        · dsimp only [sg]; rw [hop]; simp only [if_true]
          by_cases hmem : (D.gates[j + 1]'(by omega)).inputs = [10 + m]
          · simp only [hmem, if_true]
            cases c <;> simp
          · simp only [hmem, if_false]
            refine ⟨?_, ?_⟩
            · intro i hi
              obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
              have := h0.1 i0 hi0
              have hlen1 := h0.2 hop
              have hne : i0 ≠ 10 + m := by
                intro heq
                cases hins : (D.gates[j + 1]'(by omega)).inputs with
                | nil => rw [hins] at hi0; simp at hi0
                | cons a tl =>
                  cases tl with
                  | nil =>
                    rw [hins] at hi0
                    simp at hi0
                    exact hmem (by rw [hins, ← hi0, heq])
                  | cons _ _ => rw [hins] at hlen1; simp at hlen1
              dsimp only [sh]; split_ifs <;> omega
            · intro _; simp [h0.2 hop]
    have hsgEval : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
        (g.op = .not → g.inputs.length ≤ 1) →
        ∀ (w w' : List Bool), w.getD (10 + m) false = c →
        (∀ i : ℕ, i ≠ 10 + m → w'.getD (sh i) false = w.getD i false) →
        (sg g).op.eval ((sg g).inputs.map fun k => w'.getD k false) =
          g.op.eval (g.inputs.map fun k => w.getD k false) := by
      intro g hop hnot1 w w' hwc inv
      rcases g with ⟨op, ins⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · dsimp only [sg]
        simp only [reduceCtorEq, if_false, if_true]
        by_cases hmem : 10 + m ∈ ins
        · simp only [hmem, if_true]
          cases c with
          | false =>
            simp only [Bool.false_eq_true, if_false, hOpOr, hOpAnd, List.map_nil, List.any_nil]
            symm
            rw [Bool.eq_false_iff]
            intro h
            rw [List.all_eq_true] at h
            have h1 := h (w.getD (10 + m) false) (List.mem_map.mpr ⟨10 + m, hmem, rfl⟩)
            rw [hwc] at h1; exact Bool.false_ne_true h1
          | true =>
            simp only [if_true, hOpAnd, List.map_map]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
            constructor
            · rintro h _ ⟨i, hi, rfl⟩
              by_cases hie : i = 10 + m
              · subst hie; exact hwc
              · rw [← inv i hie]
                exact h _ ⟨i, ⟨hi, hie⟩, rfl⟩
            · rintro h _ ⟨i, ⟨hi, hie⟩, rfl⟩
              simpa only [Function.comp_apply, inv i hie] using h _ ⟨i, hi, rfl⟩
        · simp only [hmem, if_false, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact inv i (fun heq => hmem (heq ▸ hi))
      · dsimp only [sg]
        simp only [reduceCtorEq, if_false, if_true]
        by_cases hmem : 10 + m ∈ ins
        · simp only [hmem, if_true]
          cases c with
          | true =>
            simp only [if_true, hOpAnd, hOpOr, List.map_nil, List.all_nil]
            symm
            rw [List.any_eq_true]
            exact ⟨w.getD (10 + m) false, List.mem_map.mpr ⟨10 + m, hmem, rfl⟩, by simpa using hwc⟩
          | false =>
            simp only [Bool.false_eq_true, if_false, hOpOr, List.map_map]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
            constructor
            · rintro ⟨_, ⟨i, ⟨hi, hie⟩, rfl⟩, hb⟩
              simp only [Function.comp_apply, inv i hie] at hb
              exact ⟨_, ⟨i, hi, rfl⟩, hb⟩
            · rintro ⟨_, ⟨i, hi, rfl⟩, hb⟩
              by_cases hie : i = 10 + m
              · subst hie; rw [hwc] at hb; exact (Bool.false_ne_true hb).elim
              · exact ⟨_, ⟨i, ⟨hi, hie⟩, rfl⟩, by simpa only [Function.comp_apply, inv i hie] using hb⟩
        · simp only [hmem, if_false, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact inv i (fun heq => hmem (heq ▸ hi))
      · dsimp only [sg]
        simp only [if_true]
        have hlen1 := hnot1 rfl
        cases ins with
        | nil => simp [hOpNot]
        | cons a tl =>
          cases tl with
          | nil =>
            by_cases ha : a = 10 + m
            · subst ha
              cases c with
              | false =>
                simp only [ite_true, Bool.false_eq_true, ite_false, hOpAnd, hOpNot,
                  List.map_nil, List.map_cons, List.all_nil, List.headD_cons, hwc, Bool.not_false]
              | true =>
                simp only [ite_true, hOpOr, hOpNot,
                  List.map_nil, List.map_cons, List.any_nil, List.headD_cons, hwc, Bool.not_true]
            · have hne : ([a] : List ℕ) ≠ [10 + m] := by simp [ha]
              simp only [hne, ite_false, hOpNot, List.map_cons, List.map_nil, List.headD_cons, inv a ha]
          | cons _ _ => simp at hlen1
    have hD'Comp : ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = f x := by
      intro x
      rw [← hComp x]
      have hsp : D.gates = A ++ D.gates[m] :: B := by
        have h1 := List.take_append_drop m D.gates
        rw [List.drop_eq_getElem_cons hm] at h1
        exact h1.symm
      let w0 := A.foldl step (List.ofFn x)
      have hw0len : w0.length = 10 + m := by
        rw [fold_len, List.length_ofFn, hAlen]
      have hw1c : (step w0 D.gates[m]).getD (10 + m) false = c := by
        have h1 := hConst x
        rw [hWiresDef] at h1
        rw [hsp, List.foldl_append, List.foldl_cons] at h1
        rwa [fold_lt B (step w0 D.gates[m]) (10 + m)
          (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)] at h1
      have hstepInv : ∀ (gs : List Gate),
          (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            (g.op = .not → g.inputs.length ≤ 1)) →
          ∀ (w w' : List Bool), 10 + m < w.length → w.length = w'.length + 1 →
          w.getD (10 + m) false = c →
          (∀ i : ℕ, i ≠ 10 + m → w'.getD (sh i) false = w.getD i false) →
          ∀ i : ℕ, i ≠ 10 + m →
            ((gs.map sg).foldl step w').getD (sh i) false =
            (gs.foldl step w).getD i false := by
        intro gs
        induction gs with
        | nil => intro _ w w' _ _ _ inv i hi; exact inv i hi
        | cons g gs ih =>
          intro hgs w w' hwm hwl hwc inv i hi
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have hg0 := hgs g List.mem_cons_self
          have hgeval := hsgEval g hg0.1 hg0.2 w w' hwc inv
          apply ih (fun g1 hg1 => hgs g1 (List.mem_cons_of_mem _ hg1))
            (step w g) (step w' (sg g))
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [step]; rw [List.getD_append _ _ _ _ hwm]; exact hwc)
            _ i hi
          intro k hk
          simp only [step, hgeval]
          dsimp only [sh]
          by_cases hk2 : 10 + m < k
          · simp only [hk2, if_true]
            rcases lt_trichotomy k w.length with hlt | heq | hgt
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
              simpa only [sh, hk2, if_true] using inv k hk
            · subst heq
              have hsub : w.length - 1 = w'.length := by omega
              rw [hsub, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
              simp
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · simp only [hk2, if_false]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            simpa only [sh, hk2, if_false] using inv k hk
      have hBase : ∀ i : ℕ, i ≠ 10 + m →
          w0.getD (sh i) false = (step w0 D.gates[m]).getD i false := by
        intro i hi
        dsimp only [sh]
        by_cases hi2 : 10 + m < i
        · simp only [hi2, if_true]
          rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
        · simp only [hi2, if_false]
          exact (List.getD_append _ _ _ _ (by omega)).symm
      have hBprop : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          (g.op = .not → g.inputs.length ≤ 1) := by
        intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        have hkD : m + 1 + k < D.gates.length := by rw [hBlen] at hk; omega
        have heq : B[k] = D.gates[m + 1 + k] := List.getElem_drop
        rw [heq]
        exact ⟨(hFan _ (List.getElem_mem hkD)).1, (legal_at D (m + 1 + k) hkD hLeg).2⟩
      show (D'.gates.foldl step (List.ofFn x)).getD (sh D.output) false =
        (D.gates.foldl step (List.ofFn x)).getD D.output false
      conv_rhs => rw [hsp, List.foldl_append, List.foldl_cons]
      simp only [D', List.foldl_append]
      exact hstepInv B hBprop (step w0 D.gates[m]) w0
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)
        (by simp only [step, List.length_append, List.length_cons, List.length_nil])
        hw1c hBase D.output hOutNe
    exact noSmaller D' hD'Fan hD'Leg (by change D'.gates.length < D.gates.length; omega) hD'Comp
  have wire_at_gate : ∀ (E : Circuit) (m : ℕ) (hm : m < E.gates.length) (x : Fin 10 → Bool),
      (E.wires (List.ofFn x)).getD (10 + m) false =
        E.gates[m].op.eval (E.gates[m].inputs.map fun i =>
          if i < 10 + m then (E.wires (List.ofFn x)).getD i false else false) := by
    intro E m hm x
    let A := E.gates.take m
    let B := E.gates.drop (m + 1)
    have hsp : E.gates = A ++ E.gates[m] :: B := by
      have h1 := List.take_append_drop m E.gates
      rw [List.drop_eq_getElem_cons hm] at h1
      exact h1.symm
    let w0 := A.foldl step (List.ofFn x)
    have hw0len : w0.length = 10 + m := by
      rw [fold_len, List.length_ofFn, List.length_take]; omega
    have hpref : ∀ i < 10 + m, (E.wires (List.ofFn x)).getD i false = w0.getD i false := by
      intro i hi
      rw [hWiresDef]
      rw [hsp, List.foldl_append, List.foldl_cons]
      rw [fold_lt B (step w0 E.gates[m]) i
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hgate : (E.wires (List.ofFn x)).getD (10 + m) false =
        E.gates[m].op.eval (E.gates[m].inputs.map fun i => w0.getD i false) := by
      rw [hWiresDef]
      conv_lhs => rw [hsp, List.foldl_append, List.foldl_cons]
      rw [fold_lt B (step w0 E.gates[m]) (10 + m)
        (by simp only [step, List.length_append, List.length_cons, List.length_nil, hw0len]; omega)]
      simp only [step]
      rw [List.getD_append_right _ _ _ _ (by omega), hw0len]
      simp
    rw [hgate]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 10 + m
    · rw [if_pos hi, hpref i hi]
    · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
  have hStrict : Strict 10 D := by
    intro m hm
    have hL := legal_at D m hm hLeg
    have hF := hFan D.gates[m] (List.getElem_mem hm)
    rcases hF.1 with hop | hop | hop
    · left
      cases hins : D.gates[m].inputs with
      | nil =>
        exfalso
        apply eraseConst m hm true
        intro x
        rw [wire_at_gate D m hm x, hop, hins]
        rfl
      | cons a tl =>
        cases tl with
        | nil =>
          exfalso
          have ha : a < 10 + m := hL.1 a (by rw [hins]; simp)
          apply eraseRedir m hm a ha
          intro x
          rw [wire_at_gate D m hm x, hop, hins]
          simp [hOpAnd, ha]
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            refine ⟨Or.inl hop, by simp [hins], ?_, hins ▸ hL.1⟩
            by_cases hab : a = b
            · exfalso
              subst hab
              have ha : a < 10 + m := hL.1 a (by rw [hins]; simp)
              apply eraseRedir m hm a ha
              intro x
              rw [wire_at_gate D m hm x, hop, hins]
              simp [hOpAnd, ha]
            · simp [hins, hab]
          | cons _ _ =>
            have hle := hF.2
            rw [hins] at hle
            simp at hle
    · left
      cases hins : D.gates[m].inputs with
      | nil =>
        exfalso
        apply eraseConst m hm false
        intro x
        rw [wire_at_gate D m hm x, hop, hins]
        rfl
      | cons a tl =>
        cases tl with
        | nil =>
          exfalso
          have ha : a < 10 + m := hL.1 a (by rw [hins]; simp)
          apply eraseRedir m hm a ha
          intro x
          rw [wire_at_gate D m hm x, hop, hins]
          simp [hOpOr, ha]
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            refine ⟨Or.inr hop, by simp [hins], ?_, hins ▸ hL.1⟩
            by_cases hab : a = b
            · exfalso
              subst hab
              have ha : a < 10 + m := hL.1 a (by rw [hins]; simp)
              apply eraseRedir m hm a ha
              intro x
              rw [wire_at_gate D m hm x, hop, hins]
              simp [hOpOr, ha]
            · simp [hins, hab]
          | cons _ _ =>
            have hle := hF.2
            rw [hins] at hle
            simp at hle
    · right
      refine ⟨hop, ?_, hL.1⟩
      have hlen1 := hL.2 hop
      cases hins : D.gates[m].inputs with
      | nil =>
        exfalso
        apply eraseConst m hm true
        intro x
        rw [wire_at_gate D m hm x, hop, hins]
        rfl
      | cons a tl =>
        cases tl with
        | nil => rfl
        | cons _ _ => rw [hins] at hlen1; simp at hlen1
  have hNoDead : ∀ j < D.size - 1, ∃ g ∈ D.gates, 10 + j ∈ g.inputs := by
    intro j hj
    by_contra hnone
    push_neg at hnone
    exact eraseDead j (by unfold Circuit.size at hj; omega) (by unfold Circuit.size at hj hOutLast; omega) hnone
  have hNoDblNot : ∀ k (hk : k < D.gates.length), D.gates[k].op = .not →
      ∀ g ∈ D.gates, g.op = .not → 10 + k ∉ g.inputs := by
    intro k hk hknot g hg hgnot hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hg
    have hsm := hStrict m hm
    rcases hsm with ⟨hbo, _, _, _⟩ | ⟨_, hmlen, hmlt⟩
    · rcases hbo with h1 | h1 <;> rw [hgnot] at h1 <;> cases h1
    · have hkm : 10 + k < 10 + m := hmlt (10 + k) hmem
      have hsk := hStrict k hk
      rcases hsk with ⟨hbo, _, _, _⟩ | ⟨_, hklen, hklt⟩
      · rcases hbo with h1 | h1 <;> rw [hknot] at h1 <;> cases h1
      · obtain ⟨a, hkins⟩ := List.length_eq_one_iff.mp hklen
        have ha : a < 10 + k := hklt a (by rw [hkins]; simp)
        obtain ⟨b, hmins⟩ := List.length_eq_one_iff.mp hmlen
        rw [hmins] at hmem
        simp only [List.mem_singleton] at hmem
        subst hmem
        apply eraseRedir m hm a (by omega)
        intro x
        rw [wire_at_gate D m hm x, hgnot, hmins]
        simp only [List.map_cons, List.map_nil, if_pos hkm, hOpNot, List.headD_cons]
        rw [wire_at_gate D k hk x, hknot, hkins]
        simp [hOpNot, ha]
  have wire_input : ∀ (E : Circuit) (x : Fin 10 → Bool) (i : Fin 10),
      (E.wires (List.ofFn x)).getD i.val false = x i := by
    intro E x i
    rw [hWiresDef]
    rw [fold_lt E.gates (List.ofFn x) i.val (by simp [i.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
  have f_ess : ∀ i : Fin 10, ∃ x : Fin 10 → Bool,
      f x ≠ f (Function.update x i (!x i)) := by
    have h : ∀ i : Fin 10, ∃ j : Fin 10,
        f (fun k => decide (k = j)) ≠
        f (Function.update (fun k => decide (k = j)) i (!(decide (i = j)))) := by decide
    intro i
    obtain ⟨j, hj⟩ := h i
    exact ⟨fun k => decide (k = j), hj⟩
  have hInputRead : ∀ i : Fin 10, ∃ g ∈ D.gates, i.val ∈ g.inputs := by
    intro i
    by_contra hno
    push_neg at hno
    obtain ⟨x, hx⟩ := f_ess i
    let y := Function.update x i (!x i)
    have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, i.val ∉ g.inputs) →
        ∀ (w1 w2 : List Bool), w1.length = w2.length →
        (∀ k, k ≠ i.val → w1.getD k false = w2.getD k false) →
        ∀ k, k ≠ i.val → (gs.foldl step w1).getD k false = (gs.foldl step w2).getD k false := by
      intro gs
      induction gs with
      | nil => intro _ w1 w2 _ inv k hk; exact inv k hk
      | cons g gs ih =>
        intro hgs w1 w2 hlen inv k hk
        rw [List.foldl_cons, List.foldl_cons]
        have hgne : i.val ∉ g.inputs := hgs g List.mem_cons_self
        have hev : g.op.eval (g.inputs.map fun r => w1.getD r false) =
            g.op.eval (g.inputs.map fun r => w2.getD r false) := by
          congr 1
          apply List.map_congr_left
          intro r hr
          exact inv r (fun heq => hgne (heq ▸ hr))
        apply ih (fun g1 hg1 => hgs g1 (List.mem_cons_of_mem _ hg1))
          (step w1 g) (step w2 g) (by simp [step, hlen]) _ k hk
        intro r hr
        simp only [step, hev]
        rcases lt_trichotomy r w1.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
          exact inv r hr
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, hlen, List.getD_append_right _ _ _ _ le_rfl]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hBase : ∀ k, k ≠ i.val →
        (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
      intro k hk
      by_cases h10 : k < 10
      · rw [List.getD_eq_getElem _ _ (by simp [h10]), List.getD_eq_getElem _ _ (by simp [h10]),
          List.getElem_ofFn, List.getElem_ofFn]
        have hne : (⟨k, h10⟩ : Fin 10) ≠ i := fun h => hk (congrArg Fin.val h)
        simp [y, Function.update, hne]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hOutNeI : D.output ≠ i.val := by have := i.isLt; omega
    have hEqEval : D.eval (List.ofFn x) = D.eval (List.ofFn y) :=
      hfold D.gates hno (List.ofFn x) (List.ofFn y) (by simp) hBase D.output hOutNeI
    rw [hComp x, hComp y] at hEqEval
    exact hx hEqEval
  have hBinBound : 10 + notCount D ≤ D.size := by
    let fanout : ℕ → ℕ := fun w => (D.gates.map fun g => g.inputs.count w).sum
    have hSumGate : ∀ (gs : List Gate),
        (∀ g ∈ gs, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          (g.op = .not ∧ g.inputs.length = 1)) →
        (gs.map fun g => g.inputs.length).sum +
          (gs.filter fun g => decide (g.op = GateOp.not)).length = 2 * gs.length := by
      intro gs
      induction gs with
      | nil => intro _; simp
      | cons g gs ih =>
        intro hgs
        have h0 := hgs g List.mem_cons_self
        have h1 := ih (fun g1 hg1 => hgs g1 (List.mem_cons_of_mem _ hg1))
        simp only [List.map_cons, List.sum_cons, List.filter_cons, List.length_cons]
        rcases h0 with ⟨hbo, hl2⟩ | ⟨hnot, hl1⟩
        · have hne : g.op ≠ GateOp.not := by rcases hbo with h | h <;> rw [h] <;> decide
          simp [hne, hl2]; omega
        · simp [hnot, hl1]; omega
    have hSumD : (D.gates.map fun g => g.inputs.length).sum + notCount D = 2 * D.size := by
      apply hSumGate
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      rcases hStrict j hj with ⟨h1, h2, _, _⟩ | ⟨h1, h2, _⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have hCountSum : ∀ (l : List ℕ) (M : ℕ), (∀ x ∈ l, x < M) →
        ∑ w ∈ Finset.range M, l.count w = l.length := by
      intro l M
      induction l with
      | nil => intro _; simp
      | cons a l ih =>
        intro hall
        have ha : a < M := hall a List.mem_cons_self
        have hl := ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        simp only [List.count_cons, List.length_cons]
        rw [Finset.sum_add_distrib, hl]
        have h1 : ∑ w ∈ Finset.range M, (if a == w then 1 else 0) = 1 := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hba
            have : (a == b) = false := beq_false_of_ne (Ne.symm hba)
            simp [this]
          · intro hna
            exact (hna (Finset.mem_range.mpr ha)).elim
        omega
    let M := 10 + D.size - 1
    have hSumFan : ∑ w ∈ Finset.range M, fanout w =
        (D.gates.map fun g => g.inputs.length).sum := by
      have hAux : ∀ (gs : List Gate), (∀ g ∈ gs, ∀ x ∈ g.inputs, x < M) →
          ∑ w ∈ Finset.range M, (gs.map fun g => g.inputs.count w).sum =
          (gs.map fun g => g.inputs.length).sum := by
        intro gs
        induction gs with
        | nil => intro _; simp
        | cons g gs ih =>
          intro hgs
          simp only [List.map_cons, List.sum_cons]
          rw [Finset.sum_add_distrib,
            hCountSum g.inputs M (hgs g List.mem_cons_self),
            ih (fun g1 hg1 => hgs g1 (List.mem_cons_of_mem _ hg1))]
      apply hAux
      intro g hg x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hlt : x < 10 + j := by
        rcases hStrict j hj with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ <;> exact h x hx
      dsimp only [M]; unfold Circuit.size; omega
    have hFanPos : ∀ w ∈ Finset.range M, 1 ≤ fanout w := by
      intro w hw
      have hwlt : w < M := Finset.mem_range.mp hw
      have hex : ∃ g ∈ D.gates, w ∈ g.inputs := by
        by_cases h10 : w < 10
        · exact hInputRead ⟨w, h10⟩
        · have hj : w - 10 < D.size - 1 := by omega
          have h := hNoDead (w - 10) hj
          simpa [show 10 + (w - 10) = w by omega] using h
      obtain ⟨g, hg, hwg⟩ := hex
      have hAux : ∀ (gs : List Gate), g ∈ gs → 1 ≤ (gs.map fun g' => g'.inputs.count w).sum := by
        intro gs
        induction gs with
        | nil => intro h; simp at h
        | cons g1 gs ih =>
          intro hmem
          simp only [List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hmem with rfl | hmem
          · have : 0 < g.inputs.count w := List.count_pos_iff.mpr hwg
            omega
          · have := ih hmem; omega
      exact hAux D.gates hg
    have hNine : 9 + notCount D ≤ D.size := by
      have h1 : M ≤ ∑ w ∈ Finset.range M, fanout w := by
        have := Finset.sum_le_sum hFanPos
        simpa [Finset.sum_const, Finset.card_range] using this
      rw [hSumFan] at h1
      omega
    by_contra hlt10
    have hEq9 : 9 + notCount D = D.size := by omega
    have hFanEq1 : ∀ w < M, fanout w = 1 := by
      have hSumEq : ∑ w ∈ Finset.range M, fanout w = M := by
        rw [hSumFan]; omega
      intro w hw
      by_contra hne1
      have hge2 : 2 ≤ fanout w := by
        have := hFanPos w (Finset.mem_range.mpr hw); omega
      have hsplit := Finset.add_sum_erase (Finset.range M) fanout (Finset.mem_range.mpr hw)
      have hrest : ((Finset.range M).erase w).card ≤
          ∑ x ∈ (Finset.range M).erase w, fanout x := by
        have := Finset.sum_le_sum (s := (Finset.range M).erase w)
          (fun x hx => hFanPos x (Finset.mem_of_mem_erase hx))
        simpa [Finset.sum_const] using this
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hw), Finset.card_range] at hrest
      omega
    have hHasBin : ∃ j : ℕ, ∃ hj : j < D.gates.length, D.gates[j].op ≠ .not := by
      by_contra hall
      push_neg at hall
      have hAllNot : notCount D = D.gates.length := by
        unfold notCount
        have hfeq : D.gates.filter (fun g => decide (g.op = GateOp.not)) = D.gates := by
          rw [List.filter_eq_self]
          intro g hg
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          simp [hall j hj]
        rw [hfeq]
      unfold Circuit.size at hEq9
      omega
    let j0 := Nat.find hHasBin
    have hj0Spec := Nat.find_spec hHasBin
    obtain ⟨hj0_, hj0Bin⟩ := hj0Spec
    have hj0 : j0 < D.gates.length := hj0_
    have hPrevNot : ∀ k (hk : k < j0), (D.gates[k]'(lt_trans hk hj0)).op = .not := by
      intro k hk
      by_contra hne
      exact Nat.find_min hHasBin hk ⟨lt_trans hk hj0, hne⟩
    have hSingleRead : ∀ (w : ℕ), w < M → ∀ (j1 j2 : ℕ) (h1 : j1 < D.gates.length)
        (h2 : j2 < D.gates.length), w ∈ D.gates[j1].inputs → w ∈ D.gates[j2].inputs →
        j1 = j2 := by
      intro w hw j1 j2 h1 h2 hm1 hm2
      by_contra hne
      have hMemPos : ∀ (l : List Gate) (g0 : Gate), g0 ∈ l → w ∈ g0.inputs →
          1 ≤ (l.map fun g' => g'.inputs.count w).sum := by
        intro l
        induction l with
        | nil => intro _ h; simp at h
        | cons g2 l2 ih2 =>
          intro g0 hmem hwg
          simp only [List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hmem with rfl | hmem
          · have : 0 < g0.inputs.count w := List.count_pos_iff.mpr hwg
            omega
          · have := ih2 g0 hmem hwg; omega
      have hAux : ∀ (gs : List Gate) (p q : ℕ) (hp : p < gs.length) (hq : q < gs.length),
          p ≠ q → w ∈ gs[p].inputs → w ∈ gs[q].inputs →
          2 ≤ (gs.map fun g => g.inputs.count w).sum := by
        intro gs
        induction gs with
        | nil => intro p _ hp; simp at hp
        | cons g gs ih =>
          intro p q hp hq hpq hmp hmq
          simp only [List.map_cons, List.sum_cons]
          cases p with
          | zero =>
            cases q with
            | zero => exact (hpq rfl).elim
            | succ q =>
              have hc1 : 0 < g.inputs.count w := List.count_pos_iff.mpr hmp
              have hq' : q < gs.length := by simp at hq; omega
              have hc2 := hMemPos gs gs[q] (List.getElem_mem hq') hmq
              omega
          | succ p =>
            cases q with
            | zero =>
              have hc1 : 0 < g.inputs.count w := List.count_pos_iff.mpr hmq
              have hp' : p < gs.length := by simp at hp; omega
              have hc2 := hMemPos gs gs[p] (List.getElem_mem hp') hmp
              omega
            | succ q =>
              have := ih p q (by simp at hp; omega) (by simp at hq; omega) (by omega) hmp hmq
              omega
      have h2ge := hAux D.gates j1 j2 h1 h2 hne hm1 hm2
      have hf1 := hFanEq1 w hw
      dsimp only [fanout] at hf1
      omega
    have hj0Strict := hStrict j0 hj0
    rcases hj0Strict with ⟨hj0Op, hj0Len, hj0Nodup, hj0Lt⟩ | ⟨hj0N, _, _⟩
    swap
    · exact (hj0Bin hj0N).elim
    obtain ⟨a, b, hj0Ins⟩ := List.length_eq_two.mp hj0Len
    have habNodup : ([a, b] : List ℕ).Nodup := hj0Ins ▸ hj0Nodup
    · have habNe : a ≠ b := by simpa using habNodup
      have haLt : a < 10 + j0 := hj0Lt a (by rw [hj0Ins]; simp)
      have hbLt : b < 10 + j0 := hj0Lt b (by rw [hj0Ins]; simp)
      have hPrevInput : ∀ k (hk : k < j0),
          ∃ r : Fin 10, D.gates[k]'(by omega) = ⟨.not, [r.val]⟩ := by
        intro k hk
        have hkD : k < D.gates.length := by omega
        have hkNot := hPrevNot k hk
        rcases hStrict k hkD with ⟨hbo, _, _, _⟩ | ⟨_, hkl1, hklt⟩
        · rcases hbo with h | h <;> rw [hkNot] at h <;> cases h
        · obtain ⟨r, hkins⟩ := List.length_eq_one_iff.mp hkl1
          have hrlt : r < 10 + k := hklt r (by rw [hkins]; simp)
          have hr10 : r < 10 := by
            by_contra hge10
            have hm : r - 10 < j0 := by omega
            have hmNot := hPrevNot (r - 10) hm
            have hbad := hNoDblNot (r - 10) (by omega) hmNot D.gates[k] (List.getElem_mem hkD) hkNot
            apply hbad
            rw [hkins]
            simp [show 10 + (r - 10) = r by omega]
          refine ⟨⟨r, hr10⟩, ?_⟩
          cases hgk : D.gates[k]
          rw [hgk] at hkNot hkins
          simp only at hkNot hkins
          rw [hkNot, hkins]
      have hWireRoot : ∀ w < 10 + j0,
          ∃ (r : Fin 10) (neg : Bool),
            (w = r.val ∧ neg = false ∨
              ∃ k, ∃ hk : k < j0, w = 10 + k ∧ D.gates[k]'(lt_trans hk hj0) = ⟨.not, [r.val]⟩ ∧ neg = true) ∧
            ∀ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD w false =
              if neg then !(x r) else x r := by
        intro w hw
        by_cases h10 : w < 10
        · exact ⟨⟨w, h10⟩, false, Or.inl ⟨rfl, rfl⟩, fun x => by simpa using wire_input D x ⟨w, h10⟩⟩
        · have hk : w - 10 < j0 := by omega
          obtain ⟨r, hr⟩ := hPrevInput (w - 10) hk
          refine ⟨r, true, Or.inr ⟨w - 10, hk, by omega, hr, rfl⟩, fun x => ?_⟩
          have hwEq : w = 10 + (w - 10) := by omega
          rw [hwEq, wire_at_gate D (w - 10) (by omega) x, hr]
          simp only [List.map_cons, List.map_nil, if_pos (by have := r.isLt; omega : r.val < 10 + (w - 10)),
            hOpNot, List.headD_cons, if_true]
          rw [wire_input D x r]
      obtain ⟨u, negU, huDesc, huVal⟩ := hWireRoot a haLt
      obtain ⟨v, negV, hvDesc, hvVal⟩ := hWireRoot b hbLt
      have hAMem : a ∈ D.gates[j0].inputs := by rw [hj0Ins]; simp
      have hBMem : b ∈ D.gates[j0].inputs := by rw [hj0Ins]; simp
      have hReadOfU : ∃ ju : ℕ, ∃ hju : ju ≤ j0, u.val ∈ (D.gates[ju]'(by omega)).inputs ∧
          (a = u.val → ju = j0) ∧ (a ≠ u.val → ju < j0 ∧ a = 10 + ju) := by
        rcases huDesc with ⟨hau, _⟩ | ⟨k, hk, hak, hgk, _⟩
        · exact ⟨j0, le_rfl, hau ▸ hAMem, fun _ => rfl, fun h => (h hau).elim⟩
        · exact ⟨k, by omega, by rw [hgk]; simp, fun h => by have := u.isLt; omega, fun _ => ⟨hk, hak⟩⟩
      have hReadOfV : ∃ jv : ℕ, ∃ hjv : jv ≤ j0, v.val ∈ (D.gates[jv]'(by omega)).inputs ∧
          (b = v.val → jv = j0) ∧ (b ≠ v.val → jv < j0 ∧ b = 10 + jv) := by
        rcases hvDesc with ⟨hbv, _⟩ | ⟨k, hk, hbk, hgk, _⟩
        · exact ⟨j0, le_rfl, hbv ▸ hBMem, fun _ => rfl, fun h => (h hbv).elim⟩
        · exact ⟨k, by omega, by rw [hgk]; simp, fun h => by have := v.isLt; omega, fun _ => ⟨hk, hbk⟩⟩
      obtain ⟨ju, hju, hjuIn, hjuEq, hjuNe⟩ := hReadOfU
      obtain ⟨jv, hjv, hjvIn, hjvEq, hjvNe⟩ := hReadOfV
      have huvNe : u ≠ v := by
        intro huv
        have hEqJ : ju = jv := hSingleRead u.val (by have := u.isLt; omega) ju jv
          (by omega) (by omega) hjuIn (huv ▸ hjvIn)
        by_cases hau : a = u.val
        · have hj0u : ju = j0 := hjuEq hau
          by_cases hbv : b = v.val
          · exact habNe (hau.trans ((congrArg Fin.val huv).trans hbv.symm))
          · have := (hjvNe hbv).1; omega
        · have h1 := hjuNe hau
          by_cases hbv : b = v.val
          · have := hjvEq hbv; omega
          · have h2 := hjvNe hbv
            exact habNe (h1.2.trans ((congrArg (10 + ·) hEqJ).trans h2.2.symm))
      have hGateVal_j0 : ∀ x : Fin 10 → Bool,
          (D.wires (List.ofFn x)).getD (10 + j0) false =
            D.gates[j0].op.eval [if negU then !x u else x u, if negV then !x v else x v] := by
        intro x
        rw [wire_at_gate D j0 hj0 x, hj0Ins]
        simp only [List.map_cons, List.map_nil, if_pos haLt, if_pos hbLt, huVal x, hvVal x]
      have hAgreeOut : ∀ x y : Fin 10 → Bool,
          (∀ t : Fin 10, t ≠ u → t ≠ v → x t = y t) →
          (D.wires (List.ofFn x)).getD (10 + j0) false =
            (D.wires (List.ofFn y)).getD (10 + j0) false →
          D.eval (List.ofFn x) = D.eval (List.ofFn y) := by
        intro x y hxy hgj0
        let bad : ℕ → Prop := fun w => w = u.val ∨ w = v.val ∨ w = a ∨ w = b
        have hAll : ∀ n : ℕ, ∀ w < n, ¬ bad w →
            (D.wires (List.ofFn x)).getD w false = (D.wires (List.ofFn y)).getD w false := by
          intro n
          induction n with
          | zero => intro w hw; omega
          | succ n ih =>
            intro w hw hnb
            by_cases hwn : w < n
            · exact ih w hwn hnb
            · have hweq : w = n := by omega
              subst hweq
              by_cases h10 : w < 10
              · rw [wire_input D x ⟨w, h10⟩, wire_input D y ⟨w, h10⟩]
                apply hxy
                · intro h; exact hnb (Or.inl (congrArg Fin.val h))
                · intro h; exact hnb (Or.inr (Or.inl (congrArg Fin.val h)))
              · by_cases hlen : w < 10 + D.gates.length
                · let m := w - 10
                  have hm : m < D.gates.length := by omega
                  have hwEq : w = 10 + m := by omega
                  rcases lt_trichotomy m j0 with hmj | hmj | hmj
                  · obtain ⟨r, hr⟩ := hPrevInput m hmj
                    have hru : r ≠ u := by
                      intro h
                      have hEqJ : m = ju := hSingleRead u.val (by have := u.isLt; omega) m ju
                        hm (by omega) (by rw [hr, h]; simp) hjuIn
                      by_cases hau : a = u.val
                      · have := hjuEq hau; omega
                      · have h1 := (hjuNe hau).2
                        exact hnb (Or.inr (Or.inr (Or.inl (by omega))))
                    have hrv : r ≠ v := by
                      intro h
                      have hEqJ : m = jv := hSingleRead v.val (by have := v.isLt; omega) m jv
                        hm (by omega) (by rw [hr, h]; simp) hjvIn
                      by_cases hbv : b = v.val
                      · have := hjvEq hbv; omega
                      · have h1 := (hjvNe hbv).2
                        exact hnb (Or.inr (Or.inr (Or.inr (by omega))))
                    rw [hwEq, wire_at_gate D m hm x, wire_at_gate D m hm y, hr]
                    simp only [List.map_cons, List.map_nil,
                      if_pos (by have := r.isLt; omega : r.val < 10 + m),
                      wire_input D x r, wire_input D y r, hxy r hru hrv]
                  · rw [hwEq, hmj]; exact hgj0
                  · rw [hwEq, wire_at_gate D m hm x, wire_at_gate D m hm y]
                    congr 1
                    apply List.map_congr_left
                    intro i hi
                    have hilt : i < 10 + m := by
                      rcases hStrict m hm with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ <;> exact h i hi
                    simp only [if_pos hilt]
                    apply ih i (by omega)
                    rintro (heq | heq | heq | heq)
                    · rw [heq] at hi
                      have := hSingleRead u.val (by have := u.isLt; omega) m ju hm (by omega) hi hjuIn
                      omega
                    · rw [heq] at hi
                      have := hSingleRead v.val (by have := v.isLt; omega) m jv hm (by omega) hi hjvIn
                      omega
                    · rw [heq] at hi
                      have haM : a < M := by dsimp only [M]; unfold Circuit.size; omega
                      have := hSingleRead a haM m j0 hm hj0 hi hAMem
                      omega
                    · rw [heq] at hi
                      have hbM : b < M := by dsimp only [M]; unfold Circuit.size; omega
                      have := hSingleRead b hbM m j0 hm hj0 hi hBMem
                      omega
                · have hlx : (D.wires (List.ofFn x)).length = 10 + D.gates.length := by
                    show (D.gates.foldl step _).length = _; rw [fold_len, List.length_ofFn]
                  have hly : (D.wires (List.ofFn y)).length = 10 + D.gates.length := by
                    show (D.gates.foldl step _).length = _; rw [fold_len, List.length_ofFn]
                  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        have hOutNotBad : ¬ bad D.output := by
          have := u.isLt; have := v.isLt
          rintro (h | h | h | h) <;> change D.output + 1 = 10 + D.gates.length at hOutLast <;> omega
        exact hAll (D.output + 1) D.output (Nat.lt_succ_self _) hOutNotBad
      have hPriv : ∀ p q : Fin 10, p ≠ q →
          ∃ p1 q1 : Fin 10, p1 ≠ p ∧ p1 ≠ q ∧ q1 ≠ p ∧ q1 ≠ q ∧
            f (fun k => decide (k = p1)) = false ∧
            f (fun k => decide (k = p1 ∨ k = p)) = true ∧
            f (fun k => decide (k = p1 ∨ k = q)) = false ∧
            f (fun k => decide (k = q1)) = false ∧
            f (fun k => decide (k = q1 ∨ k = q)) = true ∧
            f (fun k => decide (k = q1 ∨ k = p)) = false := by decide
      obtain ⟨u1, v1, hu1u, hu1v, hv1u, hv1v, hf1, hf2, hf3, hf4, hf5, hf6⟩ := hPriv u v huvNe
      let val2 : Bool → Bool → Bool := fun bu bv =>
        D.gates[j0].op.eval [if negU then !bu else bu, if negV then !bv else bv]
      have hTest : ∀ (base : Fin 10 → Bool) (bu1 bv1 bu2 bv2 : Bool),
          val2 bu1 bv1 = val2 bu2 bv2 →
          f (Function.update (Function.update base u bu1) v bv1) =
            f (Function.update (Function.update base u bu2) v bv2) := by
        intro base bu1 bv1 bu2 bv2 heq
        let x := Function.update (Function.update base u bu1) v bv1
        let y := Function.update (Function.update base u bu2) v bv2
        rw [← hComp x, ← hComp y]
        apply hAgreeOut x y
        · intro t htu htv
          simp [x, y, Function.update, htu, htv]
        · rw [hGateVal_j0 x, hGateVal_j0 y]
          have hxu : x u = bu1 := by simp [x, Function.update, huvNe]
          have hxv : x v = bv1 := by simp [x, Function.update]
          have hyu : y u = bu2 := by simp [y, Function.update, huvNe]
          have hyv : y v = bv2 := by simp [y, Function.update]
          rw [hxu, hxv, hyu, hyv]
          exact heq
      have hMk : ∀ (w : Fin 10) (hwu : w ≠ u) (hwv : w ≠ v),
          (Function.update (Function.update (fun k => decide (k = w)) u false) v false =
            fun k => decide (k = w)) ∧
          (Function.update (Function.update (fun k => decide (k = w)) u true) v false =
            fun k => decide (k = w ∨ k = u)) ∧
          (Function.update (Function.update (fun k => decide (k = w)) u false) v true =
            fun k => decide (k = w ∨ k = v)) := by
        intro w hwu hwv
        refine ⟨?_, ?_, ?_⟩ <;> funext k <;> by_cases hkv : k = v <;> by_cases hku : k = u <;>
          simp [Function.update, hkv, hku, hwu, hwv, huvNe, Ne.symm hwu, Ne.symm hwv, Ne.symm huvNe]
      have hU := hMk u1 hu1u hu1v
      have hV := hMk v1 hv1u hv1v
      cases h00 : val2 false false <;> cases h10 : val2 true false <;> cases h01 : val2 false true
      · have h := hTest (fun k => decide (k = u1)) false false true false (by rw [h00, h10])
        rw [hU.1, hU.2.1, hf1, hf2] at h; exact Bool.false_ne_true h
      · have h := hTest (fun k => decide (k = u1)) false false true false (by rw [h00, h10])
        rw [hU.1, hU.2.1, hf1, hf2] at h; exact Bool.false_ne_true h
      · have h := hTest (fun k => decide (k = v1)) false false false true (by rw [h00, h01])
        rw [hV.1, hV.2.2, hf4, hf5] at h; exact Bool.false_ne_true h
      · have h := hTest (fun k => decide (k = u1)) true false false true (by rw [h10, h01])
        rw [hU.2.1, hU.2.2, hf2, hf3] at h; exact Bool.noConfusion h
      · have h := hTest (fun k => decide (k = u1)) true false false true (by rw [h10, h01])
        rw [hU.2.1, hU.2.2, hf2, hf3] at h; exact Bool.noConfusion h
      · have h := hTest (fun k => decide (k = v1)) false false false true (by rw [h00, h01])
        rw [hV.1, hV.2.2, hf4, hf5] at h; exact Bool.false_ne_true h
      · have h := hTest (fun k => decide (k = u1)) false false true false (by rw [h00, h10])
        rw [hU.1, hU.2.1, hf1, hf2] at h; exact Bool.false_ne_true h
      · have h := hTest (fun k => decide (k = u1)) false false true false (by rw [h00, h10])
        rw [hU.1, hU.2.1, hf1, hf2] at h; exact Bool.false_ne_true h
  let adj : Fin 10 → Fin 10 → Bool := fun a b =>
    edges.any fun n => (a.val == n / 10 && b.val == n % 10) || (b.val == n / 10 && a.val == n % 10)
  let toPair : Fin 10 → Fin 5 × Fin 5 := fun v =>
    if v.val = 0 then (0, 1)
    else if v.val = 1 then (2, 3)
    else if v.val = 2 then (4, 0)
    else if v.val = 3 then (1, 2)
    else if v.val = 4 then (3, 4)
    else if v.val = 5 then (2, 4)
    else if v.val = 6 then (1, 4)
    else if v.val = 7 then (1, 3)
    else if v.val = 8 then (0, 3)
    else (0, 2)
  let ofPair : Fin 5 → Fin 5 → Fin 10 := fun a b =>
    ((List.finRange 10).find? (fun v =>
      let p := toPair v
      (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a))).getD 0
  let s5Act : (Fin 5 → Fin 5) → Fin 10 → Fin 10 := fun π v =>
    let p := toPair v
    ofPair (π p.1) (π p.2)
  let mkAut : Fin 10 → Fin 10 → (Fin 10 → Fin 10) := fun u v =>
    let pu := toPair u
    let pv := toPair v
    let a0 := pu.1
    let a1 := pu.2
    if adj u v then
      let a2 := pv.1
      let a3 := pv.2
      s5Act (fun z => if z = a0 then 0 else if z = a1 then 1 else if z = a2 then 2 else if z = a3 then 3 else 4)
    else
      let sh := if pv.1 = a0 || pv.1 = a1 then pv.1 else pv.2
      let uo := if sh = a0 then a1 else a0
      let vo := if sh = pv.1 then pv.2 else pv.1
      let rest := (List.finRange 5).filter (fun z => z != sh && z != uo && z != vo)
      let r0 := rest.getD 0 0
      s5Act (fun z => if z = sh then 0 else if z = uo then 1 else if z = vo then 4 else if z = r0 then 2 else 3)
  have hAutSpec : ∀ u v : Fin 10, u ≠ v →
      (∀ i j : Fin 10, mkAut u v i = mkAut u v j → i = j) ∧
      (∀ i j : Fin 10, adj (mkAut u v i) (mkAut u v j) = adj i j) ∧
      mkAut u v u = 0 ∧
      (if adj u v then mkAut u v v = 1 else mkAut u v v = 2) := by decide
  have hAutSurj : ∀ u v : Fin 10, u ≠ v → ∀ y : Fin 10, ∃ x : Fin 10, mkAut u v x = y := by decide
  have hAdjOfEdge : ∀ n ∈ edges,
      adj (Fin.ofNat 10 (n / 10)) (Fin.ofNat 10 (n % 10)) = true := by decide
  have hEdgeOfAdj : ∀ a b : Fin 10, adj a b = true →
      ∃ n ∈ edges,
        (Fin.ofNat 10 (n / 10) = a ∧ Fin.ofNat 10 (n % 10) = b) ∨
        (Fin.ofNat 10 (n / 10) = b ∧ Fin.ofNat 10 (n % 10) = a) := by decide
  have f_eq_adj : ∀ x : Fin 10 → Bool,
      f x = decide (∃ a b : Fin 10, adj a b = true ∧ x a = true ∧ x b = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [f, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨n, hn, h1, h2⟩
      exact ⟨Fin.ofNat 10 (n / 10), Fin.ofNat 10 (n % 10), hAdjOfEdge n hn, h1, h2⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      obtain ⟨n, hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hEdgeOfAdj a b hab
      · exact ⟨n, hn, ha, hb⟩
      · exact ⟨n, hn, hb, ha⟩
  have conjCircuit : ∀ (σ : Fin 10 → Fin 10),
      (∀ i j, σ i = σ j → i = j) →
      (∀ y : Fin 10, ∃ x : Fin 10, σ x = y) →
      (∀ i j, adj (σ i) (σ j) = adj i j) →
      ∃ E : Circuit, Strict 10 E ∧ E.size = D.size ∧ E.output + 1 = 10 + E.size ∧
        notCount E = notCount D ∧
        (∀ j < E.size - 1, ∃ g ∈ E.gates, 10 + j ∈ g.inputs) ∧
        (∀ k (hk : k < E.gates.length), E.gates[k].op = .not →
          ∀ g ∈ E.gates, g.op = .not → 10 + k ∉ g.inputs) ∧
        E.gates.head? = D.gates.head?.map (fun g =>
          ⟨g.op, g.inputs.map fun w => if h : w < 10 then (σ ⟨w, h⟩).val else w⟩) ∧
        (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = f x) := by
    intro σ hInj hSurj hAdj
    let ρ : ℕ → ℕ := fun w => if h : w < 10 then (σ ⟨w, h⟩).val else w
    have hρInj : ∀ a b, ρ a = ρ b → a = b := by
      intro a b hab
      dsimp only [ρ] at hab
      split_ifs at hab with ha hb hb
      · exact congrArg Fin.val (hInj ⟨a, ha⟩ ⟨b, hb⟩ (Fin.ext hab))
      · have := (σ ⟨a, ha⟩).isLt; omega
      · have := (σ ⟨b, hb⟩).isLt; omega
      · exact hab
    have hρLt : ∀ j w, w < 10 + j → ρ w < 10 + j := by
      intro j w hw
      dsimp only [ρ]
      split_ifs with h10
      · have := (σ ⟨w, h10⟩).isLt; omega
      · exact hw
    have hρGe : ∀ k, ρ (10 + k) = 10 + k := by
      intro k; dsimp only [ρ]; rw [dif_neg (by omega)]
    let mapG : Gate → Gate := fun g => ⟨g.op, g.inputs.map ρ⟩
    let E : Circuit := ⟨D.gates.map mapG, D.output⟩
    have hEsz : E.size = D.size := List.length_map _
    refine ⟨E, ?_, hEsz, by rw [hEsz]; exact hOutLast, ?_, ?_, ?_, by simp [E, mapG, ρ, List.head?_map], ?_⟩
    · intro j hj
      have hjD : j < D.gates.length := by simpa [E] using hj
      have hEj : E.gates[j] = mapG D.gates[j] := List.getElem_map _
      rw [hEj]
      rcases hStrict j hjD with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
      · left
        refine ⟨h1, by simp [mapG, h2], ?_, ?_⟩
        · exact h3.map hρInj
        · intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          exact hρLt j i0 (h4 i0 hi0)
      · right
        refine ⟨h1, by simp [mapG, h2], ?_⟩
        intro i hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
        exact hρLt j i0 (h3 i0 hi0)
    · unfold notCount
      dsimp only [E]
      rw [List.filter_map, List.length_map]
      rfl
    · intro j hj
      obtain ⟨g, hg, hmem⟩ := hNoDead j (by omega)
      refine ⟨mapG g, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
      exact List.mem_map.mpr ⟨10 + j, hmem, hρGe j⟩
    · intro k hk hknot g hg hgnot hmem
      have hkD : k < D.gates.length := by simpa [E] using hk
      have hEk : E.gates[k] = mapG D.gates[k] := List.getElem_map _
      rw [hEk] at hknot
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨w0, hw0, hρw⟩ := List.mem_map.mp hmem
      have hwEq : w0 = 10 + k := hρInj w0 (10 + k) (hρw.trans (hρGe k).symm)
      subst hwEq
      exact hNoDblNot k hkD hknot g0 hg0 hgnot hw0
    · intro x
      have hfx : f (fun i => x (σ i)) = f x := by
        rw [f_eq_adj (fun i => x (σ i)), f_eq_adj x]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨a, b, hab, ha, hb⟩
          exact ⟨σ a, σ b, by rw [hAdj]; exact hab, ha, hb⟩
        · rintro ⟨a, b, hab, ha, hb⟩
          obtain ⟨a0, rfl⟩ := hSurj a
          obtain ⟨b0, rfl⟩ := hSurj b
          exact ⟨a0, b0, by rw [← hAdj]; exact hab, ha, hb⟩
      rw [← hfx, ← hComp (fun i => x (σ i))]
      have hStep : ∀ (gs : List Gate) (wE wD : List Bool),
          wE.length = wD.length → 10 ≤ wD.length →
          (∀ i, wE.getD (ρ i) false = wD.getD i false) →
          ∀ i, ((gs.map mapG).foldl step wE).getD (ρ i) false =
            (gs.foldl step wD).getD i false := by
        intro gs
        induction gs with
        | nil => intro wE wD _ _ inv i; exact inv i
        | cons g gs ih =>
          intro wE wD hlen h10 inv i
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have hev : (mapG g).op.eval ((mapG g).inputs.map fun k => wE.getD k false) =
              g.op.eval (g.inputs.map fun k => wD.getD k false) := by
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro k _
            exact inv k
          apply ih (step wE (mapG g)) (step wD g)
            (by simp [step, hlen]) (by simp [step]; omega) _ i
          intro k
          simp only [step, hev]
          rcases lt_trichotomy k wD.length with hlt | heq | hgt
          · have hlt' : ρ k < wE.length := by
              dsimp only [ρ]; split_ifs with h10'
              · have := (σ ⟨k, h10'⟩).isLt; omega
              · omega
            rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
            exact inv k
          · subst heq
            have hρw : ρ wD.length = wE.length := by
              dsimp only [ρ]; rw [dif_neg (by omega), hlen]
            rw [hρw, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
            simp
          · have hgt' : wE.length < ρ k := by
              dsimp only [ρ]; rw [dif_neg (by omega)]; omega
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hBase : ∀ i, (List.ofFn x).getD (ρ i) false =
          (List.ofFn fun k => x (σ k)).getD i false := by
        intro i
        by_cases h10 : i < 10
        · dsimp only [ρ]; rw [dif_pos h10]
          rw [List.getD_eq_getElem _ _ (by simp [(σ ⟨i, h10⟩).isLt]),
            List.getD_eq_getElem _ _ (by simp [h10]),
            List.getElem_ofFn, List.getElem_ofFn]
        · dsimp only [ρ]; rw [dif_neg h10]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hOutGe : 10 ≤ D.output := by omega
      have hρOut : ρ D.output = D.output := by dsimp only [ρ]; rw [dif_neg (by omega)]
      show ((D.gates.map mapG).foldl step (List.ofFn x)).getD D.output false =
        (D.gates.foldl step (List.ofFn fun k => x (σ k))).getD D.output false
      conv_lhs => rw [← hρOut]
      exact hStep D.gates (List.ofFn x) (List.ofFn fun k => x (σ k)) (by simp) (by simp) hBase D.output
  have h0lt : 0 < D.gates.length := by change 1 ≤ D.gates.length at hSizePos; omega
  have hHeadEq : D.gates.head? = some D.gates[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0lt]
  have hS0 := hStrict 0 h0lt
  rcases hS0 with ⟨hOp0, hLen0, hNodup0, hLt0⟩ | ⟨hNot0, hLen0, hLt0⟩
  · obtain ⟨u0, v0, hIns0⟩ := List.length_eq_two.mp hLen0
    have hnd : ([u0, v0] : List ℕ).Nodup := hIns0 ▸ hNodup0
    have huvNe : u0 ≠ v0 := by simpa using hnd
    have huLt : u0 < 10 := hLt0 u0 (by rw [hIns0]; simp)
    have hvLt : v0 < 10 := hLt0 v0 (by rw [hIns0]; simp)
    let uf : Fin 10 := ⟨u0, huLt⟩
    let vf : Fin 10 := ⟨v0, hvLt⟩
    have hfvNe : uf ≠ vf := fun h => huvNe (congrArg Fin.val h)
    have hA := hAutSpec uf vf hfvNe
    obtain ⟨E, hEStr, hESz, hEOut, hENot, hEDead, hEDbl, hEHead, hEComp⟩ :=
      conjCircuit (mkAut uf vf) hA.1 (hAutSurj uf vf hfvNe) hA.2.1
    have hEHeadIn : E.gates.head? ∈ ([some ⟨.and, [0, 1]⟩, some ⟨.and, [0, 2]⟩,
        some ⟨.or, [0, 1]⟩, some ⟨.or, [0, 2]⟩] : List (Option Gate)) := by
      rw [hEHead, hHeadEq]
      simp only [Option.map_some, hIns0, List.map_cons, List.map_nil, dif_pos huLt, dif_pos hvLt]
      have hu0 : (mkAut uf vf uf).val = 0 := congrArg Fin.val hA.2.2.1
      change (mkAut uf vf ⟨u0, huLt⟩).val = 0 at hu0
      rw [hu0]
      by_cases hadj : adj uf vf = true
      · have hv1 : (mkAut uf vf ⟨v0, hvLt⟩).val = 1 := by
          have := hA.2.2.2; simp only [hadj, if_true] at this; exact congrArg Fin.val this
        rw [hv1]
        rcases hOp0 with ho | ho <;> rw [ho] <;> simp
      · have hv2 : (mkAut uf vf ⟨v0, hvLt⟩).val = 2 := by
          have := hA.2.2.2; simp only [hadj, if_false] at this; exact congrArg Fin.val this
        rw [hv2]
        rcases hOp0 with ho | ho <;> rw [ho] <;> simp
    by_cases hnc : notCount E = 0
    · have hE18 : E.size ≤ 18 := by
        rcases hBud with hlt19 | ⟨g, hg, hgn⟩
        · omega
        · exfalso
          have hpos : 0 < notCount D := by
            unfold notCount
            exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simp [hgn]⟩)
          omega
      exact hMono18 E hEStr hE18 hEOut hnc hEHeadIn hEComp
    · exact hBinFirst E hEStr (by omega) hEOut (by omega) (by omega) hEDead hEDbl hEHeadIn hEComp
  · obtain ⟨u0, hIns0⟩ := List.length_eq_one_iff.mp hLen0
    have huLt : u0 < 10 := hLt0 u0 (by rw [hIns0]; simp)
    let uf : Fin 10 := ⟨u0, huLt⟩
    let vf : Fin 10 := if uf = 0 then 1 else 0
    have hfvNe : uf ≠ vf := by dsimp only [vf]; split_ifs with h <;> simp [h]
    have hA := hAutSpec uf vf hfvNe
    obtain ⟨E, hEStr, hESz, hEOut, hENot, hEDead, hEDbl, hEHead, hEComp⟩ :=
      conjCircuit (mkAut uf vf) hA.1 (hAutSurj uf vf hfvNe) hA.2.1
    have hEHeadEq : E.gates.head? = some ⟨.not, [0]⟩ := by
      rw [hEHead, hHeadEq]
      simp only [Option.map_some, hNot0, hIns0, List.map_cons, List.map_nil, dif_pos huLt]
      have hu0 : (mkAut uf vf uf).val = 0 := congrArg Fin.val hA.2.2.1
      change (mkAut uf vf ⟨u0, huLt⟩).val = 0 at hu0
      rw [hu0]
    have hNotPos : 1 ≤ notCount E := by
      rw [hENot]
      unfold notCount
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.getElem_mem h0lt, by simp [hNot0]⟩)
    exact hNotFirst E hEStr (by omega) hEOut hNotPos (by omega) hEDead hEDbl hEHeadEq hEComp
