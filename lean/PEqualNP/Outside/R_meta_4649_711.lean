import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4649_711
  (size26 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    27 ≤ C.size)
  (formula : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C.size ≤ 27 →
    PEqualNP.TopForm.IsAO2 14 C →
    (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup) →
    PEqualNP.MetaComplexity.circuitFun 14 C =
      (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
    ((C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter
      (fun w => decide (14 ≤ w))).Nodup →
    PEqualNP.CircuitLowerBounds.HasLineDegree 14 {0} C 1 ∨
      PEqualNP.CircuitLowerBounds.HasLineDegree 14 {7} C 1)
  (sharedDag : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C.size = 27 →
    C.output = 40 →
    PEqualNP.TopForm.IsAO2 14 C →
    (∀ j < 27, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup) →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
    PEqualNP.MetaComplexity.circuitFun 14 C =
      (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
    ¬ ((C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter
        (fun w => decide (14 ≤ w))).Nodup →
    PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false →
    PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i < 7)) 0 7 = false →
    False) :
  (have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; ¬∃ (x2 : List (Fin (62 : ℕ) → Bool)),     x2.length ≤ (27 : ℕ) ∧       (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧         ∀ x3 < x2.length,           ∃ (x5 : ℕ) (x6 : ℕ),             x5 ≠ x6 ∧               x5 < (14 : ℕ) + x3 ∧                 x6 < (14 : ℕ) + x3 ∧                   have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;                   have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;                   ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9) := by
  classical
  let raw : List ℕ := [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
  let seed : List (Fin 62 → Bool) := raw.map (fun n (t : Fin 62) => n.testBit t.val)
  let zero : Fin 62 → Bool := fun _ => false
  let target : Fin 62 → Bool := fun t => decide (t.val < 21)
  change ¬ ∃ s : List (Fin 62 → Bool), s.length ≤ 27 ∧ target ∈ s ∧ _
  rintro ⟨s, hlen, hmem, hgates⟩
  let wire (i : ℕ) : Fin 62 → Bool := (seed ++ s).getD i zero
  have hseedLen : seed.length = 14 := rfl
  have hwireIn (i : ℕ) (hi : i < 14) (t : Fin 62) : wire i t = (raw.getD i 0).testBit t.val := by
    have hi' : i < seed.length := hseedLen ▸ hi
    change ((seed ++ s).getD i zero) t = _
    rw [List.getD_append _ _ _ _ hi']
    have hz : zero = (fun n (u : Fin 62) => n.testBit u.val) 0 := by
      funext u; exact (Nat.zero_testBit _).symm
    change ((raw.map (fun n (u : Fin 62) => n.testBit u.val)).getD i zero) t = _
    rw [hz, List.getD_map]
  have hwireG (i : ℕ) : wire (14 + i) = s.getD i zero := by
    dsimp only [wire]
    rw [List.getD_append_right _ _ _ _ (by rw [hseedLen]; omega), hseedLen, Nat.add_sub_cancel_left]
  have hrules (i : ℕ) : ∃ (a b : ℕ) (isOr : Bool), i < s.length →
      a ≠ b ∧ a < 14 + i ∧ b < 14 + i ∧ (isOr = false → 0 < i) ∧
      ∀ t : Fin 62, wire (14 + i) t =
        if isOr then wire a t || wire b t
        else if t = 60 then (wire a 58 && wire b 60) || (wire a 60 && wire b 58)
        else if t = 61 then (wire a 59 && wire b 61) || (wire a 61 && wire b 59)
        else wire a t && wire b t := by
    by_cases hi : i < s.length
    · obtain ⟨a, b, hne, ha, hb, hor | ⟨hpos, hand⟩⟩ := hgates i hi
      · exact ⟨a, b, true, fun _ => ⟨hne, ha, hb, by simp, fun t => by rw [hwireG i, hor]; rfl⟩⟩
      · exact ⟨a, b, false, fun _ => ⟨hne, ha, hb, fun _ => hpos, fun t => by rw [hwireG i, hand]; rfl⟩⟩
    · exact ⟨0, 0, true, fun h => False.elim (hi h)⟩
  choose ga gb gisOr hrule using hrules
  obtain ⟨k, hk, hsk⟩ := List.mem_iff_getElem.mp hmem
  have hk27 : k < 27 := by omega
  have hwireK : wire (14 + k) = target := by
    rw [hwireG k, List.getD_eq_getElem _ _ hk, hsk]
  let mkGate (i : ℕ) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨if gisOr i then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [ga i, gb i]⟩
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨(List.range (k + 1)).map mkGate, 14 + k⟩
  have hCsize : C.size = k + 1 := by
    change ((List.range (k + 1)).map mkGate).length = k + 1
    simp
  have hCglen : C.gates.length = k + 1 := by simp [C]
  have hgateAt (j : ℕ) (hj : j < k + 1) : PEqualNP.MetaComplexity.NestedCover.gateAt C j = mkGate j := by
    change ((List.range (k + 1)).map mkGate).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = mkGate j
    simp [List.getD_eq_getElem?_getD, hj]
  have hCmono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    simp only [C, List.mem_map, List.mem_range] at hg
    obtain ⟨j, _, rfl⟩ := hg
    refine ⟨?_, by simp [mkGate]⟩
    cases gisOr j <;> simp [mkGate]
  have hCAO2 : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C, List.mem_map, List.mem_range] at hg
      obtain ⟨j, _, rfl⟩ := hg
      cases gisOr j <;> simp [mkGate]
    · intro j hj w hw
      rw [hCglen] at hj
      rw [hgateAt j hj] at hw
      obtain ⟨_, ha, hb, _, _⟩ := hrule j (by omega)
      simp only [mkGate, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · intro g hg
      simp only [C, List.mem_map, List.mem_range] at hg
      obtain ⟨j, _, rfl⟩ := hg
      rfl
  have hCNodup : ∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup := by
    intro j hj
    rw [hCglen] at hj
    rw [hgateAt j hj]
    obtain ⟨hne, _, _, _, _⟩ := hrule j (by omega)
    simp [mkGate, hne]
  have hOp0 : (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hgateAt 0 (by omega)]
    obtain ⟨_, _, _, h0, _⟩ := hrule 0 (by omega)
    cases h : gisOr 0
    · exact False.elim (Nat.lt_irrefl 0 (h0 h))
    · simp [mkGate, h]
  have foldLen : ∀ {α : Type} (step : List α → PEqualNP.CircuitLowerBounds.Gate → α)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List α),
      (gs.foldl (fun w g => w ++ [step w g]) init).length = init.length + gs.length := by
    intro α step gs
    induction gs with
    | nil => intro init; simp
    | cons g gs ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp
      omega
  have foldKeep : ∀ {α : Type} (d : α) (step : List α → PEqualNP.CircuitLowerBounds.Gate → α)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List α) (i : ℕ),
      i < init.length → (gs.foldl (fun w g => w ++ [step w g]) init).getD i d = init.getD i d := by
    intro α d step gs
    induction gs with
    | nil => intro init i _; rfl
    | cons g gs ih =>
      intro init i hi
      rw [List.foldl_cons, ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]
  have foldStep : ∀ {α : Type} (d : α) (step : List α → PEqualNP.CircuitLowerBounds.Gate → α)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List α) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (fun w g => w ++ [step w g]) init).getD (init.length + j) d =
        step ((gs.take j).foldl (fun w g => w ++ [step w g]) init) gs[j] := by
    intro α d step gs init j hj
    have hsplit : gs = gs.take (j + 1) ++ gs.drop (j + 1) := (List.take_append_drop (j + 1) gs).symm
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [foldKeep d step (gs.drop (j + 1)) _ (init.length + j)
      (by rw [foldLen, List.length_take, Nat.min_eq_left (by omega)]; omega)]
    rw [List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlenj : ((gs.take j).foldl (fun w g => w ++ [step w g]) init).length = init.length + j := by
      rw [foldLen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [List.getD_append_right _ _ _ _ (by omega), hlenj, Nat.sub_self]
    rfl
  have foldTake : ∀ {α : Type} (d : α) (step : List α → PEqualNP.CircuitLowerBounds.Gate → α)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List α) (j i : ℕ),
      j ≤ gs.length → i < init.length + j →
      ((gs.take j).foldl (fun w g => w ++ [step w g]) init).getD i d =
        (gs.foldl (fun w g => w ++ [step w g]) init).getD i d := by
    intro α d step gs init j i hj hi
    have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    rw [foldKeep d step (gs.drop j) _ i (by rw [foldLen, List.length_take, Nat.min_eq_left hj]; exact hi)]
  have hwireStep (x : List Bool) (hx : x.length = 14) (j : ℕ) (hj : j < k + 1) :
      (C.wires x).getD (14 + j) false =
        if gisOr j then (C.wires x).getD (ga j) false || (C.wires x).getD (gb j) false
        else (C.wires x).getD (ga j) false && (C.wires x).getD (gb j) false := by
    have hj' : j < C.gates.length := hCglen ▸ hj
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD (14 + j) false = _
    have hStep := foldStep false (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x j hj'
    rw [hx] at hStep
    rw [hStep]
    have hgj : C.gates[j] = mkGate j := by
      have hga := hgateAt j hj
      change C.gates.getD j _ = mkGate j at hga
      rw [List.getD_eq_getElem _ _ hj'] at hga
      exact hga
    obtain ⟨_, ha, hb, _, _⟩ := hrule j (by omega)
    rw [hgj]
    have ha' := foldTake false (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      C.gates x j (ga j) (Nat.le_of_lt hj') (by omega)
    have hb' := foldTake false (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      C.gates x j (gb j) (Nat.le_of_lt hj') (by omega)
    dsimp only [mkGate]
    rw [List.map_cons, List.map_cons, List.map_nil, ha', hb']
    cases gisOr j
    · change ((C.wires x).getD (ga j) false && ((C.wires x).getD (gb j) false && true)) =
        if false = true then _ else _
      simp
    · change ((C.wires x).getD (ga j) false || ((C.wires x).getD (gb j) false || false)) =
        if true = true then _ else _
      simp
  have hcolMatch (t : Fin 60) :
      ∀ w < 14 + (k + 1),
        (C.wires (List.ofFn fun i : Fin 14 => (raw.getD i.val 0).testBit t.val)).getD w false =
          wire w ⟨t.val, by omega⟩ := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases h14 : w < 14
      · change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _).getD w false = _
        rw [foldKeep false _ C.gates _ w (by simp; exact h14)]
        rw [List.getD_eq_getElem _ _ (by simp; exact h14), List.getElem_ofFn]
        exact (hwireIn w h14 ⟨t.val, by omega⟩).symm
      · have hj : w - 14 < k + 1 := by omega
        have heq : 14 + (w - 14) = w := by omega
        rw [← heq, hwireStep _ (by simp) (w - 14) hj]
        obtain ⟨_, ha, hb, _, heval⟩ := hrule (w - 14) (by omega)
        rw [ih (ga (w - 14)) (by omega) (by omega), ih (gb (w - 14)) (by omega) (by omega)]
        have h60 : (⟨t.val, by omega⟩ : Fin 62) ≠ 60 := by
          intro h; have := congrArg Fin.val h; dsimp at this; omega
        have h61 : (⟨t.val, by omega⟩ : Fin 62) ≠ 61 := by
          intro h; have := congrArg Fin.val h; dsimp at this; omega
        have hv := heval ⟨t.val, by omega⟩
        cases h : gisOr (w - 14) <;> simp [h, h60, h61] at hv ⊢ <;> exact hv.symm
  have hCevalMono : Monotone (fun x : Fin 14 → Bool => C.eval (List.ofFn x)) := by
    intro x y hxy
    have hwireMono : ∀ w < 14 + (k + 1),
        (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hx
        by_cases h14 : w < 14
        · change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _).getD w false = true at hx
          change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _).getD w false = true
          rw [foldKeep false _ C.gates _ w (by simp; exact h14)] at hx ⊢
          rw [List.getD_eq_getElem _ _ (by simp; exact h14), List.getElem_ofFn] at hx ⊢
          exact Bool.le_iff_imp.1 (hxy ⟨w, h14⟩) hx
        · have hj : w - 14 < k + 1 := by omega
          have heq : 14 + (w - 14) = w := by omega
          rw [← heq, hwireStep _ (by simp) (w - 14) hj] at hx ⊢
          obtain ⟨_, ha, hb, _, _⟩ := hrule (w - 14) (by omega)
          have iha := ih (ga (w - 14)) (by omega) (by omega)
          have ihb := ih (gb (w - 14)) (by omega) (by omega)
          cases h : gisOr (w - 14)
          · simp only [h, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hx ⊢
            exact ⟨iha hx.1, ihb hx.2⟩
          · simp only [h, ite_true, Bool.or_eq_true] at hx ⊢
            exact hx.elim (fun h1 => Or.inl (iha h1)) (fun h2 => Or.inr (ihb h2))
    rw [Bool.le_iff_imp]
    exact hwireMono (14 + k) (by omega)
  have hfanoMem : ∀ p l : Fin 7,
      p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ↔ (p.val + 7 - l.val) % 7 ∈ ([0, 1, 3] : List ℕ) := by
    decide
  have hT2 : ∀ p l : Fin 7, (p.val + 7 - l.val) % 7 ∈ ([0, 1, 3] : List ℕ) →
      ∃ t : Fin 58, t.val < 21 ∧ ∀ i : Fin 14, (raw.getD i.val 0).testBit t.val = true →
        (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
    decide +kernel
  have hT3 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, ∃ t : Fin 58, 21 ≤ t.val ∧
      (∀ l : Fin 7, ([b0, b1, b2, b3, b4, b5, b6].getD l.val false) = true →
        (raw.getD (7 + l.val) 0).testBit t.val = true) ∧
      (∀ p : Fin 7, (∀ l : Fin 7, ([b0, b1, b2, b3, b4, b5, b6].getD l.val false) = true →
        (p.val + 7 - l.val) % 7 ∉ ([0, 1, 3] : List ℕ)) →
        (raw.getD p.val 0).testBit t.val = true) := by
    decide +kernel
  have hCcol (t : Fin 58) :
      C.eval (List.ofFn fun i : Fin 14 => (raw.getD i.val 0).testBit t.val) = decide (t.val < 21) := by
    change (C.wires (List.ofFn fun i : Fin 14 => (raw.getD i.val 0).testBit t.val)).getD (14 + k) false = _
    rw [hcolMatch ⟨t.val, by omega⟩ (14 + k) (by omega), hwireK]
  have hCfano : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x
    constructor
    · intro hx
      by_contra hno
      obtain ⟨t, ht21, hL, hP⟩ := hT3 (x (Fin.natAdd 7 (0 : Fin 7))) (x (Fin.natAdd 7 (1 : Fin 7)))
        (x (Fin.natAdd 7 (2 : Fin 7))) (x (Fin.natAdd 7 (3 : Fin 7))) (x (Fin.natAdd 7 (4 : Fin 7)))
        (x (Fin.natAdd 7 (5 : Fin 7))) (x (Fin.natAdd 7 (6 : Fin 7)))
      have hgetL (l : Fin 7) :
          ([x (Fin.natAdd 7 (0 : Fin 7)), x (Fin.natAdd 7 (1 : Fin 7)), x (Fin.natAdd 7 (2 : Fin 7)),
            x (Fin.natAdd 7 (3 : Fin 7)), x (Fin.natAdd 7 (4 : Fin 7)), x (Fin.natAdd 7 (5 : Fin 7)),
            x (Fin.natAdd 7 (6 : Fin 7))].getD l.val false) =
            x (Fin.natAdd 7 l) := by
        rcases l with ⟨l, hl⟩
        rcases l with _ | _ | _ | _ | _ | _ | _ | l
        all_goals first | rfl | omega
      have hle : x ≤ (fun i : Fin 14 => (raw.getD i.val 0).testBit t.val) := by
        intro i
        refine Fin.addCases (m := 7) (n := 7)
          (motive := fun i => x i ≤ (raw.getD i.val 0).testBit t.val) ?_ ?_ i
        · intro p
          rw [Bool.le_iff_imp]
          intro hp
          exact hP p (fun l hl hinc => hno ⟨p, l, (hfanoMem p l).2 hinc, hp, (hgetL l) ▸ hl⟩)
        · intro l
          rw [Bool.le_iff_imp]
          intro hl
          have h7 : (Fin.natAdd 7 l).val = 7 + l.val := rfl
          rw [h7]
          exact hL l ((hgetL l).symm ▸ hl)
      have h1 := hCevalMono hle
      dsimp only at h1
      rw [hx, hCcol t, decide_eq_false (by omega)] at h1
      exact absurd h1 (by decide)
    · rintro ⟨p, l, hinc, hp, hl⟩
      obtain ⟨t, ht, hsub⟩ := hT2 p l ((hfanoMem p l).1 hinc)
      have hle : (fun i : Fin 14 => (raw.getD i.val 0).testBit t.val) ≤ x := by
        intro i
        rw [Bool.le_iff_imp]
        intro hi
        rcases hsub i hi with rfl | rfl
        · exact hp
        · exact hl
      have h1 := hCevalMono hle
      dsimp only at h1
      rw [hCcol t, decide_eq_true ht] at h1
      exact Bool.eq_true_of_true_le h1
  have hCfun : PEqualNP.MetaComplexity.circuitFun 14 C =
      (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
    funext x
    change C.eval (List.ofFn x) = _
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hCfano x
  have h27 : 27 ≤ C.size := size26 C hCmono hCfano
  have hk26 : k = 26 := by omega
  have hCsize27 : C.size = 27 := by omega
  have hCout40 : C.output = 40 := by dsimp [C]; omega
  let x07List : List Bool := (List.range 14).map (fun i => i == 0 || i == 7)
  let lpStep : List (Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate → Bool × Bool :=
    fun w g =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
        (ins.foldl (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
        (ins.any (·.1), ins.any (·.2))
        (false, false)
        (fun _ => (false, false))
        (false, false)
  have hlpFold (isLine : ℕ → Bool) (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      PEqualNP.ReadK.linearParts ⟨gs, 0⟩ isLine x =
        gs.foldl (fun w g => w ++ [lpStep w g])
          ((x.zipIdx).map fun p => if isLine p.2 then (false, p.1) else (p.1, false)) := by
    induction gs using List.reverseRecOn with
    | nil =>
      dsimp only [PEqualNP.ReadK.linearParts]
      apply List.map_congr_left
      intro p _
      rcases p with ⟨b, i⟩
      rfl
    | append_singleton gs g ih =>
      dsimp only [PEqualNP.ReadK.linearParts] at ih ⊢
      rw [List.foldl_append, ih, List.foldl_append]
      rcases g with ⟨op, ins⟩
      cases op <;> rfl
  have hlpMatch (isLine : ℕ → Bool) (c0 c1 : Fin 62)
      (hinit : ∀ i : Fin 14,
        ((x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))).getD i.val (false, false) =
          ((raw.getD i.val 0).testBit c0.val, (raw.getD i.val 0).testBit c1.val))
      (hand0 : ∀ j < k + 1, gisOr j = false →
        wire (14 + j) c0 = (wire (ga j) c0 && wire (gb j) c0))
      (hand1 : ∀ j < k + 1, gisOr j = false →
        wire (14 + j) c1 = ((wire (ga j) c0 && wire (gb j) c1) || (wire (ga j) c1 && wire (gb j) c0))) :
      ∀ w < 14 + (k + 1),
        (PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false) = (wire w c0, wire w c1) := by
    let lpInit : List (Bool × Bool) :=
      (x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))
    have hlpLen : lpInit.length = 14 := by simp [lpInit, x07List]
    have hlpC : PEqualNP.ReadK.linearParts C isLine x07List =
        C.gates.foldl (fun w g => w ++ [lpStep w g]) lpInit := hlpFold isLine x07List C.gates
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rw [hlpC]
      by_cases h14 : w < 14
      · rw [foldKeep (false, false) lpStep C.gates lpInit w (by omega)]
        rw [hinit ⟨w, h14⟩, hwireIn w h14 c0, hwireIn w h14 c1]
      · have hj : w - 14 < k + 1 := by omega
        have hj' : w - 14 < C.gates.length := hCglen ▸ hj
        have heq : 14 + (w - 14) = w := by omega
        have hStep := foldStep (false, false) lpStep C.gates lpInit (w - 14) hj'
        rw [hlpLen, heq] at hStep
        rw [hStep]
        have hgj : C.gates[w - 14] = mkGate (w - 14) := by
          have hga := hgateAt (w - 14) hj
          change C.gates.getD (w - 14) _ = mkGate (w - 14) at hga
          rw [List.getD_eq_getElem _ _ hj'] at hga
          exact hga
        obtain ⟨_, ha, hb, _, heval⟩ := hrule (w - 14) (by omega)
        have ha' := foldTake (false, false) lpStep C.gates lpInit (w - 14) (ga (w - 14))
          (Nat.le_of_lt hj') (by omega)
        have hb' := foldTake (false, false) lpStep C.gates lpInit (w - 14) (gb (w - 14))
          (Nat.le_of_lt hj') (by omega)
        rw [hgj]
        dsimp only [lpStep]
        rw [List.map_cons, List.map_cons, List.map_nil, ha', hb']
        have iha : (C.gates.foldl (fun w g => w ++ [lpStep w g]) lpInit).getD (ga (w - 14)) (false, false) =
            (wire (ga (w - 14)) c0, wire (ga (w - 14)) c1) := by
          rw [← hlpC]; exact ih (ga (w - 14)) (by omega) (by omega)
        have ihb : (C.gates.foldl (fun w g => w ++ [lpStep w g]) lpInit).getD (gb (w - 14)) (false, false) =
            (wire (gb (w - 14)) c0, wire (gb (w - 14)) c1) := by
          rw [← hlpC]; exact ih (gb (w - 14)) (by omega) (by omega)
        rw [iha, ihb]
        cases h : gisOr (w - 14)
        · simp only [mkGate, h, Bool.false_eq_true, ite_false, List.foldl_cons, List.foldl_nil,
            Bool.true_and, Bool.false_and, Bool.or_false]
          have h0 := hand0 (w - 14) hj h
          have h1 := hand1 (w - 14) hj h
          rw [heq] at h0 h1
          exact Prod.ext h0.symm h1.symm
        · simp only [mkGate, h, ite_true, List.any_cons, List.any_nil, Bool.or_false]
          have h0 := heval c0
          have h1 := heval c1
          simp only [h, ite_true, heq] at h0 h1
          exact Prod.ext h0.symm h1.symm
  have hlp7 : ∀ w < 14 + (k + 1),
      (PEqualNP.ReadK.linearParts C (fun i => decide (7 ≤ i)) x07List).getD w (false, false) =
        (wire w 58, wire w 60) := by
    apply hlpMatch (fun i => decide (7 ≤ i)) 58 60
    · decide
    · intro j hj h
      have hv := (hrule j (by omega)).2.2.2.2 58
      simpa [h] using hv
    · intro j hj h
      have hv := (hrule j (by omega)).2.2.2.2 60
      simpa [h] using hv
  have hlp0 : ∀ w < 14 + (k + 1),
      (PEqualNP.ReadK.linearParts C (fun i => decide (i < 7)) x07List).getD w (false, false) =
        (wire w 59, wire w 61) := by
    apply hlpMatch (fun i => decide (i < 7)) 59 61
    · decide
    · intro j hj h
      have hv := (hrule j (by omega)).2.2.2.2 59
      simpa [h] using hv
    · intro j hj h
      have hv := (hrule j (by omega)).2.2.2.2 61
      simpa [h] using hv
  have hLS7 : PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false := by
    change ((PEqualNP.ReadK.linearParts C (fun i => decide (7 ≤ i)) x07List).getD (14 + k) (false, false)).2 = false
    rw [hlp7 (14 + k) (by omega), hwireK]
    rfl
  have hLS0 : PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i < 7)) 0 7 = false := by
    change ((PEqualNP.ReadK.linearParts C (fun i => decide (i < 7)) x07List).getD (14 + k) (false, false)).2 = false
    rw [hlp0 (14 + k) (by omega), hwireK]
    rfl
  have hdegKill (marked : Finset ℕ) (isLine : ℕ → Bool)
      (hInitD : ∀ i < 14,
        (((List.range 14).map (fun u => if u ∈ marked then 1 else 0)).getD i 0 = 0 →
          x07List.getD i false =
            (((x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))).getD i (false, false)).1) ∧
        (((List.range 14).map (fun u => if u ∈ marked then 1 else 0)).getD i 0 ≤ 1 →
          x07List.getD i false = true →
            (((x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))).getD i (false, false)).1 = true ∨
            (((x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))).getD i (false, false)).2 = true))
      (hDeg : PEqualNP.CircuitLowerBounds.HasLineDegree 14 marked C 1)
      (hP0 : ((PEqualNP.ReadK.linearParts C isLine x07List).getD (14 + k) (false, false)).1 = false)
      (hP1 : ((PEqualNP.ReadK.linearParts C isLine x07List).getD (14 + k) (false, false)).2 = false) :
      False := by
    let dInit : List ℕ := (List.range 14).map (fun u => if u ∈ marked then 1 else 0)
    have hdInitLen : dInit.length = 14 := by simp [dInit]
    let lpInit : List (Bool × Bool) :=
      (x07List.zipIdx).map (fun p => if isLine p.2 then (false, p.1) else (p.1, false))
    have hlpInitLen : lpInit.length = 14 := by simp [lpInit, x07List]
    have hlpC : PEqualNP.ReadK.linearParts C isLine x07List =
        C.gates.foldl (fun w g => w ++ [lpStep w g]) lpInit := hlpFold isLine x07List C.gates
    have hx07Len : x07List.length = 14 := by simp [x07List]
    have hInv : ∀ w < 14 + (k + 1),
        ((C.lineDegrees 14 marked).getD w 0 = 0 →
          (C.wires x07List).getD w false = ((PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false)).1) ∧
        ((C.lineDegrees 14 marked).getD w 0 ≤ 1 →
          (C.wires x07List).getD w false = true →
            ((PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false)).1 = true ∨
            ((PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false)).2 = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases h14 : w < 14
        · have hdw : (C.lineDegrees 14 marked).getD w 0 = dInit.getD w 0 :=
            foldKeep 0 (fun d g => g.lineDegree d) C.gates dInit w (by omega)
          have hww : (C.wires x07List).getD w false = x07List.getD w false :=
            foldKeep false _ C.gates x07List w (by omega)
          have hlw : (PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false) =
              lpInit.getD w (false, false) := by
            rw [hlpC]; exact foldKeep (false, false) lpStep C.gates lpInit w (by omega)
          rw [hdw, hww, hlw]
          exact hInitD w h14
        · have hj : w - 14 < k + 1 := by omega
          have hj' : w - 14 < C.gates.length := hCglen ▸ hj
          have heq : 14 + (w - 14) = w := by omega
          have hgj : C.gates[w - 14] = mkGate (w - 14) := by
            have hga := hgateAt (w - 14) hj
            change C.gates.getD (w - 14) _ = mkGate (w - 14) at hga
            rw [List.getD_eq_getElem _ _ hj'] at hga
            exact hga
          obtain ⟨_, ha, hb, _, _⟩ := hrule (w - 14) (by omega)
          have hdw : (C.lineDegrees 14 marked).getD w 0 =
              if gisOr (w - 14) then
                max ((C.lineDegrees 14 marked).getD (ga (w - 14)) 0) ((C.lineDegrees 14 marked).getD (gb (w - 14)) 0)
              else
                (C.lineDegrees 14 marked).getD (ga (w - 14)) 0 + (C.lineDegrees 14 marked).getD (gb (w - 14)) 0 := by
            have hStep := foldStep 0 (fun d g => g.lineDegree d) C.gates dInit (w - 14) hj'
            rw [hdInitLen, heq] at hStep
            change (C.gates.foldl (fun d g => d ++ [g.lineDegree d]) dInit).getD w 0 = _
            rw [hStep, hgj]
            have ha' := foldTake 0 (fun d g => g.lineDegree d) C.gates dInit (w - 14) (ga (w - 14))
              (Nat.le_of_lt hj') (by omega)
            have hb' := foldTake 0 (fun d g => g.lineDegree d) C.gates dInit (w - 14) (gb (w - 14))
              (Nat.le_of_lt hj') (by omega)
            have hld : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (a b : ℕ) (d : List ℕ),
                (PEqualNP.CircuitLowerBounds.Gate.mk op [a, b]).lineDegree d =
                  if op = PEqualNP.CircuitLowerBounds.GateOp.and then d.getD a 0 + d.getD b 0
                  else max (d.getD a 0) (d.getD b 0) := by
              intro op a b d
              cases op
              · change d.getD a 0 + (d.getD b 0 + 0) = _; simp
              · change max (d.getD a 0) (max (d.getD b 0) 0) = _; simp
              · change max (d.getD a 0) (max (d.getD b 0) 0) = _; simp
              · change max (d.getD a 0) (max (d.getD b 0) 0) = _; simp
              · change max (d.getD a 0) (max (d.getD b 0) 0) = _; simp
            dsimp only [mkGate]
            rw [hld, ha', hb']
            cases gisOr (w - 14)
            · simp only [Bool.false_eq_true, ite_false, ite_true]; rfl
            · simp only [ite_true, reduceCtorEq, ite_false]; rfl
          have hww : (C.wires x07List).getD w false =
              if gisOr (w - 14) then (C.wires x07List).getD (ga (w - 14)) false || (C.wires x07List).getD (gb (w - 14)) false
              else (C.wires x07List).getD (ga (w - 14)) false && (C.wires x07List).getD (gb (w - 14)) false := by
            have hS := hwireStep x07List hx07Len (w - 14) hj
            rwa [heq] at hS
          have hlw : (PEqualNP.ReadK.linearParts C isLine x07List).getD w (false, false) =
              let pa := (PEqualNP.ReadK.linearParts C isLine x07List).getD (ga (w - 14)) (false, false)
              let pb := (PEqualNP.ReadK.linearParts C isLine x07List).getD (gb (w - 14)) (false, false)
              if gisOr (w - 14) then (pa.1 || pb.1, pa.2 || pb.2)
              else (pa.1 && pb.1, (pa.1 && pb.2) || (pa.2 && pb.1)) := by
            rw [hlpC]
            have hStep := foldStep (false, false) lpStep C.gates lpInit (w - 14) hj'
            rw [hlpInitLen, heq] at hStep
            rw [hStep, hgj]
            have ha' := foldTake (false, false) lpStep C.gates lpInit (w - 14) (ga (w - 14))
              (Nat.le_of_lt hj') (by omega)
            have hb' := foldTake (false, false) lpStep C.gates lpInit (w - 14) (gb (w - 14))
              (Nat.le_of_lt hj') (by omega)
            dsimp only [lpStep]
            rw [List.map_cons, List.map_cons, List.map_nil, ha', hb']
            cases h : gisOr (w - 14)
            · simp only [mkGate, h, Bool.false_eq_true, ite_false, List.foldl_cons, List.foldl_nil,
                Bool.true_and, Bool.false_and, Bool.or_false]
              rfl
            · simp only [mkGate, h, ite_true, List.any_cons, List.any_nil, Bool.or_false]
              rfl
          obtain ⟨iha0, iha1⟩ := ih (ga (w - 14)) (by omega) (by omega)
          obtain ⟨ihb0, ihb1⟩ := ih (gb (w - 14)) (by omega) (by omega)
          rw [hdw, hww, hlw]
          dsimp only
          cases h : gisOr (w - 14)
          · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true]
            constructor
            · intro hd0
              rw [iha0 (by omega), ihb0 (by omega)]
            · intro hd1 hv
              have hva := hv.1
              have hvb := hv.2
              by_cases hda : (C.lineDegrees 14 marked).getD (ga (w - 14)) 0 = 0
              · have hpa : ((PEqualNP.ReadK.linearParts C isLine x07List).getD (ga (w - 14)) (false, false)).1 = true := by
                  rw [← iha0 hda, hva]
                rcases ihb1 (by omega) hvb with hpb | hpb
                · left; exact ⟨hpa, hpb⟩
                · right; rw [hpa, hpb]; simp
              · have hdb : (C.lineDegrees 14 marked).getD (gb (w - 14)) 0 = 0 := by omega
                have hpb : ((PEqualNP.ReadK.linearParts C isLine x07List).getD (gb (w - 14)) (false, false)).1 = true := by
                  rw [← ihb0 hdb, hvb]
                rcases iha1 (by omega) hva with hpa | hpa
                · left; exact ⟨hpa, hpb⟩
                · right; rw [hpa, hpb]; simp
          · simp only [ite_true, Bool.or_eq_true]
            constructor
            · intro hd0
              have hda : (C.lineDegrees 14 marked).getD (ga (w - 14)) 0 = 0 := by omega
              have hdb : (C.lineDegrees 14 marked).getD (gb (w - 14)) 0 = 0 := by omega
              rw [iha0 hda, ihb0 hdb]
            · intro hd1 hv
              have hda : (C.lineDegrees 14 marked).getD (ga (w - 14)) 0 ≤ 1 := by omega
              have hdb : (C.lineDegrees 14 marked).getD (gb (w - 14)) 0 ≤ 1 := by omega
              rcases hv with hva | hvb
              · rcases iha1 hda hva with h1 | h2
                · left; left; exact h1
                · right; left; exact h2
              · rcases ihb1 hdb hvb with h1 | h2
                · left; right; exact h1
                · right; right; exact h2
    have hx07Eq : x07List = List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7) ∨ i = Fin.natAdd 7 (0 : Fin 7))) := by
      decide
    have hval07 : (C.wires x07List).getD (14 + k) false = true := by
      rw [hx07Eq]
      exact (hCfano _).2 ⟨0, 0, by decide, by decide, by decide⟩
    rcases (hInv (14 + k) (by omega)).2 hDeg hval07 with h1 | h2
    · rw [hP0] at h1; exact Bool.noConfusion h1
    · rw [hP1] at h2; exact Bool.noConfusion h2
  have hDeg7False : ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 14 {7} C 1 := by
    intro hDeg
    apply hdegKill {7} (fun i => decide (7 ≤ i)) _ hDeg
    · rw [hlp7 (14 + k) (by omega), hwireK]; rfl
    · rw [hlp7 (14 + k) (by omega), hwireK]; rfl
    · intro i hi
      have hfin : ∀ u : Fin 14,
          (((List.range 14).map (fun v => if v ∈ ({7} : Finset ℕ) then 1 else 0)).getD u.val 0 = 0 →
            x07List.getD u.val false =
              (((x07List.zipIdx).map (fun p => if decide (7 ≤ p.2) then (false, p.1) else (p.1, false))).getD u.val (false, false)).1) ∧
          (((List.range 14).map (fun v => if v ∈ ({7} : Finset ℕ) then 1 else 0)).getD u.val 0 ≤ 1 →
            x07List.getD u.val false = true →
              (((x07List.zipIdx).map (fun p => if decide (7 ≤ p.2) then (false, p.1) else (p.1, false))).getD u.val (false, false)).1 = true ∨
              (((x07List.zipIdx).map (fun p => if decide (7 ≤ p.2) then (false, p.1) else (p.1, false))).getD u.val (false, false)).2 = true) := by
        decide
      exact hfin ⟨i, hi⟩
  have hDeg0False : ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 14 {0} C 1 := by
    intro hDeg
    apply hdegKill {0} (fun i => decide (i < 7)) _ hDeg
    · rw [hlp0 (14 + k) (by omega), hwireK]; rfl
    · rw [hlp0 (14 + k) (by omega), hwireK]; rfl
    · intro i hi
      have hfin : ∀ u : Fin 14,
          (((List.range 14).map (fun v => if v ∈ ({0} : Finset ℕ) then 1 else 0)).getD u.val 0 = 0 →
            x07List.getD u.val false =
              (((x07List.zipIdx).map (fun p => if decide (p.2 < 7) then (false, p.1) else (p.1, false))).getD u.val (false, false)).1) ∧
          (((List.range 14).map (fun v => if v ∈ ({0} : Finset ℕ) then 1 else 0)).getD u.val 0 ≤ 1 →
            x07List.getD u.val false = true →
              (((x07List.zipIdx).map (fun p => if decide (p.2 < 7) then (false, p.1) else (p.1, false))).getD u.val (false, false)).1 = true ∨
              (((x07List.zipIdx).map (fun p => if decide (p.2 < 7) then (false, p.1) else (p.1, false))).getD u.val (false, false)).2 = true) := by
        decide
      exact hfin ⟨i, hi⟩
  by_cases hnd : ((C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
  · have hndOut : ((C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter
        (fun w => decide (14 ≤ w))).Nodup := by
      have h40 : decide (14 ≤ C.output) = true := by rw [hCout40]; decide
      simp only [List.filter_cons, h40, ite_true, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hmem40
      rw [List.mem_filter, List.mem_flatMap] at hmem40
      obtain ⟨⟨g, hg, h40in⟩, _⟩ := hmem40
      obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
      have hlt : C.output < 14 + j := by
        have hrb := hCAO2.2.1 j hj C.output
        change C.output ∈ (C.gates.getD j _).inputs → C.output < 14 + j at hrb
        rw [List.getD_eq_getElem _ _ hj, hgj] at hrb
        exact hrb h40in
      omega
    rcases formula C (by omega) hCAO2 hCNodup hCfun hndOut with h0 | h7
    · exact hDeg0False h0
    · exact hDeg7False h7
  · exact sharedDag C hCsize27 hCout40 hCAO2 (by simpa [hCglen, hk26] using hCNodup) hOp0 hCfun hnd hLS7 hLS0
