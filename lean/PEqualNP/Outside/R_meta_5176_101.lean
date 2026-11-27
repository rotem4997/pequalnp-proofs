import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5176_101
    (smallSize : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s0 s1 : ℕ → Bool),
      1 ≤ C.size → C.size ≤ 63 → C.output = 25 + C.size →
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 < g.inputs.getD 1 0) →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      (have w : ℕ → ℕ → Bool := fun m k => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      (∀ i < 26, s0 i = !(25034751 : ℕ).testBit i ∧ s1 i = !(67108341 : ℕ).testBit i) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s0 (26 + j) = (s0 a && s0 b) ∧ s1 (26 + j) = (s1 a && s1 b)) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          s0 (26 + j) = (s0 a || s0 b || (!(w 1 a) && !(w 1 b) && !(w 8191 (26 + j)) && !(w 25018369 (26 + j)))) ∧
          s1 (26 + j) = (s1 a || s1 b || (!(w 8192 a) && !(w 8192 b) && !(w 67100672 (26 + j)) && !(w 15860 (26 + j)))))) →
      s0 (25 + C.size) = true → s1 (25 + C.size) = true → False))
    (size64LastAnd : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s0 s1 : ℕ → Bool),
      C.size = 64 → C.output = 89 →
      (∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[63]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ k < 63, (PEqualNP.TopForm.readers 26 C k).Nonempty) →
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 < g.inputs.getD 1 0) →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      (have w : ℕ → ℕ → Bool := fun m k => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      (∀ i < 26, s0 i = !(25034751 : ℕ).testBit i ∧ s1 i = !(67108341 : ℕ).testBit i) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s0 (26 + j) = (s0 a && s0 b) ∧ s1 (26 + j) = (s1 a && s1 b)) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          s0 (26 + j) = (s0 a || s0 b || (!(w 1 a) && !(w 1 b) && !(w 8191 (26 + j)) && !(w 25018369 (26 + j)))) ∧
          s1 (26 + j) = (s1 a || s1 b || (!(w 8192 a) && !(w 8192 b) && !(w 67100672 (26 + j)) && !(w 15860 (26 + j)))))) →
      s0 89 = true → s1 89 = true → False))
    (size64LastOr : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s0 s1 : ℕ → Bool),
      C.size = 64 → C.output = 89 →
      (∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[63]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ k < 63, (PEqualNP.TopForm.readers 26 C k).Nonempty) →
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 < g.inputs.getD 1 0) →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      (have w : ℕ → ℕ → Bool := fun m k => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      (∀ i < 26, s0 i = !(25034751 : ℕ).testBit i ∧ s1 i = !(67108341 : ℕ).testBit i) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s0 (26 + j) = (s0 a && s0 b) ∧ s1 (26 + j) = (s1 a && s1 b)) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          s0 (26 + j) = (s0 a || s0 b || (!(w 1 a) && !(w 1 b) && !(w 8191 (26 + j)) && !(w 25018369 (26 + j)))) ∧
          s1 (26 + j) = (s1 a || s1 b || (!(w 8192 a) && !(w 8192 b) && !(w 67100672 (26 + j)) && !(w 15860 (26 + j)))))) →
      s0 89 = true → s1 89 = true → False)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size → x1.size ≤ (64 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false; ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)], have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ); have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ); have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ); ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
  classical
  dsimp only
  intro C h63 h64 hAO hNodup hSpec
  have hOps := hAO.1
  have hRB := hAO.2.1
  have hLen2 := hAO.2.2
  let dGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs.foldl step u).length = u.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro u; rfl
    | cons g gs ih =>
      intro u
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have wires_append : ∀ (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs₁ ++ gs₂).foldl step u = gs₂.foldl step (gs₁.foldl step u) := by
    intro gs₁ gs₂ u; exact List.foldl_append
  have wires_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length → (gs.foldl step u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u i _; rfl
    | cons g gs ih =>
      intro u i hi
      rw [List.foldl_cons, ih]
      · dsimp only [step]; rw [List.getD_append _ _ _ _ hi]
      · simp [step]; omega
  have wires_take : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length + (gs.take n).length →
      ((gs.take n).foldl step u).getD i false = (gs.foldl step u).getD i false := by
    intro n gs u i hi
    conv_rhs =>
      rw [← List.take_append_drop n gs, wires_append,
        wires_prefix _ _ _ (by rw [wires_len]; exact hi)]
  have list_len2 : ∀ l : List ℕ, l.length = 2 → l = [l.getD 0 0, l.getD 1 0] := by
    intro l hl
    cases l with
    | nil => simp at hl
    | cons x xs =>
      cases xs with
      | nil => simp at hl
      | cons y ys =>
        cases ys with
        | nil => rfl
        | cons z zs => simp at hl
  have hOutBd : 26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
    constructor
    · by_contra hlt26
      have hlt : C.output < 26 := by omega
      let q : Fin 13 := ⟨(if C.output < 13 then C.output + 1 else C.output - 13 + 1) % 13,
        Nat.mod_lt (if C.output < 13 then C.output + 1 else C.output - 13 + 1) (by decide : 0 < 13)⟩
      let z : Fin 26 → Bool := fun i =>
        if i.val < 13 then decide (i.val = q.val) else decide (i.val = 13 + q.val)
      have hzTrue : C.eval (List.ofFn z) = true := by
        refine (hSpec z).mpr ⟨q, q, Or.inl rfl, ?_, ?_⟩
        · dsimp only [z]
          change (if q.val < 13 then decide (q.val = q.val) else decide (q.val = 13 + q.val)) = true
          simp [q.isLt]
        · dsimp only [z]
          change (if 13 + q.val < 13 then decide (13 + q.val = q.val) else decide (13 + q.val = 13 + q.val)) = true
          simp [show ¬ 13 + q.val < 13 by omega]
      change (C.gates.foldl step (List.ofFn z)).getD C.output false = true at hzTrue
      rw [wires_prefix _ _ _ (by simp [hlt])] at hzTrue
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hzTrue
      dsimp only [z] at hzTrue
      by_cases h13 : C.output < 13
      · simp only [h13, ↓reduceIte, decide_eq_true_eq] at hzTrue
        dsimp only [q] at hzTrue
        simp only [h13, ↓reduceIte] at hzTrue
        omega
      · simp only [h13, ↓reduceIte, decide_eq_true_eq] at hzTrue
        dsimp only [q] at hzTrue
        simp only [h13, ↓reduceIte] at hzTrue
        omega
    · by_contra hge
      let z : Fin 26 → Bool := fun _ => true
      have hzTrue : C.eval (List.ofFn z) = true :=
        (hSpec z).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
      have hle : (C.gates.foldl step (List.ofFn z)).length ≤ C.output := by
        rw [wires_len]; simp; omega
      change (C.gates.foldl step (List.ofFn z)).getD C.output false = true at hzTrue
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] at hzTrue
      cases hzTrue
  let sortGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if a ≤ b then ⟨g.op, [a, b]⟩ else ⟨g.op, [b, a]⟩
  let C1 : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨(C.gates.take (C.output - 25)).map sortGate, C.output⟩
  have hC1Len : C1.gates.length = C.output - 25 := by
    dsimp only [C1]
    rw [List.length_map, List.length_take]
    omega
  have hC1Sz1 : 1 ≤ C1.size := by change 1 ≤ C1.gates.length; omega
  have hC1Sz64 : C1.size ≤ 64 := by
    change C1.gates.length ≤ 64
    change C.gates.length ≤ 64 at h64
    omega
  have hC1Out : C1.output = 25 + C1.size := by
    change C.output = 25 + C1.gates.length
    omega
  have hC1Wf : ∀ j < C1.gates.length,
      let g := C1.gates.getD j dGate
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ∃ a b, a < b ∧ b < 26 + j ∧ g.inputs = [a, b] := by
    intro j hj
    have hjC : j < C.gates.length := by omega
    have hjTake : j < C.output - 25 := by omega
    have hgj : C1.gates.getD j dGate = sortGate (C.gates.getD j dGate) := by
      dsimp only [C1]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_take_of_lt hjTake, List.getElem?_eq_getElem hjC,
        List.getD_eq_getElem _ _ hjC]
      rfl
    have hgMem : C.gates.getD j dGate ∈ C.gates := by
      rw [List.getD_eq_getElem _ _ hjC]; exact List.getElem_mem hjC
    have hgOp0 : (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      simpa using hOps _ hgMem
    have hgLen0 : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hgMem
    have hgNodup : (C.gates.getD j dGate).inputs.Nodup := hNodup _ hgMem
    have hgEq : (C.gates.getD j dGate).inputs =
        [(C.gates.getD j dGate).inputs.getD 0 0, (C.gates.getD j dGate).inputs.getD 1 0] :=
      list_len2 _ hgLen0
    let a0 := (C.gates.getD j dGate).inputs.getD 0 0
    let b0 := (C.gates.getD j dGate).inputs.getD 1 0
    have ha0Lt : a0 < 26 + j := hRB j hjC a0 (by change a0 ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [a0])
    have hb0Lt : b0 < 26 + j := hRB j hjC b0 (by change b0 ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [b0])
    have habNe : a0 ≠ b0 := by
      intro hab
      rw [hgEq] at hgNodup
      exact (List.nodup_cons.mp hgNodup).1 (by rw [List.mem_singleton]; exact hab)
    rw [hgj]
    dsimp only [sortGate]
    by_cases hle : a0 ≤ b0
    · have hle' : (C.gates.getD j dGate).inputs.getD 0 0 ≤ (C.gates.getD j dGate).inputs.getD 1 0 := hle
      simp only [hle', ↓reduceIte]
      exact ⟨hgOp0, a0, b0, by omega, hb0Lt, rfl⟩
    · have hle' : ¬ (C.gates.getD j dGate).inputs.getD 0 0 ≤ (C.gates.getD j dGate).inputs.getD 1 0 := hle
      simp only [hle', ↓reduceIte]
      exact ⟨hgOp0, b0, a0, by omega, ha0Lt, rfl⟩
  have hC1Fold : ∀ (y : List Bool) (k : ℕ), k ≤ C1.gates.length →
      (C1.gates.take k).foldl step y = (C.gates.take k).foldl step y := by
    intro y k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hk1 : k ≤ C1.gates.length := Nat.le_of_succ_le hk
      have hkC : k < C.gates.length := by omega
      have hkTake : k < C.output - 25 := by omega
      have hk1C : k + 1 ≤ C.gates.length := by omega
      have hTakeC1 : C1.gates.take (k + 1) = C1.gates.take k ++ [C1.gates.getD k dGate] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.getD_eq_getElem _ _ (by omega)]
      have hTakeC : C.gates.take (k + 1) = C.gates.take k ++ [C.gates.getD k dGate] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkC, Option.toList_some,
          List.getD_eq_getElem _ _ hkC]
      rw [hTakeC1, hTakeC, wires_append, wires_append, ih hk1]
      have hgk : C1.gates.getD k dGate = sortGate (C.gates.getD k dGate) := by
        dsimp only [C1]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_take_of_lt hkTake, List.getElem?_eq_getElem hkC,
          List.getD_eq_getElem _ _ hkC]
        rfl
      rw [hgk]
      have hgMem : C.gates.getD k dGate ∈ C.gates := by
        rw [List.getD_eq_getElem _ _ hkC]; exact List.getElem_mem hkC
      have hgOp0 : (C.gates.getD k dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.getD k dGate).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        simpa using hOps _ hgMem
      have hgLen0 : (C.gates.getD k dGate).inputs.length = 2 := hLen2 _ hgMem
      have hgEq : (C.gates.getD k dGate).inputs =
          [(C.gates.getD k dGate).inputs.getD 0 0, (C.gates.getD k dGate).inputs.getD 1 0] :=
        list_len2 _ hgLen0
      dsimp only [sortGate, step]
      generalize (List.foldl step y (List.take k C.gates)) = u
      simp only [List.foldl_cons, List.foldl_nil]
      split_ifs
      · conv_rhs => rw [hgEq]
      · conv_rhs => rw [hgEq]
        simp only [List.map_cons, List.map_nil]
        rcases hgOp0 with hand | hor
        · rw [hand]
          have hAndComm : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [b1, b2] =
              PEqualNP.CircuitLowerBounds.GateOp.and.eval [b2, b1] := by
            intro b1 b2; cases b1 <;> cases b2 <;> rfl
          rw [hAndComm]
        · rw [hor]
          have hOrComm : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [b1, b2] =
              PEqualNP.CircuitLowerBounds.GateOp.or.eval [b2, b1] := by
            intro b1 b2; cases b1 <;> cases b2 <;> rfl
          rw [hOrComm]
  have hC1Wires : ∀ (y : List Bool) (i : ℕ), y.length = 26 → i < 26 + C1.size →
      (C1.wires y).getD i false = (C.wires y).getD i false := by
    intro y i hy hi
    change i < 26 + C1.gates.length at hi
    change (C1.gates.foldl step y).getD i false = (C.gates.foldl step y).getD i false
    have hf := hC1Fold y C1.gates.length le_rfl
    rw [List.take_of_length_le le_rfl] at hf
    rw [hf]
    exact wires_take C1.gates.length C.gates y i (by rw [hy, List.length_take]; omega)
  have hC1Spec : ∀ z : Fin 26 → Bool, C1.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true := by
    intro z
    have hev : C1.eval (List.ofFn z) = C.eval (List.ofFn z) := by
      change (C1.wires (List.ofFn z)).getD C1.output false = (C.wires (List.ofFn z)).getD C.output false
      exact hC1Wires (List.ofFn z) C.output (by simp) (by change C.output < 26 + C1.gates.length; omega)
    rw [hev]
    exact hSpec z
  let sStep : List Bool → List Bool → List Bool → List Bool →
      PEqualNP.CircuitLowerBounds.Gate → List Bool := fun wb wx wy s g =>
    let a := g.inputs.getD 0 0
    let c := g.inputs.getD 1 0
    let cur := s.length
    s ++ [PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
      ((s.getD a false || s.getD c false) ||
        (!(wb.getD a false) && !(wb.getD c false) && !(wx.getD cur false) && !(wy.getD cur false)))
      (s.getD a false && s.getD c false)
      false (fun _ => false) false]
  let sMax : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool := fun E b =>
    let u := if b = 0 then 25034751 else 67108341
    let x := if b = 0 then 8191 else 67100672
    let y := if b = 0 then 25018369 else 15860
    let row (m : ℕ) : List Bool := List.ofFn fun i : Fin 26 => m.testBit i.val
    let s0 : List Bool := List.ofFn fun i : Fin 26 => !(u.testBit i.val)
    E.gates.foldl (sStep (E.wires (row (2 ^ b))) (E.wires (row x)) (E.wires (row y))) s0
  have s_len : ∀ (wb wx wy : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs.foldl (sStep wb wx wy) u).length = u.length + gs.length := by
    intro wb wx wy gs
    induction gs with
    | nil => intro u; rfl
    | cons g gs ih =>
      intro u
      rw [List.foldl_cons, ih]
      simp [sStep]; omega
  have s_append : ∀ (wb wx wy : List Bool) (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs₁ ++ gs₂).foldl (sStep wb wx wy) u = gs₂.foldl (sStep wb wx wy) (gs₁.foldl (sStep wb wx wy) u) := by
    intro wb wx wy gs₁ gs₂ u; exact List.foldl_append
  have s_prefix : ∀ (wb wx wy : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length → (gs.foldl (sStep wb wx wy) u).getD i false = u.getD i false := by
    intro wb wx wy gs
    induction gs with
    | nil => intro u i _; rfl
    | cons g gs ih =>
      intro u i hi
      rw [List.foldl_cons, ih]
      · dsimp only [sStep]; rw [List.getD_append _ _ _ _ hi]
      · simp [sStep]; omega
  have s_take : ∀ (wb wx wy : List Bool) (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length + (gs.take n).length →
      ((gs.take n).foldl (sStep wb wx wy) u).getD i false = (gs.foldl (sStep wb wx wy) u).getD i false := by
    intro wb wx wy n gs u i hi
    conv_rhs =>
      rw [← List.take_append_drop n gs, s_append,
        s_prefix _ _ _ _ _ _ (by rw [s_len]; exact hi)]
  have s_gate_eq : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (b j : ℕ),
      j < E.gates.length →
      (∀ i ∈ (E.gates.getD j dGate).inputs, i < 26 + j) →
      let u := if b = 0 then 25034751 else 67108341
      let x := if b = 0 then 8191 else 67100672
      let y := if b = 0 then 25018369 else 15860
      let w : ℕ → ℕ → Bool := fun m k => (E.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      let s := fun k => (sMax E b).getD k false
      let g := E.gates.getD j dGate
      let a := g.inputs.getD 0 0
      let c := g.inputs.getD 1 0
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s (26 + j) = (s a && s c)) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        s (26 + j) = (s a || s c || (!(w (2 ^ b) a) && !(w (2 ^ b) c) && !(w x (26 + j)) && !(w y (26 + j))))) := by
    intro E b j hj hbd
    dsimp only
    let u0 := if b = 0 then 25034751 else 67108341
    let x0 := if b = 0 then 8191 else 67100672
    let y0 := if b = 0 then 25018369 else 15860
    let row (m : ℕ) : List Bool := List.ofFn fun i : Fin 26 => m.testBit i.val
    let wb := E.wires (row (2 ^ b))
    let wx := E.wires (row x0)
    let wy := E.wires (row y0)
    let sInit : List Bool := List.ofFn fun i : Fin 26 => !(u0.testBit i.val)
    let pref := (E.gates.take j).foldl (sStep wb wx wy) sInit
    have hpreLen : pref.length = 26 + j := by
      dsimp only [pref]; rw [s_len, List.length_take]; simp [sInit]; omega
    have hstepLen : (sStep wb wx wy pref (E.gates.getD j dGate)).length = 26 + j + 1 := by
      dsimp only [sStep]; rw [List.length_append, List.length_singleton, hpreLen]
    have hd : E.gates.drop j = E.gates.getD j dGate :: E.gates.drop (j + 1) := by
      rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
    have hsAt : (sMax E b).getD (26 + j) false =
        (sStep wb wx wy pref (E.gates.getD j dGate)).getD (26 + j) false := by
      change (E.gates.foldl (sStep wb wx wy) sInit).getD (26 + j) false = _
      conv_lhs => rw [← List.take_append_drop j E.gates, s_append, hd, List.foldl_cons]
      exact s_prefix wb wx wy (E.gates.drop (j + 1)) _ (26 + j) (by rw [hstepLen]; omega)
    rw [hsAt]
    dsimp only [sStep]
    rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
    have hbit : ∀ v : Bool, ([v] : List Bool).getD 0 false = v := fun _ => rfl
    rw [hbit]
    have hsPre : ∀ i, i < 26 + j → pref.getD i false = (sMax E b).getD i false := by
      intro i hi
      exact s_take wb wx wy j E.gates sInit i (by simp [sInit, List.length_take]; omega)
    constructor
    · intro hor
      rw [hor]
      dsimp only [PEqualNP.CircuitLowerBounds.GateOp.casesOn]
      have ha : (E.gates.getD j dGate).inputs.getD 0 0 < 26 + j := by
        by_cases hl : 0 < (E.gates.getD j dGate).inputs.length
        · exact hbd _ (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
      have hc : (E.gates.getD j dGate).inputs.getD 1 0 < 26 + j := by
        by_cases hl : 1 < (E.gates.getD j dGate).inputs.length
        · exact hbd _ (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
      rw [hsPre _ ha, hsPre _ hc]
    · intro hand
      rw [hand]
      dsimp only [PEqualNP.CircuitLowerBounds.GateOp.casesOn]
      have ha : (E.gates.getD j dGate).inputs.getD 0 0 < 26 + j := by
        by_cases hl : 0 < (E.gates.getD j dGate).inputs.length
        · exact hbd _ (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
      have hc : (E.gates.getD j dGate).inputs.length > 1 → (E.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
        fun hl => hbd _ (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
      have hc' : (E.gates.getD j dGate).inputs.getD 1 0 < 26 + j := by
        by_cases hl : 1 < (E.gates.getD j dGate).inputs.length
        · exact hc hl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
      rw [hsPre _ ha, hsPre _ hc']
  have s_init_eq : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (b i : ℕ), i < 26 →
      (sMax E b).getD i false = !((if b = 0 then 25034751 else 67108341 : ℕ).testBit i) := by
    intro E b i hi
    dsimp only [sMax]
    rw [s_prefix _ _ _ _ _ i (by simp [hi])]
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
  have s_props : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ j < E.gates.length,
        let g := E.gates.getD j dGate
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a c, a < c ∧ c < 26 + j ∧ g.inputs = [a, c]) →
      let w : ℕ → ℕ → Bool := fun m k => (E.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      let s0 := fun k => (sMax E 0).getD k false
      let s1 := fun k => (sMax E 13).getD k false
      (∀ i < 26, s0 i = !(25034751 : ℕ).testBit i ∧ s1 i = !(67108341 : ℕ).testBit i) ∧
      PEqualNP.TopForm.IsAO2 26 E ∧
      (∀ g ∈ E.gates, g.inputs.getD 0 0 < g.inputs.getD 1 0) ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), E.gates[j]? = some g →
        let a := g.inputs.getD 0 0
        let c := g.inputs.getD 1 0
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s0 (26 + j) = (s0 a && s0 c) ∧ s1 (26 + j) = (s1 a && s1 c)) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          s0 (26 + j) = (s0 a || s0 c || (!(w 1 a) && !(w 1 c) && !(w 8191 (26 + j)) && !(w 25018369 (26 + j)))) ∧
          s1 (26 + j) = (s1 a || s1 c || (!(w 8192 a) && !(w 8192 c) && !(w 67100672 (26 + j)) && !(w 15860 (26 + j)))))) := by
    intro E hwf
    refine ⟨fun i hi => ⟨s_init_eq E 0 i hi, s_init_eq E 13 i hi⟩, ?_, ?_, fun j g hjSome => ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        rw [← List.getD_eq_getElem _ dGate hj]
        exact (hwf j hj).1
      · intro j hj
        obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hwf j hj
        change ∀ i ∈ (E.gates.getD j dGate).inputs, i < 26 + j
        rw [hIn]; intro i hi; rcases List.mem_cons.mp hi with rfl | hm
        · omega
        · rw [List.mem_singleton.mp hm]; exact hcLt
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        rw [← List.getD_eq_getElem _ dGate hj]
        obtain ⟨_, a, c, _, _, hIn⟩ := hwf j hj
        rw [hIn]; rfl
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      rw [← List.getD_eq_getElem _ dGate hj]
      obtain ⟨_, a, c, hac, _, hIn⟩ := hwf j hj
      rw [hIn]; exact hac
    · have hjL : j < E.gates.length := (List.getElem?_eq_some_iff.mp hjSome).1
      have hgEq : E.gates.getD j dGate = g := by rw [List.getD_eq_getElem?_getD, hjSome]; rfl
      obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hwf j hjL
      have hbd : ∀ i ∈ (E.gates.getD j dGate).inputs, i < 26 + j := by
        intro i hi; rw [hIn] at hi; rcases List.mem_cons.mp hi with rfl | hmem
        · omega
        · rw [List.mem_singleton.mp hmem]; exact hcLt
      have g0 := s_gate_eq E 0 j hjL hbd
      have g1 := s_gate_eq E 13 j hjL hbd
      dsimp only at g0 g1
      simp only [↓reduceIte, pow_zero] at g0 g1
      rw [show (2 ^ 13 : ℕ) = 8192 from rfl] at g1
      rw [hgEq] at g0 g1
      refine ⟨fun hor => ⟨g0.1 hor, g1.1 hor⟩, fun hand => ⟨g0.2 hand, g1.2 hand⟩⟩
  have hKill : ∀ b ∈ ([0, 13] : List ℕ), (sMax C1 b).getD C1.output false = false →
      ∃ x8 ∈ ([0, 13] : List ℕ),
        have x9 : ℕ := if x8 = 0 then 25034751 else 67108341
        have x10 : ℕ := if x8 = 0 then 8191 else 67100672
        have x11 : ℕ := if x8 = 0 then 25018369 else 15860
        ∀ (S : Set ℕ), C.output ∈ S → (∀ (i : Fin 26), i.val ∈ S → x9.testBit i.val = false) →
          ¬ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → 26 + j ∈ S →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i ∈ g.inputs, i ∈ S) ∨
              (∀ i ∈ g.inputs, (C.wires (List.ofFn fun k : Fin 26 => (2 ^ x8).testBit k.val)).getD i false = false) ∧
              (C.wires (List.ofFn fun k : Fin 26 => x10.testBit k.val)).getD (26 + j) false = false ∧
              (C.wires (List.ofFn fun k : Fin 26 => x11.testBit k.val)).getD (26 + j) false = false) := by
    intro b hb hfalse
    refine ⟨b, hb, fun S hOutS hBaseS hStepS => ?_⟩
    have hClose : ∀ k < 26 + C1.size, k ∈ S → (sMax C1 b).getD k false = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hkS
        by_cases hk26 : k < 26
        · rw [s_init_eq C1 b k hk26]
          have hbit := hBaseS ⟨k, hk26⟩ hkS
          dsimp only at hbit ⊢
          rw [hbit]; rfl
        · let j := k - 26
          have hjC1 : j < C1.gates.length := by change j < C1.size; omega
          have hjC : j < C.gates.length := by omega
          have hjTake : j < C.output - 25 := by omega
          have hC1j : C1.gates.getD j dGate = sortGate (C.gates.getD j dGate) := by
            dsimp only [C1]
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_take_of_lt hjTake, List.getElem?_eq_getElem hjC,
              List.getD_eq_getElem _ _ hjC]
            rfl
          have hkEq : 26 + j = k := by omega
          have hInS : 26 + j ∈ S := hkEq ▸ hkS
          have hgSome : C.gates[j]? = some (C.gates.getD j dGate) := by
            rw [List.getElem?_eq_getElem hjC, List.getD_eq_getElem _ _ hjC]
          have hSt := hStepS j (C.gates.getD j dGate) hgSome hInS
          obtain ⟨hOp, a, c, hac, hcLt, hIn⟩ := hC1Wf j hjC1
          have hbd : ∀ i ∈ (C1.gates.getD j dGate).inputs, i < 26 + j := by
            intro i hi; rw [hIn] at hi; rcases List.mem_cons.mp hi with rfl | hm
            · omega
            · rw [List.mem_singleton.mp hm]; exact hcLt
          have hgEqC1 := s_gate_eq C1 b j hjC1 hbd
          dsimp only at hgEqC1
          have haIdx : (C1.gates.getD j dGate).inputs.getD 0 0 = a := by rw [hIn]; rfl
          have hcIdx : (C1.gates.getD j dGate).inputs.getD 1 0 = c := by rw [hIn]; rfl
          rw [haIdx, hcIdx] at hgEqC1
          have hOpSame : (C.gates.getD j dGate).op = (C1.gates.getD j dGate).op := by
            rw [hC1j]; dsimp only [sortGate]; split_ifs <;> rfl
          have hmemC : C.gates.getD j dGate ∈ C.gates := by
            rw [List.getD_eq_getElem _ _ hjC]; exact List.getElem_mem hjC
          have hlenC : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hmemC
          have hEqC := list_len2 _ hlenC
          let x0 := (C.gates.getD j dGate).inputs.getD 0 0
          let y0 := (C.gates.getD j dGate).inputs.getD 1 0
          have hxMem : x0 ∈ (C.gates.getD j dGate).inputs := by rw [hEqC]; simp [x0]
          have hyMem : y0 ∈ (C.gates.getD j dGate).inputs := by rw [hEqC]; simp [y0]
          have hCases : (a = x0 ∧ c = y0) ∨ (a = y0 ∧ c = x0) := by
            have hin1 : (C1.gates.getD j dGate).inputs = [a, c] := hIn
            rw [hC1j] at hin1
            change (if x0 ≤ y0 then ({ op := (C.gates.getD j dGate).op, inputs := [x0, y0] } :
                PEqualNP.CircuitLowerBounds.Gate) else
                { op := (C.gates.getD j dGate).op, inputs := [y0, x0] }).inputs = [a, c] at hin1
            split_ifs at hin1
            · left
              change [x0, y0] = [a, c] at hin1
              injection hin1 with h1 h2; injection h2 with h2 _
              exact ⟨h1.symm, h2.symm⟩
            · right
              change [y0, x0] = [a, c] at hin1
              injection hin1 with h1 h2; injection h2 with h2 _
              exact ⟨h1.symm, h2.symm⟩
          have haMem : a ∈ (C.gates.getD j dGate).inputs := by
            rcases hCases with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
          have hcMem : c ∈ (C.gates.getD j dGate).inputs := by
            rcases hCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
          have hInBack : ∀ i ∈ (C.gates.getD j dGate).inputs, i = a ∨ i = c := by
            intro i hi
            rw [hEqC] at hi
            rcases List.mem_cons.mp hi with rfl | hm
            · rcases hCases with ⟨rfl, _⟩ | ⟨_, rfl⟩
              · left; rfl
              · right; rfl
            · rw [List.mem_singleton.mp hm]
              rcases hCases with ⟨_, rfl⟩ | ⟨rfl, _⟩
              · right; rfl
              · left; rfl
          rw [← hkEq]
          rcases hOp with hand | hor
          · rw [hgEqC1.2 hand]
            rcases hSt.2 (hOpSame.trans hand) with ⟨i, hiIn, hiS⟩ | ⟨hwB, hwX, hwY⟩
            · rcases hInBack i hiIn with hia | hic
              · rw [hia] at hiS; rw [ih a (by omega) (by omega) hiS]; simp
              · rw [hic] at hiS; rw [ih c (by omega) (by omega) hiS]; simp
            · have haB := hwB a haMem
              have hcB := hwB c hcMem
              rw [← hC1Wires _ a (by simp) (by omega)] at haB
              rw [← hC1Wires _ c (by simp) (by omega)] at hcB
              rw [← hC1Wires _ (26 + j) (by simp) (by omega)] at hwX hwY
              rw [haB, hcB, hwX, hwY]
              simp
          · rw [hgEqC1.1 hor]
            have hInAll := hSt.1 (hOpSame.trans hor)
            have haS := hInAll a haMem
            have hcS := hInAll c hcMem
            rw [ih a (by omega) (by omega) haS, ih c (by omega) (by omega) hcS]
            rfl
    have hT := hClose C.output (by change C.output < 26 + C1.gates.length; omega) hOutS
    change (sMax C1 b).getD C1.output false = true at hT
    rw [hfalse] at hT
    cases hT
  by_cases hs0 : (sMax C1 0).getD C1.output false = false
  · exact hKill 0 (by simp) hs0
  · have hs0T : (sMax C1 0).getD C1.output false = true := Bool.eq_true_of_not_eq_false hs0
    by_cases hs1 : (sMax C1 13).getD C1.output false = false
    · exact hKill 13 (by simp) hs1
    · have hs1T : (sMax C1 13).getD C1.output false = true := Bool.eq_true_of_not_eq_false hs1
      have hBoth : ∃ x8 ∈ ([0, 13] : List ℕ), False := by
        exfalso
        by_cases h63C1 : C1.size ≤ 63
        · obtain ⟨hInit, hAO1, hSort1, hStep⟩ := s_props C1 hC1Wf
          rw [hC1Out] at hs0T hs1T
          exact smallSize C1 (fun k => (sMax C1 0).getD k false) (fun k => (sMax C1 13).getD k false)
            hC1Sz1 h63C1 hC1Out hAO1 hSort1 hC1Spec hInit hStep hs0T hs1T
        · have hC164 : C1.size = 64 := by omega
          have hC1Len64 : C1.gates.length = 64 := hC164
          have hC1Out89 : C1.output = 89 := by omega
          by_cases hAllRead : ∀ k < 63, (PEqualNP.TopForm.readers 26 C1 k).Nonempty
          · obtain ⟨hInit, hAO1, hSort1, hStep⟩ := s_props C1 hC1Wf
            rw [hC1Out89] at hs0T hs1T
            rcases (hC1Wf 63 (by omega)).1 with hand | hor
            · have hand' : ∀ g : PEqualNP.CircuitLowerBounds.Gate,
                  C1.gates[63]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
                intro g hg; have heq : C1.gates.getD 63 dGate = g := by rw [List.getD_eq_getElem?_getD, hg]; rfl
                rw [← heq]; exact hand
              exact size64LastAnd C1 (fun k => (sMax C1 0).getD k false) (fun k => (sMax C1 13).getD k false)
                hC164 hC1Out89 hand' hAllRead hAO1 hSort1 hC1Spec hInit hStep hs0T hs1T
            · have hor' : ∀ g : PEqualNP.CircuitLowerBounds.Gate,
                  C1.gates[63]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
                intro g hg; have heq : C1.gates.getD 63 dGate = g := by rw [List.getD_eq_getElem?_getD, hg]; rfl
                rw [← heq]; exact hor
              exact size64LastOr C1 (fun k => (sMax C1 0).getD k false) (fun k => (sMax C1 13).getD k false)
                hC164 hC1Out89 hor' hAllRead hAO1 hSort1 hC1Spec hInit hStep hs0T hs1T
          · push Not at hAllRead
            obtain ⟨k0, hk63, hk0Empty⟩ := hAllRead
            have hk0Lt : k0 < C1.gates.length := by omega
            have hUnused : ∀ j < C1.gates.length, 26 + k0 ∉ (C1.gates.getD j dGate).inputs := by
              intro j hj hmem
              have hkmem : j ∈ PEqualNP.TopForm.readers 26 C1 k0 := by
                unfold PEqualNP.TopForm.readers
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_range.mpr hj, ?_⟩
                change 26 + k0 ∈ (C1.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs
                exact hmem
              rw [hk0Empty] at hkmem
              cases hkmem
            let C2 := PEqualNP.CircuitMoves.eraseGate 26 C1 k0 0
            have hC2Def : C2 =
                { gates := C1.gates.take k0 ++
                    (C1.gates.drop (k0 + 1)).map (fun g =>
                      ⟨g.op, g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 k0 0)⟩),
                  output := PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 C1.output } := by
              dsimp only [C2]; unfold PEqualNP.CircuitMoves.eraseGate; simp only [hk0Lt, ↓reduceIte]
            have hC2Len : C2.gates.length = 63 := by
              rw [hC2Def]; simp [List.length_take, List.length_drop, hC1Len64]; omega
            have hC2Sz1 : 1 ≤ C2.size := by change 1 ≤ C2.gates.length; omega
            have hC2Sz63 : C2.size ≤ 63 := by change C2.gates.length ≤ 63; omega
            have hC2Out : C2.output = 25 + C2.size := by
              have hred : C2.output = 88 := by
                rw [hC2Def, hC1Out89]
                dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
              change C2.output = 25 + C2.gates.length; omega
            have hAt1 : ∀ r < k0, C2.gates.getD r dGate = C1.gates.getD r dGate := by
              intro r hr
              rw [hC2Def, List.getD_append _ _ _ _ (by simp [List.length_take]; omega),
                List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hr]
            have hAt2 : ∀ r, k0 < r → r < 64 →
                C2.gates.getD (r - 1) dGate =
                  ⟨(C1.gates.getD r dGate).op,
                    (C1.gates.getD r dGate).inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 k0 0)⟩ := by
              intro r hkr hr
              rw [hC2Def, List.getD_append_right _ _ _ _ (by simp [List.length_take]; omega)]
              have hsub : r - 1 - (C1.gates.take k0).length = r - (k0 + 1) := by
                rw [List.length_take]; omega
              rw [hsub, List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_drop, show k0 + 1 + (r - (k0 + 1)) = r by omega,
                List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
              rfl
            have hC2Wf : ∀ j < C2.gates.length,
                let g := C2.gates.getD j dGate
                (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                  g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
                ∃ a c, a < c ∧ c < 26 + j ∧ g.inputs = [a, c] := by
              intro j hj
              by_cases hjk : j < k0
              · rw [hAt1 j hjk]; exact hC1Wf j (by omega)
              · have hjk1 : k0 < j + 1 := by omega
                have hj1 : j + 1 < 64 := by omega
                have hEq := hAt2 (j + 1) hjk1 hj1
                rw [show j + 1 - 1 = j by omega] at hEq
                rw [hEq]
                obtain ⟨hop, a, c, hac, hcLt, hIn⟩ := hC1Wf (j + 1) (by omega)
                have haNe : a ≠ 26 + k0 := fun he =>
                  hUnused (j + 1) (by omega) (by rw [hIn, he]; simp)
                have hcNe : c ≠ 26 + k0 := fun he =>
                  hUnused (j + 1) (by omega) (by rw [hIn, he]; simp)
                have hInM : (C1.gates.getD (j + 1) dGate).inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 k0 0) =
                    [PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 a,
                     PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 c] := by
                  rw [hIn]; rfl
                refine ⟨hop, PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 a,
                  PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 c, ?_, ?_, hInM⟩
                · dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                · dsimp only [PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitMoves.eraseRedirect]
                  split_ifs <;> omega
            let shiftIdx : ℕ → ℕ := fun r => if r < k0 then r else r - 1
            have hWAgree : ∀ (y : List Bool) (r : ℕ), y.length = 26 → r < 64 → r ≠ k0 →
                (C2.wires y).getD (26 + shiftIdx r) false = (C1.wires y).getD (26 + r) false := by
              intro y r hy
              induction r using Nat.strong_induction_on with
              | ind r ih =>
                intro hr64 hrNe
                have hWgate : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
                    j < E.gates.length →
                    (∀ i ∈ (E.gates.getD j dGate).inputs, i < 26 + j) →
                    (E.wires y).getD (26 + j) false =
                      (E.gates.getD j dGate).op.eval
                        ((E.gates.getD j dGate).inputs.map fun w => (E.wires y).getD w false) := by
                  intro E j hjE hrbE
                  have hd : E.gates.drop j = E.gates.getD j dGate :: E.gates.drop (j + 1) := by
                    rw [← List.getElem_cons_drop hjE, List.getD_eq_getElem _ _ hjE]
                  have hpreLen : ((E.gates.take j).foldl step y).length = 26 + j := by
                    rw [wires_len, hy, List.length_take]; omega
                  have hstepLen : (step ((E.gates.take j).foldl step y) (E.gates.getD j dGate)).length = 26 + j + 1 := by
                    dsimp only [step]; rw [List.length_append, List.length_singleton, hpreLen]
                  change (E.gates.foldl step y).getD (26 + j) false = _
                  conv_lhs =>
                    rw [← List.take_append_drop j E.gates, wires_append, hd, List.foldl_cons,
                      wires_prefix _ _ _ (by rw [hstepLen]; omega)]
                  dsimp only [step]
                  rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
                  have hval : ∀ v : Bool, ([v] : List Bool).getD 0 false = v := fun _ => rfl
                  rw [hval]
                  congr 1
                  apply List.map_congr_left
                  intro w hw
                  have hwlt := hrbE w hw
                  exact wires_take j E.gates y w (by rw [hy, List.length_take]; omega)
                have hrb1 : ∀ j < 64, ∀ i ∈ (C1.gates.getD j dGate).inputs, i < 26 + j := by
                  intro j hj _
                  obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hC1Wf j (by omega)
                  rw [hIn]; intro hi; rcases List.mem_cons.mp hi with rfl | hm
                  · omega
                  · rw [List.mem_singleton.mp hm]; exact hcLt
                have hrb2 : ∀ j < 63, ∀ i ∈ (C2.gates.getD j dGate).inputs, i < 26 + j := by
                  intro j hj _
                  obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hC2Wf j (by omega)
                  rw [hIn]; intro hi; rcases List.mem_cons.mp hi with rfl | hm
                  · omega
                  · rw [List.mem_singleton.mp hm]; exact hcLt
                by_cases hlt0 : r < k0
                · simp only [shiftIdx, hlt0, ↓reduceIte]
                  change (C2.gates.foldl step y).getD (26 + r) false = (C1.gates.foldl step y).getD (26 + r) false
                  rw [hC2Def, wires_append,
                    wires_prefix _ _ _ (by rw [wires_len, hy, List.length_take]; omega)]
                  exact wires_take k0 C1.gates y (26 + r) (by rw [hy, List.length_take]; omega)
                · have hkr : k0 < r := by omega
                  simp only [shiftIdx, hlt0, ↓reduceIte]
                  rw [hWgate C2 (r - 1) (by omega) (hrb2 (r - 1) (by omega)),
                    hWgate C1 r (by omega) (hrb1 r hr64), hAt2 r hkr hr64]
                  dsimp only
                  congr 1
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro w hw
                  dsimp only [Function.comp_apply]
                  have hwlt : w < 26 + r := hrb1 r hr64 w hw
                  have hwNe : w ≠ 26 + k0 := fun he => hUnused r (by omega) (he ▸ hw)
                  by_cases hw26 : w < 26
                  · have hredW : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 w = w := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                    rw [hredW]
                    change (C2.gates.foldl step y).getD w false = (C1.gates.foldl step y).getD w false
                    rw [wires_prefix _ _ _ (by rw [hy]; exact hw26),
                        wires_prefix _ _ _ (by rw [hy]; exact hw26)]
                  · obtain ⟨u, rfl⟩ : ∃ u, w = 26 + u := ⟨w - 26, by omega⟩
                    have hur : u < r := by omega
                    have hredU : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 (26 + u) = 26 + shiftIdx u := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect, shiftIdx]; split_ifs <;> omega
                    rw [hredU]
                    exact ih u hur (by omega) (by omega)
            have hC2Spec : ∀ z : Fin 26 → Bool, C2.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
                (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
                z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true := by
              intro z
              have hev : C2.eval (List.ofFn z) = C1.eval (List.ofFn z) := by
                change (C2.wires (List.ofFn z)).getD C2.output false = (C1.wires (List.ofFn z)).getD C1.output false
                have h88 : C2.output = 26 + shiftIdx 63 := by
                  change C2.output = 25 + C2.gates.length at hC2Out
                  simp only [shiftIdx, show ¬ (63 : ℕ) < k0 by omega, ↓reduceIte]
                  omega
                rw [h88, hC1Out89]
                exact hWAgree (List.ofFn z) 63 (by simp) (by omega) (by omega)
              rw [hev]
              exact hC1Spec z
            have hSAgree : ∀ (b r : ℕ), r < 64 → r ≠ k0 →
                (sMax C2 b).getD (26 + shiftIdx r) false = (sMax C1 b).getD (26 + r) false := by
              intro b r
              induction r using Nat.strong_induction_on with
              | ind r ih =>
                intro hr64 hrNe
                have hInit2 : ∀ i < 26, (sMax C2 b).getD i false = (sMax C1 b).getD i false := by
                  intro i hi; rw [s_init_eq C2 b i hi, s_init_eq C1 b i hi]
                have hW2 : ∀ (m w : ℕ), w < 26 + 64 → w ≠ 26 + k0 →
                    (C2.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD
                      (PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 w) false =
                    (C1.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false := by
                  intro m w hw hwNe
                  by_cases hw26 : w < 26
                  · have hred : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 w = w := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                    rw [hred]
                    change (C2.gates.foldl step _).getD w false = (C1.gates.foldl step _).getD w false
                    rw [wires_prefix _ _ _ (by simp [hw26]), wires_prefix _ _ _ (by simp [hw26])]
                  · obtain ⟨u, rfl⟩ : ∃ u, w = 26 + u := ⟨w - 26, by omega⟩
                    have hred : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 (26 + u) = 26 + shiftIdx u := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect, shiftIdx]; split_ifs <;> omega
                    rw [hred]
                    exact hWAgree _ u (by simp) (by omega) (by omega)
                have hrb1 : ∀ j < 64, ∀ i ∈ (C1.gates.getD j dGate).inputs, i < 26 + j := by
                  intro j hj _
                  obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hC1Wf j (by omega)
                  rw [hIn]; intro hi; rcases List.mem_cons.mp hi with rfl | hm
                  · omega
                  · rw [List.mem_singleton.mp hm]; exact hcLt
                have hrb2 : ∀ j < 63, ∀ i ∈ (C2.gates.getD j dGate).inputs, i < 26 + j := by
                  intro j hj _
                  obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hC2Wf j (by omega)
                  rw [hIn]; intro hi; rcases List.mem_cons.mp hi with rfl | hm
                  · omega
                  · rw [List.mem_singleton.mp hm]; exact hcLt
                have hOp1 := (hC1Wf r (by omega)).1
                have hEq2 := s_gate_eq C2 b (shiftIdx r) (by dsimp only [shiftIdx]; split_ifs <;> omega)
                  (hrb2 (shiftIdx r) (by dsimp only [shiftIdx]; split_ifs <;> omega))
                have hEq1 := s_gate_eq C1 b r (by omega) (hrb1 r hr64)
                dsimp only at hEq2 hEq1
                have hShiftIn : ∀ w, w < 26 + r → w ≠ 26 + k0 →
                    (sMax C2 b).getD (PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 w) false =
                      (sMax C1 b).getD w false := by
                  intro w hw hwNe
                  by_cases hw26 : w < 26
                  · have hred : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 w = w := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                    rw [hred]; exact hInit2 w hw26
                  · obtain ⟨u, rfl⟩ : ∃ u, w = 26 + u := ⟨w - 26, by omega⟩
                    have hred : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 (26 + u) = 26 + shiftIdx u := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect, shiftIdx]; split_ifs <;> omega
                    rw [hred]; exact ih u (by omega) (by omega) (by omega)
                obtain ⟨_, a, c, hac, hcLt, hIn⟩ := hC1Wf r (by omega)
                have haNe : a ≠ 26 + k0 := fun he => hUnused r (by omega) (by rw [hIn, he]; simp)
                have hcNe : c ≠ 26 + k0 := fun he => hUnused r (by omega) (by rw [hIn, he]; simp)
                have haIdx1 : (C1.gates.getD r dGate).inputs.getD 0 0 = a := by rw [hIn]; rfl
                have hcIdx1 : (C1.gates.getD r dGate).inputs.getD 1 0 = c := by rw [hIn]; rfl
                have hC2GateInputs : (C2.gates.getD (shiftIdx r) dGate).inputs =
                    [PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 a,
                     PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 c] ∧
                    (C2.gates.getD (shiftIdx r) dGate).op = (C1.gates.getD r dGate).op := by
                  by_cases hlt0 : r < k0
                  · simp only [shiftIdx, hlt0, ↓reduceIte]
                    rw [hAt1 r hlt0]
                    have hredA : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 a = a := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                    have hredC : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 c = c := by
                      dsimp only [PEqualNP.CircuitMoves.eraseRedirect]; split_ifs <;> omega
                    rw [hIn, hredA, hredC]; exact ⟨rfl, rfl⟩
                  · have hkr : k0 < r := by omega
                    simp only [shiftIdx, hlt0, ↓reduceIte]
                    rw [hAt2 r hkr hr64, hIn]
                    exact ⟨rfl, rfl⟩
                have haIdx2 : (C2.gates.getD (shiftIdx r) dGate).inputs.getD 0 0 =
                    PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 a := by rw [hC2GateInputs.1]; rfl
                have hcIdx2 : (C2.gates.getD (shiftIdx r) dGate).inputs.getD 1 0 =
                    PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 c := by rw [hC2GateInputs.1]; rfl
                rw [haIdx1, hcIdx1] at hEq1
                rw [haIdx2, hcIdx2] at hEq2
                have hredR : PEqualNP.CircuitMoves.eraseRedirect 26 k0 0 (26 + r) = 26 + shiftIdx r := by
                  dsimp only [PEqualNP.CircuitMoves.eraseRedirect, shiftIdx]; split_ifs <;> omega
                rcases hOp1 with hand | hor
                · rw [hEq2.2 (hC2GateInputs.2.trans hand), hEq1.2 hand,
                    hShiftIn a (by omega) haNe, hShiftIn c (by omega) hcNe,
                    hW2 (2 ^ b) a (by omega) haNe, hW2 (2 ^ b) c (by omega) hcNe,
                    ← hredR, hW2 _ (26 + r) (by omega) (by omega), hW2 _ (26 + r) (by omega) (by omega)]
                · rw [hEq2.1 (hC2GateInputs.2.trans hor), hEq1.1 hor,
                    hShiftIn a (by omega) haNe, hShiftIn c (by omega) hcNe]
            obtain ⟨hInit2, hAO2, hSort2, hStep2⟩ := s_props C2 hC2Wf
            have hs02 : (sMax C2 0).getD (25 + C2.size) false = true := by
              have ha := hSAgree 0 63 (by omega) (by omega)
              simp only [shiftIdx, show ¬ (63 : ℕ) < k0 by omega, ↓reduceIte] at ha
              have hszEq : 25 + C2.size = 26 + 62 := by change 25 + C2.gates.length = 88; omega
              rw [hszEq, ha, show (26 + 63 : ℕ) = C1.output by omega]
              exact hs0T
            have hs12 : (sMax C2 13).getD (25 + C2.size) false = true := by
              have ha := hSAgree 13 63 (by omega) (by omega)
              simp only [shiftIdx, show ¬ (63 : ℕ) < k0 by omega, ↓reduceIte] at ha
              have hszEq : 25 + C2.size = 26 + 62 := by change 25 + C2.gates.length = 88; omega
              rw [hszEq, ha, show (26 + 63 : ℕ) = C1.output by omega]
              exact hs1T
            exact smallSize C2 (fun k => (sMax C2 0).getD k false) (fun k => (sMax C2 13).getD k false)
              hC2Sz1 hC2Sz63 hC2Out hAO2 hSort2 hC2Spec hInit2 hStep2 hs02 hs12
      rcases hBoth with ⟨_, _, hF⟩
      exact False.elim hF
