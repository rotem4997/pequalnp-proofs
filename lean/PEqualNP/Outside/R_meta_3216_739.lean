import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3216_739
    (compact : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ))
    (cofactor : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.cons Bool.false x2)) (11 : ℕ))
    (residual : ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (¬ ∃ prefixGates gate suffixGates, x7.gates = prefixGates ++ gate :: suffixGates ∧
        (gate.op = .and ∧ 0 ∈ gate.inputs ∨ gate.op = .or ∧ 9 ∈ gate.inputs) ∧
        ∃ reader ∈ suffixGates, 0 ∉ reader.inputs ∧ 9 ∉ reader.inputs ∧
          10 + prefixGates.length ∈ reader.inputs) → (∀ (x15 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x15 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x16 : ℕ) => x15 (Fin.ofNat (8 : ℕ) (x16 / (8 : ℕ))) && x15 (Fin.ofNat (8 : ℕ) (x16 % (8 : ℕ)))) → ∃ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x16 ++ [Bool.false]) ≠ (x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ)) || x16 (4 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (2 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (6 : Fin (8 : ℕ)) || x16 (2 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)) || x16 (5 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)))) :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (∀ (x15 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x15 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x16 : ℕ) => x15 (Fin.ofNat (8 : ℕ) (x16 / (8 : ℕ))) && x15 (Fin.ofNat (8 : ℕ) (x16 % (8 : ℕ)))) → ∃ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x16 ++ [Bool.false]) ≠ (x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ)) || x16 (4 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (2 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (6 : Fin (8 : ℕ)) || x16 (2 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)) || x16 (5 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ))) := by
  dsimp only
  intro before between after first second output fan size outputRange gateBounds unmarked markedReads controls low
  let gates := before ++ first :: (between ++ second :: after)
  let tailCircuit : Circuit := ⟨gates, output⟩
  let reads (gate : Gate) := [0, 9].any (fun wire => gate.inputs.contains wire)
  let absorbs (tailGates : List Gate) : Prop :=
    ∃ prefixGates gate suffixGates, tailGates = prefixGates ++ gate :: suffixGates ∧
      (gate.op = .and ∧ 0 ∈ gate.inputs ∨ gate.op = .or ∧ 9 ∈ gate.inputs) ∧
      ∃ reader ∈ suffixGates, reads reader = false ∧ 10 + prefixGates.length ∈ reader.inputs
  by_cases absorbing : absorbs gates
  · let inverter : Gate := ⟨.not, [0]⟩
    let full : Circuit := ⟨inverter :: gates, output⟩
    let step (wires : List Bool) (gate : Gate) :=
      wires ++ [gate.op.eval (gate.inputs.map (fun wire => wires.getD wire false))]
    let norm (gate : Gate) : Gate :=
      ⟨gate.op, if gate.op.eval [false] = true then gate.inputs.take 1 else gate.inputs⟩
    let lowFunction (x : Fin 8 → Bool) :=
      ([1, 10, 19, 5, 14, 23, 38, 47, 60] : List ℕ).any
        (fun edge => x (Fin.ofNat 8 (edge / 8)) && x (Fin.ofNat 8 (edge % 8)))
    let edgeFunction (x : Fin 9 → Bool) :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have normalise (gate : Gate) (member : gate ∈ gates) : norm gate = gate := by
      have allowed : gate.op = .and ∨ gate.op = .or ∨ gate.op = .not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan gate member).1
      rcases gate with ⟨operation, inputs⟩
      rcases allowed with equals | equals | equals
      · change operation = .and at equals
        subst operation
        rfl
      · change operation = .or at equals
        subst operation
        rfl
      · change operation = .not at equals
        subst operation
        have arity := (gateBounds ⟨.not, inputs⟩ member).1 rfl
        change inputs.length ≤ 1 at arity
        change (⟨GateOp.not, inputs.take 1⟩ : Gate) = ⟨GateOp.not, inputs⟩
        rw [List.take_of_length_le arity]
    have normList : gates.map norm = gates := by
      calc
        gates.map norm = gates.map id := List.map_congr_left (fun gate member => normalise gate member)
        _ = gates := List.map_id _
    have anyRead (gate : Gate) : reads gate = true ↔ 0 ∈ gate.inputs ∨ 9 ∈ gate.inputs := by
      simp [reads]
    have absent (sublist : List Gate) (included : ∀ gate ∈ sublist, gate ∈ before ++ between ++ after) :
        sublist.filter reads = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro gate member
      obtain ⟨noZero, noNine⟩ := unmarked gate (included gate member)
      intro read
      exact (anyRead gate).mp read |>.elim noZero noNine
    have noneBefore := absent before (fun gate member =>
      List.mem_append_left _ (List.mem_append_left _ member))
    have noneBetween := absent between (fun gate member =>
      List.mem_append_left _ (List.mem_append_right _ member))
    have noneAfter := absent after (fun gate member => List.mem_append_right _ member)
    have firstRead : reads first = true := (anyRead first).mpr (controls first (by simp))
    have secondRead : reads second = true := (anyRead second).mpr (controls second (by simp))
    have exactlyTwo : (gates.filter reads).length = 2 := by
      simp only [gates, List.filter_append, List.filter_cons_of_pos firstRead, List.filter_cons_of_pos secondRead,
        noneBefore, noneBetween, noneAfter, List.nil_append, List.length_cons, List.length_nil]
    have stable (remaining : List Gate) (wires : List Bool) (index : ℕ) (inRange : index < wires.length) :
        (remaining.foldl step wires).getD index false = wires.getD index false := by
      induction remaining generalizing wires with
      | nil => rfl
      | cons gate rest inductionHypothesis =>
        rw [List.foldl_cons, inductionHypothesis (step wires gate) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ inRange
    have firstFormula (x : Fin 9 → Bool) :
        step (List.ofFn x) inverter = List.ofFn x ++ [!x 0] := by
      have firstBit : (List.ofFn x).getD 0 false = x 0 := by rw [List.ofFn_succ]; rfl
      change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
      rw [firstBit]
    have firstWire (x : Fin 9 → Bool) : (full.wires (List.ofFn x)).getD 9 false = !x 0 := by
      change (gates.foldl step (step (List.ofFn x) inverter)).getD 9 false = _
      rw [firstFormula, stable _ _ _ (by simp)]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have fanFull : FanInTwo full := by
      intro gate member
      change gate ∈ inverter :: gates at member
      rcases List.mem_cons.mp member with rfl | rest
      · simp [inverter]
      · exact fan gate rest
    have sizeFull : full.size ≤ 15 := by
      change (inverter :: gates).length ≤ 15
      simp only [gates, List.length_append, List.length_cons]
      omega
    have evalLow (x : Fin 8 → Bool) : circuitFun 9 full (Fin.cons false x) = lowFunction x := by
      change (gates.foldl step (step (List.ofFn (Fin.cons false x)) inverter)).getD output false = _
      rw [firstFormula]
      let zeroPrefix : Fin 9 → Bool := Fin.cons false x
      have row : List.ofFn zeroPrefix ++ [!zeroPrefix 0] = false :: List.ofFn x ++ [true] := by
        rw [List.ofFn_succ]
        simp [zeroPrefix, Fin.cons_succ]
      rw [row]
      exact low x
    have varies : ∃ x y : Fin 8 → Bool,
        circuitFun 9 full (Fin.cons false x) ≠ circuitFun 9 full (Fin.cons false y) := by
      refine ⟨fun _ => true, fun _ => false, ?_⟩
      rw [evalLow, evalLow]
      decide +kernel
    have smallCofactor : HasCircuitSize 8 (fun x => circuitFun 9 full (Fin.cons false x)) 11 := by
      refine compact full fanFull firstWire sizeFull ?_ varies
      change 3 ≤ ((gates.map norm).filter reads).length ∨
        (2 ≤ ((gates.map norm).filter reads).length ∧ absorbs (gates.map norm))
      rw [normList, exactlyTwo]
      exact Or.inr ⟨le_refl _, absorbing⟩
    have table : ∀ x : Fin 8 → Bool, lowFunction x = edgeFunction (Fin.cons false x) := by
      decide +kernel
    have relabel : (fun x => circuitFun 9 full (Fin.cons false x)) =
        (fun x => edgeFunction (Fin.cons false x)) :=
      funext (fun x => (evalLow x).trans (table x))
    have afterRelabel : HasCircuitSize 8 (fun x => edgeFunction (Fin.cons false x)) 11 :=
      relabel ▸ smallCofactor
    exact (cofactor afterRelabel).elim
  · refine residual before between after first second output fan size outputRange gateBounds
      unmarked markedReads controls ?_ low
    rintro ⟨prefixGates, gate, suffixGates, split, outputConstant, reader, follows, noZero, noNine, readsGate⟩
    exact absorbing ⟨prefixGates, gate, suffixGates, split, outputConstant, reader, follows,
      by simp [reads, noZero, noNine], readsGate⟩
