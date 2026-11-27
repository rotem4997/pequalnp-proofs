import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2509_817
    (bound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (boundInverted : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.gates.countP (fun gate => gate.inputs.contains 4) ≤ 1 →
      (∀ gate ∈ x1.gates, 4 ∈ gate.inputs →
        ∃ wire, 9 ≤ wire ∧ gate.op = GateOp.and ∧ gate.inputs = [wire, 4]) →
      (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && (!x3 (4 : Fin (9 : ℕ))) || (!x3 (4 : Fin (9 : ℕ))) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         (8 : ℕ) ≤ x4 →           x4 < (8 : ℕ) + x2.size →             have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);             have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;             (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = !x5) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [x5]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro prefixCircuit suffixCircuit cut forced prefixFan suffixFan sizeBound cutGenerated _
  let edge (x : Fin 8 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let prefixWires (x : Fin 8 → Bool) := prefixCircuit.wires (List.ofFn x)
  let cutValue (x : Fin 8 → Bool) := (prefixWires x).getD cut false
  intro _ low
  change ∀ x, suffixCircuit.eval (prefixWires x ++ [cutValue x]) = edge x at low
  change ∃ x, suffixCircuit.eval (prefixWires x ++ [forced]) ≠ (edge x || x 0 || x 3)
  by_contra! high
  let rename (i : ℕ) : ℕ := if i < 4 then i else i + 1
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let step (wires : List Bool) (g : Gate) : List Bool :=
    wires ++ [g.op.eval (g.inputs.map (fun i => wires.getD i false))]
  let switch : Gate := ⟨if forced then GateOp.or else GateOp.and, [rename cut, 4]⟩
  let combined : Circuit :=
    ⟨prefixCircuit.gates.map renameGate ++ [switch] ++ suffixCircuit.gates.map renameGate, rename suffixCircuit.output⟩
  have readWire (left right : List Bool) (control : Bool) (length : left.length = 4) (i : ℕ) :
      (left ++ control :: right).getD (rename i) false = (left ++ right).getD i false := by
    by_cases before : i < 4
    · have inside : i < left.length := by omega
      simp [rename, before, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
    · have outside : left.length ≤ i := by omega
      have shifted : left.length ≤ i + 1 := by omega
      have offset : i + 1 - left.length = (i - left.length) + 1 := by omega
      simp [rename, before, List.getD_eq_getElem?_getD, List.getElem?_append_right outside,
        List.getElem?_append_right shifted, offset]
  have run (gates : List Gate) (left right : List Bool) (control : Bool)
      (length : left.length = 4) :
      ∃ tail, gates.foldl step (left ++ right) = left ++ tail ∧
        (gates.map renameGate).foldl step (left ++ control :: right) = left ++ control :: tail := by
    induction gates generalizing right with
    | nil => exact ⟨right, rfl, rfl⟩
    | cons gate gates induction =>
      let value := gate.op.eval (gate.inputs.map (fun i => (left ++ right).getD i false))
      have plain : step (left ++ right) gate = left ++ (right ++ [value]) := by
        simp [step, value, List.append_assoc]
      have lifted : step (left ++ control :: right) (renameGate gate) =
          left ++ control :: (right ++ [value]) := by
        simp only [step, renameGate, List.map_map, Function.comp_def, readWire left right control length,
          value, List.append_assoc, List.cons_append]
      simpa only [List.foldl_cons, List.map_cons, plain, lifted] using induction (right ++ [value])
  have renamedFan (circuit : Circuit) (fan : FanInTwo circuit) :
      ∀ gate ∈ circuit.gates.map renameGate,
        gate.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gate.inputs.length ≤ 2 := by
    intro gate member
    obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp member
    simpa [renameGate] using fan original belongs
  have combinedFan : FanInTwo combined := by
    intro gate member
    simp only [combined, List.mem_append, List.mem_singleton] at member
    rcases member with (member | rfl) | member
    · exact renamedFan prefixCircuit prefixFan gate member
    · cases forced <;> simp [switch]
    · exact renamedFan suffixCircuit suffixFan gate member
  have combinedSize : combined.size ≤ 14 := by
    change (prefixCircuit.gates.map renameGate ++ [switch] ++ suffixCircuit.gates.map renameGate).length ≤ 14
    simp only [List.length_append, List.length_map, List.length_singleton]
    change prefixCircuit.gates.length + suffixCircuit.gates.length ≤ 13 at sizeBound
    omega
  let restrict (input : Fin 9 → Bool) : Fin 8 → Bool :=
    ![input 0, input 1, input 2, input 3, input 5, input 6, input 7, input 8]
  have evaluate (input : Fin 9 → Bool) :
      circuitFun 9 combined input =
        suffixCircuit.eval (prefixWires (restrict input) ++
          [if input 4 = forced then forced else cutValue (restrict input)]) := by
    let left := [input 0, input 1, input 2, input 3]
    let right := [input 5, input 6, input 7, input 8]
    have length : left.length = 4 := rfl
    have inputEight : List.ofFn (restrict input) = left ++ right := by
      simp [restrict, left, right, List.ofFn_succ]
    have inputNine : List.ofFn input = left ++ input 4 :: right := by
      simp [left, right, List.ofFn_succ]
    obtain ⟨middle, plain, lifted⟩ := run prefixCircuit.gates left right (input 4) length
    have plainPrefix : prefixWires (restrict input) = left ++ middle := by
      change prefixCircuit.gates.foldl step (List.ofFn (restrict input)) = _
      rwa [inputEight]
    let selected := if input 4 = forced then forced else cutValue (restrict input)
    have wireFour : (left ++ input 4 :: middle).getD 4 false = input 4 := by
      simp [List.getD_eq_getElem?_getD, left]
    have switchValue : step (left ++ input 4 :: middle) switch =
        left ++ input 4 :: (middle ++ [selected]) := by
      have oldCut := readWire left middle (input 4) length cut
      rw [← plainPrefix] at oldCut
      have cutRead : (left ++ input 4 :: middle).getD (rename cut) false =
          cutValue (restrict input) := oldCut
      have selectValue (original control imposed : Bool) :
          (if imposed then GateOp.or else GateOp.and).eval [original, control] =
            (if control = imposed then imposed else original) := by
        cases original <;> cases control <;> cases imposed <;> rfl
      simp only [step, switch, List.map_cons, List.map_nil, cutRead, wireFour,
        selectValue, selected, List.append_assoc, List.cons_append]
    obtain ⟨out, plainOut, liftedOut⟩ := run suffixCircuit.gates left (middle ++ [selected]) (input 4) length
    change (((prefixCircuit.gates.map renameGate ++ [switch] ++ suffixCircuit.gates.map renameGate).foldl
      step (List.ofFn input)).getD (rename suffixCircuit.output) false) =
      (suffixCircuit.gates.foldl step (prefixWires (restrict input) ++ [selected])).getD suffixCircuit.output false
    rw [inputNine, List.foldl_append, List.foldl_append, lifted, List.foldl_cons, List.foldl_nil,
      switchValue, liftedOut, plainPrefix, List.append_assoc, plainOut]
    exact readWire left out (input 4) length suffixCircuit.output
  have controlAbsent (gate : Gate) : 4 ∉ (renameGate gate).inputs := by
    intro member
    obtain ⟨index, _, coincidence⟩ := List.mem_map.mp member
    change rename index = 4 at coincidence
    unfold rename at coincidence
    split at coincidence <;> omega
  have unreferenced (gates : List Gate) :
      (gates.map renameGate).countP (fun gate => gate.inputs.contains 4) = 0 := by
    apply List.countP_eq_zero.mpr
    intro gate member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    simpa using controlAbsent original
  cases forced
  · apply (Nat.not_le_of_lt (by omega : combined.size < 15))
    apply boundInverted combined combinedFan
    · have oneControl : ([switch] : List Gate).countP (fun gate => gate.inputs.contains 4) = 1 := by
        simp [switch]
      simp only [combined, List.countP_append, unreferenced, oneControl, Nat.zero_add, Nat.add_zero, le_refl]
    · intro gate member readsControl
      simp only [combined, List.mem_append, List.mem_singleton] at member
      rcases member with (member | rfl) | member
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
        exact (controlAbsent original readsControl).elim
      · refine ⟨rename cut, ?_, rfl, rfl⟩
        simp only [rename, ite_eq_right (show ¬ cut < 4 by omega)]
        omega
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
        exact (controlAbsent original readsControl).elim
    · funext input
      rw [evaluate]
      cases control : input 4
      · simp [high, edge, restrict]
        ac_rfl
      · simp [low, edge, restrict]
  · apply (Nat.not_le_of_lt (by omega : combined.size < 15))
    apply bound combined combinedFan
    funext input
    rw [evaluate]
    cases control : input 4
    · simp [low, edge, restrict]
    · simp [high, edge, restrict]
      ac_rfl
