import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Table := BitVec 16

private def inputIndex (x : Fin 4 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) +
    (if x 2 then 4 else 0) + (if x 3 then 8 else 0)

private theorem inputIndex_lt (x : Fin 4 → Bool) : inputIndex x < 16 := by
  unfold inputIndex
  split_ifs <;> decide

private def readTable (x : Fin 4 → Bool) (t : Table) : Bool :=
  t.getLsbD (inputIndex x)

private theorem read_zero (x : Fin 4 → Bool) : readTable x 0 = false :=
  BitVec.getLsbD_zero

private theorem read_not (x : Fin 4 → Bool) (t : Table) :
    readTable x (~~~t) = !(readTable x t) := by
  simp only [readTable, BitVec.getLsbD_not, decide_eq_true (inputIndex_lt x), Bool.true_and]

private def inputs : List Table := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

private def pathFunction (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

private theorem inputList (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  simp [List.ofFn_succ]

private theorem inputTables (x : Fin 4 → Bool) : List.ofFn x = inputs.map (readTable x) := by
  rw [inputList]
  simp only [inputs, List.map_cons, List.map_nil, readTable, inputIndex]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem pathTable (x : Fin 4 → Bool) : readTable x 0xf8c8 = pathFunction x := by
  unfold readTable inputIndex pathFunction
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem table_ext (a b : Table) (h : ∀ x, readTable x a = readTable x b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let x : Fin 4 → Bool := fun j => i.testBit j
  have hx : inputIndex x = i := by
    dsimp only [x]
    interval_cases i <;> decide
  simpa only [readTable, hx] using h x

private theorem getD_table (x : Fin 4 → Bool) (ws : List Table) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

private def gateTable (ws : List Table) (g : Gate) : Table :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateTable (x : Fin 4 → Bool) (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireTables (gs : List Gate) (ws : List Table) : List Table :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

private theorem read_wireTables (x : Fin 4 → Bool) (gs : List Gate) (ws : List Table)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private theorem circuitTable (C : Circuit) (h : FanInTwo C) (x : Fin 4 → Bool) :
    circuitFun 4 C x = readTable x ((wireTables C.gates inputs).getD C.output 0) := by
  unfold circuitFun Circuit.eval
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD C.output false = _
  rw [inputTables, read_wireTables x C.gates inputs h, getD_table]

/-- Applying a binary gate to two different positions of the wire list. -/
private def pairs : List Table → List Table
  | [] => []
  | a :: ws => (ws.flatMap fun b => [a &&& b, a ||| b]) ++ pairs ws

/-- The distinct tables obtainable by one gate, also retaining those already available. -/
private def choices (ws : List Table) : List Table :=
  (ws ++ ws.map (fun a => ~~~a) ++ pairs ws).eraseDups

private theorem getD_available (ws : List Table) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

private theorem copy_choice (ws : List Table) (a : Table) (ha : a ∈ ws) : a ∈ choices ws := by
  apply List.mem_eraseDups.2
  exact List.mem_append_left _ (List.mem_append_left _ ha)

private theorem not_choice (ws : List Table) (a : Table) (ha : a ∈ ws) :
    ~~~a ∈ choices ws := by
  apply List.mem_eraseDups.2
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩))

private theorem pair_available (ws : List Table) (a b : Table) (ha : a ∈ ws) (hb : b ∈ ws) :
    a = b ∨ (a &&& b ∈ pairs ws ∧ a ||| b ∈ pairs ws) := by
  induction ws with
  | nil => simp at ha
  | cons c ws ih =>
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩)⟩
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩)⟩
      · rw [BitVec.and_comm]; simp
      · rw [BitVec.or_comm]; simp
    · rcases ih ha' hb' with h | ⟨hAnd, hOr⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_right _ hAnd, List.mem_append_right _ hOr⟩

private theorem binary_choice (ws : List Table) (a b c : Table) (ha : a ∈ ws) (hb : b ∈ ws)
    (hc : c ∈ [a &&& b, a ||| b]) : c ∈ choices ws := by
  rcases pair_available ws a b ha hb with rfl | ⟨hAnd, hOr⟩
  · have h : c = a := by simpa using hc
    exact h ▸ copy_choice ws a ha
  · apply List.mem_eraseDups.2
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hAnd
    · exact hOr

private theorem gate_choice (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gateTable ws g ∈ choices (0 :: ws) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => exact not_choice _ 0 List.mem_cons_self
    | [i], _ => exact copy_choice _ _ (getD_available ws i)
    | [i, j], _ =>
      exact binary_choice _ _ _ _ (getD_available ws i) (getD_available ws j) (by simp [gateTable])
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact copy_choice _ 0 List.mem_cons_self
    | [i], _ => exact copy_choice _ _ (getD_available ws i)
    | [i, j], _ =>
      exact binary_choice _ _ _ _ (getD_available ws i) (getD_available ws j) (by simp [gateTable])
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil => exact not_choice _ 0 List.mem_cons_self
    | cons i _ => exact not_choice _ _ (getD_available ws i)
  | mod m => simp at hop
  | maj => simp at hop

private def reachable (target : Table) : ℕ → List Table → Bool
  | 0, ws => (0 :: ws).contains target
  | 1, ws => (choices (0 :: ws)).contains target
  | fuel + 2, ws =>
      (choices (0 :: ws)).any (fun c => reachable target (fuel + 1) (ws ++ [c]))

private theorem reachable_of_available (target : Table) (fuel : ℕ) (ws : List Table)
    (h : target ∈ 0 :: ws) : reachable target fuel ws = true := by
  induction fuel generalizing ws with
  | zero => exact List.contains_iff_mem.2 h
  | succ n ih =>
    cases n with
    | zero => exact List.contains_iff_mem.2 (copy_choice _ _ h)
    | succ n =>
      exact List.any_eq_true.2 ⟨0, copy_choice _ _ List.mem_cons_self,
        ih (ws ++ [0]) (List.mem_append_left [0] h)⟩

private theorem reachable_of_circuit (gs : List Gate) (ws : List Table) (fuel o : ℕ)
    (h : FanInTwo ⟨gs, o⟩) (hsize : gs.length ≤ fuel) :
    reachable ((wireTables gs ws).getD o 0) fuel ws = true := by
  induction gs generalizing ws fuel with
  | nil => exact reachable_of_available _ _ _ (getD_available ws o)
  | cons g gs ih =>
    let c := gateTable ws g
    have hc : c ∈ choices (0 :: ws) := gate_choice ws g (h g List.mem_cons_self)
    cases fuel with
    | zero => simp at hsize
    | succ n =>
      cases n with
      | zero =>
        have htail : gs.length ≤ 0 := Nat.le_of_succ_le_succ hsize
        obtain rfl : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp htail)
        let t := (ws ++ [c]).getD o 0
        have ht : t ∈ (0 :: ws) ++ [c] := getD_available (ws ++ [c]) o
        change (choices (0 :: ws)).contains t = true
        apply List.contains_iff_mem.2
        rcases List.mem_append.1 ht with ht | ht
        · exact copy_choice _ _ ht
        · rwa [List.mem_singleton.1 ht]
      | succ n =>
        exact List.any_eq_true.2 ⟨c, hc,
          ih (ws ++ [c]) (n + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (by
            simpa using hsize)⟩

private theorem first_choices : choices (0 :: inputs) =
    [0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0xffff, 0x5555, 0x3333, 0x0f0f, 0x00ff,
     0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc,
     0xf000, 0xfff0] := by decide +kernel

-- Check each possible first result separately, keeping the kernel's computation small.
set_option maxHeartbeats 0 in
private theorem search_excludes_path : reachable 0xf8c8 3 inputs = false := by
  apply Bool.eq_false_iff.2
  intro h
  obtain ⟨c, hc, hreach⟩ := List.any_eq_true.mp h
  rw [first_choices] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change reachable 0xf8c8 2 (inputs ++ [_]) = true at hreach
    exact (Bool.eq_false_iff.mp (show _ = false by decide +kernel)) hreach

private theorem four_gates (C : Circuit) (h : FanInTwo C)
    (heval : circuitFun 4 C = pathFunction) : 4 ≤ C.size := by
  by_contra! hsmall
  have hcode : (wireTables C.gates inputs).getD C.output 0 = (0xf8c8 : Table) := by
    apply table_ext
    intro x
    rw [← circuitTable C h x, heval, pathTable]
  have hreach :=
    reachable_of_circuit C.gates inputs 3 C.output h (by unfold Circuit.size at hsmall; omega)
  rw [hcode, search_excludes_path] at hreach
  cases hreach

private def first : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

private def second : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [5, 6]⟩], 7⟩

private theorem first_value : circuitFun 4 first = pathFunction := by
  funext x
  unfold circuitFun
  rw [inputList]
  unfold pathFunction
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem second_value : circuitFun 4 second = pathFunction := by
  funext x
  unfold circuitFun
  rw [inputList]
  unfold pathFunction
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem second_minimal : IsMinimalCircuit 4 second := by
  constructor
  · intro g hg
    simp only [second, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro D hD he
    exact four_gates D hD (he.trans second_value)

private def pulse (C : Circuit) (a : Fin 4) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (fun i : Fin 4 => decide (i = a)))).getD w false

private def separates (C : Circuit) (i j : Fin 4) (a b : ℕ) : Prop :=
  (pulse C i a = true ∧ pulse C j a = false ∧ pulse C j b = true ∧ pulse C i b = false) ∨
  (pulse C j a = true ∧ pulse C i a = false ∧ pulse C i b = true ∧ pulse C j b = false)

private def born (C : Circuit) (k : ℕ) (i j : Fin 4) : Prop :=
  ∃ (g : Gate) (a b : ℕ), C.gates[k]? = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
    a < 4 + k ∧ b < 4 + k ∧ separates C i j a b

private theorem first_shared : ∃ k, born first k 0 1 ∧ born first k 1 2 := by
  refine ⟨1, ⟨⟨.and, [1, 4]⟩, 1, 4, rfl, rfl, rfl, by decide, by decide, ?_⟩,
    ⟨⟨.and, [1, 4]⟩, 1, 4, rfl, rfl, rfl, by decide, by decide, ?_⟩⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩

private theorem not_born_or (k : ℕ) (i j : Fin 4) (ins : List ℕ)
    (hk : second.gates[k]? = some ⟨.or, ins⟩) : ¬ born second k i j := by
  rintro ⟨g, _, _, hg, hop, _⟩
  rw [hk] at hg
  cases Option.some.inj hg
  cases hop

private theorem born_separates (k : ℕ) (i j : Fin 4) (a b : ℕ)
    (hk : second.gates[k]? = some ⟨.and, [a, b]⟩)
    (h : born second k i j) : separates second i j a b := by
  obtain ⟨g, u, v, hg, _, hin, _, _, hsep⟩ := h
  rw [hk] at hg
  cases Option.some.inj hg
  simp only [List.cons.injEq, and_true] at hin
  obtain ⟨rfl, rfl⟩ := hin
  exact hsep

private theorem second_separate : ¬ ∃ k, born second k 0 1 ∧ born second k 1 2 := by
  rintro ⟨k, h01, h12⟩
  have hk : k < 4 := by
    obtain ⟨g, _, _, hg, _⟩ := h01
    by_contra! hn
    rw [List.getElem?_eq_none (show second.gates.length ≤ k from hn)] at hg
    cases hg
  interval_cases k
  · exact not_born_or 0 0 1 [1, 3] rfl h01
  · have h := born_separates 1 0 1 2 4 rfl h01
    rcases h with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ <;> cases h
  · have h := born_separates 2 1 2 0 1 rfl h12
    rcases h with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ <;> cases h
  · exact not_born_or 3 0 1 [5, 6] rfl h01

end PEqualNP.Outside.Meta203

open PEqualNP.Outside.Meta203 PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_203 :
    ∀ C1 C2 : PEqualNP.CircuitLowerBounds.Circuit,
      C1 = { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩], output := 7 } →
      C2 = { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩], output := 7 } →
      PEqualNP.MetaComplexity.IsMinimalCircuit 4 C2 ∧
      PEqualNP.MetaComplexity.circuitFun 4 C2 = PEqualNP.MetaComplexity.circuitFun 4 C1 ∧
      (∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C1.gates[j]? = some g ∧
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          g.inputs = [a, b] ∧
          a < 4 + j ∧
          b < 4 + j ∧
          (((C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD a false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = false ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD b false = false) ∨
            ((C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD a false = false ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD b false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = false))) ∧
        (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C1.gates[j]? = some g ∧
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          g.inputs = [a, b] ∧
          a < 4 + j ∧
          b < 4 + j ∧
          (((C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD a false = false ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD b false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = false) ∨
            ((C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD a false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = false ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = true ∧
              (C1.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD b false = false)))) ∧
      ¬ ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C2.gates[j]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        g.inputs = [a, b] ∧
        a < 4 + j ∧
        b < 4 + j ∧
        (((C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD a false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = false ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD b false = false) ∨
          ((C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD a false = false ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 0)))).getD b false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = false))) ∧
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C2.gates[j]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        g.inputs = [a, b] ∧
        a < 4 + j ∧
        b < 4 + j ∧
        (((C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD a false = false ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD b false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = false) ∨
          ((C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD a false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD a false = false ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 1)))).getD b false = true ∧
            (C2.wires (List.ofFn (fun i : Fin 4 => decide (i = 2)))).getD b false = false))) := by
  rintro C1 C2 rfl rfl
  change IsMinimalCircuit 4 second ∧ circuitFun 4 second = circuitFun 4 first ∧
    (∃ k, born first k 0 1 ∧ born first k 1 2) ∧
    ¬ ∃ k, born second k 0 1 ∧ born second k 1 2
  exact ⟨second_minimal, second_value.trans first_value.symm, first_shared, second_separate⟩
