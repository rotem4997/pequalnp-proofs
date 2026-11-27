import PEqualNP.MetaComplexity.Helpers.LgpB.OrChain

/-!
# Evaluating a circuit on all inputs at once

Helper for "MCSP is in NP". A circuit on `n` inputs is evaluated on all `2 ^ n` inputs
together: every wire carries its whole column of values, one entry per input, the entry of
the input `x` at position `tableIndex x`. One gate adds one column, computed pointwise from
the columns it reads. The column of the output wire is then the truth table of the circuit.

Contents:

* `tableIndex` is a bijection onto the numbers below `2 ^ n`, with inverse `bitsOf`;
* `inputColumn`, `gateColumn`, `columns` and their correctness against `Circuit.wires`;
* `outputColumn`, the truth table of a circuit, and what it means for it to agree with a
  total or a partial table.
-/

namespace PEqualNP.MetaComplexity.LgpB
open PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Table positions -/

theorem tableIndex_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem tableIndex_lt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [tableIndex_succ, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem testBit_tableIndex : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := tableIndex_lt (fun i : Fin n => x i.castSucc)
    rw [tableIndex_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

/-- The input whose table position is `j`: bit `i` of `j` on input wire `i`. -/
def bitsOf (n j : ℕ) : Fin n → Bool := fun i => Nat.testBit j i

theorem tableIndex_bitsOf {n j : ℕ} (h : j < 2 ^ n) : tableIndex (bitsOf n j) = j := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact testBit_tableIndex (bitsOf n j) ⟨i, hi⟩
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (tableIndex_lt _) hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h hp)]

theorem bitsOf_tableIndex {n : ℕ} (x : Fin n → Bool) : bitsOf n (tableIndex x) = x := by
  funext i
  exact testBit_tableIndex x i

theorem tableIndex_injective {n : ℕ} :
    Function.Injective (tableIndex : (Fin n → Bool) → ℕ) := by
  intro x y h
  rw [← bitsOf_tableIndex x, ← bitsOf_tableIndex y, h]

/-- `tableIndex` is a bijection from the inputs onto the positions below `2 ^ n`. -/
theorem tableIndex_bijOn (n : ℕ) :
    Set.BijOn (tableIndex : (Fin n → Bool) → ℕ) Set.univ {j | j < 2 ^ n} :=
  ⟨fun x _ => tableIndex_lt x, fun _ _ _ _ h => tableIndex_injective h,
    fun _ hj => ⟨bitsOf n _, trivial, tableIndex_bitsOf hj⟩⟩

/-- A statement about all inputs is a statement about all positions below `2 ^ n`. -/
theorem forall_input_iff {n : ℕ} (P : (Fin n → Bool) → Prop) :
    (∀ x, P x) ↔ ∀ j < 2 ^ n, P (bitsOf n j) := by
  constructor
  · intro h j _; exact h _
  · intro h x
    have := h (tableIndex x) (tableIndex_lt x)
    rwa [bitsOf_tableIndex] at this

/-! ## Lists read with a default -/

theorem getD_map_range {α : Type} (N : ℕ) (f : ℕ → α) (d : α) (j : ℕ) (h : j < N) :
    ((List.range N).map f).getD j d = f j := by
  simp [h]

theorem getD_map_default {α β : Type} (l : List α) (f : α → β) (a : ℕ) (d : α) :
    (l.map f).getD a (f d) = f (l.getD a d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[a]? <;> rfl

/-- Two lists of the same length are equal when they agree at every position below it. -/
theorem eq_of_getD {α : Type} (l l' : List α) (d : α) (N : ℕ) (h : l.length = N)
    (h' : l'.length = N) (e : ∀ j < N, l.getD j d = l'.getD j d) : l = l' := by
  apply List.ext_getElem (h.trans h'.symm)
  intro j h1 h2
  have := e j (h ▸ h1)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-! ## Columns -/

/-- The column of input wire `i` over the `2 ^ n` inputs: entry `j` is bit `i` of `j`. -/
def inputColumn (n i : ℕ) : List Bool :=
  (List.range (2 ^ n)).map fun j => Nat.testBit j i

theorem length_inputColumn (n i : ℕ) : (inputColumn n i).length = 2 ^ n := by
  simp [inputColumn]

theorem getD_inputColumn (n i j : ℕ) (h : j < 2 ^ n) :
    (inputColumn n i).getD j false = Nat.testBit j i :=
  getD_map_range _ _ _ _ h

theorem getD_inputColumn_tableIndex {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (inputColumn n i).getD (tableIndex x) false = x i := by
  rw [getD_inputColumn _ _ _ (tableIndex_lt x), testBit_tableIndex]

/-- The column of a gate over `N` positions: at each position, the gate's operation on the
entries of the columns it reads. A missing column or a missing entry reads `false`. -/
def gateColumn (g : Gate) (N : ℕ) (cols : List (List Bool)) : List Bool :=
  (List.range N).map fun j => g.op.eval (g.inputs.map fun a => (cols.getD a []).getD j false)

theorem length_gateColumn (g : Gate) (N : ℕ) (cols : List (List Bool)) :
    (gateColumn g N cols).length = N := by
  simp [gateColumn]

/-- Run gates on a list of columns: every gate appends its column. -/
def columns (gs : List Gate) (cols : List (List Bool)) (N : ℕ) : List (List Bool) :=
  gs.foldl (fun c g => c ++ [gateColumn g N c]) cols

theorem columns_nil (cols : List (List Bool)) (N : ℕ) : columns [] cols N = cols := rfl

theorem columns_cons (g : Gate) (gs : List Gate) (cols : List (List Bool)) (N : ℕ) :
    columns (g :: gs) cols N = columns gs (cols ++ [gateColumn g N cols]) N := rfl

theorem columns_append (gs gs' : List Gate) (cols : List (List Bool)) (N : ℕ) :
    columns (gs ++ gs') cols N = columns gs' (columns gs cols N) N := by
  simp [columns, List.foldl_append]

theorem columns_snoc (gs : List Gate) (g : Gate) (cols : List (List Bool)) (N : ℕ) :
    columns (gs ++ [g]) cols N
      = columns gs cols N ++ [gateColumn g N (columns gs cols N)] := by
  rw [columns_append]; rfl

theorem length_columns (gs : List Gate) : ∀ (cols : List (List Bool)) (N : ℕ),
    (columns gs cols N).length = cols.length + gs.length := by
  induction gs with
  | nil => intro cols N; rfl
  | cons g gs ih =>
    intro cols N
    rw [columns_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem length_of_mem_columns (gs : List Gate) : ∀ (cols : List (List Bool)) (N : ℕ),
    (∀ c ∈ cols, c.length = N) → ∀ c ∈ columns gs cols N, c.length = N := by
  induction gs with
  | nil => intro cols N h; exact h
  | cons g gs ih =>
    intro cols N h
    rw [columns_cons]
    apply ih
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h c hc
    · rw [List.mem_singleton.1 hc, length_gateColumn]

/-- The row of a list of columns at position `j`: the entry `j` of every column. -/
def rowAt (cols : List (List Bool)) (j : ℕ) : List Bool :=
  cols.map fun c => c.getD j false

theorem getD_rowAt (cols : List (List Bool)) (j a : ℕ) :
    (rowAt cols j).getD a false = (cols.getD a []).getD j false :=
  getD_map_default cols (fun c => c.getD j false) a []

/-- The columns of the wires, read at one position, are the wires on that row. -/
theorem rowAt_columns (gs : List Gate) : ∀ (cols : List (List Bool)) (N j : ℕ), j < N →
    rowAt (columns gs cols N) j = wiresFrom gs (rowAt cols j) := by
  induction gs with
  | nil => intro cols N j _; rfl
  | cons g gs ih =>
    intro cols N j hj
    rw [columns_cons, ih _ _ _ hj]
    have e : rowAt (cols ++ [gateColumn g N cols]) j
        = rowAt cols j ++ [g.op.eval (g.inputs.map fun i => (rowAt cols j).getD i false)] := by
      have e1 : (gateColumn g N cols).getD j false
          = g.op.eval (g.inputs.map fun a => (cols.getD a []).getD j false) :=
        getD_map_range _ _ _ _ hj
      have e2 : (fun i => (rowAt cols j).getD i false)
          = (fun a => (cols.getD a []).getD j false) := by
        funext a; exact getD_rowAt cols j a
      rw [e2, ← e1]
      simp [rowAt]
    rw [e]
    rfl

/-- The columns of the input wires of a circuit on `n` inputs. -/
def inputColumns (n : ℕ) : List (List Bool) :=
  List.ofFn fun i : Fin n => inputColumn n i

theorem length_inputColumns (n : ℕ) : (inputColumns n).length = n := by
  simp [inputColumns]

theorem rowAt_inputColumns {n : ℕ} (x : Fin n → Bool) :
    rowAt (inputColumns n) (tableIndex x) = List.ofFn x := by
  unfold rowAt inputColumns
  rw [List.map_ofFn]
  congr 1
  funext i
  exact getD_inputColumn_tableIndex x i

/-- The columns of all wires of `C` on `n` inputs: the input columns, then one per gate. -/
def wireColumns (C : Circuit) (n : ℕ) : List (List Bool) :=
  columns C.gates (inputColumns n) (2 ^ n)

theorem wireColumns_eq (C : Circuit) (n : ℕ) :
    wireColumns C n
      = columns C.gates (List.ofFn fun i : Fin n => inputColumn n i) (2 ^ n) := rfl

theorem length_wireColumns (C : Circuit) (n : ℕ) :
    (wireColumns C n).length = n + C.gates.length := by
  rw [wireColumns, length_columns, length_inputColumns]

theorem length_of_mem_wireColumns (C : Circuit) (n : ℕ) :
    ∀ c ∈ wireColumns C n, c.length = 2 ^ n := by
  apply length_of_mem_columns
  intro c hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hc
  exact length_inputColumn n i

theorem rowAt_wireColumns (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    rowAt (wireColumns C n) (tableIndex x) = C.wires (List.ofFn x) := by
  rw [wireColumns, rowAt_columns _ _ _ _ (tableIndex_lt x), rowAt_inputColumns, wires_eq]

/-- Correctness of the columns: the entry of column `a` at the position of the input `x` is
the value of wire `a` on `x`. -/
theorem getD_wireColumns (C : Circuit) {n : ℕ} (x : Fin n → Bool) (a : ℕ) :
    ((columns C.gates (List.ofFn fun i : Fin n => inputColumn n i) (2 ^ n)).getD a []).getD
      (tableIndex x) false = (C.wires (List.ofFn x)).getD a false := by
  rw [← wireColumns_eq, ← getD_rowAt, rowAt_wireColumns]

/-- The value of the circuit is read in the column of its output wire. -/
theorem eval_eq_getD_columns (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    C.eval (List.ofFn x)
      = ((columns C.gates (List.ofFn fun i : Fin n => inputColumn n i) (2 ^ n)).getD
          C.output []).getD (tableIndex x) false :=
  (getD_wireColumns C x C.output).symm

/-! ## The output column -/

/-- The truth table of `C` on `n` inputs, read off the columns: the column of the output wire,
or `2 ^ n` times `false` when the output wire does not exist. -/
def outputColumn (C : Circuit) (n : ℕ) : List Bool :=
  (List.range (2 ^ n)).map fun j => ((wireColumns C n).getD C.output []).getD j false

theorem length_outputColumn (C : Circuit) (n : ℕ) : (outputColumn C n).length = 2 ^ n := by
  simp [outputColumn]

theorem getD_outputColumn (C : Circuit) (n j : ℕ) (h : j < 2 ^ n) :
    (outputColumn C n).getD j false = ((wireColumns C n).getD C.output []).getD j false :=
  getD_map_range _ _ _ _ h

theorem getD_outputColumn_tableIndex (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    (outputColumn C n).getD (tableIndex x) false = C.eval (List.ofFn x) := by
  rw [getD_outputColumn _ _ _ (tableIndex_lt x), eval_eq_getD_columns]
  rfl

theorem getD_outputColumn_eval (C : Circuit) (n j : ℕ) (h : j < 2 ^ n) :
    (outputColumn C n).getD j false = C.eval (List.ofFn (bitsOf n j)) := by
  rw [← getD_outputColumn_tableIndex, tableIndex_bitsOf h]

/-- The output column is the list of the values of the circuit, position by position. -/
theorem outputColumn_eq_map_eval (C : Circuit) (n : ℕ) :
    outputColumn C n = (List.range (2 ^ n)).map fun j => C.eval (List.ofFn (bitsOf n j)) := by
  apply eq_of_getD _ _ false (2 ^ n) (length_outputColumn C n) (by simp)
  intro j hj
  rw [getD_outputColumn_eval _ _ _ hj, getD_map_range _ _ _ _ hj]

/-- When the output wire exists, the output column is its column. -/
theorem outputColumn_of_lt (C : Circuit) (n : ℕ) (h : C.output < n + C.gates.length) :
    outputColumn C n = (wireColumns C n).getD C.output [] := by
  have hl : C.output < (wireColumns C n).length := by rw [length_wireColumns]; exact h
  have hm : (wireColumns C n).getD C.output [] ∈ wireColumns C n := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  apply eq_of_getD _ _ false (2 ^ n) (length_outputColumn C n)
    (length_of_mem_wireColumns C n _ hm)
  intro j hj
  exact getD_outputColumn C n j hj

/-- When the output wire does not exist, the output column is all `false`. -/
theorem outputColumn_of_le (C : Circuit) (n : ℕ) (h : n + C.gates.length ≤ C.output) :
    outputColumn C n = List.replicate (2 ^ n) false := by
  have hl : (wireColumns C n).length ≤ C.output := by rw [length_wireColumns]; exact h
  apply eq_of_getD _ _ false (2 ^ n) (length_outputColumn C n) (by simp)
  intro j hj
  rw [getD_outputColumn C n j hj, List.getD_eq_default _ _ hl]
  simp

/-- A circuit computes the function of a total table of length `2 ^ n` exactly when its output
column is the table. -/
theorem eval_eq_tableFun_iff (C : Circuit) (n : ℕ) (T : List Bool) (hT : T.length = 2 ^ n) :
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = tableFun n T x) ↔ outputColumn C n = T := by
  constructor
  · intro h
    apply eq_of_getD _ _ false (2 ^ n) (length_outputColumn C n) hT
    intro j hj
    rw [getD_outputColumn_eval _ _ _ hj, h, tableFun, tableIndex_bitsOf hj]
  · intro h x
    rw [← getD_outputColumn_tableIndex, h]
    rfl

/-- A circuit is consistent with a partial table exactly when its output column has the
defined entries of the table at the positions below `2 ^ n`. -/
theorem consistent_iff (C : Circuit) (n : ℕ) (T : List (Option Bool)) :
    Consistent n T (fun x : Fin n → Bool => C.eval (List.ofFn x)) ↔
      ∀ j < 2 ^ n, ∀ b : Bool, T.getD j none = some b →
        (outputColumn C n).getD j false = b := by
  unfold Consistent
  rw [forall_input_iff]
  constructor
  · intro h j hj b hb
    rw [getD_outputColumn_eval _ _ _ hj]
    exact h j hj b (by rw [tableIndex_bitsOf hj]; exact hb)
  · intro h j hj b hb
    rw [tableIndex_bitsOf hj] at hb
    show C.eval (List.ofFn (bitsOf n j)) = b
    rw [← getD_outputColumn_eval _ _ _ hj]
    exact h j hj b hb

/-! ## Bounded wire indices

A wire index at least `m` reads `false` as long as fewer than `m` wires exist, so every index
can be cut down to `m`. This bounds the length of a circuit written with unary indices. -/

/-- Cut every wire index of a gate down to `m`. -/
def clampGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map fun a => min a m⟩

theorem getD_min {w : List Bool} {m : ℕ} (h : w.length ≤ m) (a : ℕ) :
    w.getD (min a m) false = w.getD a false := by
  by_cases ha : a ≤ m
  · rw [Nat.min_eq_left ha]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

theorem wiresFrom_clamp (m : ℕ) (gs : List Gate) : ∀ w : List Bool,
    w.length + gs.length ≤ m → wiresFrom (gs.map (clampGate m)) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    rw [List.length_cons] at h
    have hw : w.length ≤ m := by omega
    have e : (clampGate m g).op.eval ((clampGate m g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      have e1 : ((clampGate m g).inputs.map fun i => w.getD i false)
          = g.inputs.map fun i => w.getD i false := by
        simp only [clampGate, List.map_map]
        apply List.map_congr_left
        intro a _
        exact getD_min hw a
      rw [e1]; rfl
    have s1 : wiresFrom ((g :: gs).map (clampGate m)) w
        = wiresFrom (gs.map (clampGate m))
            (w ++ [(clampGate m g).op.eval ((clampGate m g).inputs.map fun i => w.getD i false)]) :=
      rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, e]
    apply ih
    rw [List.length_append, List.length_singleton]
    omega

/-- Cut every wire index of a circuit, the output included, down to `m`. -/
def clampCircuit (m : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (clampGate m), min C.output m⟩

theorem eval_clampCircuit (m : ℕ) (C : Circuit) (x : List Bool)
    (h : x.length + C.gates.length ≤ m) : (clampCircuit m C).eval x = C.eval x := by
  have hl : (wiresFrom C.gates x).length ≤ m := by rw [length_wiresFrom]; exact h
  show (wiresFrom (C.gates.map (clampGate m)) x).getD (min C.output m) false
    = (wiresFrom C.gates x).getD C.output false
  rw [wiresFrom_clamp m _ _ h, getD_min hl]

theorem size_clampCircuit (m : ℕ) (C : Circuit) : (clampCircuit m C).size = C.size := by
  simp [clampCircuit, Circuit.size]

theorem fanInTwo_clampCircuit (m : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (clampCircuit m C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  have := h g' hg'
  exact ⟨this.1, by simpa [clampGate] using this.2⟩

/-! ## Evaluation by delivering one wire at a time

A second way to evaluate, on one input, in which every step is a single left to right pass.
A row is the list of the gates not yet evaluated, each operand being either a value already
delivered or a reference counting how many more wires must be delivered first, together with
one more operand for the output wire. A step removes the first gate, which has all the values
it will ever get, and delivers its value to the references that have counted down to zero.
A reference that never receives a value reads `false`. -/

/-- An operand: a reference to the wire `d` places ahead of the next one to be delivered, or a
value already delivered. -/
inductive Arg where
  /-- A wire not delivered yet: `d` more wires come before it. -/
  | ref (d : ℕ)
  /-- A delivered value. -/
  | val (b : Bool)

/-- What an operand reads now: its value, or `false` if none was delivered. -/
def Arg.read : Arg → Bool
  | Arg.ref _ => false
  | Arg.val b => b

/-- Deliver the value `v` of the next wire to an operand. -/
def Arg.sub (v : Bool) : Arg → Arg
  | Arg.ref 0 => Arg.val v
  | Arg.ref (d + 1) => Arg.ref d
  | Arg.val b => Arg.val b

/-- A gate with partly delivered operands. -/
structure Cell where
  /-- The operation. -/
  op : GateOp
  /-- The operands. -/
  args : List Arg

/-- The value of a cell on what its operands read now. -/
def Cell.value (c : Cell) : Bool := c.op.eval (c.args.map Arg.read)

/-- Deliver the value `v` of the next wire to a cell. -/
def Cell.sub (v : Bool) (c : Cell) : Cell := ⟨c.op, c.args.map (Arg.sub v)⟩

/-- One step on a row: remove the first cell and deliver its value to the others and to the
output operand. A row with no cell is left alone. -/
def rowStep : List Cell × Arg → List Cell × Arg
  | ([], o) => ([], o)
  | (c :: r, o) => (r.map (Cell.sub c.value), Arg.sub c.value o)

/-- The operand for wire `a` once the wires `w` are delivered. -/
def argAt (w : List Bool) (a : ℕ) : Arg :=
  if a < w.length then Arg.val (w.getD a false) else Arg.ref (a - w.length)

/-- The cell of a gate once the wires `w` are delivered. -/
def cellAt (w : List Bool) (g : Gate) : Cell := ⟨g.op, g.inputs.map (argAt w)⟩

theorem argAt_nil (a : ℕ) : argAt [] a = Arg.ref a := rfl

theorem cellAt_nil (g : Gate) : cellAt [] g = ⟨g.op, g.inputs.map Arg.ref⟩ := rfl

theorem read_argAt (w : List Bool) (a : ℕ) : (argAt w a).read = w.getD a false := by
  unfold argAt
  split
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem sub_argAt (w : List Bool) (v : Bool) (a : ℕ) :
    Arg.sub v (argAt w a) = argAt (w ++ [v]) a := by
  unfold argAt
  rw [List.length_append, List.length_singleton]
  by_cases h1 : a < w.length
  · have h1' : a < w.length + 1 := by omega
    simp only [h1, h1', ↓reduceIte]
    rw [List.getD_append _ _ _ _ h1]; rfl
  · by_cases h2 : a = w.length
    · subst h2
      have h3 : w.length < w.length + 1 := by omega
      simp only [lt_self_iff_false, h3, ↓reduceIte, Nat.sub_self]
      rw [getD_snoc_eq]; rfl
    · have h3 : ¬ a < w.length + 1 := by omega
      simp only [h1, h3, ↓reduceIte]
      obtain ⟨d, hd⟩ : ∃ d, a - w.length = d + 1 := ⟨a - w.length - 1, by omega⟩
      rw [hd, show a - (w.length + 1) = d by omega]; rfl

theorem value_cellAt (w : List Bool) (g : Gate) :
    (cellAt w g).value = g.op.eval (g.inputs.map fun a => w.getD a false) := by
  unfold Cell.value cellAt
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact read_argAt w a

theorem sub_cellAt (w : List Bool) (v : Bool) (g : Gate) :
    Cell.sub v (cellAt w g) = cellAt (w ++ [v]) g := by
  unfold Cell.sub cellAt
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact sub_argAt w v a

theorem rowStep_cons (w : List Bool) (g : Gate) (gs : List Gate) (out : ℕ) :
    rowStep ((g :: gs).map (cellAt w), argAt w out)
      = (gs.map (cellAt (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])),
          argAt (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) out) := by
  show ((gs.map (cellAt w)).map (Cell.sub (cellAt w g).value), Arg.sub (cellAt w g).value _) = _
  rw [value_cellAt, sub_argAt, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g' _
  exact sub_cellAt w _ g'

theorem rowStep_iterate_nil (k : ℕ) (o : Arg) : rowStep^[k] ([], o) = ([], o) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

/-- After `k` steps the first `k` gates are evaluated and their wires delivered. -/
theorem rowStep_iterate (gs : List Gate) (out : ℕ) : ∀ (k : ℕ) (w : List Bool),
    rowStep^[k] (gs.map (cellAt w), argAt w out)
      = ((gs.drop k).map (cellAt (wiresFrom (gs.take k) w)),
          argAt (wiresFrom (gs.take k) w) out) := by
  induction gs with
  | nil =>
    intro k w
    simp only [List.take_nil, List.drop_nil, List.map_nil]
    exact rowStep_iterate_nil k _
  | cons g gs ih =>
    intro k w
    cases k with
    | zero => rfl
    | succ k =>
      rw [Function.iterate_succ_apply, rowStep_cons, ih]
      rfl

/-- After at least as many steps as there are gates, no cell is left and the output operand
reads the value of the output wire. -/
theorem rowStep_iterate_all (gs : List Gate) (out : ℕ) (w : List Bool) (k : ℕ)
    (h : gs.length ≤ k) :
    rowStep^[k] (gs.map (cellAt w), argAt w out) = ([], argAt (wiresFrom gs w) out) := by
  rw [rowStep_iterate, List.drop_of_length_le h, List.take_of_length_le h]
  rfl

/-- An input bit as a gate reading no wire: AND for `true`, OR for `false`. -/
def constGate (b : Bool) : Gate := ⟨if b = true then GateOp.and else GateOp.or, []⟩

theorem wiresFrom_constGate (l : List Bool) : ∀ w : List Bool,
    wiresFrom (l.map constGate) w = w ++ l := by
  induction l with
  | nil => intro w; simp [wiresFrom]
  | cons b l ih =>
    intro w
    have s : wiresFrom ((b :: l).map constGate) w
        = wiresFrom (l.map constGate)
            (w ++ [(constGate b).op.eval ((constGate b).inputs.map fun i => w.getD i false)]) :=
      rfl
    have e : (constGate b).op.eval ((constGate b).inputs.map fun i => w.getD i false) = b := by
      cases b <;> simp [constGate, GateOp.eval]
    rw [s, e, ih, List.append_assoc]
    rfl

/-- The row of a circuit on the input bits `x`: the input bits as gates reading nothing, then
the gates, every operand a reference, and the output wire as the output operand. -/
def initRow (C : Circuit) (x : List Bool) : List Cell × Arg :=
  ((x.map constGate ++ C.gates).map (cellAt []), argAt [] C.output)

/-- Running the row of a circuit for at least as many steps as it has wires leaves the value of
the circuit in the output operand. -/
theorem rowStep_initRow (C : Circuit) (x : List Bool) (k : ℕ)
    (h : x.length + C.gates.length ≤ k) :
    ∃ o : Arg, rowStep^[k] (initRow C x) = ([], o) ∧ o.read = C.eval x := by
  refine ⟨argAt (wiresFrom (x.map constGate ++ C.gates) []) C.output, ?_, ?_⟩
  · exact rowStep_iterate_all _ _ _ _ (by simpa using h)
  · rw [read_argAt, wiresFrom_append, wiresFrom_constGate, List.nil_append]
    rfl

end PEqualNP.MetaComplexity.LgpB
