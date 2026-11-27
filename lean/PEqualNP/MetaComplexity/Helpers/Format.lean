import PEqualNP.MetaComplexity.Helpers.RowCode

/-!
# The format of a witness for partial MCSP, checked by finite-state transducers

Helper for "partial MCSP is in NP". A witness is a string over `Sym`: a list of rows, each row
being input bits (bare `A` for `true`, bare `O` for `false`), then the gates of a circuit with
every operand a reference, then the output reference, then a table entry.

* `WRow`, `encW`, `encWs`: rows as data and their code, equal to `encState` of `initRow`
  (`encWs_eq_encState`).
* `inc`, `bitsL`: the binary counter on the input bits.
* The transducers `neutStr`, `headStr`, `tailStr`, `tabStr`, `gatesStr`, `succStr` on the
  witness and `unaryStr`, `instStr`, `sepFlags` on the instance, each given by a transition
  function, an end function and a start state, with their values on coded rows.

The well-formedness transducer and the unique reading of a code are in `WellFormed`.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Machines

/-! ## Rows as data -/

/-- The symbol of an input bit: a cell with no operand. -/
def bsym : Bool → Sym
  | true => Sym.A
  | false => Sym.O

/-- A reference operand as a string. -/
def encRef (a : ℕ) : List Sym := Sym.R :: List.replicate a Sym.t

/-- A gate as a string, every operand a reference. -/
def encGate (g : Gate) : List Sym := opSym g.op :: g.inputs.flatMap encRef

/-- The gates and the output reference of a circuit as a string. -/
def encBody (C : Circuit) : List Sym := C.gates.flatMap encGate ++ Sym.Z :: encRef C.output

/-- A witness row: input bits, a circuit, a table entry. -/
abbrev WRow : Type := List Bool × Circuit × Option Bool

/-- A row without its entry. -/
def rowPre (w : WRow) : List Sym := w.1.map bsym ++ encBody w.2.1

/-- A row as a string. -/
def encW (w : WRow) : List Sym := rowPre w ++ [symE w.2.2]

/-- A list of rows as a string. -/
def encWs (W : List WRow) : List Sym := W.flatMap encW

theorem encWs_cons (w : WRow) (W : List WRow) : encWs (w :: W) = encW w ++ encWs W := rfl

theorem encCell_cellAt (g : Gate) : encCell (cellAt [] g) = encGate g := by
  simp only [encCell, cellAt, encGate, List.flatMap_map]
  rfl

theorem encCell_const (b : Bool) : encCell (cellAt [] (constGate b)) = [bsym b] := by
  cases b <;> rfl

theorem encW_eq_encRow (w : WRow) : encW w = encRow (initRow w.2.1 w.1, w.2.2) := by
  obtain ⟨bs, C, e⟩ := w
  have h1 : ∀ x : List Bool,
      ((x.map constGate).map (cellAt [])).flatMap encCell = x.map bsym := by
    intro x
    induction x with
    | nil => rfl
    | cons b x ih =>
      simp only [List.map_cons, List.flatMap_cons, encCell_const, ih]
      rfl
  have h2 : ∀ gs : List Gate, (gs.map (cellAt [])).flatMap encCell = gs.flatMap encGate := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons, List.flatMap_cons, encCell_cellAt, ih]
  show (bs.map bsym ++ (C.gates.flatMap encGate ++ Sym.Z :: encRef C.output)) ++ [symE e]
    = ((bs.map constGate ++ C.gates).map (cellAt [])).flatMap encCell
        ++ Sym.Z :: (encArg (Arg.ref C.output) ++ [symE e])
  rw [List.map_append, List.flatMap_append, h1, h2]
  simp only [List.append_assoc, List.cons_append]
  rfl

/-- The code of a list of rows is the code of the state made of their initial rows. -/
theorem encWs_eq_encState (W : List WRow) :
    encWs W = encState (W.map fun w => ((initRow w.2.1 w.1, w.2.2) : Row)) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    rw [encWs_cons, ih, encW_eq_encRow]
    rfl

/-- A gate with operation AND, OR or NOT and one or two operands. -/
def GoodGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    (g.inputs.length = 1 ∨ g.inputs.length = 2)

/-- A circuit all of whose gates are good. -/
def GoodC (C : Circuit) : Prop := ∀ g ∈ C.gates, GoodGate g

theorem goodGate_inputs {g : Gate} (h : GoodGate g) :
    (∃ a, g.inputs = [a]) ∨ ∃ a b, g.inputs = [a, b] := by
  obtain ⟨op, ins⟩ := g
  rcases h.2 with h | h
  · left
    match ins, h with
    | [a], _ => exact ⟨a, rfl⟩
  · right
    match ins, h with
    | [a, b], _ => exact ⟨a, b, rfl⟩

theorem opSym_cases (op : GateOp) : opSym op = Sym.A ∨ opSym op = Sym.O ∨ opSym op = Sym.N := by
  cases op <;> simp [opSym]

theorem encGate_one (op : GateOp) (a : ℕ) (T : List Sym) :
    encGate ⟨op, [a]⟩ ++ T = opSym op :: Sym.R :: (List.replicate a Sym.t ++ T) := by
  simp [encGate, encRef]

theorem encGate_two (op : GateOp) (a b : ℕ) (T : List Sym) :
    encGate ⟨op, [a, b]⟩ ++ T
      = opSym op :: Sym.R :: (List.replicate a Sym.t ++ Sym.R :: (List.replicate b Sym.t ++ T)) := by
  simp [encGate, encRef]

theorem encBody_append (C : Circuit) (r : List Sym) :
    encBody C ++ r = C.gates.flatMap encGate ++ Sym.Z :: (encRef C.output ++ r) := by
  simp [encBody]

theorem encW_append (w : WRow) (r : List Sym) :
    encW w ++ r = w.1.map bsym ++ (encBody w.2.1 ++ symE w.2.2 :: r) := by
  simp [encW, rowPre]

/-- A string that starts like the part of a row after its input bits: the output mark, or an
operation followed by a reference. -/
def BodyStart (X : List Sym) : Prop :=
  (∃ r, X = Sym.Z :: r) ∨ ∃ s r, X = s :: Sym.R :: r ∧ (s = Sym.A ∨ s = Sym.O ∨ s = Sym.N)

theorem bodyStart_encBody (C : Circuit) (hC : GoodC C) (r : List Sym) :
    BodyStart (encBody C ++ r) := by
  rw [encBody_append]
  cases hg : C.gates with
  | nil => exact Or.inl ⟨_, rfl⟩
  | cons g gs =>
    have hgood : GoodGate g := hC g (by rw [hg]; exact List.mem_cons_self)
    obtain ⟨op, ins⟩ := g
    rw [List.flatMap_cons, List.append_assoc]
    rcases goodGate_inputs hgood with ⟨a, ha⟩ | ⟨a, b, ha⟩
    · simp only at ha
      subst ha
      rw [encGate_one]
      exact Or.inr ⟨_, _, rfl, opSym_cases op⟩
    · simp only at ha
      subst ha
      rw [encGate_two]
      exact Or.inr ⟨_, _, rfl, opSym_cases op⟩

theorem isEnd_bsym (b : Bool) : (bsym b).isEnd = false := by cases b <;> rfl

theorem isEnd_encRef (a : ℕ) : ∀ s ∈ encRef a, s.isEnd = false := isEnd_encArg (Arg.ref a)

theorem isEnd_encBody (C : Circuit) : ∀ s ∈ encBody C, s.isEnd = false := by
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨g, _, hg⟩ := List.mem_flatMap.1 hs
    rw [← encCell_cellAt] at hg
    exact isEnd_encCell _ s hg
  · rcases List.mem_cons.1 hs with rfl | hs
    · rfl
    · exact isEnd_encRef _ s hs

theorem isEnd_bits (bs : List Bool) : ∀ s ∈ bs.map bsym, s.isEnd = false := by
  intro s hs
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hs
  exact isEnd_bsym b

theorem isEnd_rowPre (w : WRow) : ∀ s ∈ rowPre w, s.isEnd = false := by
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · exact isEnd_bits _ s hs
  · exact isEnd_encBody _ s hs

/-- The row with its entry removed. -/
def neutW (w : WRow) : WRow := (w.1, w.2.1, none)

/-! ## The binary counter -/

/-- Add one to a number written in binary, least significant bit first, keeping the length. -/
def inc : List Bool → List Bool
  | [] => []
  | false :: l => true :: l
  | true :: l => false :: inc l

/-- The `m` lowest bits of `j`, least significant first. -/
def bitsL : ℕ → ℕ → List Bool
  | 0, _ => []
  | m + 1, j => decide (j % 2 = 1) :: bitsL m (j / 2)

theorem length_bitsL (m : ℕ) : ∀ j, (bitsL m j).length = m := by
  induction m with
  | zero => intro j; rfl
  | succ m ih => intro j; simp [bitsL, ih]

theorem bitsL_eq_ofFn (m : ℕ) : ∀ j, bitsL m j = List.ofFn (bitsOf m j) := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
    intro j
    rw [List.ofFn_succ, bitsL, ih]
    congr 1
    · simp [bitsOf, Nat.testBit_zero]
    · congr 1
      funext i
      simp [bitsOf, Nat.testBit_succ]

theorem inc_bitsL (m : ℕ) : ∀ j, inc (bitsL m j) = bitsL m (j + 1) := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
    intro j
    by_cases h : j % 2 = 1
    · have h1 : ¬ (j + 1) % 2 = 1 := by omega
      have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
      simp [bitsL, inc, h, h1, h2, ih]
    · have h1 : (j + 1) % 2 = 1 := by omega
      have h2 : (j + 1) / 2 = j / 2 := by omega
      simp [bitsL, inc, h, h1, h2]

theorem bitsL_zero (m : ℕ) : bitsL m 0 = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bitsL, ih, List.replicate_succ]

theorem bitsL_eq_zero_iff (m : ℕ) : ∀ k, bitsL m k = List.replicate m false ↔ 2 ^ m ∣ k := by
  induction m with
  | zero => intro k; simp [bitsL]
  | succ m ih =>
    intro k
    have e : bitsL (m + 1) k = List.replicate (m + 1) false
        ↔ ¬ k % 2 = 1 ∧ bitsL m (k / 2) = List.replicate m false := by
      simp [bitsL, List.replicate_succ]
    rw [e, ih]
    constructor
    · rintro ⟨h1, c, hc⟩
      refine ⟨c, ?_⟩
      have : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by ring
      omega
    · rintro ⟨c, hc⟩
      have : 2 ^ (m + 1) * c = 2 * (2 ^ m * c) := by ring
      exact ⟨by omega, c, by omega⟩

theorem false_mem_bitsL (m : ℕ) : ∀ j, j + 1 < 2 ^ m → false ∈ bitsL m j := by
  induction m with
  | zero => intro j h; simp at h
  | succ m ih =>
    intro j h
    rw [pow_succ] at h
    by_cases h1 : j % 2 = 1
    · have := ih (j / 2) (by omega)
      simp [bitsL, this]
    · simp [bitsL, h1]

theorem not_false_mem_bitsL (m : ℕ) : false ∉ bitsL m (2 ^ m - 1) := by
  induction m with
  | zero => simp [bitsL]
  | succ m ih =>
    have hp : 0 < 2 ^ m := Nat.pos_of_ne_zero (by simp)
    have h1 : (2 ^ (m + 1) - 1) % 2 = 1 := by rw [pow_succ]; omega
    have h2 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by rw [pow_succ]; omega
    simp only [bitsL, h1, h2, decide_true, List.mem_cons, Bool.false_eq_true, false_or]
    exact ih

/-! ## Removing the entries -/

/-- A symbol with a table entry replaced by the absent entry. -/
def neutSym (s : Sym) : Sym := if s.isEnd then Sym.En else s

/-- The transducer that removes the entries. -/
def δneut : Unit → Sym → Unit × Option Sym × Option Sym :=
  fun _ s => ((), some (neutSym s), none)

/-- Nothing is written at the end of the input. -/
def finNeut : Unit → Option Sym := fun _ => none

/-- The string with every entry replaced by the absent entry. -/
def neutStr (l : List Sym) : List Sym := fstRun2 δneut finNeut () l

theorem neutStr_eq_map (l : List Sym) : neutStr l = l.map neutSym := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    show neutSym s :: neutStr l = _
    rw [ih]
    rfl

theorem neutSym_of_not_end {s : Sym} (h : s.isEnd = false) : neutSym s = s := by
  simp [neutSym, h]

theorem neutSym_symE (e : Option Bool) : neutSym (symE e) = Sym.En := by
  rcases e with _ | _ | _ <;> rfl

theorem map_neutSym_of_not_end (l : List Sym) (h : ∀ s ∈ l, s.isEnd = false) :
    l.map neutSym = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.map_cons, neutSym_of_not_end (h s List.mem_cons_self),
      ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]

theorem map_neutSym_encW (w : WRow) : (encW w).map neutSym = encW (neutW w) := by
  show (rowPre w ++ [symE w.2.2]).map neutSym = rowPre w ++ [Sym.En]
  rw [List.map_append, map_neutSym_of_not_end _ (isEnd_rowPre w)]
  simp [neutSym_symE]

theorem neutStr_encWs (W : List WRow) : neutStr (encWs W) = encWs (W.map neutW) := by
  rw [neutStr_eq_map]
  induction W with
  | nil => rfl
  | cons w W ih =>
    rw [encWs_cons, List.map_append, ih, map_neutSym_encW]
    rfl

/-! ## The first row, and the other rows -/

/-- The transducer that keeps the first row, without its entry. The state says whether the
first row is over. -/
def δhead : Bool → Sym → Bool × Option Sym × Option Sym
  | false, s => (s.isEnd, some (neutSym s), none)
  | true, _ => (true, none, none)

/-- Nothing is written at the end of the input. -/
def finHead : Bool → Option Sym := fun _ => none

/-- The first row, without its entry. -/
def headStr (l : List Sym) : List Sym := fstRun2 δhead finHead false l

/-- The transducer that drops the first row and removes the entries of the others. -/
def δtail : Bool → Sym → Bool × Option Sym × Option Sym
  | false, s => (s.isEnd, none, none)
  | true, s => (true, some (neutSym s), none)

/-- Nothing is written at the end of the input. -/
def finTail : Bool → Option Sym := fun _ => none

/-- The rows after the first, without their entries. -/
def tailStr (l : List Sym) : List Sym := fstRun2 δtail finTail false l

theorem head_pre (l r : List Sym) (h : ∀ s ∈ l, s.isEnd = false) :
    fstRun2 δhead finHead false (l ++ r) = l ++ fstRun2 δhead finHead false r := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δhead false s = (false, some s, none) := by simp [δhead, hs, neutSym]
    show (δhead false s).2.1.toList ++ (δhead false s).2.2.toList
      ++ fstRun2 δhead finHead (δhead false s).1 (l ++ r) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem head_done (r : List Sym) : fstRun2 δhead finHead true r = [] := by
  induction r with
  | nil => rfl
  | cons s r ih => exact ih

theorem headStr_encW (w : WRow) (r : List Sym) : headStr (encW w ++ r) = encW (neutW w) := by
  show fstRun2 δhead finHead false ((rowPre w ++ [symE w.2.2]) ++ r) = rowPre w ++ [Sym.En]
  rw [List.append_assoc, head_pre _ _ (isEnd_rowPre w)]
  congr 1
  have : fstRun2 δhead finHead false ([symE w.2.2] ++ r)
      = Sym.En :: fstRun2 δhead finHead true r := by
    rcases w.2.2 with _ | _ | _ <;> rfl
  rw [this, head_done]

theorem tail_pre (l r : List Sym) (h : ∀ s ∈ l, s.isEnd = false) :
    fstRun2 δtail finTail false (l ++ r) = fstRun2 δtail finTail false r := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δtail false s = (false, none, none) := by simp [δtail, hs]
    show (δtail false s).2.1.toList ++ (δtail false s).2.2.toList
      ++ fstRun2 δtail finTail (δtail false s).1 (l ++ r) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem tail_copy (r : List Sym) : fstRun2 δtail finTail true r = r.map neutSym := by
  induction r with
  | nil => rfl
  | cons s r ih =>
    show neutSym s :: fstRun2 δtail finTail true r = _
    rw [ih]
    rfl

theorem tailStr_encW (w : WRow) (r : List Sym) : tailStr (encW w ++ r) = neutStr r := by
  show fstRun2 δtail finTail false ((rowPre w ++ [symE w.2.2]) ++ r) = _
  rw [List.append_assoc, tail_pre _ _ (isEnd_rowPre w), neutStr_eq_map, ← tail_copy]
  rcases w.2.2 with _ | _ | _ <;> rfl

theorem headStr_encWs (w : WRow) (W : List WRow) : headStr (encWs (w :: W)) = encW (neutW w) :=
  headStr_encW w _

theorem tailStr_encWs (w : WRow) (W : List WRow) :
    tailStr (encWs (w :: W)) = encWs (W.map neutW) := by
  rw [encWs_cons, tailStr_encW, neutStr_encWs]

/-! ## The table entries -/

/-- The transducer that writes the entries in the code of a partial table. -/
def δtab : Unit → Sym → Unit × Option Bool × Option Bool
  | _, Sym.E0 => ((), some true, some false)
  | _, Sym.E1 => ((), some true, some true)
  | _, Sym.En => ((), some false, some false)
  | _, _ => ((), none, none)

/-- Nothing is written at the end of the input. -/
def finTab : Unit → Option Bool := fun _ => none

/-- The entries of the rows, as `encodePartial` writes them. -/
def tabStr (l : List Sym) : List Bool := fstRun2 δtab finTab () l

theorem tab_pre (l r : List Sym) (h : ∀ s ∈ l, s.isEnd = false) :
    fstRun2 δtab finTab () (l ++ r) = fstRun2 δtab finTab () r := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δtab () s = ((), none, none) := by cases s <;> first | rfl | simp [Sym.isEnd] at hs
    show (δtab () s).2.1.toList ++ (δtab () s).2.2.toList
      ++ fstRun2 δtab finTab (δtab () s).1 (l ++ r) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem tabStr_encWs (W : List WRow) :
    tabStr (encWs W) = PEqualNP.MetaComplexity.encodePartial (W.map fun w => w.2.2) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    show fstRun2 δtab finTab () ((rowPre w ++ [symE w.2.2]) ++ encWs W) = _
    rw [List.append_assoc, tab_pre _ _ (isEnd_rowPre w)]
    have : fstRun2 δtab finTab () ([symE w.2.2] ++ encWs W)
        = PEqualNP.MetaComplexity.encodePartial [w.2.2] ++ tabStr (encWs W) := by
      rcases w.2.2 with _ | _ | _ <;> rfl
    rw [this, ih]
    simp [PEqualNP.MetaComplexity.encodePartial]

/-! ## Counting the gates of the first row -/

/-- The states of the gate counter: in the first row, with a flag set when the last symbol was
an operation; or after the first row. -/
inductive GQ where
  | run (afterOp : Bool)
  | done
  deriving DecidableEq, Fintype

/-- The transducer that writes one mark for every cell of the first row that has an operand:
a mark for every reference that directly follows an operation. -/
def δgates : GQ → Sym → GQ × Option Bool × Option Bool
  | GQ.run _, Sym.A => (GQ.run true, none, none)
  | GQ.run _, Sym.O => (GQ.run true, none, none)
  | GQ.run _, Sym.N => (GQ.run true, none, none)
  | GQ.run true, Sym.R => (GQ.run false, some true, none)
  | GQ.run _, s => (if s.isEnd then GQ.done else GQ.run false, none, none)
  | GQ.done, _ => (GQ.done, none, none)

/-- Nothing is written at the end of the input. -/
def finGates : GQ → Option Bool := fun _ => none

/-- One mark for every cell of the first row that has an operand. -/
def gatesStr (l : List Sym) : List Bool := fstRun2 δgates finGates (GQ.run false) l

theorem gates_body (b : Bool) (X : List Sym) (h : BodyStart X) :
    fstRun2 δgates finGates (GQ.run b) X = fstRun2 δgates finGates (GQ.run false) X := by
  rcases h with ⟨r, rfl⟩ | ⟨s, r, rfl, rfl | rfl | rfl⟩ <;> cases b <;> rfl

theorem gates_bits (bs : List Bool) (b : Bool) (X : List Sym) (h : BodyStart X) :
    fstRun2 δgates finGates (GQ.run b) (bs.map bsym ++ X)
      = fstRun2 δgates finGates (GQ.run false) X := by
  induction bs generalizing b with
  | nil => exact gates_body b X h
  | cons c bs ih =>
    have : fstRun2 δgates finGates (GQ.run b) ((c :: bs).map bsym ++ X)
        = fstRun2 δgates finGates (GQ.run true) (bs.map bsym ++ X) := by
      cases c <;> cases b <;> rfl
    rw [this, ih]

theorem gates_ticks (d : ℕ) (X : List Sym) :
    fstRun2 δgates finGates (GQ.run false) (List.replicate d Sym.t ++ X)
      = fstRun2 δgates finGates (GQ.run false) X := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem gates_op (op : GateOp) (Y : List Sym) :
    fstRun2 δgates finGates (GQ.run false) (opSym op :: Sym.R :: Y)
      = true :: fstRun2 δgates finGates (GQ.run false) Y := by
  cases op <;> rfl

theorem gates_gate (g : Gate) (hg : GoodGate g) (Y : List Sym) :
    fstRun2 δgates finGates (GQ.run false) (encGate g ++ Y)
      = true :: fstRun2 δgates finGates (GQ.run false) Y := by
  obtain ⟨op, ins⟩ := g
  rcases goodGate_inputs hg with ⟨a, ha⟩ | ⟨a, b, ha⟩
  · simp only at ha
    subst ha
    rw [encGate_one, gates_op, gates_ticks]
  · simp only at ha
    subst ha
    rw [encGate_two, gates_op, gates_ticks]
    show true :: fstRun2 δgates finGates (GQ.run false) (List.replicate b Sym.t ++ Y) = _
    rw [gates_ticks]

theorem gates_gates (gs : List Gate) (hg : ∀ g ∈ gs, GoodGate g) (Y : List Sym) :
    fstRun2 δgates finGates (GQ.run false) (gs.flatMap encGate ++ Y)
      = List.replicate gs.length true ++ fstRun2 δgates finGates (GQ.run false) Y := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.append_assoc, gates_gate g (hg g List.mem_cons_self),
      ih fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')]
    rfl

theorem gates_done (r : List Sym) : fstRun2 δgates finGates GQ.done r = [] := by
  induction r with
  | nil => rfl
  | cons s r ih => exact ih

theorem gates_out (o : ℕ) (e : Option Bool) (r : List Sym) :
    fstRun2 δgates finGates (GQ.run false) (Sym.Z :: (encRef o ++ symE e :: r)) = [] := by
  show fstRun2 δgates finGates (GQ.run false) (List.replicate o Sym.t ++ symE e :: r) = []
  rw [gates_ticks]
  have : fstRun2 δgates finGates (GQ.run false) (symE e :: r)
      = fstRun2 δgates finGates GQ.done r := by
    rcases e with _ | _ | _ <;> rfl
  rw [this, gates_done]

theorem gatesStr_encWs (w : WRow) (W : List WRow) (hw : GoodC w.2.1) :
    gatesStr (encWs (w :: W)) = List.replicate w.2.1.gates.length true := by
  show fstRun2 δgates finGates (GQ.run false) (encW w ++ encWs W) = _
  rw [encW_append, gates_bits _ _ _ (bodyStart_encBody _ hw _), encBody_append,
    gates_gates _ hw, gates_out, List.append_nil]

/-! ## The successor of every row -/

/-- The states of the successor transducer: carrying, with no symbol held; carrying, holding an
input bit symbol not yet known to be an input bit; copying the rest of the row. -/
inductive SuccQ where
  | carry
  | pend (b : Bool)
  | copy
  deriving DecidableEq, Fintype

/-- The successor transducer: add one to the input bits of every row and remove its entry. A
symbol `A` or `O` is an input bit unless a reference follows it, so it is held for one step. -/
def δsucc : SuccQ → Sym → SuccQ × Option Sym × Option Sym
  | SuccQ.carry, Sym.A => (SuccQ.pend true, none, none)
  | SuccQ.carry, Sym.O => (SuccQ.pend false, none, none)
  | SuccQ.carry, s => (if s.isEnd then SuccQ.carry else SuccQ.copy, some (neutSym s), none)
  | SuccQ.pend b, Sym.R => (SuccQ.copy, some (bsym b), some Sym.R)
  | SuccQ.pend true, Sym.A => (SuccQ.pend true, some Sym.O, none)
  | SuccQ.pend true, Sym.O => (SuccQ.pend false, some Sym.O, none)
  | SuccQ.pend b, s =>
      (if s.isEnd then SuccQ.carry else SuccQ.copy, some (bsym (!b)), some (neutSym s))
  | SuccQ.copy, s => (if s.isEnd then SuccQ.carry else SuccQ.copy, some (neutSym s), none)

/-- Nothing is written at the end of the input. -/
def finSucc : SuccQ → Option Sym := fun _ => none

/-- Every row with its input bits incremented and its entry removed. -/
def succStr (l : List Sym) : List Sym := fstRun2 δsucc finSucc SuccQ.carry l

theorem succ_copy (l r : List Sym) (h : ∀ s ∈ l, s.isEnd = false) :
    fstRun2 δsucc finSucc SuccQ.copy (l ++ r) = l ++ fstRun2 δsucc finSucc SuccQ.copy r := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δsucc SuccQ.copy s = (SuccQ.copy, some s, none) := by simp [δsucc, hs, neutSym]
    show (δsucc SuccQ.copy s).2.1.toList ++ (δsucc SuccQ.copy s).2.2.toList
      ++ fstRun2 δsucc finSucc (δsucc SuccQ.copy s).1 (l ++ r) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem succ_copy_end (e : Option Bool) (r : List Sym) :
    fstRun2 δsucc finSucc SuccQ.copy (symE e :: r)
      = Sym.En :: fstRun2 δsucc finSucc SuccQ.carry r := by
  rcases e with _ | _ | _ <;> rfl

theorem succ_carry_body (X : List Sym) (h : BodyStart X) :
    fstRun2 δsucc finSucc SuccQ.carry X = fstRun2 δsucc finSucc SuccQ.copy X := by
  rcases h with ⟨r, rfl⟩ | ⟨s, r, rfl, rfl | rfl | rfl⟩ <;> rfl

theorem succ_pend (bs : List Bool) (b : Bool) (X : List Sym) (h : BodyStart X) :
    fstRun2 δsucc finSucc (SuccQ.pend b) (bs.map bsym ++ X)
      = (inc (b :: bs)).map bsym ++ fstRun2 δsucc finSucc SuccQ.copy X := by
  induction bs generalizing b with
  | nil =>
    rcases h with ⟨r, rfl⟩ | ⟨s, r, rfl, rfl | rfl | rfl⟩ <;> cases b <;> rfl
  | cons c bs ih =>
    cases b with
    | true =>
      have : fstRun2 δsucc finSucc (SuccQ.pend true) ((c :: bs).map bsym ++ X)
          = Sym.O :: fstRun2 δsucc finSucc (SuccQ.pend c) (bs.map bsym ++ X) := by
        cases c <;> rfl
      rw [this, ih]
      rfl
    | false =>
      have : fstRun2 δsucc finSucc (SuccQ.pend false) ((c :: bs).map bsym ++ X)
          = Sym.A :: bsym c :: fstRun2 δsucc finSucc SuccQ.copy (bs.map bsym ++ X) := by
        cases c <;> rfl
      rw [this, succ_copy _ _ (isEnd_bits bs)]
      rfl

theorem succ_row (w : WRow) (hw : GoodC w.2.1) (rest : List Sym) :
    fstRun2 δsucc finSucc SuccQ.carry (encW w ++ rest)
      = encW (inc w.1, w.2.1, none) ++ fstRun2 δsucc finSucc SuccQ.carry rest := by
  obtain ⟨bs, C, e⟩ := w
  have hX := bodyStart_encBody C hw (symE e :: rest)
  have hc : fstRun2 δsucc finSucc SuccQ.copy (encBody C ++ symE e :: rest)
      = encBody C ++ Sym.En :: fstRun2 δsucc finSucc SuccQ.carry rest := by
    rw [succ_copy _ _ (isEnd_encBody C), succ_copy_end]
  rw [encW_append, encW_append]
  show fstRun2 δsucc finSucc SuccQ.carry (bs.map bsym ++ (encBody C ++ symE e :: rest))
    = (inc bs).map bsym ++ (encBody C ++ Sym.En :: fstRun2 δsucc finSucc SuccQ.carry rest)
  cases bs with
  | nil =>
    show fstRun2 δsucc finSucc SuccQ.carry (encBody C ++ symE e :: rest) = _
    rw [succ_carry_body _ hX, hc]
    rfl
  | cons b bs =>
    have : fstRun2 δsucc finSucc SuccQ.carry ((b :: bs).map bsym ++ (encBody C ++ symE e :: rest))
        = fstRun2 δsucc finSucc (SuccQ.pend b) (bs.map bsym ++ (encBody C ++ symE e :: rest)) := by
      cases b <;> rfl
    rw [this, succ_pend _ _ _ hX, hc]

theorem succStr_encWs (W : List WRow) (hW : ∀ w ∈ W, GoodC w.2.1) :
    succStr (encWs W) = encWs (W.map fun w => (inc w.1, w.2.1, none)) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    show fstRun2 δsucc finSucc SuccQ.carry (encW w ++ encWs W) = _
    rw [succ_row w (hW w List.mem_cons_self)]
    show _ ++ succStr (encWs W) = _
    rw [ih fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')]
    rfl

/-! ## The instance -/

/-- The transducer that keeps the leading `true` symbols. The state says whether a `false` was
read. -/
def δunary : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, some true, none)
  | false, false => (true, none, none)
  | true, _ => (true, none, none)

/-- Nothing is written at the end of the input. -/
def finUnary : Bool → Option Bool := fun _ => none

/-- The leading `true` symbols of the instance. -/
def unaryStr (x : List Bool) : List Bool := fstRun2 δunary finUnary false x

/-- The transducer that keeps what follows the first `false`. -/
def δinst : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (!b, none, none)
  | true, b => (true, some b, none)

/-- Nothing is written at the end of the input. -/
def finInst : Bool → Option Bool := fun _ => none

/-- Everything after the first `false` of the instance. -/
def instStr (x : List Bool) : List Bool := fstRun2 δinst finInst false x

/-- The transducer that remembers whether a `false` was read. It writes nothing before the end
of the input. -/
def δsep : Bool → Bool → Bool × Option Bool × Option Bool
  | q, b => (q || !b, none, none)

/-- At the end of the input: whether a `false` was read. -/
def finSep : Bool → Option Bool := fun q => some q

/-- One flag: whether the instance contains a `false`. -/
def sepFlags (x : List Bool) : List Bool := fstRun2 δsep finSep false x

theorem unary_done (r : List Bool) : fstRun2 δunary finUnary true r = [] := by
  induction r with
  | nil => rfl
  | cons b r ih => exact ih

theorem unaryStr_eq (s : ℕ) (r : List Bool) :
    unaryStr (List.replicate s true ++ false :: r) = List.replicate s true := by
  induction s with
  | zero => exact unary_done r
  | succ s ih =>
    show true :: unaryStr (List.replicate s true ++ false :: r) = _
    rw [ih]
    rfl

theorem inst_copy (r : List Bool) : fstRun2 δinst finInst true r = r := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    show b :: fstRun2 δinst finInst true r = _
    rw [ih]

theorem instStr_eq (s : ℕ) (r : List Bool) :
    instStr (List.replicate s true ++ false :: r) = r := by
  induction s with
  | zero => exact inst_copy r
  | succ s ih => exact ih

theorem sep_true (r : List Bool) : fstRun2 δsep finSep true r = [true] := by
  induction r with
  | nil => rfl
  | cons b r ih => exact ih

theorem sepFlags_eq (s : ℕ) (r : List Bool) :
    sepFlags (List.replicate s true ++ false :: r) = [true] := by
  induction s with
  | zero => exact sep_true r
  | succ s ih => exact ih

/-- An instance whose flag is true is some `true` symbols, a `false`, and the rest. -/
theorem sepFlags_sound (x : List Bool) (h : (sepFlags x).all id = true) :
    ∃ s r, x = List.replicate s true ++ false :: r := by
  induction x with
  | nil => exact absurd h (by decide)
  | cons b x ih =>
    cases b with
    | false => exact ⟨0, x, rfl⟩
    | true =>
      obtain ⟨s, r, hx⟩ := ih h
      exact ⟨s + 1, r, by rw [hx]; rfl⟩

end PEqualNP.MetaComplexity.Helpers
