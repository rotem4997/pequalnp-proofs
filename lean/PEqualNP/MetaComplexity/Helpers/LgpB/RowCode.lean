import PEqualNP.MetaComplexity.Helpers.LgpB.Columns
import PEqualNP.Library.Machines.Transducer

/-!
# Rows as strings, and one evaluation step as a finite-state transducer

Helper for "MCSP is in NP". A row (`List Cell × Arg`, see `Columns`) together with a table entry
is written as a string over the alphabet `Sym`; a state is the concatenation of its rows.

* `encArg`, `encCell`, `encRow`, `encState`: the encoders.
* `δstep`, `finStep`, `StepQ.start`: a transducer whose run on an encoded state is the encoded
  state after one `rowStep` on every row (`step_encState`, `step_iterate_encState`), and which
  never lengthens any string (`step_length_le`).
* `δout`, `finOut`, `OutQ.init`: a transducer that writes one flag per row: whether the row has
  no cell left and its entry is absent or equal to what the output operand reads
  (`out_encState_gen`, `out_encState`).
* `out_step_initRow`: the two together on the rows of a circuit.
-/

namespace PEqualNP.MetaComplexity.LgpB
open PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Machines

/-! ## The alphabet and the encoders -/

/-- The symbols. `A`, `O`, `N` start a cell (AND, OR, NOT), its operands follow. `R` starts a
reference operand, followed by its countdown in ticks `t`. `V0`, `V1` are delivered operands.
`Z` starts the output operand of the row. `E0`, `E1`, `En` hold the table entry of the row
(`false`, `true`, absent) and end the row. -/
inductive Sym where
  | A | O | N | R | t | V0 | V1 | Z | E0 | E1 | En
  deriving DecidableEq

instance : Fintype Sym :=
  Fintype.ofList [Sym.A, Sym.O, Sym.N, Sym.R, Sym.t, Sym.V0, Sym.V1, Sym.Z, Sym.E0, Sym.E1,
    Sym.En] (fun x => by cases x <;> simp)

/-- The symbol of a delivered value. -/
def symV : Bool → Sym
  | false => Sym.V0
  | true => Sym.V1

/-- The symbol of a table entry. -/
def symE : Option Bool → Sym
  | some false => Sym.E0
  | some true => Sym.E1
  | none => Sym.En

/-- The symbol that starts a cell. Only AND, OR, NOT have their own symbol. -/
def opSym : GateOp → Sym
  | GateOp.or => Sym.O
  | GateOp.not => Sym.N
  | _ => Sym.A

/-- The symbols that end a row. -/
def Sym.isEnd : Sym → Bool
  | Sym.E0 => true
  | Sym.E1 => true
  | Sym.En => true
  | _ => false

/-- An operand as a string. -/
def encArg : Arg → List Sym
  | Arg.ref d => Sym.R :: List.replicate d Sym.t
  | Arg.val b => [symV b]

/-- A cell as a string: its operation, then its operands. -/
def encCell (c : Cell) : List Sym := opSym c.op :: c.args.flatMap encArg

/-- A row with its table entry. -/
abbrev Row : Type := (List Cell × Arg) × Option Bool

/-- A row as a string: its cells, the output operand, the table entry. -/
def encRow (r : Row) : List Sym :=
  r.1.1.flatMap encCell ++ Sym.Z :: (encArg r.1.2 ++ [symE r.2])

/-- A list of rows as a string. -/
def encState (rows : List Row) : List Sym := rows.flatMap encRow

/-- A cell whose operation is AND, OR or NOT. -/
def Cell.Std (c : Cell) : Prop :=
  c.op = GateOp.and ∨ c.op = GateOp.or ∨ c.op = GateOp.not

/-- A row all of whose cells are AND, OR or NOT. -/
def RowStd (r : List Cell × Arg) : Prop := ∀ c ∈ r.1, c.Std

theorem rowStd_rowStep (r : List Cell × Arg) (h : RowStd r) : RowStd (rowStep r) := by
  obtain ⟨cs, o⟩ := r
  cases cs with
  | nil => exact h
  | cons c cs =>
    intro c' hc'
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.1 hc'
    exact h c'' (List.mem_cons_of_mem _ hc'')

theorem rowStd_iterate (k : ℕ) (r : List Cell × Arg) (h : RowStd r) : RowStd (rowStep^[k] r) := by
  induction k generalizing r with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (rowStd_rowStep r h)

theorem rowStd_initRow (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x : List Bool) : RowStd (initRow C x) := by
  intro c hc
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg
    cases b
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · exact hC g hg

theorem isEnd_encArg (a : Arg) : ∀ s ∈ encArg a, s.isEnd = false := by
  intro s hs
  cases a with
  | ref d =>
    rcases List.mem_cons.1 hs with rfl | hs
    · rfl
    · rw [List.eq_of_mem_replicate hs]; rfl
  | val b =>
    rw [List.mem_singleton.1 hs]
    cases b <;> rfl

theorem isEnd_opSym (op : GateOp) : (opSym op).isEnd = false := by cases op <;> rfl

theorem isEnd_encCell (c : Cell) : ∀ s ∈ encCell c, s.isEnd = false := by
  intro s hs
  rcases List.mem_cons.1 hs with rfl | hs
  · exact isEnd_opSym _
  · obtain ⟨a, _, ha⟩ := List.mem_flatMap.1 hs
    exact isEnd_encArg a s ha

/-! ## The step transducer -/

/-- How the value of the cell being removed is accumulated. -/
inductive Mode where
  | and | or | fresh | done
  deriving DecidableEq

instance : Fintype Mode :=
  Fintype.ofList [Mode.and, Mode.or, Mode.fresh, Mode.done] (fun x => by cases x <;> simp)

/-- Take one more operand reading into the accumulated value. For NOT only the first counts. -/
def eatStep : Mode × Bool → Bool → Mode × Bool
  | (Mode.and, a), b => (Mode.and, a && b)
  | (Mode.or, a), b => (Mode.or, a || b)
  | (Mode.fresh, _), b => (Mode.done, !b)
  | (Mode.done, a), _ => (Mode.done, a)

/-- The accumulator before any operand. -/
def initP : GateOp → Mode × Bool
  | GateOp.or => (Mode.or, false)
  | GateOp.not => (Mode.fresh, true)
  | _ => (Mode.and, true)

/-- The states of the step transducer: at the start of a row; copying a row that has no cell;
removing the first cell; copying the rest of the row while delivering the value `v`, with
`pend` set when a reference symbol has been read and not yet written. -/
inductive StepQ where
  | start
  | pass
  | eat (p : Mode × Bool)
  | copy (v : Bool) (pend : Bool)
  deriving DecidableEq, Fintype

/-- The step transducer. -/
def δstep : StepQ → Sym → StepQ × Option Sym × Option Sym
  | StepQ.start, Sym.A => (StepQ.eat (Mode.and, true), none, none)
  | StepQ.start, Sym.O => (StepQ.eat (Mode.or, false), none, none)
  | StepQ.start, Sym.N => (StepQ.eat (Mode.fresh, true), none, none)
  | StepQ.start, s => (if s.isEnd then StepQ.start else StepQ.pass, some s, none)
  | StepQ.pass, s => (if s.isEnd then StepQ.start else StepQ.pass, some s, none)
  | StepQ.eat p, Sym.V0 => (StepQ.eat (eatStep p false), none, none)
  | StepQ.eat p, Sym.V1 => (StepQ.eat (eatStep p true), none, none)
  | StepQ.eat p, Sym.R => (StepQ.eat (eatStep p false), none, none)
  | StepQ.eat p, Sym.t => (StepQ.eat p, none, none)
  | StepQ.eat p, s => (if s.isEnd then StepQ.start else StepQ.copy p.2 false, some s, none)
  | StepQ.copy v false, Sym.R => (StepQ.copy v true, none, none)
  | StepQ.copy v false, s => (if s.isEnd then StepQ.start else StepQ.copy v false, some s, none)
  | StepQ.copy v true, Sym.t => (StepQ.copy v false, some Sym.R, none)
  | StepQ.copy v true, Sym.R => (StepQ.copy v true, some (symV v), none)
  | StepQ.copy v true, s =>
      (if s.isEnd then StepQ.start else StepQ.copy v false, some (symV v), some s)

/-- Nothing is written at the end of the input. -/
def finStep : StepQ → Option Sym := fun _ => none

/-- One step on a string. -/
def stepStr (l : List Sym) : List Sym := fstRun2 δstep finStep StepQ.start l

/-- A string whose first symbol exists and is not a tick. -/
def Guard (l : List Sym) : Prop := ∃ s r, l = s :: r ∧ s ≠ Sym.t

theorem guard_encArg (a : Arg) (l : List Sym) : Guard (encArg a ++ l) := by
  cases a with
  | ref d => exact ⟨Sym.R, _, rfl, by decide⟩
  | val b => cases b <;> exact ⟨_, _, rfl, by decide⟩

theorem opSym_ne_t (op : GateOp) : opSym op ≠ Sym.t := by cases op <;> simp [opSym]

theorem guard_cells (cs : List Cell) (l : List Sym) (h : Guard l) :
    Guard (cs.flatMap encCell ++ l) := by
  cases cs with
  | nil => exact h
  | cons c cs => exact ⟨opSym c.op, _, rfl, opSym_ne_t _⟩

theorem guard_args (as : List Arg) (l : List Sym) (h : Guard l) :
    Guard (as.flatMap encArg ++ l) := by
  cases as with
  | nil => exact h
  | cons a as =>
    rw [List.flatMap_cons, List.append_assoc]
    exact guard_encArg a _

/-! ### Removing the first cell -/

theorem eat_ticks (p : Mode × Bool) (d : ℕ) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.eat p) (List.replicate d Sym.t ++ rest)
      = fstRun2 δstep finStep (StepQ.eat p) rest := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem eat_arg (p : Mode × Bool) (a : Arg) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.eat p) (encArg a ++ rest)
      = fstRun2 δstep finStep (StepQ.eat (eatStep p a.read)) rest := by
  cases a with
  | ref d => exact eat_ticks _ d rest
  | val b => cases b <;> rfl

theorem eat_args (as : List Arg) (p : Mode × Bool) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.eat p) (as.flatMap encArg ++ rest)
      = fstRun2 δstep finStep (StepQ.eat ((as.map Arg.read).foldl eatStep p)) rest := by
  induction as generalizing p with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.append_assoc, eat_arg, ih]
    rfl

theorem foldl_eatStep_and (l : List Bool) (a : Bool) :
    l.foldl eatStep (Mode.and, a) = (Mode.and, a && l.all id) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [eatStep, ih, Bool.and_assoc]

theorem foldl_eatStep_or (l : List Bool) (a : Bool) :
    l.foldl eatStep (Mode.or, a) = (Mode.or, a || l.any id) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [eatStep, ih, Bool.or_assoc]

theorem foldl_eatStep_done (l : List Bool) (a : Bool) :
    l.foldl eatStep (Mode.done, a) = (Mode.done, a) := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [eatStep] using ih

theorem foldl_eatStep_value (c : Cell) (h : c.Std) :
    ((c.args.map Arg.read).foldl eatStep (initP c.op)).2 = c.value := by
  obtain ⟨op, as⟩ := c
  rcases h with h | h | h <;> simp only at h <;> subst h
  · simp [initP, foldl_eatStep_and, Cell.value, GateOp.eval]
  · simp [initP, foldl_eatStep_or, Cell.value, GateOp.eval]
  · cases as with
    | nil => rfl
    | cons a as =>
      simp [initP, eatStep, foldl_eatStep_done, Cell.value, GateOp.eval]

theorem start_op (op : GateOp) (l : List Sym) :
    fstRun2 δstep finStep StepQ.start (opSym op :: l)
      = fstRun2 δstep finStep (StepQ.eat (initP op)) l := by
  cases op <;> rfl

/-- At the end of the removed cell the next symbol starts a cell or the output operand. -/
theorem eat_boundary (p : Mode × Bool) (cs : List Cell) (l : List Sym) :
    fstRun2 δstep finStep (StepQ.eat p) (cs.flatMap encCell ++ Sym.Z :: l)
      = fstRun2 δstep finStep (StepQ.copy p.2 false) (cs.flatMap encCell ++ Sym.Z :: l) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [List.flatMap_cons, List.append_assoc]
    show fstRun2 δstep finStep (StepQ.eat p) (opSym c.op :: _)
      = fstRun2 δstep finStep (StepQ.copy p.2 false) (opSym c.op :: _)
    cases c.op <;> rfl

/-! ### Copying the rest of the row -/

theorem copy_ticks (v : Bool) (d : ℕ) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.copy v false) (List.replicate d Sym.t ++ rest)
      = List.replicate d Sym.t ++ fstRun2 δstep finStep (StepQ.copy v false) rest := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show Sym.t :: fstRun2 δstep finStep (StepQ.copy v false) (List.replicate d Sym.t ++ rest) = _
    rw [ih]; rfl

theorem copy_pend (v : Bool) (s : Sym) (r : List Sym) (h : s ≠ Sym.t) :
    fstRun2 δstep finStep (StepQ.copy v true) (s :: r)
      = symV v :: fstRun2 δstep finStep (StepQ.copy v false) (s :: r) := by
  cases s <;> first | rfl | exact absurd rfl h

theorem copy_arg (v : Bool) (a : Arg) (rest : List Sym) (h : Guard rest) :
    fstRun2 δstep finStep (StepQ.copy v false) (encArg a ++ rest)
      = encArg (Arg.sub v a) ++ fstRun2 δstep finStep (StepQ.copy v false) rest := by
  cases a with
  | ref d =>
    cases d with
    | zero =>
      obtain ⟨s, r, rfl, hs⟩ := h
      show fstRun2 δstep finStep (StepQ.copy v true) (s :: r) = _
      rw [copy_pend v s r hs]; rfl
    | succ d =>
      show Sym.R :: fstRun2 δstep finStep (StepQ.copy v false) (List.replicate d Sym.t ++ rest)
        = _
      rw [copy_ticks]; rfl
  | val b => cases b <;> rfl

theorem copy_args (v : Bool) (as : List Arg) (rest : List Sym) (h : Guard rest) :
    fstRun2 δstep finStep (StepQ.copy v false) (as.flatMap encArg ++ rest)
      = (as.map (Arg.sub v)).flatMap encArg
          ++ fstRun2 δstep finStep (StepQ.copy v false) rest := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.append_assoc, copy_arg v a _ (guard_args as rest h), ih,
      List.map_cons, List.flatMap_cons, List.append_assoc]

theorem copy_op (v : Bool) (op : GateOp) (l : List Sym) :
    fstRun2 δstep finStep (StepQ.copy v false) (opSym op :: l)
      = opSym op :: fstRun2 δstep finStep (StepQ.copy v false) l := by
  cases op <;> rfl

theorem copy_cells (v : Bool) (cs : List Cell) (rest : List Sym) (h : Guard rest) :
    fstRun2 δstep finStep (StepQ.copy v false) (cs.flatMap encCell ++ rest)
      = (cs.map (Cell.sub v)).flatMap encCell
          ++ fstRun2 δstep finStep (StepQ.copy v false) rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc]
    show fstRun2 δstep finStep (StepQ.copy v false)
      (opSym c.op :: (c.args.flatMap encArg ++ (cs.flatMap encCell ++ rest))) = _
    rw [copy_op, copy_args v _ _ (guard_cells cs rest h), ih, List.map_cons, List.flatMap_cons]
    show _ = (opSym c.op :: (c.args.map (Arg.sub v)).flatMap encArg ++ _) ++ _
    simp only [List.cons_append, List.append_assoc]

theorem copy_end (v : Bool) (e : Option Bool) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.copy v false) (symE e :: rest)
      = symE e :: fstRun2 δstep finStep StepQ.start rest := by
  rcases e with _ | _ | _ <;> rfl

theorem guard_end (e : Option Bool) (rest : List Sym) : Guard (symE e :: rest) :=
  ⟨_, _, rfl, by rcases e with _ | _ | _ <;> decide⟩

/-- Copying the rest of a row: the cells, the output operand and the entry. -/
theorem copy_row (v : Bool) (cs : List Cell) (o : Arg) (e : Option Bool) (rest : List Sym) :
    fstRun2 δstep finStep (StepQ.copy v false) (encRow ((cs, o), e) ++ rest)
      = encRow ((cs.map (Cell.sub v), Arg.sub v o), e)
          ++ fstRun2 δstep finStep StepQ.start rest := by
  have e1 : encRow ((cs, o), e) ++ rest
      = cs.flatMap encCell ++ Sym.Z :: (encArg o ++ symE e :: rest) := by
    simp [encRow]
  have e2 : encRow ((cs.map (Cell.sub v), Arg.sub v o), e)
        ++ fstRun2 δstep finStep StepQ.start rest
      = (cs.map (Cell.sub v)).flatMap encCell ++ Sym.Z :: (encArg (Arg.sub v o)
          ++ symE e :: fstRun2 δstep finStep StepQ.start rest) := by
    simp [encRow]
  rw [e1, e2, copy_cells v cs _ ⟨Sym.Z, _, rfl, by decide⟩]
  show _ ++ Sym.Z :: fstRun2 δstep finStep (StepQ.copy v false) (encArg o ++ symE e :: rest) = _
  rw [copy_arg v o _ (guard_end e rest), copy_end]

/-! ### A row with no cell -/

theorem pass_run (l : List Sym) (h : ∀ s ∈ l, s.isEnd = false) (rest : List Sym) :
    fstRun2 δstep finStep StepQ.pass (l ++ rest)
      = l ++ fstRun2 δstep finStep StepQ.pass rest := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δstep StepQ.pass s = (StepQ.pass, some s, none) := by simp [δstep, hs]
    show (δstep StepQ.pass s).2.1.toList ++ (δstep StepQ.pass s).2.2.toList
      ++ fstRun2 δstep finStep (δstep StepQ.pass s).1 (l ++ rest) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem pass_end (e : Option Bool) (rest : List Sym) :
    fstRun2 δstep finStep StepQ.pass (symE e :: rest)
      = symE e :: fstRun2 δstep finStep StepQ.start rest := by
  rcases e with _ | _ | _ <;> rfl

/-! ### A whole row, and a list of rows -/

theorem step_row (r : Row) (h : RowStd r.1) (rest : List Sym) :
    fstRun2 δstep finStep StepQ.start (encRow r ++ rest)
      = encRow (rowStep r.1, r.2) ++ fstRun2 δstep finStep StepQ.start rest := by
  obtain ⟨⟨cs, o⟩, e⟩ := r
  cases cs with
  | nil =>
    show Sym.Z :: fstRun2 δstep finStep StepQ.pass ((encArg o ++ [symE e]) ++ rest)
      = Sym.Z :: ((encArg o ++ [symE e]) ++ fstRun2 δstep finStep StepQ.start rest)
    rw [List.append_assoc, pass_run _ (isEnd_encArg o), List.singleton_append, pass_end,
      List.append_assoc]
    rfl
  | cons c cs =>
    have hc : c.Std := h c List.mem_cons_self
    have e1 : encRow ((c :: cs, o), e) ++ rest
        = opSym c.op :: (c.args.flatMap encArg ++ (encRow ((cs, o), e) ++ rest)) := by
      simp [encRow, encCell]
    rw [e1, start_op, eat_args]
    have e2 : encRow ((cs, o), e) ++ rest
        = cs.flatMap encCell ++ Sym.Z :: (encArg o ++ symE e :: rest) := by
      simp [encRow]
    rw [e2, eat_boundary, ← e2, foldl_eatStep_value c hc, copy_row]
    rfl

theorem step_rows (rows : List Row) (h : ∀ r ∈ rows, RowStd r.1) (rest : List Sym) :
    fstRun2 δstep finStep StepQ.start (encState rows ++ rest)
      = encState (rows.map fun r => (rowStep r.1, r.2))
          ++ fstRun2 δstep finStep StepQ.start rest := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    show fstRun2 δstep finStep StepQ.start ((encRow r ++ encState rows) ++ rest)
      = (encRow (rowStep r.1, r.2) ++ encState (rows.map fun r => (rowStep r.1, r.2))) ++ _
    rw [List.append_assoc, step_row r (h r List.mem_cons_self),
      ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr'), List.append_assoc]

/-- One run of the step transducer over an encoded state performs `rowStep` on every row. -/
theorem step_encState (rows : List Row) (h : ∀ r ∈ rows, RowStd r.1) :
    fstRun2 δstep finStep StepQ.start (encState rows)
      = encState (rows.map fun r => (rowStep r.1, r.2)) := by
  have := step_rows rows h []
  rw [List.append_nil] at this
  rw [this]
  exact List.append_nil _

/-- `k` runs of the step transducer perform `k` steps on every row. -/
theorem step_iterate_encState (k : ℕ) (rows : List Row) (h : ∀ r ∈ rows, RowStd r.1) :
    stepStr^[k] (encState rows) = encState (rows.map fun r => (rowStep^[k] r.1, r.2)) := by
  induction k generalizing rows with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    show stepStr^[k] (fstRun2 δstep finStep StepQ.start (encState rows)) = _
    rw [step_encState rows h, ih, List.map_map]
    · rfl
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      exact rowStd_rowStep _ (h r' hr')

/-! ### A step never lengthens a string -/

/-- One for a state holding a reference symbol not yet written. -/
def StepQ.pend : StepQ → ℕ
  | StepQ.copy _ true => 1
  | _ => 0

theorem δstep_potential (q : StepQ) (s : Sym) :
    (δstep q s).2.1.toList.length + (δstep q s).2.2.toList.length + (δstep q s).1.pend
      ≤ 1 + q.pend := by
  rcases q with _ | _ | p | ⟨v, _ | _⟩ <;> cases s <;> simp [δstep, StepQ.pend, Sym.isEnd]

theorem step_length_le_gen (l : List Sym) (q : StepQ) :
    (fstRun2 δstep finStep q l).length ≤ l.length + q.pend := by
  induction l generalizing q with
  | nil => simp [fstRun2, finStep]
  | cons s l ih =>
    have h1 := δstep_potential q s
    have h2 := ih (δstep q s).1
    simp only [fstRun2, List.length_append, List.length_cons]
    omega

/-- On every string, the output of the step transducer is at most as long as the input. -/
theorem step_length_le (l : List Sym) :
    (fstRun2 δstep finStep StepQ.start l).length ≤ l.length :=
  step_length_le_gen l StepQ.start

/-! ## The output transducer -/

/-- The states of the output transducer: at the start of a row; after `Z`; after the output
operand, holding what it reads; in a row that is not of the form `Z`, operand, entry. -/
inductive OutQ where
  | init
  | z
  | got (b : Bool)
  | bad
  deriving DecidableEq, Fintype

/-- The output transducer: one flag at the end of every row. -/
def δout : OutQ → Sym → OutQ × Option Bool × Option Bool
  | OutQ.init, Sym.Z => (OutQ.z, none, none)
  | OutQ.z, Sym.V0 => (OutQ.got false, none, none)
  | OutQ.z, Sym.V1 => (OutQ.got true, none, none)
  | OutQ.z, Sym.R => (OutQ.got false, none, none)
  | OutQ.got b, Sym.t => (OutQ.got b, none, none)
  | OutQ.got b, Sym.E0 => (OutQ.init, some (!b), none)
  | OutQ.got b, Sym.E1 => (OutQ.init, some b, none)
  | OutQ.got _, Sym.En => (OutQ.init, some true, none)
  | _, s => if s.isEnd then (OutQ.init, some false, none) else (OutQ.bad, none, none)

/-- Nothing is written at the end of the input. -/
def finOut : OutQ → Option Bool := fun _ => none

/-- The flags of a string. -/
def outStr (l : List Sym) : List Bool := fstRun2 δout finOut OutQ.init l

/-- The flag of a row: no cell is left, and the entry is absent or is what the output operand
reads. -/
def rowFlag (r : Row) : Bool :=
  r.1.1.isEmpty && decide (r.2 = none ∨ r.2 = some r.1.2.read)

theorem out_got_ticks (b : Bool) (d : ℕ) (rest : List Sym) :
    fstRun2 δout finOut (OutQ.got b) (List.replicate d Sym.t ++ rest)
      = fstRun2 δout finOut (OutQ.got b) rest := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem out_arg (a : Arg) (rest : List Sym) :
    fstRun2 δout finOut OutQ.z (encArg a ++ rest)
      = fstRun2 δout finOut (OutQ.got a.read) rest := by
  cases a with
  | ref d => exact out_got_ticks false d rest
  | val b => cases b <;> rfl

theorem out_end (b : Bool) (e : Option Bool) (rest : List Sym) :
    fstRun2 δout finOut (OutQ.got b) (symE e :: rest)
      = decide (e = none ∨ e = some b) :: fstRun2 δout finOut OutQ.init rest := by
  rcases e with _ | _ | _ <;> cases b <;> rfl

theorem out_bad_run (l : List Sym) (h : ∀ s ∈ l, s.isEnd = false) (e : Option Bool)
    (rest : List Sym) :
    fstRun2 δout finOut OutQ.bad (l ++ symE e :: rest)
      = false :: fstRun2 δout finOut OutQ.init rest := by
  induction l with
  | nil => rcases e with _ | _ | _ <;> rfl
  | cons s l ih =>
    have hs : s.isEnd = false := h s List.mem_cons_self
    have : δout OutQ.bad s = (OutQ.bad, none, none) := by simp [δout, hs]
    show (δout OutQ.bad s).2.1.toList ++ (δout OutQ.bad s).2.2.toList
      ++ fstRun2 δout finOut (δout OutQ.bad s).1 (l ++ symE e :: rest) = _
    rw [this, ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem out_init_op (op : GateOp) (l : List Sym) :
    fstRun2 δout finOut OutQ.init (opSym op :: l) = fstRun2 δout finOut OutQ.bad l := by
  cases op <;> rfl

theorem out_row (r : Row) (rest : List Sym) :
    fstRun2 δout finOut OutQ.init (encRow r ++ rest)
      = rowFlag r :: fstRun2 δout finOut OutQ.init rest := by
  obtain ⟨⟨cs, o⟩, e⟩ := r
  cases cs with
  | nil =>
    show fstRun2 δout finOut OutQ.z ((encArg o ++ [symE e]) ++ rest) = _
    rw [List.append_assoc, out_arg, List.singleton_append, out_end]
    simp [rowFlag]
  | cons c cs =>
    have e1 : encRow ((c :: cs, o), e) ++ rest
        = opSym c.op :: ((c.args.flatMap encArg ++ (cs.flatMap encCell ++ Sym.Z :: encArg o))
            ++ symE e :: rest) := by
      simp [encRow, encCell]
    rw [e1, out_init_op, out_bad_run]
    · rfl
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · obtain ⟨a, _, ha⟩ := List.mem_flatMap.1 hs
        exact isEnd_encArg a s ha
      · rcases List.mem_append.1 hs with hs | hs
        · obtain ⟨c', _, hc'⟩ := List.mem_flatMap.1 hs
          exact isEnd_encCell c' s hc'
        · rcases List.mem_cons.1 hs with rfl | hs
          · rfl
          · exact isEnd_encArg o s hs

/-- On any encoded state the output transducer writes the flag of every row; a row that still
has a cell gets `false`. -/
theorem out_encState_gen (rows : List Row) :
    fstRun2 δout finOut OutQ.init (encState rows) = rows.map rowFlag := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    show fstRun2 δout finOut OutQ.init (encRow r ++ encState rows) = _
    rw [out_row, ih]
    rfl

/-- On an encoded state whose rows have no cell left, the flags say whether each entry is
absent or equal to what the output operand reads. -/
theorem out_encState (rows : List Row) (h : ∀ r ∈ rows, r.1.1 = []) :
    fstRun2 δout finOut OutQ.init (encState rows)
      = rows.map fun r => decide (r.2 = none ∨ r.2 = some r.1.2.read) := by
  rw [out_encState_gen]
  apply List.map_congr_left
  intro r hr
  simp [rowFlag, h r hr]

/-! ## Both together on the rows of a circuit -/

/-- Take the rows of a circuit with AND, OR, NOT gates on the inputs `p.1` with entries `p.2`,
run the step transducer at least as many times as there are wires, then the output transducer:
the flags say whether each entry is absent or equal to the value of the circuit. -/
theorem out_step_initRow (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (ps : List (List Bool × Option Bool)) (k : ℕ)
    (hk : ∀ p ∈ ps, p.1.length + C.gates.length ≤ k) :
    fstRun2 δout finOut OutQ.init
        ((fstRun2 δstep finStep StepQ.start)^[k]
          (encState (ps.map fun p => (initRow C p.1, p.2))))
      = ps.map fun p => decide (p.2 = none ∨ p.2 = some (C.eval p.1)) := by
  have h1 := step_iterate_encState k (ps.map fun p => ((initRow C p.1, p.2) : Row)) (by
    intro r hr
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
    exact rowStd_initRow C hC p.1)
  have h1' : (fstRun2 δstep finStep StepQ.start)^[k]
      (encState (ps.map fun p => (initRow C p.1, p.2))) = _ := h1
  rw [h1', List.map_map, out_encState_gen, List.map_map]
  apply List.map_congr_left
  intro p hp
  obtain ⟨o, ho, hr⟩ := rowStep_initRow C p.1 k (hk p hp)
  simp [rowFlag, ho, hr]

end PEqualNP.MetaComplexity.LgpB
