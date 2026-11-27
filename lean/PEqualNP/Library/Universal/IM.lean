import Mathlib.Tactic

/-!
# A numbered micro-instruction machine

Helper module (proofs only, no statement may use it). The intermediate model between the pinned
library's stack machines and a universal machine: everything is a natural number, so a program
is plain data.

* A configuration is a program counter (`none` once halted), a state number and a list of
  stacks of symbol numbers.
* A program is a list of instructions. Each instruction is one step and does one thing: push,
  pop, peek, load, branch, goto or halt. What a stack machine computes with a function on its
  finite state is here a lookup in a table, a list of numbers read with default `0`.
* `pop` and `peek` read the table at `state * w + c`, where `c` is `0` on an empty stack and
  `s + 1` when the top symbol is `s`, and `w` is the row width.
-/

namespace PEqualNP.Library.Universal

/-- One instruction. `next` fields are program counters. -/
inductive Instr
  | push (k : ℕ) (tbl : List ℕ) (next : ℕ)
  | pop (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | peek (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | load (tbl : List ℕ) (next : ℕ)
  | branch (tbl : List ℕ) (next₁ next₂ : ℕ)
  | goto (tbl : List ℕ)
  | halt
  deriving DecidableEq, Repr

/-- A configuration: program counter (`none` once halted), state, stacks. -/
structure Cfg where
  pc : Option ℕ
  state : ℕ
  stk : List (List ℕ)
  deriving DecidableEq, Repr

/-- The index read by `pop` and `peek`: `0` on an empty stack, `s + 1` on top symbol `s`. -/
def topIndex (st : List ℕ) : ℕ :=
  match st with
  | [] => 0
  | s :: _ => s + 1

/-- Run one instruction. -/
def exec (i : Instr) (v : ℕ) (S : List (List ℕ)) : Cfg :=
  match i with
  | .push k tbl next => ⟨some next, v, S.set k (tbl.getD v 0 :: S.getD k [])⟩
  | .pop k tbl w next =>
    ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S.set k (S.getD k []).tail⟩
  | .peek k tbl w next => ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S⟩
  | .load tbl next => ⟨some next, tbl.getD v 0, S⟩
  | .branch tbl next₁ next₂ => ⟨some (if tbl.getD v 0 ≠ 0 then next₁ else next₂), v, S⟩
  | .goto tbl => ⟨some (tbl.getD v 0), v, S⟩
  | .halt => ⟨none, v, S⟩

/-- One step: a halted configuration stays; a program counter outside the program halts. -/
def step (P : List Instr) (c : Cfg) : Cfg :=
  match c.pc with
  | none => c
  | some n =>
    match P[n]? with
    | none => ⟨none, c.state, c.stk⟩
    | some i => exec i c.state c.stk

/-- A program with its entry point and its stacks: `nstk` stacks, input on stack `kin`, output
on stack `kout`. -/
structure Code where
  prog : List Instr
  nstk : ℕ
  pc₀ : ℕ
  state₀ : ℕ
  kin : ℕ
  kout : ℕ
  deriving DecidableEq, Repr

/-- The initial configuration on an input, a list of symbol numbers. -/
def Code.init (c : Code) (input : List ℕ) : Cfg :=
  ⟨some c.pc₀, c.state₀, (List.replicate c.nstk []).set c.kin input⟩

/-- The configuration after `t` steps. -/
def Code.run (c : Code) (input : List ℕ) (t : ℕ) : Cfg :=
  (step c.prog)^[t] (c.init input)

/-- The code halts within `t` steps with exactly `out` on its output stack. -/
def Code.outputsWithin (c : Code) (input : List ℕ) (t : ℕ) (out : List ℕ) : Prop :=
  (c.run input t).pc = none ∧ (c.run input t).stk.getD c.kout [] = out

end PEqualNP.Library.Universal
