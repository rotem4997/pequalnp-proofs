import Mathlib.Data.List.OfFn

/-!
# Deterministic branching programs

A branching program on input bits is a list of states. State `0` is the start. Each state reads
one input bit and names two successors, one for the bit `false` and one for the bit `true`; a
successor is either another state or one of the two sinks, "output `false`" and "output `true`".
The size of a program is its number of states; the sinks are not counted.

Programs are required to be FORWARD: every successor state has a larger index than the state
that names it, and exists. A path then visits at most `size` states, so evaluation with `size`
steps of fuel is exact. Without this condition a program could loop, and a loop is not a
branching program.

As for circuits (`PEqualNP.CircuitLowerBounds`), an input is a list of bits and a bit position
past its end reads `false`; `HasBPSize` asks that every state read a bit below `n`. The empty
program outputs `false`, so the constant `false` has size zero and the constant `true` has size
one.
-/

namespace PEqualNP.BranchingProgram

/-- A successor: another state, by its index, or a sink with its output. -/
inductive Next where
  /-- Go to the state with this index. -/
  | state (q : ℕ)
  /-- Stop and output this bit. -/
  | out (b : Bool)

/-- A state: the input bit it reads, its successor on `false` and its successor on `true`. -/
structure State where
  /-- The position of the input bit read. -/
  var : ℕ
  /-- The successor when the bit is `false`. -/
  lo : Next
  /-- The successor when the bit is `true`. -/
  hi : Next

/-- A branching program: its states; the start is state `0`. -/
abbrev Program := List State

/-- Run `P` on `x` from state `q` with `fuel` steps; out of fuel or at a missing state, `false`. -/
def Program.run (P : Program) (x : List Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, q =>
    match P[q]? with
    | none => false
    | some s =>
      match (if x.getD s.var false then s.hi else s.lo) with
      | Next.out b => b
      | Next.state q' => Program.run P x fuel q'

/-- The output of `P` on `x`: run from state `0` with one step per state. -/
def Program.eval (P : Program) (x : List Bool) : Bool :=
  P.run x P.length 0

/-- The size of a program: its number of states. Sinks are not counted. -/
def Program.size (P : Program) : ℕ :=
  P.length

/-- Every successor state of state `i` has an index larger than `i` and below the size. -/
def Program.Forward (P : Program) : Prop :=
  ∀ (i : ℕ) (s : State), P[i]? = some s → ∀ q : ℕ,
    (s.lo = Next.state q ∨ s.hi = Next.state q) → i < q ∧ q < P.length

/-- Every state reads an input bit below `n`. -/
def Program.ReadsBelow (n : ℕ) (P : Program) : Prop :=
  ∀ s ∈ P, s.var < n

/-- The Boolean function `f` on `n` inputs has a branching program with at most `s` states: a
forward program reading only bits below `n`, with at most `s` states, that outputs `f x` on
every input `x`. -/
def HasBPSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ P : Program, P.Forward ∧ P.ReadsBelow n ∧ P.size ≤ s ∧
    ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x

end PEqualNP.BranchingProgram
