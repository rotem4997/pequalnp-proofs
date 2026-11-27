import PEqualNP.Defs.Search
import PEqualNP.Library.Universal.IM
import Mathlib.Tactic

/-!
# Helpers: the tableau formula of a micro-instruction code (definitions)

Helper module (proofs only, no statement may use it). The formula `tableau c zs m T` is a CNF
that is satisfiable exactly when the code `c`, started on the input symbols `zs` followed by
some witness of at most `m` symbols `2` or `3`, halts within `T` steps with `[1]` on its
output stack. The proof is in `TableauSound.lean` and `TableauComplete.lean`.

## Variables

A variable is named by a list of indices `l`, and its number `uvar l` is the number whose binary
digits, least significant first, are `false^a ++ [true]` for each index `a` of `l` in order
(`bits_uvar`). The number is huge but its code is short and needs no binary arithmetic; `uvar`
is injective on all lists. Three kinds:

* `vP t q = uvar [0, q, t]`: at time `t` the program counter has code `q`; code `0` is
  "halted", code `n + 1` is the counter `n`.
* `vQ t v = uvar [1, v, t]`: at time `t` the state is `v`.
* `vC t k j x = uvar [2, k, x, j, t]`: at time `t`, cell `j` of stack `k`, counted from the TOP
  of the stack, has value `x`; value `0` is "blank" (below the bottom), value `s + 1` is the
  symbol `s`.

## Clauses

Every clause is one of: an implication `imp prem concl` (all premises and the conclusion are
positive variables), a positive clause of three literals ("this witness cell is blank, `2` or
`3`"), a negative unit clause (only at the last time), or the empty clause (only when the
output stack does not exist). There are NO at-most-one clauses: the correct value of every
group is forced true by implications, and the negative units at the last time reject.

All data are bounded by `bound c`, a number that depends on the code only.
-/

namespace PEqualNP.Library.SearchHelpers.Tab

open PEqualNP.Library.Universal PEqualNP.Search

/-- The number of a variable named by a list of indices: binary digits, least significant
first, `false^a ++ [true]` for each index `a`. -/
def uvar : List ℕ → ℕ
  | [] => 0
  | a :: r => 2 ^ a * (2 * uvar r + 1)

/-- Variable: at time `t` the program counter code is `q`. -/
def vP (t q : ℕ) : ℕ := uvar [0, q, t]

/-- Variable: at time `t` the state is `v`. -/
def vQ (t v : ℕ) : ℕ := uvar [1, v, t]

/-- Variable: at time `t`, cell `j` (from the top) of stack `k` has value `x`. -/
def vC (t k j x : ℕ) : ℕ := uvar [2, k, x, j, t]

/-- The implication clause: if all of `prem` are true then `concl` is true. -/
def imp (prem : List ℕ) (concl : ℕ) : Clause :=
  prem.map (fun x => (x, false)) ++ [(concl, true)]

/-- The code of a program counter: `0` when halted, `n + 1` at counter `n`. -/
def pcCode : Option ℕ → ℕ
  | none => 0
  | some n => n + 1

/-- The instruction run at a program counter code: `halt` when halted or outside the program. -/
def instrAt (P : List Instr) : ℕ → Instr
  | 0 => .halt
  | q + 1 => P.getD q .halt

/-- The code of the next program counter, from the instruction and the state. -/
def nextCode (i : Instr) (v : ℕ) : ℕ :=
  match i with
  | .push _ _ next => next + 1
  | .pop _ _ _ next => next + 1
  | .peek _ _ _ next => next + 1
  | .load _ next => next + 1
  | .branch tbl next₁ next₂ => (if tbl.getD v 0 ≠ 0 then next₁ else next₂) + 1
  | .goto tbl => tbl.getD v 0 + 1
  | .halt => 0

/-- The stack an instruction reads the top of, if any. -/
def rdStack (i : Instr) : Option ℕ :=
  match i with
  | .pop k _ _ _ => some k
  | .peek k _ _ _ => some k
  | _ => none

/-- The next state, from the instruction, the state and the top index `a` of the stack read. -/
def newState (i : Instr) (v a : ℕ) : ℕ :=
  match i with
  | .pop _ tbl w _ => tbl.getD (v * w + a) 0
  | .peek _ tbl w _ => tbl.getD (v * w + a) 0
  | .load tbl _ => tbl.getD v 0
  | _ => v

/-- What an instruction does to one stack. -/
inductive Op
  | keep
  | push (tbl : List ℕ)
  | pop
  deriving DecidableEq, Repr

/-- What the instruction `i` does to the stack `k`. -/
def stackOp (i : Instr) (k : ℕ) : Op :=
  match i with
  | .push k' tbl _ => if k' = k then .push tbl else .keep
  | .pop k' _ _ _ => if k' = k then .pop else .keep
  | _ => .keep

/-- The ways to read the top index of the stack `o` at time `t`: each is a list of premises and
the index read. A stack that does not exist (`k ≥ K`) reads as empty. Symbols are below `B`. -/
def reads (K B t : ℕ) (o : Option ℕ) : List (List ℕ × ℕ) :=
  match o with
  | none => [([], 0)]
  | some k =>
    if k < K then (List.range (B + 1)).map fun x => ([vC t k 0 x], x)
    else [([], 0)]

/-- Clauses for the next program counter, at time `t` and counter code `q` with instruction `i`. -/
def pcClauses (B t q : ℕ) (i : Instr) : CNF :=
  (List.range B).map fun v => imp [vP t q, vQ t v] (vP (t + 1) (nextCode i v))

/-- Clauses for the next state. -/
def stateClauses (K B t q : ℕ) (i : Instr) : CNF :=
  (List.range B).flatMap fun v =>
    (reads K B t (rdStack i)).map fun r =>
      imp (vP t q :: vQ t v :: r.1) (vQ (t + 1) (newState i v r.2))

/-- Clauses for the next content of stack `k` under the operation `op`: `keep` copies every
cell, `push` writes the top cell and shifts the others down, `pop` shifts up and blanks the
last cell. -/
def cellClauses (H B t q k : ℕ) (op : Op) : CNF :=
  match op with
  | .keep =>
    (List.range H).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k j x] (vC (t + 1) k j x)
  | .push tbl =>
    ((List.range B).map fun v =>
      imp [vP t q, vQ t v] (vC (t + 1) k 0 (tbl.getD v 0 + 1)))
    ++ ((List.range (H - 1)).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k j x] (vC (t + 1) k (j + 1) x))
  | .pop =>
    ((List.range (H - 1)).flatMap fun j =>
      (List.range (B + 1)).map fun x => imp [vP t q, vC t k (j + 1) x] (vC (t + 1) k j x))
    ++ [imp [vP t q] (vC (t + 1) k (H - 1) 0)]

/-- All clauses of one step, from time `t` to time `t + 1`. -/
def stepClauses (K H B : ℕ) (P : List Instr) (t : ℕ) : CNF :=
  (List.range (B + 1)).flatMap fun q =>
    pcClauses B t q (instrAt P q) ++ stateClauses K B t q (instrAt P q) ++
      (List.range K).flatMap fun k => cellClauses H B t q k (stackOp (instrAt P q) k)

/-- The clauses of time `0`. The input stack holds, from the top, the input `zs` in cells
`0 .. n - 1`, then the witness in cells `n .. n + m - 1` (each blank, `2` or `3`, and a blank is
followed by a blank), then blanks. -/
def initClauses (c : Code) (zs : List ℕ) (m H : ℕ) : CNF :=
  [imp [] (vP 0 (c.pc₀ + 1)), imp [] (vQ 0 c.state₀)]
  ++ ((List.range c.nstk).flatMap fun k =>
    if k = c.kin then [] else (List.range H).map fun j => imp [] (vC 0 k j 0))
  ++ (if c.kin < c.nstk then
      ((List.range zs.length).map fun j => imp [] (vC 0 c.kin j (zs.getD j 0 + 1)))
      ++ ((List.range m).map fun j =>
        [(vC 0 c.kin (zs.length + j) 0, true), (vC 0 c.kin (zs.length + j) 3, true),
          (vC 0 c.kin (zs.length + j) 4, true)])
      ++ ((List.range (m - 1)).map fun j =>
        imp [vC 0 c.kin (zs.length + j) 0] (vC 0 c.kin (zs.length + (j + 1)) 0))
      ++ ((List.range H).map fun j => imp [] (vC 0 c.kin (zs.length + m + j) 0))
    else [])

/-- The clauses of the last time `T`: halted, and the output stack is exactly `[1]`. -/
def finalClauses (c : Code) (B T : ℕ) : CNF :=
  ((List.range B).map fun p => [(vP T (p + 1), false)])
  ++ (if c.kout < c.nstk then
      [[(vC T c.kout 0 0, false)]]
      ++ ((List.range B).flatMap fun x =>
        if x = 1 then [] else [[(vC T c.kout 0 (x + 1), false)]])
      ++ ((List.range B).map fun x => [(vC T c.kout 1 (x + 1), false)])
    else [[]])

/-- A number bounding one instruction: its table entries and its next counters. -/
def Instr.bd : Instr → ℕ
  | .push _ tbl next => tbl.sum + next
  | .pop _ tbl _ next => tbl.sum + next
  | .peek _ tbl _ next => tbl.sum + next
  | .load tbl next => tbl.sum + next
  | .branch _ next₁ next₂ => next₁ + next₂
  | .goto tbl => tbl.sum
  | .halt => 0

/-- The bound on all data of a run of `c` on symbols below `4`: every counter, state and symbol
is below it. It depends on the code only. -/
def bound (c : Code) : ℕ :=
  c.pc₀ + c.state₀ + (c.prog.map Instr.bd).sum + 4

/-- The number of cells per stack. -/
def cellsOf (n m T : ℕ) : ℕ := n + m + T + 2

/-- The tableau formula: the code `c` run for `T` steps on the input symbols `zs` followed by
at most `m` witness symbols, each `2` or `3`. -/
def tableau (c : Code) (zs : List ℕ) (m T : ℕ) : CNF :=
  initClauses c zs m (cellsOf zs.length m T)
  ++ ((List.range T).flatMap fun t =>
    stepClauses c.nstk (cellsOf zs.length m T) (bound c) c.prog t)
  ++ finalClauses c (bound c) T

end PEqualNP.Library.SearchHelpers.Tab
