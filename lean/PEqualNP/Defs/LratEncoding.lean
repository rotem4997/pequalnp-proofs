/-!
# Root definitions for the CNF encoding of small AND/OR circuits (definitions only)

The formula `enc2 n s g rows` says: there is a circuit of AND and OR gates of fan-in two with `s`
gate slots (padding allowed) on `n` inputs, in a normal form, whose output equals `g r` on every
row `r` of `rows` (input `i` is bit `i` of `r`). A library lemma shows that a circuit with at most `s` gates computing `f` makes
`enc2 n s (rowFun n f) rows` satisfiable, so an unsatisfiability certificate gives a size lower
bound. The library's definitions of the same names are proved equal to these by `rfl`.

`enc2Cube n s k` (for `k < enc2CubeCount n s`) is one cube of a split of `enc2 n s g rows` into
pieces: unit clauses fixing the first source and the operation of the last gate. Every
assignment satisfying `enc2` satisfies some cube (the covering lemma in the library), so the
lower bound follows from the unsatisfiability of every piece `enc2 n s g rows ++ enc2Cube n s k`.

Literals are natural numbers: variable `v` positive is `2 * v`, negative is `2 * v + 1`; a
formula is a list of clauses, a clause a list of literals. Encoding variable `x` is checker
variable `x + 1` (so variable `0` is never used).

Every definition here is a definition, not a result, and copies the library text verbatim.
-/

namespace PEqualNP.Defs.LratEncoding

/-- The truth value of literal `l` under the assignment `a`. -/
def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

/-- A clause is satisfied by `a` when one of its literals is true. -/
def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

/-- A formula (list of clauses) is satisfiable when one assignment satisfies every clause. -/
def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

/-- The function on rows: row `r` is the input whose bit `i` is bit `i` of `r`. -/
def rowFun (n : Nat) (f : (Fin n → Bool) → Bool) (r : Nat) : Bool := f fun i => r.testBit i

section formula
variable (n s : Nat)

/-- The width of one block of variables. -/
def wd : Nat := 2 ^ n + n + s + 1

/-- Variable `(kd * (s + 1) + j) * wd + a`: kind `kd` (0 operation, 1 first source, 2 second
source, 3 gate value, 4 and 5 source values, 6 output source, 7 padding), gate `j`, slot `a`. -/
def ix (kd j a : Nat) : Nat := (kd * (s + 1) + j) * wd n s + a

/-- The literal "variable `v` is true". -/
def P (v : Nat) : Nat := 2 * v + 2
/-- The literal "variable `v` is false". -/
def Q (v : Nat) : Nat := 2 * v + 3
/-- The literal saying variable `v` has value `b`. -/
def L (v : Nat) (b : Bool) : Nat := if b then P v else Q v

/-- At least one operation per gate (0 AND, 1 OR, 2 TRUE). -/
def fOp : List (List Nat) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

/-- At least one source per gate and side (gate `j` reads a wire `0 .. n + j`). -/
def fSrcAlo : List (List Nat) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

/-- The value of source `e` of gate `j` on row `r` is the value of the wire it reads. -/
def srcEq (e j k r : Nat) : List (List Nat) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

/-- `srcEq` for every side, gate, row and wire. -/
def fSrcEq (rows : List Nat) : List (List Nat) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

/-- The value of gate `j` on row `r` is its operation on its source values. -/
def gateCl (j r : Nat) : List (List Nat) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

/-- `gateCl` for every gate and row. -/
def fGate (rows : List Nat) : List (List Nat) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

/-- At least one output source. -/
def fOutAlo : List (List Nat) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

/-- The output source carries `g` on row `r`. -/
def outEq (g : Nat → Bool) (k r : Nat) : List (List Nat) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

/-- `outEq` for every row and wire. -/
def fOutEq (g : Nat → Bool) (rows : List Nat) : List (List Nat) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

/-- Normal form: the output is the last wire, or the last gate is padding. -/
def fOut : List (List Nat) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

/-- Normal form: padding is exactly `(TRUE, F, F)`; a gate that is not padding is not `TRUE`
and reads no `F`. -/
def fPad : List (List Nat) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

/-- Normal form: the padding gates come first. -/
def fPre : List (List Nat) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

/-- Normal form: no gate reads a padding wire. -/
def fPadRd : List (List Nat) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

/-- Normal form: a gate that is not padding has its first source below its second. -/
def fOrd : List (List Nat) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

/-- Normal form: a gate before the last that is not padding is read by a later gate. -/
def fUsed : List (List Nat) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

/-- The formula: a circuit of AND and OR gates with `s` gates (padding allowed) on `n` inputs,
in normal form, computing `g` on every row of `rows`. -/
def enc (g : Nat → Bool) (rows : List Nat) : List (List Nat) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

/-- The escape literals of the order at `j`: gate `j` is padding, or gate `j + 1` reads `n + j`. -/
def lexBase (j : Nat) : List Nat :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

/-- The order: unless gate `j` is padding or gate `j + 1` reads wire `n + j`, the triple
`(s1, s2, op)` of gate `j` is lexicographically below that of gate `j + 1`. -/
def fLex : List (List Nat) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

/-- The formula `enc2 n s g rows`: `enc` (a circuit of AND and OR gates of fan-in two with `s`
gate slots on `n` inputs, in normal form, equal to `g` on every row of `rows`) together with the
lexicographic order of adjacent independent gates `fLex`. -/
def enc2 (g : Nat → Bool) (rows : List Nat) : List (List Nat) := enc n s g rows ++ fLex n s

/-- The number of cubes of the split of `enc2 n s g rows`: `n + s` first sources times three
operations of the last gate. -/
def enc2CubeCount : Nat := 3 * (n + s)

/-- Cube `k` of the split of `enc2 n s g rows` (for `k < enc2CubeCount n s`): two unit clauses,
"the first source of the last gate `s - 1` is wire `k % (n + s)`" and "the operation of the last
gate is `k / (n + s)`" (0 AND, 1 OR, 2 TRUE). -/
def enc2Cube (k : Nat) : List (List Nat) :=
  [[P (ix n s 1 (s - 1) (k % (n + s)))], [P (ix n s 0 (s - 1) (k / (n + s)))]]

end formula

end PEqualNP.Defs.LratEncoding
