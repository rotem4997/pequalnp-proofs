import PEqualNP.Defs.ReadK

/-!
# JOIN: the lowest AND of a proof tree that holds both sides of an incidence 

A companion of `PEqualNP/Defs/ReadK.lean`, in the same namespace `PEqualNP.ReadK`, built only
on that module: `andStep`, `insertNew`, `leafVectors` and the
root circuits. Proof trees are counted, never built, by the same multiplicity recursion as
`readVectors`.

Sentence. For an incidence (p, l) (wire `p` a point input, wire `l` a line input) the AND gate
on wire `g` is a JOIN of (p, l) in `C` when some proof tree of {p, l} in `C` (from the output:
one input at every OR, all inputs at every AND, every leaf `p` or `l`) passes through `g` with
`g`'s two child subtrees, in that tree, having only `p` leaves (at least one) on one side and
only `l` leaves (at least one) on the other. Such a `g` is a lowest AND of the tree whose
subtree holds both `p` and `l`.

Computation (how it matches the sentence). For the list `G` of wires to watch, every wire
carries the set of AUGMENTED COUNT VECTORS of its proof trees with leaves in {p, l}: entry 0
the number of `p` leaves, entry 1 the number of `l` leaves, and entry `2 + i` the number of
occurrences, in the tree, of the gate on wire `G[i]` as a join (that is, with one child subtree
all `p` and the other all `l`). Entries are capped at `k + 1` (here `capAdd`/`andStep` of the
root). Inputs: `p` carries (1, 0, 0, ...), `l` carries (0, 1, 0, ...), any other input nothing.
OR: the union of its inputs' sets. AND: the sums of one vector from each input (start: the zero
vector). When the gate on wire `w` is an AND reading exactly two wires `a`, `b` and `w` is in
`G`, it ALSO carries u + v + (unit at every position of `w` in `G`) for every `u` of `a` with
entry 0 at least 1 and entry 1 zero and every `v` of `b` with entry 0 zero and entry 1 at least
1, or the same with `a` and `b` exchanged: these are the trees through `w` that are pure on its
two sides, with `w` counted as a join. (A pure child subtree holds no join, so its mark entries
are zero and nothing is counted twice.) By induction on the wires: SOME output vector has every mark entry at least 1
exactly when SOME proof tree with leaves in {p, l} has every gate of `G` as a join. (The set also
holds the unmarked sum of the same split, so a vector may carry fewer marks than its tree has
joins: a mark is never an exact count, and a mark of zero never means "not a join".) So
`joinsInTree C n G p l` (some output vector with every mark entry at least 1) says: ONE proof
tree of {p, l} has every gate of `G` as a join, and `isJoin C n g p l`
(the case `G = [g]`) is the sentence above. The cap changes no answer: with `k = 0` every entry
is capped at 1, and only "zero or not" is ever read.

Read-bounded form: `joinsInReadKTree C n G p l k` asks the same of a proof tree reading each of
`p` and `l` at most `k` times (cap `k + 1`, output vector with entries 0 and 1 at most `k`), for
statements about joins of READ-k trees (READ-2 works with `k = 2`).

Caveats.
* `g` is a WIRE number (gate number `j` is wire `n + j`). Only an AND gate reading exactly two
  wires can be a join; an AND of another fan-in is never one here (the READ-2 setting is fan-in
  two). `AND(a, a)` with `a = x_p OR y_l` is a join (one copy gives `p`, the other `l`).
* Nothing checks that `p` is a point or `l` a line, that `p` and `l` differ, or that `C`
  computes an incidence function; a statement wanting these says so. For `p = l` the notion is
  degenerate (the input carries (1, 1)), and is not meant.
* Forward reads: a gate reading a wire at or after its own carries nothing for it (as in
  `readVectors`), so no proof tree goes through a forward read.
* A join of (p, l) need not be a prime-implicant fact: if {p, l} is no implicant of the output
  there is no proof tree, and no gate is a join.
-/

namespace PEqualNP.ReadK

open PEqualNP.CircuitLowerBounds

/-- The AUGMENTED COUNT VECTORS of all wires of `C` on `n` inputs, for the incidence (p, l) and
the watched wires `G`, entries capped at `k + 1`: entry 0 counts `p` leaves, entry 1 counts `l`
leaves, entry `2 + i` counts the occurrences of the gate on wire `G[i]` as a JOIN (an AND of two
wires whose two child subtrees are all `p` on one side, all `l` on the other). Inputs first,
then one set per gate. OR: union; AND: sums (start: the zero vector); an AND of two wires on a
watched wire also gets the pure splits, marked; other gates: none. -/
def joinVectors (C : Circuit) (n : ℕ) (G : List ℕ) (p l : ℕ) (k : ℕ) :
    List (List (List ℕ)) :=
  C.gates.foldl
    (fun R g =>
      let w := R.length
      let ins := g.inputs.map fun i => R.getD i []
      let zero := (List.range (2 + G.length)).map fun _ => 0
      let mark := (List.range (2 + G.length)).map fun j => if 2 ≤ j ∧ G.getD (j - 2) 0 = w then 1 else 0
      let pureP := fun (v : List ℕ) => decide (1 ≤ v.getD 0 0 ∧ v.getD 1 0 = 0)
      let pureL := fun (v : List ℕ) => decide (v.getD 0 0 = 0 ∧ 1 ≤ v.getD 1 0)
      let splits := fun (A B : List (List ℕ)) =>
        andStep k (andStep k (A.filter pureP) (B.filter pureL)) [mark]
      R ++ [match g.op with
        | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and =>
            let base := ins.foldl (andStep k) [zero]
            if w ∈ G ∧ g.inputs.length = 2 then
              let A := ins.getD 0 []
              let B := ins.getD 1 []
              (splits B A).foldl insertNew ((splits A B).foldl insertNew base)
            else base
        | _ => []])
    ((List.range n).map fun i =>
      if i = p ∨ i = l then
        [(List.range (2 + G.length)).map fun j => if (j = 0 ∧ i = p) ∨ (j = 1 ∧ i = l) then 1 else 0]
      else [])

/-- ONE proof tree of {p, l} in `C` (leaves only `p` and `l`) has EVERY gate of `G` (wire
numbers) as a JOIN of (p, l): an AND of two wires whose two child subtrees, in that tree, have
only `p` leaves on one side and only `l` leaves on the other. -/
def joinsInTree (C : Circuit) (n : ℕ) (G : List ℕ) (p l : ℕ) : Bool :=
  ((joinVectors C n G p l 0).getD C.output []).any fun v => (v.drop 2).all fun a => decide (1 ≤ a)

/-- THE NOTION. The AND gate on wire `g` is a JOIN of the incidence (p, l) in `C` on `n` inputs:
some proof tree of {p, l} (from the output, one input at each OR, all at each AND, leaves only
`p` and `l`) passes through `g`, an AND of two wires, with `g`'s two child subtrees having only
`p` leaves on one side and only `l` leaves on the other (so `g` is a lowest AND of the tree
holding both). -/
def isJoin (C : Circuit) (n : ℕ) (g p l : ℕ) : Bool :=
  joinsInTree C n [g] p l

/-- READ-k form: ONE proof tree of {p, l} reading each of `p` and `l` at most `k` times has every
gate of `G` as a join of (p, l). -/
def joinsInReadKTree (C : Circuit) (n : ℕ) (G : List ℕ) (p l : ℕ) (k : ℕ) : Bool :=
  ((joinVectors C n G p l k).getD C.output []).any fun v =>
    decide (v.getD 0 0 ≤ k ∧ v.getD 1 0 ≤ k) && (v.drop 2).all fun a => decide (1 ≤ a)

end PEqualNP.ReadK
