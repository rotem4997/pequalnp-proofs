import PEqualNP.Defs.MetaComplexityMinimal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ENat.Lattice
import PEqualNP.Defs.LineDegree

/-!
# READ-k monotone circuits

Circuits are the root circuits (`PEqualNP.CircuitLowerBounds.Circuit`) on `n` inputs, wires
`0 .. n - 1` the inputs, gate number `j` wire `n + j`. The notion is for AND/OR circuits (any
fan-in); a gate of any other kind has no proof tree here.

Words.
* A PRIME IMPLICANT of the function a circuit computes on `n` inputs is a set `S` of inputs such
  that the input with exactly `S` true makes the output true, and no proper subset of `S` does.
  For a monotone function this is the usual minimal set of variables whose AND implies the
  function.
* A PROOF TREE of `S` in `C`: start at the output, take ONE input at every OR gate and ALL inputs
  at every AND gate, and stop at input wires, every leaf an input of `S`. (A wire read twice is
  unfolded twice: a proof tree is a tree, not a subcircuit.) When `S` is prime, its leaves are
  then exactly `S`, since the leaves alone already force the output true.
* `C` is READ-k on `S` if some proof tree of `S` has every variable of `S` as a leaf at most `k`
  times. `C` is READ-k if it is READ-k on every prime implicant of the function it computes.

Computation (the multiplicity recursion, joint version). For the list `S`, every wire carries the
set of COUNT VECTORS of its proof trees (entry `i` the number of leaves equal to `S[i]`), each
entry capped at `k + 1`: an input of `S` carries its unit vector, any other input nothing; an OR
gate the union of its inputs' sets; an AND gate the sums of one vector from each input (start: the
zero vector, the empty AND being true). `C` is READ-k on `S` when the output's set holds a vector
with every entry at most `k`. The cap changes no answer (an entry above `k` stays above `k` under
sums), and keeps every set inside `(k + 2) ^ |S|` vectors.

Names.
* `readVectors C n S k`: the capped count-vector sets of all wires.
* `readsAtMost C n S k`: READ-k on the list `S` (Bool).
* `IsPrimeImplicant n C S`, `IsReadK n C k`: the two Props above (`S : Finset (Fin n)`).
* `eachReadsAtMost C n S k`: the SCALAR recursion (see the caveat), kept to show it differs.

Sources matched: an in-house script (per incident pair, Pareto sets of (point count, line count) pairs, OR = union, AND = pairwise sums,
read = max of the two counts, minimized jointly over trees); and the printed notion of read-k
(every prime implicant has, in the polynomial the circuit produces, a
monomial on exactly its variables with every degree at most k). These two AGREE with this file:
one tree (one monomial) must bound every variable at once.

They DIFFER from a per-variable search reading ("an OR takes the minimum over its TRUE
children, an AND the sum", one number per variable): that minimizes each variable over its OWN best
tree, so it bounds a different tree for each variable. It is `eachReadsAtMost` below, and it is
strictly weaker: on the circuit AND(AND(x0, x1), OR(x0, x1)) it gives 1 for x0 and
1 for x1 (calling it read-1), while every proof tree reads x0 or x1 twice (read-2, not read-1).
The two agree when the implicant has one variable.

Caveats.
* `IsReadK` quantifies over the prime implicants of the function `C` computes, not of a function
  given separately; for "`C` computes `f` and is READ-k" state both.
* Nothing here asks fan-in two or monotone gates; a statement wanting them says so
  (`PEqualNP.MetaComplexity.FanInTwo`, `IsMonotoneCircuit`). A NOT, MOD or MAJ gate carries no
  vector, so a proof tree never passes through one.
* `readsAtMost` expects `S` without repetitions and with entries below `n`; `IsReadK` feeds it
  the sorted members of a `Finset (Fin n)`.
* A wire index that does not exist carries no vector (like the root's `false`).

# Part two: the double re-read set and the single-read cost

Setting: a bipartite incidence structure on `n` inputs; `isLine i` says input `i` is a LINE input,
the others are POINT inputs; `E` lists the edges as pairs (point, line) of wire numbers; the
function is the OR over edges of (point AND line).

Words.
* The LINEAR PARTS of a wire, at an input: part 0 = the wire's value with every line input set
  false; part 1 = the OR of its proof-tree terms with exactly one line leaf. Computed by DERIVED
  WIRES, no trees: a line input `y` gives (false, y), a point input `x` gives (x, false); an OR
  gives the ORs of the parts; an AND of a and b gives (a0 AND b0, (a0 AND b1) OR (a1 AND b0)),
  folded over any fan-in from (true, false). Any other gate gives (false, false).
* Edge (p, l) is LINE-SINGLE in `C` (in E_y(C)) if the output's part 1 is true at the input with
  only p and l true: some proof tree with every leaf p or l has exactly one leaf l (the tree may
  have no leaf p; that happens only when the circuit accepts the line alone). POINT-SINGLE (E_x(C)): the
  same with the roles of points and lines exchanged (`isLine` negated).
* The DOUBLE RE-READ SET D(C): the edges of `E` that are neither line-single nor point-single.
  `C` is SINGLE-READ if D(C) is empty.
* The SINGLE-READ COST of `f`: the least size of an AND/OR fan-in-two circuit computing `f` on `n`
  inputs that is single-read; `⊤` when there is none.

Names: `linearParts`, `lineSingle`, `doubleReread` (exactly the proposal's text, moved
from namespace `PEqualNP.CircuitLowerBounds` to `PEqualNP.ReadK`), `IsSingleRead`, `AndOrFanInTwo` (the parallel of `FanInTwo` with no NOT),
`HasSingleReadSize` (atlas form: a single-read circuit of at most `s` gates computes `f`),
`srSize` (the `sInf` form, in `ℕ∞`).

Changes from the proposal: the namespace (one module for both notions); the proposal states the
cost only as an existence pair and avoids an inf in a definition, while a least size is wanted:
both are given, `srSize` is the `sInf` of the sizes in
`HasSingleReadSize`'s witnesses. Circuits counted by the cost: AND and OR only, fan-in at most two
(no NOT), as the concept file says; so "sr(F) >= size(F)" in the concept file compares with the
MONOTONE size, not the root's `HasCircuitSize` (which allows NOT).

Relation to READ-k (on paper, not built): a READ-1 proof tree of {p, l} reads l once, so a circuit
READ-1 on every edge is single-read; the converse fails (a single-read circuit may read the other
side of an edge any number of times).

Caveats.
* D(C) depends on the edge list `E` and on `isLine`, both data; nothing checks that `C` computes
  the incidence function of `E`, or that `E` lists point-line pairs.
* Inputs are the list of `n` bits; a pair naming a wire at or above `n` is never single.
-/

namespace PEqualNP.ReadK

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Add `v` to the list `A` unless it is already there. -/
def insertNew (A : List (List ℕ)) (v : List ℕ) : List (List ℕ) :=
  if v ∈ A then A else A ++ [v]

/-- Entrywise sum of two count vectors, each entry capped at `k + 1`. -/
def capAdd (k : ℕ) (u v : List ℕ) : List ℕ :=
  List.zipWith (fun a b => min (a + b) (k + 1)) u v

/-- The count vectors of an AND of two wires: one vector from each, summed and capped. -/
def andStep (k : ℕ) (A B : List (List ℕ)) : List (List ℕ) :=
  (A.flatMap fun u => B.map fun v => capAdd k u v).foldl insertNew []

/-- The count vectors of an input wire `i` for the list `S`: the unit vector at `i` if `i` is in
`S`, none otherwise. -/
def leafVectors (S : List ℕ) (k : ℕ) (i : ℕ) : List (List ℕ) :=
  if i ∈ S then [S.map fun j => if j = i then min 1 (k + 1) else 0] else []

/-- The capped count-vector sets of all wires of `C` on `n` inputs, for the list `S`: inputs
first, then one set per gate. OR: union; AND: sums (start: the zero vector); other gates: none. -/
def readVectors (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) : List (List (List ℕ)) :=
  C.gates.foldl
    (fun R g =>
      let ins := g.inputs.map fun i => R.getD i []
      R ++ [match g.op with
        | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
        | _ => []])
    ((List.range n).map (leafVectors S k))

/-- `C` is READ-k on the variable list `S`: some proof tree of `S` (one input at each OR, all at
each AND, leaves in `S`) has every variable of `S` as a leaf at most `k` times. -/
def readsAtMost (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) : Bool :=
  ((readVectors C n S k).getD C.output []).any fun v => v.all fun a => decide (a ≤ k)

/-- The input on `n` wires whose true inputs are exactly the members of `S`. -/
def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

/-- `S` is a PRIME IMPLICANT of the function `C` computes on `n` inputs: the input with exactly
`S` true makes the output true, and the input with exactly `T` true does not, for every proper
subset `T` of `S`. -/
def IsPrimeImplicant (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Prop :=
  circuitFun n C (setInput S) = true ∧ ∀ T ∈ S.ssubsets, circuitFun n C (setInput T) = false

instance (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Decidable (IsPrimeImplicant n C S) := by
  unfold IsPrimeImplicant; infer_instance

/-- The members of `S` as a list of wire numbers, in increasing order. -/
def setList {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter fun i => decide (i ∈ S)).map Fin.val

/-- `C` is READ-k on `n` inputs: every prime implicant of the function it computes has a proof
tree in `C` reading each of its variables at most `k` times. -/
def IsReadK (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), IsPrimeImplicant n C S → readsAtMost C n (setList S) k = true

instance (n : ℕ) (C : Circuit) (k : ℕ) : Decidable (IsReadK n C k) := by
  unfold IsReadK; infer_instance

/-- The SCALAR multiplicity recursion for the variable `v` and the implicant list `S` (a per-variable
reading as relayed): `none` = no proof tree with leaves in `S`; an input is `some 1` if it is `v`,
`some 0` if it is another member of `S`; an OR takes the least over its inputs that have one; an
AND the sum, `none` if one input has none. -/
def scalarMults (C : Circuit) (n : ℕ) (S : List ℕ) (v : ℕ) : List (Option ℕ) :=
  C.gates.foldl
    (fun R g =>
      let ins := g.inputs.map fun i => R.getD i none
      R ++ [match g.op with
        | GateOp.or => ins.foldl (fun acc o => match acc, o with
            | none, o => o
            | some a, none => some a
            | some a, some b => some (min a b)) none
        | GateOp.and => ins.foldl (fun acc o => match acc, o with
            | some a, some b => some (a + b)
            | _, _ => none) (some 0)
        | _ => none])
    ((List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none)

/-- The scalar reading of READ-k on `S`: for EACH variable separately, its least count over proof
trees is at most `k`. Weaker than `readsAtMost` (the trees may differ per variable). -/
def eachReadsAtMost (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) : Bool :=
  S.all fun v => match (scalarMults C n S v).getD C.output none with
    | some m => decide (m ≤ k)
    | none => false

/-! ## Part two: the double re-read set and the single-read cost -/

/-- The two linear parts of every wire at input `x`: part 0 = the wire with every LINE input
(`isLine i`) set false; part 1 = the OR of its proof-tree terms with exactly one line leaf. AND and
OR of any fan-in; any other gate gives (false, false). -/
def linearParts (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) : List (Bool × Bool) :=
  C.gates.foldl
    (fun w g =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      w ++ [match g.op with
        | GateOp.or  => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)])
    ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))

/-- Edge (p, l) is LINE-SINGLE in `C`: the output's part 1 is true at the input with only
`p` and `l` true. -/
def lineSingle (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (p l : ℕ) : Bool :=
  ((linearParts C isLine ((List.range n).map fun i => i == p || i == l)).getD C.output
    (false, false)).2

/-- The DOUBLE RE-READ SET of `C` over the edge list `E` (pairs point, line): the edges single on
neither side. -/
def doubleReread (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.filter fun e =>
    !(lineSingle C n isLine e.1 e.2) && !(lineSingle C n (fun i => !isLine i) e.1 e.2)

/-- `C` is SINGLE-READ over `E`: its double re-read set is empty. -/
def IsSingleRead (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (E : List (ℕ × ℕ)) : Prop :=
  doubleReread C n isLine E = []

instance (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (E : List (ℕ × ℕ)) :
    Decidable (IsSingleRead C n isLine E) := by
  unfold IsSingleRead; infer_instance

/-- Every gate of `C` is an AND or an OR gate reading at most two wires. -/
def AndOrFanInTwo (C : Circuit) : Prop :=
  IsMonotoneCircuit C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

instance (C : Circuit) : Decidable (AndOrFanInTwo C) := by
  unfold AndOrFanInTwo; infer_instance

/-- Some AND/OR fan-in-two circuit with at most `s` gates computes `f` on `n` inputs and is
single-read over `E`. -/
def HasSingleReadSize (n : ℕ) (isLine : ℕ → Bool) (E : List (ℕ × ℕ))
    (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, AndOrFanInTwo C ∧ C.size ≤ s ∧ circuitFun n C = f ∧ IsSingleRead C n isLine E

/-- The SINGLE-READ COST of `f`: the least size of an AND/OR fan-in-two circuit computing `f` on
`n` inputs that is single-read over `E` (`⊤` when there is none). -/
noncomputable def srSize (n : ℕ) (isLine : ℕ → Bool) (E : List (ℕ × ℕ))
    (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ C : Circuit, AndOrFanInTwo C ∧ circuitFun n C = f ∧
    IsSingleRead C n isLine E ∧ s = C.size}

end PEqualNP.ReadK
