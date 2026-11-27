import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.CircuitMoves

/-!
# Low wires, alive sets and low merges at a line

The setting is the root circuit model of `PEqualNP.Defs.CircuitLowerBounds`, on the edge function
of a bipartite graph with sides points and lines. There are `P` points and `L` lines, and
`P + L` inputs, POINTS FIRST: point `p` is input `p` (the variable `x_p`), line `w` is input
`P + w` (the variable `y_w`). The incidence is `inc : Fin P → Fin L → Bool` (`inc p w = true`:
point `p` lies on line `w`); a Bool so that every notion below is decidable. Wires are numbered
as in `Circuit.wires`: wire `i < P + L` is an input, gate number `j` (from `0`) is wire
`P + L + j`; a wire that does not exist reads `false`.

The objects (the paper "the merge identity", section "Definitions").

* The RESTRICTION of a wire `g` to a line `w` is the function of the point inputs obtained by
  setting `y_w` true and every other line input false. `restrictInput P L w pts` is that input
  for the point values `pts`.
* `g` is LOW for `w` when its restriction is at most `S_w`, the OR of the points of `w`: on
  every point assignment, `g` true on the restricted input implies some point of `w` is on.
* The ALIVE SET of `g` at `w` is the set of points `p` such that `g` is true on the input with
  `x_p` and `y_w` on and every other input off (`pointLineInput P L p w`).
* A LOW MERGE at `w` is an OR gate `a OR b` that is low for `w` and whose two operands have
  INCOMPARABLE alive sets at `w` (neither is a subset of the other).

Names.
* `restrictInput P L w pts`: the input with points `pts`, line `w` on, other lines off.
* `pointLineInput P L p w`: the input with only `x_p` and `y_w` on.
* `lineSum P L inc w pts`: the value of `S_w` on the points `pts`.
* `wireVal C x g`: the value of wire `g` of `C` on the input `x`.
* `IsLow P L inc C g w`: wire `g` is low for line `w`.
* `aliveSet P L C g w : Finset (Fin P)`: the alive set of wire `g` at line `w`.
* `IsLowMerge P L inc C g w`: wire `g` is a low merge at line `w`.
All three predicates are decidable (instances below).

Caveats a statement must respect.
* AND/OR-only is NOT built in: it is a hypothesis of the paper, stated with
  `PEqualNP.CircuitLowerBounds.IsMonotoneCircuit`. On a circuit with NOT, MOD or MAJORITY gates
  the definitions still evaluate, but the facts of the paper (an OR gate low for `w` has both
  operands low, a low wire's alive set lies on `w`, ...) are about AND/OR circuits.
* Fan-in two is built into `IsLowMerge` only: the gate must be an OR gate whose input list is
  EXACTLY `[a, b]` (two reads, in this order; the definition is symmetric in `a` and `b`). An
  OR gate of any other fan-in is never a low merge. `IsLow` and `aliveSet` apply to any wire.
  The paper counts circuits of fan-in two; a statement that wants it for every gate says so.
* `IsLowMerge` asks both operands to be EARLIER wires (`a < g`, `b < g`) and `g` to be a gate
  (`P + L ≤ g`). The paper's gates read earlier wires; an operand at or above `g` reads `false`
  in the root model, and its value in the final wire list is not what the gate read, so such a
  gate is excluded rather than given a meaning.
* `a = b` is allowed by the shape but is never a merge (equal alive sets are comparable).
* The definitions are SEMANTIC on the restricted inputs only: `IsLow` and `aliveSet` read the
  circuit on the `2^P` restricted inputs at `w` and the `P` inputs `pointLineInput`, nothing
  else. `aliveSet` does not use the incidence; if `g` is low for `w` it lies inside the points
  of `w` (a lemma, not built in).
* This is the plain LOW MERGE of the inequality form. The NEW low merge of the sharper form
  (joining two classes along the order of the gates) is a different notion and is not defined
  here; a low merge need not be new (in the star circuit, the sum of a second line can be a
  low merge at the first).
* Inputs have length exactly `P + L`; a statement that the circuit computes the edge function
  uses `Circuit.eval` on inputs of that length with the same points-first order.
-/

namespace PEqualNP.LowMerge

open PEqualNP.CircuitLowerBounds

/-- The input with the points as given by `pts`, line `w` on and every other line off, points
first: `x_p = pts p`, `y_w = true`, `y_v = false` for `v ≠ w`. -/
def restrictInput (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) : List Bool :=
  List.ofFn pts ++ List.ofFn (fun v : Fin L => decide (v = w))

/-- The input with only `x_p` and `y_w` on. -/
def pointLineInput (P L : ℕ) (p : Fin P) (w : Fin L) : List Bool :=
  restrictInput P L w (fun q => decide (q = p))

/-- The value of `S_w`, the OR of the points of line `w`, on the point values `pts`. -/
def lineSum (P L : ℕ) (inc : Fin P → Fin L → Bool) (w : Fin L) (pts : Fin P → Bool) : Bool :=
  decide (∃ p : Fin P, inc p w = true ∧ pts p = true)

/-- The value of wire `g` of `C` on input `x` (`false` if there is no such wire). -/
def wireVal (C : Circuit) (x : List Bool) (g : ℕ) : Bool :=
  (C.wires x).getD g false

/-- LOW: wire `g` of `C` is low for line `w`. On every point assignment, if `g` is true on the
input with those points, line `w` on and every other line off, then some point of `w` is on. -/
def IsLow (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) : Prop :=
  ∀ pts : Fin P → Bool, wireVal C (restrictInput P L w pts) g = true →
    lineSum P L inc w pts = true

/-- ALIVE SET: the points `p` such that wire `g` of `C` is true on the input with only `x_p` and
`y_w` on. -/
def aliveSet (P L : ℕ) (C : Circuit) (g : ℕ) (w : Fin L) : Finset (Fin P) :=
  Finset.univ.filter (fun p => wireVal C (pointLineInput P L p w) g = true)

attribute [local instance] PEqualNP.CircuitMoves.gateDecEq

/-- LOW MERGE: wire `g` of `C` is a gate `OR(a, b)` of fan-in exactly two with `a, b` earlier
wires, `g` is low for line `w`, and the alive sets of `a` and `b` at `w` are incomparable. -/
def IsLowMerge (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Prop :=
  P + L ≤ g ∧ ∃ a < g, ∃ b < g,
    C.gates[g - (P + L)]? = some ⟨GateOp.or, [a, b]⟩ ∧
    IsLow P L inc C g w ∧
    ¬ aliveSet P L C a w ⊆ aliveSet P L C b w ∧
    ¬ aliveSet P L C b w ⊆ aliveSet P L C a w

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Decidable (IsLow P L inc C g w) := by
  unfold IsLow; infer_instance

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Decidable (IsLowMerge P L inc C g w) := by
  unfold IsLowMerge; infer_instance

end PEqualNP.LowMerge
