import PEqualNP.Defs.EdgeOwnership
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# The split count of a line in an AND/OR circuit

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n` (the POINTS): wire `i < n` is the input `x_i`, gate number `g` is wire `n + g`, and a gate
reads the wires named in its input list (a wire that does not exist yet reads `false`). A family
of point sets `Ls : Fin m → Finset (Fin n)` (the LINES; for a plane, its lines; for a graph, its
edges as two-element sets) comes with one output gate per line, `outs : Fin m → ℕ`, a GATE
NUMBER (the output of line `j` is wire `n + outs j`).

The object (a notion of the fleet, founders' point 0i). Let `1_p` be the input true exactly at
the point `p`. The SINGLETON SET `S_g` of gate `g` is the set of points `p` at which gate `g` is
true on `1_p`. Gate `g` is COUNTED AT line `j` when `g` is an existing gate, `g` is the output
gate of `j` or lies in its strict cone, and `S_g` meets the line `Ls j` in at least two points.
The WEIGHT `w(g)` is the number of lines at which `g` is counted. The SPLIT COUNT of line `j` is
  `sigma(j) = sum over the gates g counted at j of 1 / w(g)` (a rational number).
A gate shared by several lines whose tests it serves (meets each in two points) is charged
fractionally to each of them.

* `unitInput p`: the input `1_p`, true exactly at `p`.
* `singletonSet n C g`: the points `p` with gate `g` true at `1_p`.
* `InConeOrSelf n C g o`: gate `g` is gate `o` or lies in the strict cone of gate `o`.
* `Counted n C L o g`: gate `g` exists, is in the cone of the output gate `o` (itself included),
  and its singleton set meets `L` in at least two points.
* `weight n C Ls outs g`: the number of lines `j` at which `g` is counted.
* `contribution n C Ls outs j g`: `1 / weight` if `g` is counted at `j`, else `0`.
* `splitCount n C Ls outs j`: the split count `sigma(j)`, in `ℚ`.
* `splitCountScaled n C Ls outs j`: the natural number `sigma(j) * m!` (every weight of a
  counted gate lies between `1` and `m`, so it divides `m!`).

Caveats a statement must respect.
* Gate numbers, not wire numbers: `outs j` and `g` count gates from `0`, gate `g` is wire `n + g`.
  An output number at or past `C.gates.length` names no gate: nothing is counted at that line.
* The cone is that of `PEqualNP.EdgeOwnership.InCone` (strict, through wires really read), plus
  the output gate itself.
* The definition reads only the inputs of weight one (`1_p`), and does not itself require `C` to
  be monotone, of fan-in two, to use only AND and OR gates, to read only earlier wires, or to
  compute anything: state those as hypotheses. With NOT gates it is still defined, but it is not
  the thinker's notion.
* A gate counted nowhere contributes to no line; the sum of `sigma(j)` over all lines is the
  number of gates counted at some line (on paper), at most `C.gates.length`.
* An AND gate with no inputs is true at every one-point input, so it is counted at every line
  whose cone holds it: a statement that wants the thinker's notion assumes every gate has exactly
  two inputs, each an earlier wire (red team's read, 2026-11-24).
* `Ls` need not be the lines of a plane: any family of point sets is allowed, repeated sets
  included (a repeated line raises the weights).
-/

namespace PEqualNP.SplitCount

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

/-- The input `1_p` on `Fin n`: true exactly at the point `p`. -/
def unitInput {n : ℕ} (p : Fin n) : Fin n → Bool :=
  fun w => decide (w = p)

/-- The SINGLETON SET of gate number `g` of `C` (wire `n + g`): the points `p` such that the gate
is true on the input `1_p`. -/
def singletonSet (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => gateVal n C g (unitInput p) = true

/-- Gate `g` is gate `o` itself or lies in the strict cone of gate `o` (`InCone`). -/
def InConeOrSelf (n : ℕ) (C : Circuit) (g o : ℕ) : Prop :=
  g = o ∨ InCone n C g o

instance (n : ℕ) (C : Circuit) (g o : ℕ) : Decidable (InConeOrSelf n C g o) := by
  unfold InConeOrSelf; infer_instance

/-- Gate `g` of `C` is COUNTED at the line `L` with output gate `o`: `g` is an existing gate, it
is `o` or lies in the strict cone of `o`, and its singleton set meets `L` in at least two
points. -/
def Counted (n : ℕ) (C : Circuit) (L : Finset (Fin n)) (o g : ℕ) : Prop :=
  g < C.gates.length ∧ InConeOrSelf n C g o ∧ 2 ≤ (singletonSet n C g ∩ L).card

instance (n : ℕ) (C : Circuit) (L : Finset (Fin n)) (o g : ℕ) :
    Decidable (Counted n C L o g) := by
  unfold Counted; infer_instance

/-- The WEIGHT of gate `g`: the number of lines `j` (line `Ls j`, output gate `outs j`) at which
`g` is counted. -/
def weight (n : ℕ) (C : Circuit) {m : ℕ} (Ls : Fin m → Finset (Fin n)) (outs : Fin m → ℕ)
    (g : ℕ) : ℕ :=
  (Finset.univ.filter fun j => Counted n C (Ls j) (outs j) g).card

/-- What gate `g` contributes to the split count of line `j`: `1 / weight` when `g` is counted at
`j`, and `0` otherwise. -/
def contribution (n : ℕ) (C : Circuit) {m : ℕ} (Ls : Fin m → Finset (Fin n))
    (outs : Fin m → ℕ) (j : Fin m) (g : ℕ) : ℚ :=
  if Counted n C (Ls j) (outs j) g then 1 / (weight n C Ls outs g : ℚ) else 0

/-- The SPLIT COUNT `sigma(j)` of line `j`: the sum, over the gates `g` of `C` counted at `j`, of
`1 / w(g)`, where `w(g)` is the number of lines at which `g` is counted. -/
def splitCount (n : ℕ) (C : Circuit) {m : ℕ} (Ls : Fin m → Finset (Fin n))
    (outs : Fin m → ℕ) (j : Fin m) : ℚ :=
  ∑ g ∈ Finset.range C.gates.length, contribution n C Ls outs j g

/-- The natural-valued companion of the split count: `sigma(j) * m!`, computed as the sum over
the gates `g` counted at `j` of `m! / w(g)` (the weight of a counted gate lies between `1` and
`m`, so the division is exact). -/
def splitCountScaled (n : ℕ) (C : Circuit) {m : ℕ} (Ls : Fin m → Finset (Fin n))
    (outs : Fin m → ℕ) (j : Fin m) : ℕ :=
  ∑ g ∈ Finset.range C.gates.length,
    if Counted n C (Ls j) (outs j) g then m.factorial / weight n C Ls outs g else 0

end PEqualNP.SplitCount
