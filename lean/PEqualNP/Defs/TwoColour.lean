import PEqualNP.Defs.TopForm

/-!
# Two-colour OR gates and their count T(C)

The setting is the one of `PEqualNP.Defs.TopForm`: a circuit of the root model
(`PEqualNP.Defs.CircuitLowerBounds`) on the inputs `Fin n`; wire `i < n` is the input `x_i`, gate
number `j` is wire `n + j`. The inputs are split into POINTS and LINES of an incidence structure by
a Boolean `isLine : ℕ → Bool` on the input index (as `doubleReread` of `PEqualNP.Defs.ReadK` takes
it): input `i` is a line when `isLine i = true`, a point otherwise. For the Fano incidence of the
root (points `0 .. 6`, lines `7 .. 13`) this is `fun i => decide (7 ≤ i)`.

The notions (for the two-sided surcharge `|C| - (|E| + tau - 1) - T`).
* OR-REACH of a wire: the inputs reached from it going DOWN through OR gates only; an AND gate's
  own reach is EMPTY (it does not look through itself); an input wire reaches itself.
* TWO-COLOUR OR: an OR gate whose OR-reach contains both a point input and a line input.
* T(C): the number of two-colour OR gates.

REUSE. The OR-reach is the root's `orIn n C w` (`PEqualNP.Defs.TopForm`, built on
`CleanedNonEdge.OrReaches`); no new reach is defined here. Reading the definitions: `orIn n C w`
is `{w}` for an input wire `w < n` (`OrReaches` needs `n ≤ w`); for the wire of an AND gate it is
empty (the OR closure of a non-OR gate is that gate alone, and `orIn` only collects inputs read by
OR gates of the closure); for the wire of an OR gate it is the union of the reaches of its
earlier operands, which is the script's recursion `r(g) = r(a) ∪ r(b)` with `r(AND) = ∅` and
`r(x) = {x}`; a wire past the last gate reaches nothing (the script likewise gives `∅` to a name
that is neither a gate nor a variable). So on every wire of a circuit whose gates read earlier
wires (`ReadsBack`, part of `IsAO2`) the two agree. The sanity file checks the three cases on
U1r-30 by `decide`.

* `IsTwoColour n C isLine g`: gate `g` exists, is an OR gate, and `orIn n C (n + g)` has a point
  and a line.
* `twoColour n C isLine`: the finset of such gate indices.
* `tCount n C isLine`: `T(C)`, its cardinality.

Caveats a statement must respect.
* `isLine` is data, not checked against any incidence: a statement fixes it. T depends only on
  the point/line split, not on which point lies on which line.
* `orIn` reads OR gates' input lists: under `IsAO2` (fan-in exactly two, earlier wires) this is
  the script's reach; for a gate that reads a later wire, the later wire contributes no gate to
  the OR closure (`orStep` filters it), but an input index in the list is still collected.
* Only OR gates are counted: an AND gate is never two-colour, whatever its operands reach.
* `n` must be the number of inputs of the circuit; `isLine` is applied to the input index as a
  natural number.
-/

namespace PEqualNP.TwoColour

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

attribute [local instance] gateOpDecEq

/-- Gate `g` of `C` is a TWO-COLOUR OR: it exists, is an OR gate, and its OR-reach
`orIn n C (n + g)` contains a point input and a line input (`isLine` false, resp. true). -/
def IsTwoColour (n : ℕ) (C : Circuit) (isLine : ℕ → Bool) (g : ℕ) : Prop :=
  g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧
    (∃ i ∈ orIn n C (n + g), isLine (i : ℕ) = false) ∧
    (∃ i ∈ orIn n C (n + g), isLine (i : ℕ) = true)

instance (n : ℕ) (C : Circuit) (isLine : ℕ → Bool) (g : ℕ) :
    Decidable (IsTwoColour n C isLine g) := by
  unfold IsTwoColour; infer_instance

/-- The two-colour OR gates of `C`, as gate indices. -/
def twoColour (n : ℕ) (C : Circuit) (isLine : ℕ → Bool) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g => IsTwoColour n C isLine g

/-- `T(C)`: the number of two-colour OR gates of `C`. -/
def tCount (n : ℕ) (C : Circuit) (isLine : ℕ → Bool) : ℕ :=
  (twoColour n C isLine).card

end PEqualNP.TwoColour
