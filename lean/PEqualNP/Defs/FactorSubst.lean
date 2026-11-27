import PEqualNP.Defs.TopForm

/-!
# Factor substitution: rewriting the reads of an AND gate, the live size, the OR closure

The setting is the one of `PEqualNP.Defs.EdgeOwnership` and `PEqualNP.Defs.TopForm`: a circuit of
the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs `Fin n`; wire `i < n` is the input
`x_i`, gate number `j` is wire `n + j`, a gate reads the wires named in its input list, and a wire
that does not exist yet when a gate is evaluated reads `false`. Later statements apply these
definitions by these names and in this argument order.

THE OPERATION (FACTOR SUBSTITUTION). For an AND
gate `c = a AND b`, the rewrite replaces, at every read of `c` by a gate `r`, the wire of `c` by a
wire `sigma(r)` (on paper one of the two operand wires `a`, `b`, chosen per reader), then deletes
`c` and the gates left dead. Here the rewrite is split in two parts on purpose:

* `substReads C n c sigma`: the circuit with every occurrence of the wire `n + c` in the input list
  of gate `r` replaced by the wire `sigma r`. The choice `sigma : ℕ → ℕ` is DATA (a wire index per
  reading gate), not computed from the circuit. NOTHING IS RENUMBERED: gate `c` and every gate made
  dead stay in the gate list, so every other wire keeps its index. Deleting with renumbering is
  avoided on purpose: it would shift every later wire and make "every gate outside the closure
  keeps its function" a statement about two different numberings. `substReads` keeps `c` in the
  list as a dead gate (no gate reads it any more, unless `sigma` sends some reader back to `n + c`).
* `liveGates n C`: the gates the output depends on: the output gate and its strict cone
  (`InCone` of `EdgeOwnership`). `liveSize n C := (liveGates n C).card`: the size measure under
  which "delete `c` and the dead gates" is a drop. On paper (not checked): `liveSize n C` equals
  the size of the circuit obtained from `C` by deleting every gate outside `liveGates n C` and
  renumbering, and that circuit computes the same function.

THE CLOSURE OBJECTS the lemma (stated elsewhere on these names, not here) will name:

* `orClosure n C c`: `O`, the gates reached from `c` by paths of OR gates only, `c` excluded: the
  gates `g ≠ c` with `c` in the OR closure of the wire of `g` (`OrReaches n C (n + g) c` of
  `CleanedNonEdge`, which walks down through OR gates and stops at non-OR gates). Such a `g` is
  an OR gate.
* `frontier n C c`: the gates outside `O` and other than `c` whose input list contains the wire of
  `c` or of a gate of `O`. Under the lemma's hypotheses these are AND gates (an OR gate reading
  `O + {c}` through an earlier wire is in `O`).

Caveats a statement must respect.
* `sigma` is read only at gates that read `n + c`: at every other gate it is ignored. `sigma r`
  is any wire number; nothing checks that it is earlier than `n + r` or that it is an operand of
  `c`. A `sigma r` at or past `n + r` reads `false` in the root model.
* The output index is not changed: if the output wire is `n + c` itself, `substReads` leaves the
  output on the (unchanged) gate `c`. The lemma's (H3) excludes this.
* Every read is replaced, including a read of `n + c` by a gate `r ≤ c` (such a read is of a
  wire not computed yet, which reads `false` before the rewrite; afterwards it reads `sigma r`).
  Under `ReadsBack` there is no such read.
* A reader of `c` that is itself dead is rewritten too; this changes nothing the output sees.
* `liveGates` follows only reads of earlier wires, as `InCone` does; it is empty when the output
  wire is an input wire, and also when it is past the last gate (such an output reads `false`).
* `frontier` looks at the input lists by membership, as `readers` of `TopForm` does: a gate that
  names the wire of `c` or of a gate of `O` at or past its own wire is counted, although it reads
  `false` there. Under `ReadsBack` this does not occur.
* Fan-in two, AND/OR gates only and `c` being an AND gate are hypotheses of the lemma
  (`IsAO2 n C`, `(gateAt C c).op = GateOp.and`), not of these definitions; every definition here
  is meaningful on any circuit of the root model.
-/

namespace PEqualNP.FactorSubst

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge

/-- The circuit `C` on `n` inputs with every read of the wire `n + c` (of gate `c`) by gate `r`
replaced by the wire `sigma r`. No gate is removed and nothing is renumbered; the output index is
unchanged. -/
def substReads (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) : Circuit :=
  ⟨C.gates.mapIdx fun r g => ⟨g.op, g.inputs.map fun i => if i = n + c then sigma r else i⟩,
    C.output⟩

/-- The live gates of `C` on `n` inputs: the output gate (gate `C.output - n`, when the output
wire is a gate's wire) and every gate strictly inside its cone. -/
def liveGates (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    n ≤ C.output ∧ (j = C.output - n ∨ InCone n C j (C.output - n))

/-- The live size: the number of gates the output depends on. -/
def liveSize (n : ℕ) (C : Circuit) : ℕ := (liveGates n C).card

/-- `O`: the gates other than `c` reached from gate `c` by paths of OR gates only (gate `c` is in
the OR closure of their wire). -/
def orClosure (n : ℕ) (C : Circuit) (c : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g => g ≠ c ∧ OrReaches n C (n + g) c

/-- The frontier of `c`: the gates outside `O` and other than `c` whose input list contains the
wire of `c` or of a gate of `O`. -/
def frontier (n : ℕ) (C : Circuit) (c : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun k => k ≠ c ∧ k ∉ orClosure n C c ∧
    ∃ w ∈ insert c (orClosure n C c), n + w ∈ (gateAt C k).inputs

end PEqualNP.FactorSubst
