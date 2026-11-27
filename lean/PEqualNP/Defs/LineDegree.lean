import PEqualNP.Defs.CircuitLowerBounds

/-!
# Line-degree of an AND/OR circuit over a set of marked inputs

A syntactic label on the wires of a root circuit (`PEqualNP.CircuitLowerBounds.Circuit`), for
circuits whose inputs split in two sides: the marked inputs (the lines, in the papers on the
edge function of a bipartite graph with sides points and lines) and the unmarked ones (the
points). On `n` inputs, wire by wire, in the same order as `Circuit.wires` and
`Circuit.depths`:

* a marked input wire has degree `1`, an unmarked input wire degree `0`;
* an AND gate has the SUM of the degrees of all the wires it reads, with repetitions
  (so `y AND y` has degree `2`), at any fan-in;
* an OR gate has the MAXIMUM of the degrees of all the wires it reads, at any fan-in;
* a gate reading no wire (the constant `true` for AND, `false` for OR) has degree `0`;
* a wire index that does not exist when the gate is evaluated counts as degree `0` (such a
  wire reads `false` in `Circuit.wires`);
* any other gate (NOT, MOD, MAJORITY) gets the MAXIMUM of the degrees of the wires it reads.
  This value is a convention only: the notion is for circuits of AND and OR gates, and every
  statement about line-degree should assume `IsMonotoneCircuit`.

The line-degree of the circuit is the degree of its output wire (`0` if there is no such wire).

Names:
* `Circuit.lineDegrees C n marked`: the list of the degrees of all wires of `C` on `n` inputs.
* `Circuit.lineDeg C n marked`: the degree of the output wire.
* `HasLineDegree n marked C D`: `C` has line-degree at most `D`.
* `IsMonotoneCircuit C`: every gate of `C` is an AND or an OR gate (any fan-in).

The marked set is `marked : Finset ℕ`, a set of input positions: it does not depend on `n`, its
membership is decidable, and positions at or above `n` are ignored (they are gate wires, not
inputs, and their degree comes from the gate).

Caveats a statement must respect:
* The degree is SYNTACTIC, not semantic: `y AND y` has degree `2` although it computes `y`. It
  is not the degree of the computed function as a polynomial, and two circuits computing the
  same function may have different line-degrees.
* The degree depends on the number of inputs `n` (which wires are inputs), so `n` is an
  argument; use the same `n` as in `Circuit.Decides`.
* No fan-in bound is built in. The papers count AND/OR circuits of fan-in two; a statement that
  wants this says so (for instance with `PEqualNP.MetaComplexity.Monotone2`).
* This is the ADDITIVE line-degree (AND sums, with repetition). The papers also use a second
  notion, the most distinct line variables in one formal term; the additive degree is at least
  that one. A statement says which it means, and no statement moves between them.
* The degree is that of the OUTPUT wire. In an AND/OR circuit it bounds every gate that reaches
  the output and says nothing of gates the output never reads.
* A row for the papers' test lemma states "at most `D` lines" and includes the input with no
  line variable (degree `0`).
-/

namespace PEqualNP.CircuitLowerBounds

/-- Equality of gate operations is decidable. Not a global instance (the circuit module does not
declare one); a local instance here, for the test `g.op = GateOp.and` in `Gate.lineDegree`. -/
@[instance_reducible]
def lineDegreeGateOpDecEq : DecidableEq GateOp := by
  intro a b
  cases a <;> cases b <;>
    first
    | exact isTrue rfl
    | (rename_i m m'
       exact if h : m = m' then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl)))
    | exact isFalse (by intro h; cases h)

attribute [local instance] lineDegreeGateOpDecEq

/-- The line-degree of one gate, given the list `d` of the degrees of the wires before it: the sum
over its inputs for AND, the maximum for every other operation (OR, and by convention NOT, MOD,
MAJORITY). A missing wire counts `0`. -/
def Gate.lineDegree (g : Gate) (d : List ℕ) : ℕ :=
  if g.op = GateOp.and then (g.inputs.map fun i => d.getD i 0).sum
  else (g.inputs.map fun i => d.getD i 0).foldr max 0

/-- The line-degree of every wire of `C` on `n` inputs, with the inputs at positions in `marked`
of degree `1` and the others of degree `0`: the input degrees, then one degree per gate. -/
def Circuit.lineDegrees (C : Circuit) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  C.gates.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)

/-- The line-degree of `C` on `n` inputs over the marked inputs: the degree of its output wire
(`0` if there is none). -/
def Circuit.lineDeg (C : Circuit) (n : ℕ) (marked : Finset ℕ) : ℕ :=
  (C.lineDegrees n marked).getD C.output 0

/-- `C`, on `n` inputs, has line-degree at most `D` over the marked inputs. -/
def HasLineDegree (n : ℕ) (marked : Finset ℕ) (C : Circuit) (D : ℕ) : Prop :=
  C.lineDeg n marked ≤ D

/-- Every gate of `C` is an AND or an OR gate, of any fan-in. The setting of line-degree. -/
def IsMonotoneCircuit (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or

instance (n : ℕ) (marked : Finset ℕ) (C : Circuit) (D : ℕ) :
    Decidable (HasLineDegree n marked C D) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (C : Circuit) : Decidable (IsMonotoneCircuit C) := by
  unfold IsMonotoneCircuit; infer_instance

end PEqualNP.CircuitLowerBounds
