import PEqualNP.Defs.TopForm
import PEqualNP.Defs.ReadK
import PEqualNP.Defs.ReadTwo

/-!
# Cores, maximal cores and lift fixed points of a monotone circuit on a graph

The setting is the one of `PEqualNP.Defs.TopForm`: a circuit `C` of the root model on the inputs
`Fin n` (wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`), the inputs the vertices
of a graph `G`, and `F = graphFun G ∅` the edge function of `G`. The intended `G` is an incidence
graph (points, then lines; an edge is an incidence), and `C` an AND/OR circuit of fan-in two
(`IsAO2`), but nothing here assumes either: a statement wanting them says so.

These are new notions, not printed ones. Where the prose that proposed them is less precise, this
file follows the in-house scripts that compute them.

Words.
* An IMPLICANT GATE: a gate below `F` (`BelowF`) that is true at some input (not identically
  false). An IMPLICANT WIRE: the same for any wire, inputs included (`wval`).
* A CORE: an implicant gate `g` such that (i) NOT both operands of `g` are implicant GATES (an
  operand that is an input wire never counts as an implicant gate here, as in the printer), and
  (ii) `g` is READ MORE THAN ONCE at some incidence it accepts: there is an edge `uv` of `G` with
  `g` true at `1_uv` such that the circuit `C` with its output moved to `g` is NOT READ-1 on the
  list `[u, v]` (`ReadK.readsAtMost ... 1 = false`): every proof tree of `{u, v}` in the cone of
  `g` has `u` or `v` as a leaf at least twice. (Where `uv` is accepted and `g` is below `F`, every
  proof tree of `{u, v}` has both `u` and `v` as leaves, so this is exactly the printer's "read
  level of the cone on the accepted incidences is not 1".)
* The CONE of `g` (`coneSet`): `g` together with every gate strictly inside its cone (`InCone`).
* A MAXIMAL CORE: a core lying in no other core's cone (strictly inside no core's cone).
* THE IMPLICANT LIFT APPLIES AT `(h, b)`: `h`
  is a gate of the output cone, an OR gate, NOT below `F`, and its operand `b` is an implicant
  wire. The lift then rewires `h`'s readers to `h`'s other operand, deletes `h`, and ORs the
  operand `b` onto the output; size is unchanged.
* A LIFT FIXED POINT: a circuit at which the lift applies nowhere.

Names.
* `atGate n C j`: `C` with output wire `n + j`.
* `IsImpGate G C j`, `IsImpWire G C w`: implicant gate, implicant wire.
* `IsImpOperand G C w`: `w` is the wire of an implicant gate (`n ≤ w` and gate `w - n`).
* `ReadTwiceAt C j u v`: `atGate n C j` is not READ-1 on `[u, v]`.
* `IsCore G C j`, `cores G C`; `coneSet n C j`; `IsMaximalCore G C j`, `maximalCores G C`.
* `InOutputCone n C j`: gate `j` is the output gate or strictly inside its cone.
* `LiftAt G C h b`, `LiftApplies G C`, `IsLiftFixedPoint G C`.
* The incidences a core accepts are `TopForm.gammaE G C j` (no new name).

Readings chosen (where the prose admitted more than one).
* "Read more than once" is the root's READ-k at `k = 1` (`readsAtMost`, the joint proof-tree
  reading), at the pair `[u, v]` of the edge, in the circuit with output `g` (the vectors of the
  wire `n + g` depend only on the cone of `g`).
* "Not both inputs below `F`" is the printer's test: an operand counts only if it is a GATE that
  is below `F` and not identically false. In the incidence setting no input wire is below `F`
  anyway (a single vertex is no edge).
* The lift's condition is the script's, which is stronger than the one-sentence form ("a wire
  `t <= f` read by an OR gate"): the script also asks the OR gate to be NOT below `F`, `t` to be not
  identically false, and looks only at gates the output reads (the printer drops dead gates). `t`
  may be an input wire, as in the code.
* Every "below `F`" quantifies over all `2^n` inputs (the printer uses the decisive inputs of a
  monotone function, which give the same answer for monotone circuits).

Caveats.
* `opnd` (of `TopForm`) reads operand positions `0` and `1` with default wire `0`: only under
  `IsAO2` does it name the two real operands.
* `InCone` is the strict cone, so a core is never in its own cone; `IsMaximalCore` ranges over
  gates `i < C.gates.length` (every core is one).
* `readsAtMost` wants a list without repetitions: an edge has `u ≠ v`.
* A gate index at or past `C.gates.length` is never a core and never a lift site.
-/

namespace PEqualNP.Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo

attribute [local instance] gateOpDecEq

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- `C` with its output moved to the wire `n + j` of gate `j`. -/
def atGate (n : ℕ) (C : Circuit) (j : ℕ) : Circuit := { C with output := n + j }

/-- Gate `j` is an IMPLICANT GATE: below `F` and true at some input. -/
def IsImpGate (j : ℕ) : Prop := BelowF G C j ∧ ∃ x : Fin n → Bool, gateVal n C j x = true

instance (j : ℕ) : Decidable (IsImpGate G C j) := by unfold IsImpGate; infer_instance

/-- Wire `w` (input or gate) is an IMPLICANT WIRE: wherever it is true `F` is true, and it is true
at some input. -/
def IsImpWire (w : ℕ) : Prop :=
  (∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) ∧ ∃ x : Fin n → Bool, wval C x w = true

instance (w : ℕ) : Decidable (IsImpWire G C w) := by unfold IsImpWire; infer_instance

/-- Wire `w` is the wire of an implicant GATE (not an input wire). -/
def IsImpOperand (w : ℕ) : Prop := n ≤ w ∧ IsImpGate G C (w - n)

instance (w : ℕ) : Decidable (IsImpOperand G C w) := by unfold IsImpOperand; infer_instance

/-- Gate `j` is READ MORE THAN ONCE at the pair `u v`: the circuit with output `j` is not READ-1
on the list `[u, v]` (every proof tree has `u` or `v` as a leaf twice or more). -/
def ReadTwiceAt (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  readsAtMost (atGate n C j) n [u.val, v.val] 1 = false

instance (j : ℕ) (u v : Fin n) : Decidable (ReadTwiceAt n C j u v) := by
  unfold ReadTwiceAt; infer_instance

/-- Gate `j` is a CORE: an implicant gate, not both of whose operands are implicant gates, read
more than once at some edge of `G` it accepts. -/
def IsCore (j : ℕ) : Prop :=
  j < C.gates.length ∧ IsImpGate G C j ∧
    ¬ (IsImpOperand G C (opnd C j 0) ∧ IsImpOperand G C (opnd C j 1)) ∧
    ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧ ReadTwiceAt n C j u v

instance (j : ℕ) : Decidable (IsCore G C j) := by unfold IsCore; infer_instance

/-- The cores of `C`. -/
def cores : Finset ℕ := gatesWhere C (IsCore G C)

/-- The CONE of gate `j`: `j` itself and every gate strictly inside its cone. -/
def coneSet (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ :=
  insert j ((Finset.range C.gates.length).filter fun i => InCone n C i j)

/-- Gate `j` is a MAXIMAL CORE: a core strictly inside the cone of no core. -/
def IsMaximalCore (j : ℕ) : Prop :=
  IsCore G C j ∧ ∀ i < C.gates.length, IsCore G C i → ¬ InCone n C j i

instance (j : ℕ) : Decidable (IsMaximalCore G C j) := by unfold IsMaximalCore; infer_instance

/-- The maximal cores of `C`. -/
def maximalCores : Finset ℕ := gatesWhere C (IsMaximalCore G C)

/-- Gate `j` lies in the output cone: it is the output gate, or strictly inside its cone. -/
def InOutputCone (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (C.output = n + j ∨ (n ≤ C.output ∧ InCone n C j (C.output - n)))

instance (n : ℕ) (j : ℕ) : Decidable (InOutputCone n C j) := by unfold InOutputCone; infer_instance

/-- The implicant lift APPLIES at gate `h`, operand `b`: `h` is an OR gate of the output cone, not
below `F`, whose operand `b` is an implicant wire. -/
def LiftAt (h : ℕ) (b : Fin 2) : Prop :=
  InOutputCone n C h ∧ (gateAt C h).op = GateOp.or ∧ ¬ BelowF G C h ∧ IsImpWire G C (opnd C h b)

instance (h : ℕ) (b : Fin 2) : Decidable (LiftAt G C h b) := by unfold LiftAt; infer_instance

/-- The implicant lift applies somewhere in `C`. -/
def LiftApplies : Prop := ∃ h < C.gates.length, ∃ b : Fin 2, LiftAt G C h b

instance : Decidable (LiftApplies G C) := by unfold LiftApplies; infer_instance

/-- `C` is a LIFT FIXED POINT: the implicant lift applies nowhere. -/
def IsLiftFixedPoint : Prop := ¬ LiftApplies G C

instance : Decidable (IsLiftFixedPoint G C) := by unfold IsLiftFixedPoint; infer_instance

end PEqualNP.Core
