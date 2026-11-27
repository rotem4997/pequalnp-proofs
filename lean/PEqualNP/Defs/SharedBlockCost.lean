import PEqualNP.Defs.BlindGate
import PEqualNP.Defs.BicliqueBlockCost

/-!
# OR cost of a set family and the shared block cost of a graph

A new notion, defined here.

OR COST. Fix `n` inputs `Fin n`. An OR CIRCUIT is a root circuit
(`PEqualNP.CircuitLowerBounds.Circuit`) on `n` inputs in which every gate is an OR gate reading
EXACTLY two wires, each an earlier wire (an input or an earlier gate). No AND, no NOT, no constant.
A wire `w` of `C` COMPUTES the OR of a vertex set `s` when it exists (`w < n + C.gates.length`)
and, on every input `x : Fin n → Bool`, it is true exactly when some `i ∈ s` has `x i = true`.
The OR COST of a finite family of sets is the fewest gates of one OR circuit that has, for every
set of the family, a wire computing its OR. One wire may serve several sets and one gate may be
read by many gates (sharing is the point). A singleton `{i}` is served by the input wire `i`, at
cost `0`.

SHARED BLOCK COST. For a simple graph `G` on `Fin n` and a block cover `F` of its edges (the
root's `PEqualNP.BicliqueBlockCost.IsBlockCover`), the SIDES of `F` are all the sets `A` and `B`
of its blocks `(A, B)`, as one `Finset` (a set that is a side of two blocks is counted once). The
shared cost of `F` is

  (OR cost of the sides of `F`) + `F.card` (one AND per block) + (`F.card - 1`) (the top OR tree),

and the SHARED BLOCK COST `sbc G` is its least value over block covers. It is the size of an
AND/OR circuit of fan-in two for the edge function of `G` (side ORs, then one AND per block, then
an OR tree), so it is an upper bound on the least AND/OR size; it is at most `bc G` (no sharing:
a side `s` costs `|s| - 1` ORs by a chain: `Scratch.sbc_le_bc`, conjecture until checked), with
equality when no two sides share an OR (on paper, not proved).

Names:
* `isOrOp`: the operation is OR.
* `IsOrCircuit n C`: every gate `j` of `C` is an OR gate with exactly two inputs, each `< n + j`.
* `ComputesOr n C w s`: wire `w` exists and computes the OR of the inputs in `s`.
* `IsOrCircuitFor n C fam`: `C` is an OR circuit and every `s ∈ fam` has a wire computing its OR.
* `HasOrCost n fam c`: some OR circuit with at most `c` gates is one for `fam`.
* `orCost n fam`: the least such `c` (an `sInf` on `ℕ`).
* `sides F`: the sides of a family of blocks, `F.image Prod.fst ∪ F.image Prod.snd`.
* `HasSharedBlockCost G c`: some block cover `F` of `G` and some `k` with `HasOrCost n (sides F) k`
  and `k + F.card + (F.card - 1) ≤ c`.
* `sbc G`: the least `c` with `HasSharedBlockCost G c` (an `sInf` on `ℕ`).

Caveats a statement must respect.
* WHY `ℕ` AND `sInf`. For a family of NONEMPTY sets the value is always attained: one chain of
  `|s| - 1` ORs per set `s` is an OR circuit for the family, so the set of costs is nonempty
  (proved, conjecture until checked: `Scratch.hasOrCost_flat` in
  `Library/Helpers/ScratchSharedBlockCost.lean`). A family that CONTAINS THE EMPTY SET has no OR
  circuit: no wire computes the constant `false` (inputs are not constant, OR gates of two wires
  are true where a read wire is, there are no constants, and a missing wire is not allowed as a
  serving wire). So `HasOrCost n fam c` is false for every `c` and `orCost n fam` reads `0`
  (`sInf ∅ = 0` on `ℕ`): state rows with `HasOrCost`, or assume every set nonempty, never read
  `orCost` of a family with `∅`. With `n = 0` the only set is `∅`, so only the empty family has
  a cost (`0`).
* `sbc` never meets the empty set: block sides are nonempty by `IsBlock`. Every graph has a block
  cover (one block `({u}, {v})` per edge, oriented once), so `sbc G` is attained
  (`Scratch.exists_hasBlockCost` with `Scratch.hasSharedBlockCost_of_hasBlockCost`). The empty graph has the empty cover: `sbc = 0`, the family term `0 - 1` being truncated
  as in `familyCost`.
* REUSE. The family is a `Finset`, so a set listed twice is one set. Distinct sets need distinct
  wires (they differ on some single-input vector), and a set of size at least two needs a gate
  wire, never an input.
* INPUTS COST 0. An input wire computes its singleton; the inputs are not counted in `c`.
* The OR gate reads EXACTLY two wires, possibly the same wire twice (`OR(a, a) = a`, a wasted
  gate): allowed, it only adds cost. A gate reading its own or a later wire is NOT allowed.
* The notion is SEMANTIC on all `2^n` inputs. `decide` on `ComputesOr` enumerates them: fine for
  small `n` only. `HasOrCost` is not decidable (it quantifies over circuits): an upper bound is
  proved by a witness circuit, a lower bound needs an argument.
* The field `C.output` plays no part.
* `sbc G` is an UPPER bound on the least AND/OR size of the edge function (a cover and its OR
  circuit give a circuit). That it EQUALS the least size on the 52 small bipartite classes with a
  4-cycle is computed by script, not checked; do not read it as a predicted size elsewhere.
-/

namespace PEqualNP.SharedBlockCost

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost

/-- The operation is OR. -/
def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

/-- `C` is an OR circuit on `n` inputs: every gate `j` (wire `n + j`) is an OR gate reading exactly
two wires, each an earlier wire (`< n + j`). -/
def IsOrCircuit (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (h : j < C.gates.length), isOrOp (C.gates[j]'h).op = true ∧
    (C.gates[j]'h).inputs.length = 2 ∧ ∀ i ∈ (C.gates[j]'h).inputs, i < n + j

instance (n : ℕ) (C : Circuit) : Decidable (IsOrCircuit n C) := by
  unfold IsOrCircuit; infer_instance

/-- Wire `w` of `C` (on `n` inputs) exists and computes the OR of the inputs in `s`. -/
def ComputesOr (n : ℕ) (C : Circuit) (w : ℕ) (s : Finset (Fin n)) : Prop :=
  w < n + C.gates.length ∧
    ∀ x : Fin n → Bool, (PEqualNP.BlindGate.wireValue C n x w = true ↔ ∃ i ∈ s, x i = true)

instance (n : ℕ) (C : Circuit) (w : ℕ) (s : Finset (Fin n)) : Decidable (ComputesOr n C w s) := by
  unfold ComputesOr; infer_instance

/-- `C` is an OR circuit with, for every set of `fam`, a wire computing its OR. -/
def IsOrCircuitFor (n : ℕ) (C : Circuit) (fam : Finset (Finset (Fin n))) : Prop :=
  IsOrCircuit n C ∧ ∀ s ∈ fam, ∃ w < n + C.gates.length, ComputesOr n C w s

instance (n : ℕ) (C : Circuit) (fam : Finset (Finset (Fin n))) :
    Decidable (IsOrCircuitFor n C fam) := by
  unfold IsOrCircuitFor; infer_instance

/-- Some OR circuit with at most `c` gates has a wire for every set of `fam`. -/
def HasOrCost (n : ℕ) (fam : Finset (Finset (Fin n))) (c : ℕ) : Prop :=
  ∃ C : Circuit, IsOrCircuitFor n C fam ∧ C.gates.length ≤ c

/-- The OR cost of `fam`: the least `c` with `HasOrCost n fam c` (`0` if there is none, which
happens exactly when some set of `fam` is empty). -/
noncomputable def orCost (n : ℕ) (fam : Finset (Finset (Fin n))) : ℕ :=
  sInf {c : ℕ | HasOrCost n fam c}

/-- The sides of a family of blocks: every `A` and every `B` of its blocks `(A, B)`. -/
def sides {n : ℕ} (F : Finset (Block n)) : Finset (Finset (Fin n)) :=
  F.image Prod.fst ∪ F.image Prod.snd

/-- Some block cover `F` of `G`, with an OR circuit of `k` gates for its sides, has
`k + F.card + (F.card - 1) ≤ c`. -/
def HasSharedBlockCost {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∃ F : Finset (Block n), IsBlockCover G F ∧
    ∃ k, HasOrCost n (sides F) k ∧ k + F.card + (F.card - 1) ≤ c

/-- The shared block cost: the least `c` with `HasSharedBlockCost G c`. -/
noncomputable def sbc {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | HasSharedBlockCost G c}

end PEqualNP.SharedBlockCost
