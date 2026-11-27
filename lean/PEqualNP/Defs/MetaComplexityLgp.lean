import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.Base

/-!
# The last-gate problem as a promise problem in P, for the meta-complexity program

An instance of the last-gate problem is a pair `(n, C)`: a number of inputs and a circuit
(`PEqualNP.Defs.MetaComplexityMinimal`). This module writes an instance as a binary string
(`encodeLgp`: `n` in unary, then the gates, then the output index) and states that the problem
is in P as a promise problem (`LgpInP`): some polynomial-time test separates the two sides
`LgpYes` and `LgpNo`; on every other instance its answer is free. The number of inputs is in
unary on purpose: a large `n` with a small circuit is not a short instance.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The binary code of a gate operation: AND is `[false, false]`, OR is `[false, true]`, NOT is
`[true, false]`, MOD `m` is `[true, true, false]` followed by `encodeNat m`, and MAJORITY is
`[true, true, true]`. -/
def encodeGateOp : GateOp → List Bool
  | GateOp.and => [false, false]
  | GateOp.or => [false, true]
  | GateOp.not => [true, false]
  | GateOp.mod m => [true, true, false] ++ encodeNat m
  | GateOp.maj => [true, true, true]

/-- The binary code of a gate: the code of its operation, then the list of the wire indices it
reads, each in binary (`encodeList encodeNat`). -/
def encodeGate (g : Gate) : List Bool :=
  encodeGateOp g.op ++ encodeList encodeNat g.inputs

/-- The binary code of an instance `(n, C)` of the last-gate problem: `n` in unary (`n` times
`true`, then `false`), then the list of the gates of `C`, then the index of its output wire in
binary. -/
def encodeLgp (p : ℕ × Circuit) : List Bool :=
  List.replicate p.1 true ++ false :: (encodeList encodeGate p.2.gates ++ encodeNat p.2.output)

/-- The last-gate problem is in P, as a promise problem: some test computable in time
polynomial in the length of `encodeLgp (n, C)` answers `true` on every minimal circuit and
`false` on every circuit exactly one gate above the minimum, on `n` inputs. Nothing is required
on any other instance. -/
def LgpInP : Prop :=
  ∃ f : ℕ × Circuit → Bool,
    PEqualNP.Library.ComputableInPolyTime encodeLgp Computability.encodeBool f ∧
      ∀ p : ℕ × Circuit, (LgpYes p.1 p.2 → f p = true) ∧ (LgpNo p.1 p.2 → f p = false)

end PEqualNP.MetaComplexity
