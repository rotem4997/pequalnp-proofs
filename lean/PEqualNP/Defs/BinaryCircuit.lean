import PEqualNP.Defs.MetaComplexity

/-!
# Circuits over all two-input gates, for the meta-complexity program

A binary circuit is a list of gates; each gate is a Boolean function of two arguments together
with the indices of the two wires it reads. Evaluation follows the root `Circuit` exactly:
wires `0` to `n - 1` are the inputs, gate number `j` (from `0`) produces wire `n + j`, a wire
that does not exist (yet) reads `false`, and the value of the circuit is the value of its
output wire (`false` if there is none). Size is the number of gates; inputs are not counted.

Every gate counts, also a gate that negates or copies one wire or ignores both (a constant).
So the constant `false` has size zero (an output wire that does not exist) and the constant
`true` has size one, as on the root.
-/


namespace PEqualNP.MetaComplexity

/-- A gate over the full binary basis: any function of two Boolean arguments, and the indices
of the two wires it reads. -/
structure BinaryGate where
  /-- The operation: any of the sixteen Boolean functions of two arguments. -/
  op : Bool → Bool → Bool
  /-- The index of the wire read as the left argument. -/
  left : ℕ
  /-- The index of the wire read as the right argument. -/
  right : ℕ

/-- A circuit over the full binary basis: its gates in evaluation order and the index of its
output wire. -/
structure BinaryCircuit where
  /-- The gates. Gate number `j` (from `0`) produces wire `(input length) + j`. -/
  gates : List BinaryGate
  /-- The index of the output wire. -/
  output : ℕ

/-- The values of all wires on input `x`: the bits of `x`, then one value per gate. A wire
that does not exist when a gate is evaluated reads `false`. -/
def BinaryCircuit.wires (C : BinaryCircuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

/-- The value of the circuit on input `x`: the value of its output wire, `false` if there is
none. -/
def BinaryCircuit.eval (C : BinaryCircuit) (x : List Bool) : Bool :=
  (C.wires x).getD C.output false

/-- The size: the number of gates. -/
def BinaryCircuit.size (C : BinaryCircuit) : ℕ :=
  C.gates.length

/-- The function `f` on `n` inputs has a circuit over the full binary basis with at most `s`
gates. The parallel of `HasCircuitSize`, with every two-input gate allowed. -/
def HasBinarySize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : BinaryCircuit, C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

end PEqualNP.MetaComplexity
