import PEqualNP.Defs.MetaComplexity

/-!
# Minimal circuits and the last-gate problem, for the meta-complexity program

Circuits, their size and `FanInTwo` are those of `PEqualNP.Defs.CircuitLowerBounds` and
`PEqualNP.Defs.MetaComplexity`. This module adds: the function a circuit computes on `n`
inputs, minimal circuits, near-minimal circuits (at most one gate above the minimum), and the
two sides of the last-gate problem: given a near-minimal circuit, is it minimal. Nothing here
speaks of machines or of an encoding of circuits as strings.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The function the circuit `C` computes on `n` inputs: its value on the input string
`List.ofFn x`. Wires `0` to `n - 1` are the inputs; a wire that does not exist reads `false`. -/
def circuitFun (n : ℕ) (C : Circuit) : (Fin n → Bool) → Bool :=
  fun x => C.eval (List.ofFn x)

/-- `C` is a minimal circuit on `n` inputs: it uses AND, OR and NOT gates of fan-in at most two,
and every circuit of that kind computing the same function on `n` inputs has at least as many
gates. Size counts every gate, NOT gates and constant gates included; inputs are not counted. -/
def IsMinimalCircuit (n : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧ ∀ D : Circuit, FanInTwo D → circuitFun n D = circuitFun n C → C.size ≤ D.size

/-- `C` is near-minimal on `n` inputs: fan-in two AND, OR, NOT, and at most one gate more than
any such circuit computing the same function on `n` inputs. The promise of the last-gate
problem. -/
def NearMinimal (n : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧ ∀ D : Circuit, FanInTwo D → circuitFun n D = circuitFun n C → C.size ≤ D.size + 1

/-- The YES side of the last-gate problem on `n` inputs: the minimal circuits. -/
def LgpYes (n : ℕ) (C : Circuit) : Prop := IsMinimalCircuit n C

/-- The NO side: near-minimal and not minimal, that is, exactly one gate above the minimum. -/
def LgpNo (n : ℕ) (C : Circuit) : Prop := NearMinimal n C ∧ ¬ IsMinimalCircuit n C

end PEqualNP.MetaComplexity
