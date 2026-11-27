import PEqualNP.Defs.MetaComplexityLgp

/-!
# The monotone last-gate problem, for the meta-complexity program

The same problem as in `PEqualNP.Defs.MetaComplexityMinimal` and `PEqualNP.Defs.MetaComplexityLgp`
with NOT gates forbidden on both sides: circuits use AND and OR gates of fan-in at most two, and
minimality is among such circuits only. Instances are written as strings by the same `encodeLgp`.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The circuit uses only AND and OR gates, each reading at most two wires: `FanInTwo` without
NOT. An AND gate reading no wire is the constant `true` and an OR gate reading no wire is the
constant `false`; a gate reading one wire copies it. -/
def Monotone2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- `C` is a minimal monotone circuit on `n` inputs: it uses AND and OR gates of fan-in at most
two, and every circuit of that kind computing the same function on `n` inputs has at least as
many gates. Every gate counts, constant gates included; inputs are not counted. -/
def IsMinimalMonoCircuit (n : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size

/-- `C` is near-minimal among monotone circuits on `n` inputs: fan-in two AND, OR, and at most
one gate more than any such circuit computing the same function on `n` inputs. -/
def NearMinimalMono (n : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size + 1

/-- The YES side of the monotone last-gate problem on `n` inputs: the minimal monotone circuits. -/
def MonoLgpYes (n : ℕ) (C : Circuit) : Prop := IsMinimalMonoCircuit n C

/-- The NO side: near-minimal among monotone circuits and not minimal among them, that is,
exactly one gate above the monotone minimum. -/
def MonoLgpNo (n : ℕ) (C : Circuit) : Prop := NearMinimalMono n C ∧ ¬ IsMinimalMonoCircuit n C

/-- The monotone last-gate problem is in P, as a promise problem, on the same instance code as
`LgpInP`: some test computable in time polynomial in the length of `encodeLgp (n, C)` answers
`true` on every minimal monotone circuit and `false` on every monotone circuit exactly one gate
above the monotone minimum, on `n` inputs. Nothing is required on any other instance. -/
def MonoLgpInP : Prop :=
  ∃ f : ℕ × Circuit → Bool,
    PEqualNP.Library.ComputableInPolyTime encodeLgp Computability.encodeBool f ∧
      ∀ p : ℕ × Circuit, (MonoLgpYes p.1 p.2 → f p = true) ∧ (MonoLgpNo p.1 p.2 → f p = false)

end PEqualNP.MetaComplexity
