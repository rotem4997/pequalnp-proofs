import Mathlib.Order.Nat
import Mathlib.Data.Int.Basic
import PEqualNP.Defs.MetaComplexity

/-!
# The pendant bit of a Boolean function at an input

For a Boolean function `f` on `n` inputs and an input `v`, the PENDANT FUNCTION `pendF n f v` is
the function on `n + 1` inputs `f(x) OR (x_v AND y)`, where `y` is the fresh LAST input
(`Fin.last n`) and the old inputs are read through `Fin.castSucc`. The PENDANT BIT is the integer

  `pendantBit n f v = size(f) + 2 - size(pendF n f v)`,

where `size` is the least number of gates of a circuit computing the function, in the model of
`PEqualNP.MetaComplexity.HasCircuitSize`: AND, OR and NOT gates reading at most two wires, every
gate counted (NOT gates and constant gates included), inputs free.

* `minCircuitSize n f`: the least `s` with `HasCircuitSize n f s`.
* `pendF n f v`: the pendant function `f(x) OR (x_v AND y)` on `n + 1` inputs.
* `pendantBit n f v`: the pendant bit, an integer.

Caveats a statement must respect.
* The size model is `HasCircuitSize`, NOT the strict model `PEqualNP.MinimumComplex.cc`. They
  price constants differently: here the constant `false` has size `0` (an output wire that does
  not exist reads `false`) and the constant `true` has size `1` (an AND gate reading no wire);
  in the strict model both cost `2` gates on `n ≥ 1` inputs, and `cc` is `0` at `n = 0`. Here
  gates may also read one wire twice, read one wire only, or read no wire. On paper the two
  sizes agree on non-constant functions of `n ≥ 1` inputs (a least circuit needs no constant
  and no repeated or copying gate); that agreement is NOT stated here. This model is chosen
  because it reproduces the concept's non-examples (constant `false` has bit `1`; it would be
  `3` in the strict model).
* `minCircuitSize` is `sInf` of a set of naturals. The set is never empty (every function has a
  circuit: `PEqualNP.CircuitLowerBounds.Helpers.hasCircuitSize_all`), so the infimum is
  attained; the definition itself does not rely on that.
* The bit is an integer, subtraction in `ℤ`. It is NOT always `0` or `1`: constant `true` and
  `f = x_v` give `2`, constant `false` gives `1`. "The bit is `0` or `1`" is a theorem under
  hypotheses (`f` non-constant and `f x = false` for some `x` with `x_v = true`), never part of
  the definition.
-/

namespace PEqualNP.PendantBit

open PEqualNP.MetaComplexity

/-- The least number of gates of a circuit of AND, OR and NOT gates of fan-in at most two
computing `f` on `n` inputs (every gate counted, inputs free), as `sInf` over
`HasCircuitSize`. -/
noncomputable def minCircuitSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {s | HasCircuitSize n f s}

/-- The pendant function of `f` at the input `v`: on `n + 1` inputs, `f` of the first `n`
inputs, OR the AND of input `v` with the fresh last input `Fin.last n`. -/
def pendF (n : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n) : (Fin (n + 1) → Bool) → Bool :=
  fun x => f (fun i => x i.castSucc) || (x v.castSucc && x (Fin.last n))

/-- The pendant bit of `f` at `v`: `size(f) + 2 - size(pendF n f v)`, in the integers. -/
noncomputable def pendantBit (n : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n) : ℤ :=
  (minCircuitSize n f : ℤ) + 2 - (minCircuitSize (n + 1) (pendF n f v) : ℤ)

end PEqualNP.PendantBit
