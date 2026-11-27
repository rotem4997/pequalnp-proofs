import Mathlib.Data.List.OfFn
import PEqualNP.Defs.MetaComplexity

/-!
# Sparse partial MCSP, for the meta-complexity program

Partial MCSP with the partial truth table given as a list of rows, not as a table of length
`2 ^ n`. A row is a point of `{0,1}^m` and the value the function must take there. Circuits and
their size are those of `PEqualNP.Defs.MetaComplexity` (`HasCircuitSize`). Nothing here speaks
of machines.
-/

namespace PEqualNP.MetaComplexity

/-- The binary code of a list of rows on `m` variables: each row `(x, b)` is written as the `m`
bits `x 0, ..., x (m - 1)` followed by the value `b`, so `m + 1` bits per row, rows in order. -/
def encodeRows (m : ℕ) (rows : List ((Fin m → Bool) × Bool)) : List Bool :=
  rows.flatMap fun r : (Fin m → Bool) × Bool => List.ofFn r.1 ++ [r.2]

/-- Sparse partial MCSP, the minimum circuit size problem for a partial function given as a list
of rows, as a language over `Bool`. An instance is a size bound `s` in unary (`s` times `true`),
one `false`, the number of variables `m` in unary (`m` times `true`), one `false`, then the code
`encodeRows m rows` of a list of rows. It is a member when some total function on `m` variables
that takes the value `b` at `x` for every row `(x, b)` has a circuit with at most `s` gates.
Rows may repeat; two rows with the same point and different values admit no such function, so
the instance is not a member. A string of any other shape is not a member. The numbers `s`, `m`
and the list of rows are determined by the string. -/
def SparsePartialMCSP : Language Bool :=
  {w | ∃ (m s : ℕ) (rows : List ((Fin m → Bool) × Bool)),
    w = List.replicate s true ++ false :: (List.replicate m true ++ false :: encodeRows m rows) ∧
      ∃ f : (Fin m → Bool) → Bool, (∀ r ∈ rows, f r.1 = r.2) ∧ HasCircuitSize m f s}

end PEqualNP.MetaComplexity
