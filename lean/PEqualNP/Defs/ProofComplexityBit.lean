import PEqualNP.Defs.ProofComplexityLin
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Definitions of the proof complexity program: the bit pigeonhole principle and linear rank

* `BPHP m l`: the bit (binary) pigeonhole formula with `m` pigeons and `2 ^ l` holes, where
  each pigeon names its hole by `l` bits.
* `linRank C`: the rank, over the field with two elements, of the set of linear forms that
  occur in the linear clause `C`. This is the rank of the linear system that is the negation
  of `C`, the width measure of Res(⊕) used by Efremenko, Garlik and Itsykson (STOC 2024).
-/

namespace PEqualNP.ProofComplexity

/-- The bit pigeonhole formula with `m` pigeons and `2 ^ l` holes. The variable `(i, b)` is
bit `b` of the hole of pigeon `i`, so an assignment sends each pigeon to a hole, a string of
`l` bits. The clauses: for each two different pigeons `i`, `i'` and each hole `α`, the clause
"not both `i` and `i'` go to `α`", that is, some bit of `i` or some bit of `i'` differs from
the matching bit of `α`. It is unsatisfiable exactly when `m > 2 ^ l`. -/
def BPHP (m l : ℕ) : Set (Clause (Fin m × Fin l)) :=
  {C | ∃ (i i' : Fin m) (α : Fin l → Bool), i ≠ i' ∧
    C = Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
        Finset.univ.image (fun b : Fin l => ((i', b), !α b))}

/-- The rank of a linear clause: the dimension, over the field with two elements, of the
span of the linear forms of its equations, each form `f` read as its indicator vector in
`V → ZMod 2`. The right-hand sides of the equations play no role. The empty clause has rank
`0`, and a clause that comes from an ordinary clause has rank equal to its number of
variables. -/
noncomputable def linRank {V : Type} [DecidableEq V] (C : LinClause V) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
    ((fun q : LinEq V => (fun v : V => if v ∈ q.1 then (1 : ZMod 2) else 0)) ''
      (C : Set (LinEq V))))

end PEqualNP.ProofComplexity
