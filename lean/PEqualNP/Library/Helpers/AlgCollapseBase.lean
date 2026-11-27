import PEqualNP.Defs
import PEqualNP.Library.Helpers.QueryEvasion

/-!
# The multilinear extension of an oracle, for the algebrizing collapse

`mlext A` assigns to every finite field `GaloisField p k` and arity `m` the multilinear
polynomial that equals the oracle `A` on the Boolean cube (a point `z` is the string
`List.ofFn z`). Used for L-lib-077 (Aaronson and Wigderson 2009: NP^E inside P^A).
-/

namespace PEqualNP.Library.Helpers.AlgCollapseBase

open Classical in
/-- The multilinear extension of `A` over every finite field. -/
noncomputable def mlext (A : Language Bool) : PEqualNP.Library.AlgExtension :=
  fun p _ k m =>
    PEqualNP.Library.Helpers.QueryEvasion.interp (GaloisField p k) m
      (fun z => if List.ofFn z ∈ A then 1 else 0)

end PEqualNP.Library.Helpers.AlgCollapseBase
