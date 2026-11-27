import PEqualNP.Library.Machines.ConstList

/-!
# L-lib-066: every constant function to a fixed binary string is polynomial-time computable

The machine `Machines.constList u` erases its input, then pushes the symbols of `u` (last symbol
first, so that the output stack reads `u`) and halts, in `n + 1` steps on an input of length `n`.
-/

namespace PEqualNP.Library

theorem L066 :
    ∀ u : List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => u) :=
  fun u => Machines.constList_polyTime u

end PEqualNP.Library
