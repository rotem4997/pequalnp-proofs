import PEqualNP.Library.Machines.Clock
import PEqualNP.Library.Machines.ConstList

/-- Polynomial clocks: writing `p (length of the input)` ones takes polynomial time. Sums by
pairing and appending, powers and coefficients by unary multiplication. -/
theorem PEqualNP.Library.L055 : ∀ p : Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
  fun p => PEqualNP.Library.Machines.clock_polyTime
    (fun l => PEqualNP.Library.Machines.constList_polyTime l) p
