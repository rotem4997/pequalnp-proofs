import PEqualNP.Library.Machines.SquareClock

/-- Quadratic clock: duplicate the input, then multiply the two lengths in unary. -/
theorem PEqualNP.Library.L101 : ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate (x.length ^ 2) true) (fun n : ℕ => c * n ^ 2 + c) :=
  ⟨27, PEqualNP.Library.Machines.square_time⟩
