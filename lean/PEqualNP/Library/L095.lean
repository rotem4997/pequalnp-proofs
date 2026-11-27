import PEqualNP.Library.Helpers.PadTest

/-- A polynomial-time test on the exponentially padded pair `(1 ^ (2 ^ (|u z| ^ k) + k) 0 (u z), v z)`
runs within `2 ^ (n ^ j) + j` steps for some `j`. -/
theorem PEqualNP.Library.L095 : ∀ (k : ℕ) (u v : List Bool → List Bool) (h : List Bool × List Bool → Bool), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v → PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair Computability.encodeBool h → ∃ j : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) Computability.encodeBool (fun z : List Bool => h (List.replicate (2 ^ ((u z).length ^ k) + k) true ++ false :: u z, v z)) (fun n : ℕ => 2 ^ (n ^ j) + j) :=
  PEqualNP.Library.Helpers.padTest
