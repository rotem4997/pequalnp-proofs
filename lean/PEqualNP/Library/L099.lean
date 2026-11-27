import PEqualNP.Library.Machines.Reverse

/-- Reversal of binary strings is computable in polynomial time. -/
theorem PEqualNP.Library.L099 : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x.reverse) :=
  ⟨PEqualNP.Library.Machines.Rev.reverseComputable⟩
