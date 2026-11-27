import PEqualNP.Library.Machines.Const

/-- The full language is in P: the machine that erases its input and answers `true`. -/
theorem PEqualNP.Library.L039 : (Set.univ : Set (List Bool)) ∈ PEqualNP.Library.P :=
  ⟨fun _ => true, fun _ => by simp, ⟨PEqualNP.Library.Machines.constBoolComputable true⟩⟩
