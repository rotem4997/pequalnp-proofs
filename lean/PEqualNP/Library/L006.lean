import PEqualNP.Library.Machines.Const

/-- The empty language is in P: the machine that erases its input and answers `false`. -/
theorem PEqualNP.Library.L006 : (∅ : Set (List Bool)) ∈ PEqualNP.Library.P :=
  ⟨fun _ => false, fun _ => by simp, ⟨PEqualNP.Library.Machines.constBoolComputable false⟩⟩
