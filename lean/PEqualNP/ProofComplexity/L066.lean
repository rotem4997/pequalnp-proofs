import PEqualNP.ProofComplexity.Helpers.CrossRefutation

namespace PEqualNP.ProofComplexity

/-- L-pcx-066: the cross formula on four variables has a Res(2, ⊕) refutation of 11 lines. -/
theorem L066 : ∃ π : List (PEqualNP.ProofComplexity.LinKLine (Fin 4)), PEqualNP.ProofComplexity.IsLinKRefutation 2 ({{((0 : Fin 4), true), (1, true)}, {((2 : Fin 4), true), (3, true)}, {((0 : Fin 4), false), (2, false)}, {((0 : Fin 4), false), (3, false)}, {((1 : Fin 4), false), (2, false)}, {((1 : Fin 4), false), (3, false)}} : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) π ∧ π.length = 11 :=
  ⟨Helpers.Cross.crossPi, Helpers.Cross.cross_refutation⟩

end PEqualNP.ProofComplexity
