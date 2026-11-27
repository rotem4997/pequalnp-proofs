import PEqualNP.Library.L004
import PEqualNP.Library.L073
import PEqualNP.CircuitLowerBounds.L001

/-- P is contained in P/poly. -/
theorem PEqualNP.MetaComplexity.L005 :
    PEqualNP.Library.P ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro L hL
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 L).1 hL
  obtain ⟨c, hc⟩ := PEqualNP.Library.L073 _ L hk
  refine ⟨Polynomial.C c * (Polynomial.X ^ k + Polynomial.C k + Polynomial.X + 1) ^ 3, ?_⟩
  refine PEqualNP.CircuitLowerBounds.L001 _ _ (fun n => le_of_eq ?_) hc
  simp
