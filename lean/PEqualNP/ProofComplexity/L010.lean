import PEqualNP.Library.L008
import PEqualNP.Library.L010

/-- L-pcx-010: if P = NP then NP is closed under complement. -/
theorem PEqualNP.ProofComplexity.L010 : PEqualNP.Library.P = PEqualNP.Library.NP → ∀ L : Language Bool, L ∈ PEqualNP.Library.NP → Lᶜ ∈ PEqualNP.Library.NP := by
  intro h L hL
  have h1 : L ∈ PEqualNP.Library.P := by simp only [h, hL]
  have h2 : Lᶜ ∈ PEqualNP.Library.P := PEqualNP.Library.L008 L h1
  exact PEqualNP.Library.L010 h2
