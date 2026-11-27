import PEqualNP.Library.L008
import PEqualNP.Library.L010

/-- P is inside NP and coNP: P is inside NP and closed under complement. -/
theorem PEqualNP.Library.L042 :
    PEqualNP.Library.P ⊆ PEqualNP.Library.NP ∩ PEqualNP.Library.coNP :=
  fun L hL => ⟨PEqualNP.Library.L010 hL,
    show Lᶜ ∈ PEqualNP.Library.NP from PEqualNP.Library.L010 (PEqualNP.Library.L008 L hL)⟩
