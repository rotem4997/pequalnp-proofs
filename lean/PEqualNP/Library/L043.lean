import PEqualNP.Library.L008

/-- If P = NP then NP = coNP, because P is closed under complement. -/
theorem PEqualNP.Library.L043 :
    PEqualNP.Library.P = PEqualNP.Library.NP → PEqualNP.Library.NP = PEqualNP.Library.coNP := by
  intro h
  ext L
  constructor
  · intro hL
    show Lᶜ ∈ PEqualNP.Library.NP
    rw [← h] at hL ⊢
    exact PEqualNP.Library.L008 L hL
  · intro hL
    have hL' : Lᶜ ∈ PEqualNP.Library.NP := hL
    rw [← h] at hL' ⊢
    have := PEqualNP.Library.L008 Lᶜ hL'
    rwa [compl_compl] at this
