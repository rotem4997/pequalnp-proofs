import PEqualNP.Library.Ladner.Machine

/-- Ladner (1975): if P differs from NP, some language in NP is outside P and is not NP-hard.
The language pads an NP-complete verifier language by a power whose exponent is a slowly
growing stage function, obtained by delayed diagonalization against the clocked deciders. -/
theorem PEqualNP.Library.L019 : PEqualNP.Library.P ≠ PEqualNP.Library.NP →
    ∃ L ∈ PEqualNP.Library.NP, L ∉ PEqualNP.Library.P ∧ ¬ PEqualNP.Library.NPHard L := by
  intro hne
  obtain ⟨cA, q, hA⟩ := PEqualNP.Library.Ladner.verifier
  obtain ⟨h1, h2, h3⟩ := PEqualNP.Library.Ladner.core cA q hA
    (PEqualNP.Library.Ladner.stage_succ cA q) (PEqualNP.Library.Ladner.sound cA q)
    (PEqualNP.Library.Ladner.live cA q) PEqualNP.Library.Ladner.cover
    PEqualNP.Library.Ladner.dec_in_P (PEqualNP.Library.Ladner.pad_in_P cA q)
    (PEqualNP.Library.Ladner.brute cA q) hne
  exact ⟨_, h1, h2, h3⟩
