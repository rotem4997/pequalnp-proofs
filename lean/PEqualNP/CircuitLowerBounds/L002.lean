import PEqualNP.Defs

/-- AC0 is contained in ACC0: an AC0 circuit is an AC0[m] circuit that uses no MOD gate. -/
theorem PEqualNP.CircuitLowerBounds.L002 :
    PEqualNP.CircuitLowerBounds.AC0 ⊆ PEqualNP.CircuitLowerBounds.ACC0 := by
  rintro L ⟨p, d, hL⟩
  refine ⟨0, p, d, fun n => ?_⟩
  obtain ⟨C, hg, hs, hdep, hd⟩ := hL n
  refine ⟨C, fun g hgm => ⟨?_, (hg g hgm).2⟩, hs, hdep, hd⟩
  rcases (hg g hgm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
