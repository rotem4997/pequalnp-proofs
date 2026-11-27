import PEqualNP.Defs
import PEqualNP.Library.L045
import PEqualNP.Library.Helpers.PolyExp

/-- NP is contained in NEXP. -/
theorem PEqualNP.Library.L048 : PEqualNP.Library.NP ⊆ PEqualNP.Library.NEXP := by
  intro L hL
  obtain ⟨R, p, hR, hlen, hmem⟩ := PEqualNP.Library.L045 L hL
  obtain ⟨k, hk⟩ := PEqualNP.Library.Helpers.polynomial_le_two_pow_pow_add p
  refine ⟨R, k, hR, fun x => ?_⟩
  rw [hmem x]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (hlen x w hw).trans (hk _), hw⟩, fun ⟨w, _, hw⟩ => ⟨w, hw⟩⟩
