import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# The rung: from the smooth restriction to the superquadratic bound

Proof of the step statement `PEqualNP.Gct.Rung.AssemblyBound`: the statements of L-gct-057,
L-gct-024 and L-gct-023 together imply the statement of L-gct-056. A helper module; nothing
here is a recorded lemma.
-/

namespace PEqualNP.Gct.Rung

theorem assemblyBound : AssemblyBound := by
  intro h057 h024 h023 R m0
  obtain ⟨m, r, d, G, g, hm0, hm1, hr, hd, hbig, hhom, hsm, hdeg, hG⟩ := h057 (11 * R) m0
  refine ⟨m, hm0, hm1, ?_⟩
  intro n hn
  have hGn : PEqualNP.Gct.HasBorderDetExpression G n := by
    rw [← hG]
    exact h023 (Fin m × Fin m) (Fin d) (PEqualNP.Gct.permPoly ℂ m) g n hdeg hn
  have h := h024 d r n G hd hr hhom hsm hGn
  have : 11 * (R * m ^ 2) ≤ 11 * n := by
    calc 11 * (R * m ^ 2) = 11 * R * m ^ 2 := by ring
      _ ≤ (r - 1) * (d - 1) := hbig
      _ ≤ 11 * n := h
  omega

end PEqualNP.Gct.Rung
