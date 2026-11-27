import PEqualNP.Defs

/-- P is the union of DTIME over polynomial bounds. -/
theorem PEqualNP.Library.L003 : ∀ L : Language Bool, L ∈ PEqualNP.Library.P ↔
    ∃ p : Polynomial ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => Polynomial.eval n p) := by
  intro L
  constructor
  · rintro ⟨f, hf, ⟨c⟩⟩
    exact ⟨c.time, f, hf, c.toTM2ComputableInTime, fun n => le_rfl⟩
  · rintro ⟨p, f, hf, c, hc⟩
    refine ⟨f, hf, ⟨⟨c.toTM2ComputableAux, p, fun a => ?_⟩⟩⟩
    exact ⟨(c.outputsFun a).toEvalsTo, (c.outputsFun a).steps_le_m.trans (hc _)⟩
