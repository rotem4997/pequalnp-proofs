import PEqualNP.Library.L045
import PEqualNP.Library.Machines.ReduceNP

/-- NP is closed downward under polynomial-time many-one reductions: compose the verifier with the reduction on the first component. -/
theorem PEqualNP.Library.L017 : ∀ L₁ L₂ : Language Bool, PEqualNP.Library.PolyTimeReducible L₁ L₂ → L₂ ∈ PEqualNP.Library.NP → L₁ ∈ PEqualNP.Library.NP := by
  rintro L₁ L₂ ⟨f, hf, hred⟩ h₂
  obtain ⟨R, p, ⟨fR, hfR, hcR⟩, hshort, hL⟩ := PEqualNP.Library.L045 L₂ h₂
  obtain ⟨q, hq⟩ := PEqualNP.Library.Machines.output_length_poly f hf
  refine ⟨{xw | (f xw.1, xw.2) ∈ R}, p.comp q,
    ⟨fun xw => fR (f xw.1, xw.2), fun xw => hfR (f xw.1, xw.2),
      PEqualNP.Library.Machines.cpt_comp (PEqualNP.Library.Machines.cpt_first hf) hcR⟩,
    fun x => ?_⟩
  refine (hred x).trans ((hL (f x)).trans ⟨?_, ?_⟩)
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rw [Polynomial.eval_comp]
    exact (hshort (f x) w hw).trans (PEqualNP.Library.Machines.eval_mono p (hq x))
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩
