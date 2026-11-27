import PEqualNP.MetaComplexity.Helpers.MachinePair

/-- Pairing of two polynomial-time outputs: the pair is written as the concatenation of
the two codes. -/
theorem PEqualNP.MetaComplexity.L504 : ∀ (α β γ : Type) (ea : α → List Bool) (eb : β → List Bool) (ec : γ → List Bool) (f : α → β) (g : α → γ), PEqualNP.Library.ComputableInPolyTime ea eb f → PEqualNP.Library.ComputableInPolyTime ea ec g → PEqualNP.Library.ComputableInPolyTime ea (fun p : β × γ => eb p.1 ++ ec p.2) (fun a : α => (f a, g a)) :=
  PEqualNP.MetaComplexity.Helpers.MachinePair.cpt_pairApp
