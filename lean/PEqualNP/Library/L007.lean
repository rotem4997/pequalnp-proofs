import PEqualNP.Library.Machines.ComposeRun

/-- Polynomial-time computable functions compose: run the first machine, move its output to the
input stack of the second, run the second. -/
theorem PEqualNP.Library.L007 : ∀ (α β γ αΓ βΓ γΓ : Type) (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ),
    PEqualNP.Library.ComputableInPolyTime ea eb f →
    PEqualNP.Library.ComputableInPolyTime eb ec g →
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a : α => g (f a)) :=
  fun _ _ _ _ _ _ ea eb ec f g ⟨c1⟩ ⟨c2⟩ =>
    PEqualNP.Library.Machines.comp_polyTime ea eb ec f g c1 c2
