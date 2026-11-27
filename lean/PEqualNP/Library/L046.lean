import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.AllTrue

/-- P is closed under intersection: run both deciders on the input, pair the two answer bits,
and answer whether both are true. -/
theorem PEqualNP.Library.L046 : ∀ L₁ L₂ : Language Bool, L₁ ∈ PEqualNP.Library.P →
    L₂ ∈ PEqualNP.Library.P → L₁ ⊓ L₂ ∈ PEqualNP.Library.P := by
  rintro L₁ L₂ ⟨f₁, h₁, ⟨c₁⟩⟩ ⟨f₂, h₂, ⟨c₂⟩⟩
  have g₁ : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => [f₁ x]) :=
    ⟨⟨c₁.toTM2ComputableAux, c₁.time, c₁.outputsFun⟩⟩
  have g₂ : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => [f₂ x]) :=
    ⟨⟨c₂.toTM2ComputableAux, c₂.time, c₂.outputsFun⟩⟩
  have h := PEqualNP.Library.Machines.cpt_comp (PEqualNP.Library.Machines.cpt_pair g₁ g₂)
    PEqualNP.Library.Machines.allTrue_polyTime
  refine ⟨fun x => f₁ x && f₂ x, fun x => ?_, ?_⟩
  · exact (and_congr (h₁ x) (h₂ x)).trans Bool.and_eq_true_iff.symm
  · have e : (fun x : List Bool => f₁ x && f₂ x) =
        (fun x : List Bool => (([f₁ x], [f₂ x]) : List Bool × List Bool).1.append
          (([f₁ x], [f₂ x]) : List Bool × List Bool).2 |>.all id) := by
      funext x; simp
    rw [e]; exact h
