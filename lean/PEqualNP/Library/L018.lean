import PEqualNP.Library.L010
import PEqualNP.Library.L016

/-- An NP-complete language is in P exactly when P = NP. -/
theorem PEqualNP.Library.L018 : ∀ L : Language Bool, PEqualNP.Library.NPComplete L →
    (L ∈ PEqualNP.Library.P ↔ PEqualNP.Library.P = PEqualNP.Library.NP) := by
  rintro L ⟨hnp, hhard⟩
  constructor
  · intro hp
    exact Set.Subset.antisymm PEqualNP.Library.L010
      (fun L' hL' => PEqualNP.Library.L016 L' L (hhard L' hL') hp)
  · intro h
    rw [h]; exact hnp
