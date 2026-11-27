import Mathlib.Order.CompletePartialOrder
import PEqualNP.Library.L012
import PEqualNP.Library.L044

/-- P is strictly inside EXP: P is inside EXP, and some EXP language is not in P. -/
theorem PEqualNP.Library.L051 : PEqualNP.Library.P ⊂ PEqualNP.Library.EXP := by
  refine ⟨PEqualNP.Library.L044, fun h => ?_⟩
  obtain ⟨L, hL, hnot⟩ := PEqualNP.Library.L012
  exact hnot (h hL)
