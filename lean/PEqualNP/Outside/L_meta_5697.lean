import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5697 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.junk x1 x3 = ∅ → ∀ x5 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF x1 x3 x5 := by
  intro G _ C hj j hlt hand x hx
  by_contra hF
  have hmem : j ∈ PEqualNP.TopForm.junk G C := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, hand, hlt, x, hx, by simpa using hF⟩
  rw [hj] at hmem
  exact absurd hmem (Finset.notMem_empty j)
