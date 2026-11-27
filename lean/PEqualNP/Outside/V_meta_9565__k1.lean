import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

namespace PEqualNP.Outside.V_meta_9565__k1
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.LinkN

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩], 4⟩

theorem lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (255 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 1 ≤ t := by
  by_contra hlt
  obtain ⟨D, hD, hs, hr⟩ := h
  obtain ⟨gs, o⟩ := D
  have hg : gs = [] := List.length_eq_zero_iff.mp (by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using (by omega : PEqualNP.CircuitLowerBounds.Circuit.size ⟨gs, o⟩ = 0))
  subst hg
  by_cases ho : o < 4
  · revert hr; clear hs hD; revert ho; revert o; decide +kernel
  · have hz : ∀ x : Fin 4 → Bool, (255 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x) = false := fun x => by
      refine Eq.trans (Eq.symm (hr x)) ?_
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp; omega)
    revert hz; decide +kernel

end PEqualNP.Outside.V_meta_9565__k1

theorem PEqualNP.Outside.V_meta_9565__k1 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (255 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 1 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (255 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 1 ≤ t :=
  ⟨⟨PEqualNP.Outside.V_meta_9565__k1.C, by simp [PEqualNP.Outside.V_meta_9565__k1.C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩, PEqualNP.Outside.V_meta_9565__k1.lower⟩
