import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9412
open PEqualNP.CircuitLowerBounds



theorem least (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = F) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = F ∧
      D.size ≤ C.size ∧ ∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E →
        PEqualNP.MetaComplexity.circuitFun n E = F → D.size ≤ E.size := by
  classical
  have hex : ∃ k, ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = F ∧ D.size = k := ⟨C.size, C, h, hf, rfl⟩
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, ?_, ?_⟩
  · rw [hDs]; exact Nat.find_min' hex ⟨C, h, hf, rfl⟩
  · intro E hE hEf
    rw [hDs]; exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩

end PEqualNP.Outside.L_meta_9412

open PEqualNP.Outside.L_meta_9412 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9412 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = fun (x8 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 = fun (x10 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x10 → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x10 = fun (x12 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) → x9.size ≤ x10.size := by
  intro x1 x2 x3 x4 x5 _ h5 hf
  exact least _ _ x5 h5 hf
