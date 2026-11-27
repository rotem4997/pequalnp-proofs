import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5727 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → ∀ (x12 : Finset (Fin x2 × Fin x2)), (7656 : ℕ) < Min.min (Finset.image Prod.fst x12).card (Finset.image Prod.snd x12).card → (44 : ℕ) * ((Finset.image Prod.fst x12).card + (Finset.image Prod.snd x12).card - (1 : ℕ)) < x12.card → (∀ x15 ∈ x12, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x17 = Fin.castAdd x2 x15.1 ∨ x17 = Fin.natAdd x2 x15.2)) = Bool.true) → ¬(44 : ℕ) * x5.size < x12.card → x12.card ≤ (44 : ℕ) * x5.size := by
  set_option maxRecDepth 100000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; nlinarith)
  | (intros; positivity)
  | (intros; aesop)
