import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3491_2
    (count : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬ (I p l ∧ I p k ∧ I q l ∧ I q k)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ z : Fin (n + m) → Bool,
        PEqualNP.MetaComplexity.circuitFun (n + m) C z =
          decide (∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      (PEqualNP.ReadTwo.incid I).card ≤ C.size)
    (cover : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬ (I p l ∧ I p k ∧ I q l ∧ I q k)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ z : Fin (n + m) → Bool,
        PEqualNP.MetaComplexity.circuitFun (n + m) C z =
          decide (∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ T : Finset (Fin (n + m)),
        (∀ (p : Fin n) (l : Fin m), I p l → Fin.castAdd m p ∈ T ∨ Fin.natAdd n l ∈ T) ∧
        T.card ≤ C.size + 1 - (PEqualNP.ReadTwo.incid I).card)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3]
        (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
        ¬ (x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
          Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2),
            x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧
              x8 (Fin.natAdd x1 x10) = Bool.true)) →
      ∃ (x9 : Finset (Fin (x1 + x2))),
        (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 →
          Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧
        (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  intro n m I _ C hsq hao hfun
  obtain ⟨T, hcov, hsize⟩ := cover n m I C hsq hao hfun
  refine ⟨T, hcov, ?_⟩
  have hcount := count n m I C hsq hao hfun
  have hsub : C.size + 1 - (PEqualNP.ReadTwo.incid I).card +
      (PEqualNP.ReadTwo.incid I).card = C.size + 1 :=
    Nat.sub_add_cancel (by omega)
  omega
