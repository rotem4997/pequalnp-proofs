import Mathlib
import PEqualNP.Defs

-- Split L-meta-2418 on whether C already has line-degree at most 1.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2418_1
    (already :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬inc p w
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        (∀ p w : Fin 13, inc p w → PEqualNP.MetaComplexity.circuitFun 26 C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
          PEqualNP.MetaComplexity.circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false)
      let thin := fun x : Fin 26 → Bool =>
        ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 63 → good C →
        PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ∃ D, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size ∧
          PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          ∀ x, thin x → PEqualNP.MetaComplexity.circuitFun 26 D x = PEqualNP.MetaComplexity.circuitFun 26 C x)
    (highDeg :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬inc p w
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        (∀ p w : Fin 13, inc p w → PEqualNP.MetaComplexity.circuitFun 26 C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
          PEqualNP.MetaComplexity.circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false)
      let thin := fun x : Fin 26 → Bool =>
        ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 63 → good C →
        ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ∃ D, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size ∧
          PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          ∀ x, thin x → PEqualNP.MetaComplexity.circuitFun 26 D x = PEqualNP.MetaComplexity.circuitFun 26 C x) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  intro x1 x2 x3 x4 x5 C hmono hsize hgood
  by_cases hdeg : PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) C (1 : ℕ)
  · exact already C hmono hsize hgood hdeg
  · exact highDeg C hmono hsize hgood hdeg
