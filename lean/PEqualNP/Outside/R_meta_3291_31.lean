import Mathlib
import PEqualNP.Defs

-- Reuses the three incidence estimates from the reduction R_meta_2130_1.
-- The first two are L_meta_2970 and L_meta_2972. The third is L_meta_2974.
theorem PEqualNP.Outside.R_meta_3291_31
    (lineBound : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (pointBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (rereadBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false}
        ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I instI C hq hN hcol huniq hmodel hsound
  have noRectangle : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ (I p l ∧ I r l ∧ I p m ∧ I r m) := by
    rintro p r l m hpr hlm ⟨hpl, hrl, hpm, hrm⟩
    obtain ⟨_, _, uniqueLine⟩ := huniq p r hpr
    exact hlm ((uniqueLine l ⟨hpl, hrl⟩).trans (uniqueLine m ⟨hpm, hrm⟩).symm)
  have hL := lineBound N I C noRectangle hmodel
    (fun z hz => hsound z (hz.trans (by omega)))
  have hP := pointBound q N I C (by omega) hN hcol huniq hmodel hsound
  have hR := rereadBound q N I C (by omega) hN hcol huniq hmodel hsound
  let accepts (e : Fin N × Fin N) := PEqualNP.MetaComplexity.circuitFun (N + N) C
    (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2))
  let readLine (e : Fin N × Fin N) := PEqualNP.ReadK.lineSingle C (N + N)
    (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
  let readPoint (e : Fin N × Fin N) := PEqualNP.ReadK.lineSingle C (N + N)
    (fun i => decide (i < N)) e.1.val (N + e.2.val)
  let hits := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ accepts e = true
  let lines := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readLine e = true
  let points := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readPoint e = true
  let rest := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ accepts e = true ∧ readLine e = false ∧ readPoint e = false
  have cover : hits ⊆ (lines ∪ points) ∪ rest := by
    intro e he
    obtain ⟨hi, ha⟩ := (Finset.mem_filter.mp he).2
    simp only [lines, points, rest, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases readLine e <;> cases readPoint e <;> simp [hi, ha]
  rw [Fintype.card_subtype] at hL hP hR ⊢
  change lines.card ≤ 10 * C.size at hL
  change points.card ≤ 10 * C.size at hP
  change rest.card ≤ 24 * C.size at hR
  change hits.card ≤ 44 * C.size
  have h := Finset.card_le_card cover
  have hp := Finset.card_union_le lines points
  have hr := Finset.card_union_le (lines ∪ points) rest
  omega
