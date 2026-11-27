import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity PEqualNP.TopForm
theorem PEqualNP.Outside.R_meta_4297_1
    (hRectangles : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (C : Circuit),
      IsAO2 (Np + Nl) C → C.output < Np + Nl + C.gates.length →
      (∀ z : Fin (Np + Nl) → Bool,
        circuitFun (Np + Nl) C z =
          decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧
            z (Fin.natAdd Np l) = true)) →
      (∀ i < C.gates.length, ∀ a b,
        C.gates[i]? = some ⟨GateOp.or, [a, b]⟩ →
          (Np + Nl ≤ b → WireBelowOutput (Np + Nl) C b →
            WireBelowOutput (Np + Nl) C a) ∧
          (Np + Nl ≤ a → WireBelowOutput (Np + Nl) C a →
            WireBelowOutput (Np + Nl) C b)) →
      ∃ B : List (Finset (Fin Np) × Finset (Fin Nl)),
        (∀ R ∈ B, R.1.Nonempty ∧ R.2.Nonempty ∧
          ∀ p ∈ R.1, ∀ l ∈ R.2, I p l) ∧
        (∀ p l, I p l ↔ ∃ R ∈ B, p ∈ R.1 ∧ l ∈ R.2) ∧
        (B.map fun R => R.1.card + R.2.card).sum - 1 ≤ C.size)
    (hStars : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (B : List (Finset (Fin Np) × Finset (Fin Nl))),
      (∀ p p' l l', p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      (∀ R ∈ B, R.1.Nonempty ∧ R.2.Nonempty ∧
        ∀ p ∈ R.1, ∀ l ∈ R.2, I p l) →
      (∀ p l, I p l ↔ ∃ R ∈ B, p ∈ R.1 ∧ l ∈ R.2) →
      ∃ W : List (ℕ × List ℕ),
        (∀ b ∈ W, b.2 ≠ [] ∧
          ((b.1 < Np ∧ ∀ w ∈ b.2, Np ≤ w ∧ w < Np + Nl) ∨
            (Np ≤ b.1 ∧ b.1 < Np + Nl ∧ ∀ w ∈ b.2, w < Np))) ∧
        (∀ p l, I p l ↔ ∃ b ∈ W,
          (b.1 = (p : Fin Np).val ∧ Np + (l : Fin Nl).val ∈ b.2) ∨
          (b.1 = Np + (l : Fin Nl).val ∧ (p : Fin Np).val ∈ b.2)) ∧
        (W.map fun b => b.2.length).sum + W.length - 1 ≤
          (B.map fun R => R.1.card + R.2.card).sum - 1) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl,
        p ≠ p' → l ≠ l' →
          ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      IsAO2 (Np + Nl) C → C.output < Np + Nl + C.gates.length →
      (∀ z : Fin (Np + Nl) → Bool,
        MetaComplexity.circuitFun (Np + Nl) C z =
          decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
            z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ i < C.gates.length, ∀ a b,
        C.gates[i]? = some ⟨GateOp.or, [a, b]⟩ →
          (Np + Nl ≤ b → WireBelowOutput (Np + Nl) C b →
            WireBelowOutput (Np + Nl) C a) ∧
          (Np + Nl ≤ a → WireBelowOutput (Np + Nl) C a →
            WireBelowOutput (Np + Nl) C b)) →
      ∃ W : List (ℕ × List ℕ),
        (∀ b ∈ W, b.2 ≠ [] ∧
          ((b.1 < Np ∧ ∀ w ∈ b.2, Np ≤ w ∧ w < Np + Nl) ∨
            (Np ≤ b.1 ∧ b.1 < Np + Nl ∧ ∀ w ∈ b.2, w < Np))) ∧
        (∀ p l, I p l ↔ ∃ b ∈ W,
          (b.1 = (p : Fin Np).val ∧ Np + (l : Fin Nl).val ∈ b.2) ∨
          (b.1 = Np + (l : Fin Nl).val ∧ (p : Fin Np).val ∈ b.2)) ∧
        (W.map fun b => b.2.length).sum + W.length - 1 ≤ C.size := by
  intro Np Nl I _ C hNoFour hAO hOut hFun hOr
  obtain ⟨B, hB, hCover, hCost⟩ := hRectangles Np Nl I C hAO hOut hFun hOr
  obtain ⟨W, hW, hInc, hWCost⟩ :=
    hStars Np Nl I B hNoFour hB hCover
  refine ⟨W, hW, hInc, ?_⟩
  exact hWCost.trans hCost
