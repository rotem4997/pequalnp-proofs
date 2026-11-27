import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8843_643
    (h_seed :
      let inc : Fin 13 → Fin 13 → Prop :=
        fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ 63 →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ p l : Fin 13, inc p l →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ l ∈ W, ¬inc p l) ∧
          (∀ l : Fin 13, (P.filter fun p => inc p l).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter fun l => inc p l).card ≤ 2) ∧
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => Fin.addCases (fun p => decide (p ∈ P))
              (fun l => decide (l ∈ W)) i) = true)
    (h_lines :
      let inc : Fin 13 → Fin 13 → Prop :=
        fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ 63 →
        PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        (∀ p l : Fin 13, inc p l →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ l ∈ W, ¬inc p l) ∧
          (∀ l : Fin 13, (P.filter fun p => inc p l).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter fun l => inc p l).card ≤ 2) ∧
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => Fin.addCases (fun p => decide (p ∈ P))
              (fun l => decide (l ∈ W)) i) = true)
    (h_points :
      let inc : Fin 13 → Fin 13 → Prop :=
        fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ 63 →
        PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ p l : Fin 13, inc p l →
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ l ∈ W, ¬inc p l) ∧
          (∀ l : Fin 13, (P.filter fun p => inc p l).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter fun l => inc p l).card ≤ 2) ∧
          PEqualNP.MetaComplexity.circuitFun 26 C
            (fun i => Fin.addCases (fun p => decide (p ∈ P))
              (fun l => decide (l ∈ W)) i) = true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true := by
  intro x1 C hm hs hyes
  by_cases hl : PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1
  · exact h_lines C hm hs hl hyes
  · by_cases hp : PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1
    · exact h_points C hm hs hp hyes
    · exact h_seed C hm hs hl hp hyes
