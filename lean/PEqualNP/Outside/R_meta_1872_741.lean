import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_1872_741
    (hPropagate : ∀ (n : ℕ) (C : Circuit) (g w : ℕ) (x : List Bool),
      x.length = n → OrReaches n C w g →
      (C.wires x).getD (n + g) false = true → (C.wires x).getD w false = true)
    (hLower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (26 ≤ x2 → ¬ OrReaches 26 x1 x3 (x2 - 26)) →
        (26 ≤ x3 → ¬ OrReaches 26 x1 x2 (x3 - 26)) →
        have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b hMono hBack ha hb
  dsimp only
  intro hCover hReject hA hB
  have hab : 26 ≤ a → ¬ OrReaches 26 C b (a - 26) := by
    intro hA26 hPath
    obtain ⟨p, l, _, hAt, hBt⟩ := hA
    let x := (List.ofFn fun u : Fin 13 => decide (u = p)) ++
      (List.ofFn fun v : Fin 13 => decide (v = l))
    have hLen : x.length = 26 := by simp [x]
    have hA' : (C.wires x).getD (26 + (a - 26)) false = true := by
      rw [Nat.add_sub_of_le hA26]
      exact hAt
    have hB' : (C.wires x).getD b false = false := hBt
    have hGot := hPropagate 26 C (a - 26) b x hLen hPath hA'
    rw [hB'] at hGot
    contradiction
  have hba : 26 ≤ b → ¬ OrReaches 26 C a (b - 26) := by
    intro hB26 hPath
    obtain ⟨p, l, _, hBt, hAt⟩ := hB
    let x := (List.ofFn fun u : Fin 13 => decide (u = p)) ++
      (List.ofFn fun v : Fin 13 => decide (v = l))
    have hLen : x.length = 26 := by simp [x]
    have hB' : (C.wires x).getD (26 + (b - 26)) false = true := by
      rw [Nat.add_sub_of_le hB26]
      exact hBt
    have hA' : (C.wires x).getD a false = false := hAt
    have hGot := hPropagate 26 C (b - 26) a x hLen hPath hB'
    rw [hA'] at hGot
    contradiction
  exact hLower C a b hMono hBack ha hb hab hba hCover hReject hA hB
