import Mathlib
import PEqualNP.Defs

-- Split on how many wires the final AND reads: 0, 1 or 2. With no wires the AND is constantly
-- true, so it accepts the empty pair of sets, which has no incident pair; that case is proved
-- here. The cases of a single wire and of two wires remain.
theorem PEqualNP.Outside.R_meta_6530_815
    (single :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length = (1 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size)
    (double :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length = (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size := by
  intro x1 x2 hm hl
  rcases (by omega : x2.length = 0 ∨ x2.length = 1 ∨ x2.length = 2) with h | h | h
  · rw [List.length_eq_zero_iff] at h
    subst h
    intro H
    exfalso
    obtain ⟨x7, hx7, _⟩ := (H ∅ ∅).mp rfl
    exact absurd hx7 (Finset.notMem_empty x7)
  · exact single x1 x2 hm h
  · exact double x1 x2 hm h
