import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Separate the necessary shared gate from the remaining shared-circuit lower bound. -/
theorem PEqualNP.Outside.R_meta_18928_1
  (overlap :
    let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
    let one := fun a i : Fin 25 => decide (i = a)
    ∀ (D : Circuit) (p q : ℕ) (a : Fin 25), Monotone2 D →
      (∀ x, (W D p x && W D q x) = true ↔ target x) →
      (∀ i, W D p (one i) = true ↔ i = a) →
      (∃ i, W D q (one i) = true) →
D.size ≤ 56 → (∃ j < D.size, PEqualNP.SharedOr.InOutCone 25 D (25+j) p ∧ PEqualNP.SharedOr.InOutCone 25 D (25+j) q))
  (cost :
    let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
    let one := fun a i : Fin 25 => decide (i = a)
    ∀ (D : Circuit) (p q : ℕ) (a : Fin 25), Monotone2 D →
      (∀ x, (W D p x && W D q x) = true ↔ target x) →
      (∀ i, W D p (one i) = true ↔ i = a) →
      (∃ i, W D q (one i) = true) →
      (∀ i, W D q (one i) = true → target (fun z => decide (z=a ∨ z=i))) →
      (∃ j < D.size, PEqualNP.SharedOr.InOutCone 25 D (25+j) p ∧ PEqualNP.SharedOr.InOutCone 25 D (25+j) q) → 57 ≤ D.size) :
    let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
    let one := fun a i : Fin 25 => decide (i = a)
    ∀ (D : Circuit) (p q : ℕ) (a : Fin 25), Monotone2 D →
      (∀ x, (W D p x && W D q x) = true ↔ target x) →
      (∀ i, W D p (one i) = true ↔ i = a) →
      (∃ i, W D q (one i) = true) →
      (∀ i, W D q (one i) = true → target (fun z => decide (z=a ∨ z=i))) → 57 ≤ D.size := by
  intro _ _ _ _ D p q a mono rep solo partner neighborhood
  by_contra! small
  exact (Nat.not_le_of_gt small) (cost D p q a mono rep solo partner neighborhood (overlap D p q a mono rep solo partner (by omega)))
