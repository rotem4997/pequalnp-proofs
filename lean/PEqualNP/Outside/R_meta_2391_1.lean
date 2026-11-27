import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

-- The three test inputs are a singleton, two points, and a nonincident point and line.
theorem PEqualNP.Outside.R_meta_2391_1
    (criterion : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (T : Fin n → Fin n → Prop),
      (∀ u v : Fin n, ¬ G.Adj u v → ∃ e : G ≃g G, T (e u) (e v)) →
      (∀ C : Circuit, IsLeastAO G C → ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ u v : Fin n, T u v → gateVal n C j (pairInput u v) = false) →
      ∀ C : Circuit, IsLeastAO G C → junk G C = ∅)
    (orbits : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ u v : Fin 26, ¬ G.Adj u v → ∃ e : G ≃g G,
        e u = 0 ∧ (e v = 0 ∨ e v = 1 ∨ e v = 14))
    (tests : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : Circuit, IsLeastAO G C → ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ v : Fin 26, v = 0 ∨ v = 1 ∨ v = 14 → gateVal 26 C j (pairInput 0 v) = false) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ := by
  intro G _ C adj least
  let T (u v : Fin 26) : Prop := u = 0 ∧ (v = 0 ∨ v = 1 ∨ v = 14)
  apply criterion 26 G T (orbits G adj) _ C least
  intro B hB j hj hop u v h
  obtain ⟨rfl, hv⟩ := h
  exact tests G adj B hB j hj hop v hv
