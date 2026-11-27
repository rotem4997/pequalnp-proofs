import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- Separate the cost of obtaining one read-once witness for each edge from the
-- cost of polarizing the degree-two witnesses of such a circuit.
theorem PEqualNP.Outside.R_meta_2001_1
    (normalize : ∃ a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ R : Circuit, Monotone2 R ∧ IsReadK n R 1 ∧ R.size + 1 ≤ a * (C.size + 1) ∧
        ∀ x : Fin n → Bool, R.eval (List.ofFn x) = C.eval (List.ofFn x))
    (polarize : ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ R : Circuit, Monotone2 R → IsReadK n R 1 →
      (∀ x : Fin n → Bool, R.eval (List.ofFn x) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ b * (R.size + 1) ∧
        ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ y v = true)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  obtain ⟨a, ha⟩ := normalize
  obtain ⟨b, hb⟩ := polarize
  refine ⟨b * a, ?_⟩
  intro n G inst hdegree hgirth C hmono hgraph
  obtain ⟨R, hmR, hread, hsizeR, hRC⟩ := ha n G hdegree hgirth C hmono hgraph
  obtain ⟨D, hmD, hsizeD, hD⟩ := hb n G R hmR hread (fun x => (hRC x).trans (hgraph x))
  refine ⟨D, hmD, ?_, hD⟩
  calc
    D.size + 1 ≤ b * (R.size + 1) := hsizeD
    _ ≤ b * (a * (C.size + 1)) := Nat.mul_le_mul_left b hsizeR
    _ = b * a * (C.size + 1) := (Nat.mul_assoc _ _ _).symm
