import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2389_509
    (flatten : ∀ C : Circuit, IsAO2 26 C → C.size < 64 →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ C.size ∧
        (∀ z : Fin 26 → Bool, D.eval (List.ofFn z) = C.eval (List.ofFn z)) ∧
        ¬ (∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧
          (gateAt D j).op = GateOp.and ∧ InCone 26 D i j))
    (flatBound : ∀ D : Circuit, IsAO2 26 D →
      (∀ z : Fin 26 → Bool, D.eval (List.ofFn z) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      ¬ (∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧
        (gateAt D j).op = GateOp.and ∧ InCone 26 D i j) →
      64 ≤ D.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  intro C hc hcomputes
  by_contra hsize
  have hsmall : C.size < 64 := Nat.lt_of_not_ge hsize
  obtain ⟨D, hd, hdsize, hdeval, hflat⟩ := flatten C hc hsmall hcomputes
  have hbound := flatBound D hd (fun z => by rw [hdeval z]; exact hcomputes z) hflat
  exact hsize (hbound.trans hdsize)
