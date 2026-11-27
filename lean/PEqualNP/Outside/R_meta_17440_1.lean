import PEqualNP.Defs

-- The first step extracts a priced biclique cover from the circuit.
-- The second step only concerns the finite graph and its cover.
-- A chosen centre can be shared by several pieces.
theorem PEqualNP.Outside.R_meta_17440_1
    (hCover :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ z : Fin (n + m) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C z =
            Decidable.decide (∃ (a : Fin n) (b : Fin m),
              (a, b) ∈ E ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true)) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) ∧
          (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + 1)
    (hMinVC :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
        (k : ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) →
        (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (X : Finset (Fin n)) (Y : Finset (Fin m)),
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧
          E.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C hC4 hAO hFun
  -- The bicliques can overlap. Keep their total cost with multiplicity
  -- until the graph-only step has selected a cover by distinct vertices.
  -- The first inequality charges each edge at least once.
  -- The second passes on the original gate budget without changing it.
  obtain ⟨k, A, B, hNonempty, hContained, hCovers, hCost⟩ :=
    hCover n m E C hC4 hAO hFun
  -- Each nonempty biclique in a graph without a four-cycle has a
  -- singleton side. Its centre contributes at most one to the cover,
  -- while its leaves pay for all the edges of that biclique.
  obtain ⟨X, Y, hHits, hUnionCost⟩ :=
    hMinVC n m E k A B hC4 hNonempty hContained hCovers
  refine ⟨X, Y, hHits, ?_⟩
  calc
    E.card + X.card + Y.card
        ≤ ∑ i : Fin k, ((A i).card + (B i).card) := hUnionCost
    _ ≤ C.size + 1 := hCost
