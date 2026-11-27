import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6390_324
    (hexagon : ∀ (m : ℕ) (E : Finset (Fin 3 × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin 3) (l k : Fin m), p ≠ q → l ≠ k →
        ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      (∀ d : Fin 3, ∃ l : Fin m, ∀ p : Fin 3, (p,l) ∈ E ↔ p ≠ d) →
      PEqualNP.TopForm.IsAO2 (3+m) C →
      (∀ x : Fin (3+m) → Bool, PEqualNP.MetaComplexity.circuitFun (3+m) C x =
        decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd 3 e.2) = true)) →
      E.card + 2 ≤ C.size)
    (residue : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let ends (F : Finset (Fin n × Fin m)) : Finset (Fin (n+m)) :=
        F.biUnion fun e => {Fin.castAdd m e.1, Fin.natAdd n e.2}
      (¬ (n = 3 ∧ ∀ d : Fin n, ∃ l : Fin m, ∀ p : Fin n, (p,l) ∈ E ↔ p ≠ d)) →
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ x : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C x =
        decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) →
      (¬ ∃ (F H : Finset (Fin n × Fin m)) (v : Fin (n+m)),
        F.Nonempty ∧ F ∪ H = E ∧ Disjoint (ends F) (ends H) ∧
          ∀ e ∈ F, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → ∃ (x10 : Finset (Fin x1)) (x11 : Finset (Fin x2)), (∀ x12 ∈ x3, x12.1 ∈ x10 ∨ x12.2 ∈ x11) ∧ x3.card + x10.card + x11.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C
  dsimp only
  intro square legal computes noStar
  by_cases three : n = 3 ∧ ∀ d : Fin n, ∃ l : Fin m, ∀ p : Fin n, (p,l) ∈ E ↔ p ≠ d
  · obtain ⟨hrows, pairs⟩ := three
    subst n
    have cost := hexagon m E C square pairs legal computes
    refine ⟨Finset.univ, ∅, fun e _ => Or.inl (Finset.mem_univ e.1), ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, Nat.add_zero]
    omega
  · exact residue n m E C three square legal computes noStar
