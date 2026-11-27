import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5064_574
    (hthreshold : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card →
      (∀ a d b c : Fin n, a ≠ d → b ≠ c →
        ¬ ((a,b) ∈ E ∧ (a,c) ∈ E ∧ (d,b) ∈ E ∧ (d,c) ∈ E)) →
      (∀ a, (a,σ a) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      n+n ≤ C.size)
    (hremaining : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      n + 1 < E.card → n+n ≤ C.size →
      (∀ a d b c : Fin n, a ≠ d → b ≠ c →
        ¬ ((a,b) ∈ E ∧ (a,c) ∈ E ∧ (d,b) ∈ E ∧ (d,c) ∈ E)) →
      (∀ a, (a,σ a) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      ((∃ a : Fin n, ∀ b : Fin n, (a,b) ∈ E → b = σ a) ∨
        ∃ b : Fin n, ∀ a : Fin n, (a,b) ∈ E → σ a = b) →
      E.card + n ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E σ C hextra _ hrect hmatch hAO hcomp hleaf
  have hsize := hthreshold n E σ C hextra hrect hmatch hAO hcomp
  by_cases h : n + 1 < E.card
  · exact hremaining n E σ C h hsize hrect hmatch hAO hcomp hleaf
  · omega
