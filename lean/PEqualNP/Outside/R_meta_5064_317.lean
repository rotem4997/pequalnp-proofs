import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Take three disjoint copies. At each matched edge incident to a leaf, choose one
-- leaf endpoint, choosing the row when both are leaves. Feed its input in copy
-- i from the OR of that input in copies i and i+1 modulo three. This adds one
-- edge per added OR and raises every leaf degree. Each doubled matching edge
-- lifts to a six-cycle. A rectangle projecting to two base edges would need
-- both doubled edges to share a vertex, impossible for a matching.
-- The graph child records this construction as a Boolean substitution identity.
-- The circuit child implements the substitutions and joins the three outputs.
theorem PEqualNP.Outside.R_meta_5064_317
    (graph :
      let edge := fun (n : ℕ) (E : Finset (Fin n × Fin n)) (z : Fin (n+n) → Bool) =>
        decide (∃ u v, (u,v) ∈ E ∧ z (Fin.castAdd n u) = true ∧ z (Fin.natAdd n v) = true)
      let free := fun (n : ℕ) (E : Finset (Fin n × Fin n)) =>
        ∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        free n E → (∀ p, (p, σ p) ∈ E) →
        let m := 3*n
        ∃ (F : Finset (Fin m × Fin m)) (τ : Equiv.Perm (Fin m))
          (a b : Fin 3 → Fin (n+n) → Fin (m+m)),
          free m F ∧ (∀ p, (p, τ p) ∈ F) ∧
          ((∀ u, ∃ v, v ≠ τ u ∧ (u,v) ∈ F) ∧ (∀ v, ∃ u, τ u ≠ v ∧ (u,v) ∈ F)) ∧
          F.card = 3*E.card + Fintype.card {t : Fin 3 × Fin (n+n) // a t.1 t.2 ≠ b t.1 t.2} ∧
          ∀ z, edge m F z = decide (∃ i, edge n E (fun w => z (a i w) || z (b i w)) = true))
    (compile : ∀ (p q : ℕ) (a b : Fin 3 → Fin p → Fin q) (C : Circuit), 0 < q → IsAO2 p C →
        ∃ D : Circuit, IsAO2 q D ∧
          D.size = 3*C.size + Fintype.card {t : Fin 3 × Fin p // a t.1 t.2 ≠ b t.1 t.2} + 2 ∧
          ∀ z, circuitFun q D z = decide (∃ i, circuitFun p C (fun w => z (a i w) || z (b i w)) = true))
    (leafless : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      ((∀ u : Fin x1, ∃ v : Fin x1, v ≠ x3 u ∧ (u, v) ∈ x2) ∧ (∀ v : Fin x1, ∃ u : Fin x1, x3 u ≠ v ∧ (u, v) ∈ x2)) →
      x2.card + x1 ≤ x4.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      ((∃ u : Fin x1, ∀ v : Fin x1, (u, v) ∈ x2 → v = x3 u) ∨ (∃ v : Fin x1, ∀ u : Fin x1, (u, v) ∈ x2 → x3 u = v)) →
      x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E σ C hE hsize hfree hmatch hC heval _
  obtain ⟨F, τ, a, b, hf, hm, hr, hcount, hsub⟩ := graph n E σ hfree hmatch
  have hn : 0 < n := by
    obtain ⟨⟨u, v⟩, _⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    exact Nat.zero_lt_of_lt u.isLt
  obtain ⟨D, hD, hcost, hsem⟩ := compile (n+n) _ a b C (by omega) hC
  have hfun : ∀ z, circuitFun (3*n + 3*n) D z = decide (∃ u v,
      (u,v) ∈ F ∧ z (Fin.castAdd (3*n) u) = true ∧ z (Fin.natAdd (3*n) v) = true) := by
    intro z
    rw [hsem z]
    simpa only [heval] using (hsub z).symm
  have bound := leafless (3*n) F τ D (by omega) (by omega) hf hm hD hfun hr
  omega
