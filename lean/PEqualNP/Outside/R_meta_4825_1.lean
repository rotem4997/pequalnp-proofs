import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4825_1
    (h1 : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → (∀ a : Fin n, (a, p a) ∈ E) → PEqualNP.TopForm.IsAO2 (n+n) C → (∀ z : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) C z = decide (∃ a b : Fin n, (a,b) ∈ E ∧ z (Fin.castAdd n a) = true ∧ z (Fin.natAdd n b) = true)) → PEqualNP.ReadK.IsReadK (n+n) C 1 → E.card + n ≤ C.size + 1)
    (h2 : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), n < E.card → (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) → (∀ a : Fin n, (a, p a) ∈ E) → PEqualNP.TopForm.IsAO2 (n+n) C → (∀ z : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) C z = decide (∃ a b : Fin n, (a,b) ∈ E ∧ z (Fin.castAdd n a) = true ∧ z (Fin.natAdd n b) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (n+n) D ∧ (∀ z : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) D z = decide (∃ a b : Fin n, (a,b) ∈ E ∧ z (Fin.castAdd n a) = true ∧ z (Fin.natAdd n b) = true)) ∧ PEqualNP.ReadK.IsReadK (n+n) D 1 ∧ D.size ≤ C.size) : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → x4.output + (1 : ℕ) = x1 + x1 + x4.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset = Finset.range (x1 + x1 + x4.size - (1 : ℕ)) → x2.card - x1 ≤ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset.card := by
  intro n E p C x5 hm hfour hmatch hao hfun hout hwires
  obtain ⟨D, hDA, hDF, hDR, hDC⟩ := h2 n E p C hm hfour hmatch hao hfun
  have hbound := h1 n E p D hfour hmatch hDA hDF hDR
  have hlength : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * C.size := by
    have aux : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g.inputs.length = 2) →
        (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * gs.length := by
      intro gs hh
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have hg : g.inputs.length = 2 := hh g (by simp)
        have ht : ∀ g ∈ gs, g.inputs.length = 2 := by
          intro g hg; exact hh g (by simp [hg])
        simp only [List.flatMap_cons, List.length_append, List.length_cons, ih ht, hg]
        omega
    exact aux C.gates hao.2.2
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := by omega
    subst n
    have hh : E.Nonempty := Finset.card_pos.mp hm
    obtain ⟨⟨a, b⟩, hab⟩ := hh
    exact Fin.elim0 a
  have hcard : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card = n+n+C.size-1 := by
    rw [hwires, Finset.card_range]
  have hle := List.toFinset_card_le (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)
  omega
