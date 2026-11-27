import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3262_1
    (trim : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), 0 < n →
      (∀ (x6 : Fin n), (x6, π x6) ∈ E) → PEqualNP.TopForm.IsAO2 (n + n) C → (∀ (x8 : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x8 = Decidable.decide (∃ (x9 : Fin n) (x10 : Fin n), (x9, x10) ∈ E ∧ x8 (Fin.castAdd n x9) = Bool.true ∧ x8 (Fin.natAdd n x10) = Bool.true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ C.size ∧ PEqualNP.TopForm.IsAO2 (n+n) D ∧ (∀ x, PEqualNP.MetaComplexity.circuitFun (n+n) D x = PEqualNP.MetaComplexity.circuitFun (n+n) C x) ∧ (D.output :: D.gates.flatMap (fun g => g.inputs)).toFinset.card = 2*n + D.size)
    (sharing : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), 0 < n →
      (∀ (x5 x6 x7 x8 : Fin n), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ E ∧ (x5, x8) ∈ E ∧ (x6, x7) ∈ E ∧ (x6, x8) ∈ E)) → (∀ (x6 : Fin n), (x6, π x6) ∈ E) → PEqualNP.TopForm.IsAO2 (n + n) C → (∀ (x8 : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x8 = Decidable.decide (∃ (x9 : Fin n) (x10 : Fin n), (x9, x10) ∈ E ∧ x8 (Fin.castAdd n x9) = Bool.true ∧ x8 (Fin.natAdd n x10) = Bool.true)) →
      let uses := C.output :: C.gates.flatMap (fun g => g.inputs);
      E.card ≤ n + (uses.length - uses.toFinset.card)) : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E π C square matching model computes
  by_cases hn : n = 0
  · subst n
    have h0 : E.card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr (fun e _ => Fin.elim0 e.1))
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨D, size, hD, same, distinct⟩ := trim n E π C hnpos matching model computes
  have h := sharing n E π D hnpos square matching hD (fun x => (same x).trans (computes x))
  have lengths (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ht : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap (fun g => g.inputs)).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.flatMap_cons, List.length_append, ht g (by simp),
        ih (fun q hq => ht q (by simp [hq])), List.length_cons]
      omega
  have hl := lengths D.gates hD.2.2
  change E.card ≤ n + ((D.output :: D.gates.flatMap (fun g => g.inputs)).length - (D.output :: D.gates.flatMap (fun g => g.inputs)).toFinset.card) at h
  rw [List.length_cons, hl, distinct] at h
  change E.card ≤ n + (2 * D.size + 1 - (2 * n + D.size)) at h
  have enough := List.toFinset_card_le (D.output :: D.gates.flatMap (fun g => g.inputs))
  rw [distinct, List.length_cons, hl] at enough
  change 2*n + D.size ≤ 2*D.size + 1 at enough
  omega
