import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5373_436
    (bound : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ))
    (compile : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  intro x1 x2 x3 x4 x5 x6 adj cycle hC hA hF hsub hl hr hleaf
  have hex : ∃ x15 ∈ x3, x15 ∉ x4 := by
    by_contra! covered
    have separated (i : Fin x1) (j : Fin x2) : Fin.castAdd x2 i ≠ Fin.natAdd x1 j := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have unique {u v w : Fin (x1 + x2)} (hv : x6.Adj u v) (hw : x6.Adj u w) : v = w := by
      obtain ⟨e, he, hv⟩ := (adj u v).mp hv
      obtain ⟨f, hf, hw⟩ := (adj u w).mp hw
      obtain ⟨hu, hv⟩ | ⟨hv, hu⟩ := hv <;>
        obtain ⟨hu', hw⟩ | ⟨hw, hu'⟩ := hw
      · have hef := hl e (covered e he) f (covered f hf) (by simpa using hu.symm.trans hu')
        exact hv.trans (hef ▸ hw.symm)
      · exact (separated e.1 f.2 (hu.symm.trans hu')).elim
      · exact (separated f.1 e.2 (hu'.symm.trans hu)).elim
      · have hvf := congrArg Fin.val (hu.symm.trans hu')
        have hef := hr e (covered e he) f (covered f hf) (Fin.ext (by simp at hvf; omega))
        exact hv.trans (hef ▸ hw.symm)
    apply cycle
    intro u p hp
    exact hp.snd_ne_penultimate (unique (p.adj_snd hp.not_nil) (p.adj_penultimate hp.not_nil).symm)
  obtain ⟨e, he, heM⟩ := hex
  obtain ⟨A, B, hcov, hbd⟩ := bound x1 x2 x3 x5 hC hA hF
  obtain ⟨D, hDA, hDs, hDF, -⟩ := compile x1 x2 (x3.erase e) A B
    (fun d hd => hcov d (Finset.mem_of_mem_erase hd))
  have hcard := Finset.card_erase_of_mem he
  have hE : 0 < x3.card := Finset.card_pos.mpr ⟨e, he⟩
  have hpos : 0 < A.card + B.card := by
    rcases hcov e he with h | h
    · have := Finset.card_pos.mpr ⟨_, h⟩
      omega
    · have := Finset.card_pos.mpr ⟨_, h⟩
      omega
  refine ⟨e, he, heM, D, ?_, hDA, hDF⟩
  omega
