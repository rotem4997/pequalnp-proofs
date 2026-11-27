import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem eval_empty_lt (n : ℕ) (C : Circuit) (hgs : C.gates = []) (ho : C.output < n)
    (f : Fin n → Bool) :
    circuitFun n C f = f ⟨C.output, ho⟩ := by
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hgs, List.foldl_nil, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using ho), List.getElem_ofFn]
  rfl

theorem eval_empty_ge (n : ℕ) (C : Circuit) (hgs : C.gates = []) (ho : ¬ C.output < n)
    (f : Fin n → Bool) :
    circuitFun n C f = false := by
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hgs, List.foldl_nil, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by simp; omega)]
  rfl

theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   x5.size = (0 : ℕ) →     (87 : ℕ) ≤ x1 →       x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →         (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) →           (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) →             PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →               (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →                 let x14 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x14 : Fin (x2 + x2)) (x15 : Fin x2 × Fin x2) => x14 = Fin.castAdd x2 x15.1 ∨ x14 = Fin.natAdd x2 x15.2;                 (∀ x15 ∈ x6, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x14 x17 x15)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x2 ≤ x17)) (↑x15.1) (x2 + ↑x15.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x17 < x2)) (↑x15.1) (x2 + ↑x15.2) = Bool.false) → (∀ x16 ∈ x6, ∀ (x18 : Fin (x2 + x2)), x14 x18 x16 → (24 : ℕ) < (Finset.filter (x14 x18) x6).card) → x6.card ≤ (24 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 x6 hsize hx1 _ _ _ _ hzero x14 hx6 _
  have hempty : x6 = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    have hgs : x5.gates = [] := List.eq_nil_of_length_eq_zero hsize
    have htrue := (hx6 p hp).2.1
    by_cases ho : x5.output < x2 + x2
    · rw [eval_empty_lt (x2 + x2) x5 hgs ho, decide_eq_true_eq] at htrue
      let w : Fin (x2 + x2) := ⟨x5.output, ho⟩
      have hw : w = Fin.castAdd x2 p.1 ∨ w = Fin.natAdd x2 p.2 := htrue
      let g : Fin (x2 + x2) → Bool := fun i => decide (i = w)
      have hg_eval : circuitFun (x2 + x2) x5 g = true := by
        rw [eval_empty_lt (x2 + x2) x5 hgs ho]
        simp [g, w]
      rcases hw with hw | hw
      · have hdisj : ∀ q : Fin x2, Fin.natAdd x2 q ≠ w := by
          intro q hq
          have hv := congrArg Fin.val (hq.trans hw)
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
          have := p.1.isLt
          omega
        have hcard : Fintype.card { q : Fin x2 // g (Fin.natAdd x2 q) = Bool.true } ≤ x1 := by
          rw [Fintype.card_subtype]
          have hf : (Finset.univ.filter fun q : Fin x2 => g (Fin.natAdd x2 q) = Bool.true) = ∅ := by
            ext q
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, g, decide_eq_true_eq]
            exact hdisj q
          rw [hf]
          simp
        have hno : ¬∃ (u : Fin x2) (v : Fin x2), x3 u v ∧ g (Fin.castAdd x2 u) = Bool.true ∧ g (Fin.natAdd x2 v) = Bool.true := by
          rintro ⟨u, v, _, _, hv⟩
          simp only [g, decide_eq_true_eq] at hv
          exact hdisj v hv
        have hf0 := hzero g hcard hno
        rw [hg_eval] at hf0
        cases hf0
      · have hdisj : ∀ u : Fin x2, Fin.castAdd x2 u ≠ w := by
          intro u hu
          have hv := congrArg Fin.val (hu.trans hw)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          have := u.isLt
          omega
        have hcard : Fintype.card { q : Fin x2 // g (Fin.natAdd x2 q) = Bool.true } ≤ x1 := by
          rw [Fintype.card_subtype]
          have hsub : (Finset.univ.filter fun q : Fin x2 => g (Fin.natAdd x2 q) = Bool.true) ⊆ {p.2} := by
            intro q hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, decide_eq_true_eq] at hq
            have hv := congrArg Fin.val (hq.trans hw)
            simp only [Fin.val_natAdd] at hv
            exact Finset.mem_singleton.mpr (Fin.ext (by omega))
          have hc := Finset.card_le_card hsub
          simp only [Finset.card_singleton] at hc
          omega
        have hno : ¬∃ (u : Fin x2) (v : Fin x2), x3 u v ∧ g (Fin.castAdd x2 u) = Bool.true ∧ g (Fin.natAdd x2 v) = Bool.true := by
          rintro ⟨u, v, _, hu, _⟩
          simp only [g, decide_eq_true_eq] at hu
          exact hdisj u hu
        have hf0 := hzero g hcard hno
        rw [hg_eval] at hf0
        cases hf0
    · rw [eval_empty_ge (x2 + x2) x5 hgs ho] at htrue
      cases htrue
  simp [hempty]

end PEqualNP.Outside.L_meta_7203

theorem PEqualNP.Outside.L_meta_7203 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   x5.size = (0 : ℕ) →     (87 : ℕ) ≤ x1 →       x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →         (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) →           (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) →             PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →               (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →                 let x14 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x14 : Fin (x2 + x2)) (x15 : Fin x2 × Fin x2) => x14 = Fin.castAdd x2 x15.1 ∨ x14 = Fin.natAdd x2 x15.2;                 (∀ x15 ∈ x6, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x14 x17 x15)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x2 ≤ x17)) (↑x15.1) (x2 + ↑x15.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x17 < x2)) (↑x15.1) (x2 + ↑x15.2) = Bool.false) → (∀ x16 ∈ x6, ∀ (x18 : Fin (x2 + x2)), x14 x18 x16 → (24 : ℕ) < (Finset.filter (x14 x18) x6).card) → x6.card ≤ (24 : ℕ) * x5.size :=
  PEqualNP.Outside.L_meta_7203.main
