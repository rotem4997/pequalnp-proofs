import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_8734 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x5.gates = [] → Fintype.card { x14 : Fin x2 × Fin x2 // x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 h2 _ _ _ _ _ hrej hg
  refine le_of_eq_of_le (Fintype.card_eq_zero_iff.mpr ⟨?_⟩) (Nat.zero_le _)
  rintro ⟨⟨a, b⟩, hab, hv⟩
  dsimp only at hv
  have hcf : ∀ x : Fin (x2 + x2) → Bool,
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x = (List.ofFn x).getD x5.output false := by
    intro x
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires
    rw [hg]
    rfl
  rw [hcf] at hv
  by_cases ho : x5.output < x2 + x2
  · have hget : ∀ x : Fin (x2 + x2) → Bool,
        (List.ofFn x).getD x5.output false = x ⟨x5.output, ho⟩ := by
      intro x
      simp [List.getD_eq_getElem?_getD, ho]
    have hc : Fintype.card { x13 : Fin x2 // (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.natAdd x2 x13) = Bool.true } ≤ x1 := by
      refine le_trans (Fintype.card_le_one_iff.mpr ?_) (by omega)
      rintro ⟨u, hu⟩ ⟨v, hv'⟩
      simp only [decide_eq_true_eq] at hu hv'
      have h := congrArg Fin.val (hu.trans hv'.symm)
      simp only [Fin.coe_natAdd] at h
      apply Subtype.ext
      apply Fin.ext
      show u.val = v.val
      omega
    have hn : ¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.castAdd x2 x14) = Bool.true ∧ (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) (Fin.natAdd x2 x15) = Bool.true := by
      rintro ⟨p, l, _, hp, hl⟩
      simp only [decide_eq_true_eq] at hp hl
      have h := congrArg Fin.val (hp.trans hl.symm)
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at h
      have := p.isLt
      omega
    have hr := hrej (fun i : Fin (x2 + x2) => decide (i = ⟨x5.output, ho⟩)) hc hn
    rw [hcf, hget] at hr
    simp at hr
  · simp [List.getD_eq_getElem?_getD, ho] at hv
