import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4990_1
    (charge : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) → E.card + M.card ≤ C.size + 1)
    (matchingCover : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)),
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
        (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card + B.card ≤ M.card) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Finset ℕ), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬(x3 x8 x10 ∧ x3 x8 x11 ∧ x3 x9 x10 ∧ x3 x9 x11)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → (∀ x11 ∈ x6, x11 < x1 ∨ ∃ x13 < x5.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs, x14 ∈ x6) → (∀ x12 ∈ x7, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x5.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).inputs, x15 ∈ x7) → (∀ x13 < x5.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x16 : ℕ) (x17 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs = [x16, x17] ∧ x16 ∈ x7 ∧ x17 ∈ x6) → ∃ (x14 : Finset (Fin (x1 + x2))), (∀ (x15 : Fin x1) (x16 : Fin x2), x3 x15 x16 → Fin.castAdd x2 x15 ∈ x14 ∨ Fin.natAdd x1 x16 ∈ x14) ∧ (PEqualNP.ReadTwo.incid x3).card + x14.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m I _ C _ _ hCycle hAO hCorrect _ _ _
  let E : Finset (Fin n × Fin m) := ReadTwo.incid I
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by
    dsimp only [E]
    delta ReadTwo.incid
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨M, A, B, hSub, hFst, hSnd, hCover, hCard⟩ := matchingCover n m E
  have bound := charge n m E M C (by simpa only [mem] using hCycle) hAO
    (by simpa only [mem] using hCorrect) hSub
    (fun _ he _ hf h => hFst _ he _ hf h) (fun _ he _ hf h => hSnd _ he _ hf h)
  let T : Finset (Fin (n + m)) := A.image (Fin.castAdd m) ∪ B.image (Fin.natAdd n)
  refine ⟨T, ?_, ?_⟩
  · intro p l hpl
    rcases hCover (p,l) ((mem p l).2 hpl) with hp | hl
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  · have hT : T.card ≤ A.card + B.card := by
      apply le_trans (Finset.card_union_le _ _)
      exact Nat.add_le_add Finset.card_image_le Finset.card_image_le
    change E.card + T.card ≤ C.size + 1
    omega
