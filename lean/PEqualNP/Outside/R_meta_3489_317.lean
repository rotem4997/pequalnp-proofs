import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3489_317
    (geometry : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2],   have x4 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x4 : Finset (Fin x1)) (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide ¬∃ x7 ∈ x4, x2 x6 x7) (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) x5;   ∀ (x5 : Finset (Fin x1)), Fintype.card { x6 : Fin x1 // x4 x5 (Fin.natAdd x1 x6) = Bool.true } = x5.card ∧ ¬∃ (x6 : Fin x1) (x7 : Fin x1), x2 x6 x7 ∧ x4 x5 (Fin.castAdd x1 x6) = Bool.true ∧ x4 x5 (Fin.natAdd x1 x7) = Bool.true)
    (bound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    87 ≤ q → n = q^2+q+1 →
    (∀ l, Fintype.card {p // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    PEqualNP.TopForm.IsAO2 (n+n) C →
    ∀ (A B : Finset (Fin n)),
    let f := PEqualNP.MetaComplexity.circuitFun (n+n) C
    let T := (A ×ˢ B).filter fun e => I e.1 e.2 ∧
      f (fun i => decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) = true
    7656 < min A.card B.card → 44*(A.card+B.card-1) < T.card →
    (∀ S ⊆ B, S.card ≤ q → f (Fin.addCases
      (fun p => decide (¬ ∃ l ∈ S, I p l)) (fun l => decide (l ∈ S))) = false) →
    T.card ≤ 44*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → ∀ (x12 : Finset (Fin x2 × Fin x2)), (7656 : ℕ) < Min.min (Finset.image Prod.fst x12).card (Finset.image Prod.snd x12).card → (44 : ℕ) * ((Finset.image Prod.fst x12).card + (Finset.image Prod.snd x12).card - (1 : ℕ)) < x12.card → (∀ x15 ∈ x12, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x17 = Fin.castAdd x2 x15.1 ∨ x17 = Fin.natAdd x2 x15.2)) = Bool.true) → x12.card ≤ (44 : ℕ) * x5.size := by
  intro q n I inst C hq hn hdeg hpair hAO sound E hlarge hdense good
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let f := PEqualNP.MetaComplexity.circuitFun (n+n) C
  let T := (A ×ˢ B).filter fun e => I e.1 e.2 ∧
    f (fun i => decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) = true
  have inc : E ⊆ T := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩, good e he⟩
  have count := Finset.card_le_card inc
  apply count.trans
  apply bound q n I C hq hn hdeg hpair hAO A B hlarge (lt_of_lt_of_le hdense count)
  intro S _ hS
  obtain ⟨card, independent⟩ := geometry n I S
  exact sound _ (card.trans_le hS) independent
