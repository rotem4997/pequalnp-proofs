import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- If forcing a gate to zero loses at most 44 pairs, a smaller counterexample survives.
theorem PEqualNP.Outside.R_meta_3489_463
    (discard : ∀ (n : ℕ) (D : Circuit) (j : Fin D.size), IsAO2 n D →
      let Z : Circuit := ⟨D.gates.set j.val ⟨GateOp.or, []⟩, D.output⟩
      ∃ D' : Circuit, IsAO2 n D' ∧ D'.size < D.size ∧
        circuitFun n D' = circuitFun n Z ∧
        ∀ z, circuitFun n D' z = true → circuitFun n D z = true)
    (critical : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      87 ≤ q → N = q^2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N + N) D →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) D z = false) →
      ∀ T : Finset (Fin N × Fin N),
        (∀ e ∈ T, I e.1 e.2 ∧ circuitFun (N + N) D
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
        (∀ j : Fin D.size, 44 < (T.filter fun e => circuitFun (N + N)
          ⟨D.gates.set j.val ⟨GateOp.or, []⟩, D.output⟩
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = false).card) →
        T.card ≤ 44 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → ∀ (x12 : Finset (Fin x2 × Fin x2)), (7656 : ℕ) < Min.min (Finset.image Prod.fst x12).card (Finset.image Prod.snd x12).card → (44 : ℕ) * ((Finset.image Prod.fst x12).card + (Finset.image Prod.snd x12).card - (1 : ℕ)) < x12.card → (∀ x15 ∈ x12, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x17 = Fin.castAdd x2 x15.1 ∨ x17 = Fin.natAdd x2 x15.2)) = Bool.true) → x12.card ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I instI D hq hN hcol huni hAO hsound E _ _ hE
  let n : ℕ := N + N
  let edge (e : Fin N × Fin N) (i : Fin n) : Bool :=
    decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
  let sound (C : Circuit) : Prop := ∀ z : Fin n → Bool,
    Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
    (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    circuitFun n C z = false
  let accepts (C : Circuit) (T : Finset (Fin N × Fin N)) : Prop :=
    ∀ e ∈ T, I e.1 e.2 ∧ circuitFun n C (edge e) = true
  let zeroGate (C : Circuit) (j : Fin C.size) : Circuit :=
    ⟨C.gates.set j.val ⟨GateOp.or, []⟩, C.output⟩
  have bound : ∀ (s : ℕ) (C : Circuit), C.size = s → IsAO2 n C →
      sound C → ∀ T, accepts C T → T.card ≤ 44 * s := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro C hsize ha hf T ht
      by_cases hall : ∀ j : Fin C.size, 44 <
          (T.filter fun e => circuitFun n (zeroGate C j) (edge e) = false).card
      · rw [← hsize]
        exact critical q N I C hq hN hcol huni ha hf T ht hall
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        obtain ⟨C', ha', hlt, heq, hle⟩ := discard n C j ha
        change circuitFun n C' = circuitFun n (zeroGate C j) at heq
        let U := T.filter fun e => circuitFun n (zeroGate C j) (edge e) = true
        have hf' : sound C' := by
          intro z hz havoid
          cases h : circuitFun n C' z with
          | false => rfl
          | true =>
            have hc := hle z h
            rw [hf z hz havoid] at hc
            cases hc
        have ht' : accepts C' U := by
          intro e he
          obtain ⟨heT, heZ⟩ := Finset.mem_filter.mp he
          refine ⟨(ht e heT).1, ?_⟩
          rw [heq]
          exact heZ
        have hu := ih C'.size (hsize ▸ hlt) C' rfl ha' hf' U ht'
        have hsplit := Finset.card_filter_add_card_filter_not (s := T)
          (fun e => circuitFun n (zeroGate C j) (edge e) = true)
        have hnot : (T.filter fun e => ¬ circuitFun n (zeroGate C j) (edge e) = true) =
            (T.filter fun e => circuitFun n (zeroGate C j) (edge e) = false) := by
          ext e
          simp only [Finset.mem_filter, Bool.not_eq_true]
        rw [hnot] at hsplit
        change U.card + (T.filter fun e => circuitFun n (zeroGate C j) (edge e) = false).card =
          T.card at hsplit
        omega
  exact bound D.size D rfl hAO hsound E hE
