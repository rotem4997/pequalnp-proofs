import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3600_672
    (trace : ∀ (d : ℕ) (C : Circuit) (A : Type) (x : A → Fin d → Bool),
      Monotone2 C →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < d + j) →
      ∃ W : ℕ → Set A,
        (∀ i : Fin d, W i.val = {t | x t i = true}) ∧
        (∀ j < C.size, ∃ a b : ℕ, a < b ∧ b < d + j ∧
          (W (d + j) = W a ∩ W b ∨ W (d + j) = W a ∪ W b)) ∧
        (∀ t : A, t ∈ W C.output ↔ circuitFun d C (x t) = true))
    (bound : ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R]
      (m o : ℕ) (W : ℕ → Set ((Fin n × Fin n) ⊕ Finset (Fin n))),
      300 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l : Fin n, Fintype.card {p : Fin n // R p l} = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, R p l ∧ R r l) →
      o < n + n + m →
      (∀ p : Fin n, W p.val = {t | Sum.elim (fun e => e.1 = p)
        (fun B => ∀ l ∈ B, ¬ R p l) t}) →
      (∀ l : Fin n, W (n + l.val) = {t | Sum.elim (fun e => e.2 = l)
        (fun B => l ∈ B) t}) →
      (∀ j < m, ∃ a b : ℕ, a < b ∧ b < n + n + j ∧
        (W (n + n + j) = W a ∩ W b ∨ W (n + n + j) = W a ∪ W b)) →
      (∀ p l : Fin n, R p l → Sum.inl (p, l) ∈ W o) →
      (∀ B : Finset (Fin n), B.card ≤ q → Sum.inr B ∉ W o) →
      n * q ≤ 100 * m) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R inst C hq hn hcol hmeet hm _ hout _ hpairs hpos hneg
  classical
  let X : ((Fin n × Fin n) ⊕ Finset (Fin n)) → Fin (n + n) → Bool :=
    Sum.elim (fun e z => decide (z = Fin.castAdd n e.1 ∨ z = Fin.natAdd n e.2))
      (fun B => Fin.addCases (fun p => decide (∀ l ∈ B, ¬ R p l))
        (fun l => decide (l ∈ B)))
  obtain ⟨W, hinputs, hsteps, houtput⟩ := trace (n+n) C _ X hm hpairs
  have sep (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  apply bound q n R C.size C.output W hq hn hcol hmeet hout
  · intro p
    rw [show p.val = (Fin.castAdd n p).val from rfl, hinputs]
    ext t
    cases t with
    | inl e =>
      change decide (Fin.castAdd n p = Fin.castAdd n e.1 ∨ Fin.castAdd n p = Fin.natAdd n e.2) = true ↔ e.1 = p
      simp only [decide_eq_true_eq, sep, or_false]
      exact ⟨fun h => Fin.ext ((congrArg Fin.val h).symm), fun h => h ▸ rfl⟩
    | inr B => simp only [Set.mem_ofPred_eq, Sum.elim, X, Fin.addCases_left, decide_eq_true_eq]
  · intro l
    rw [show n + l.val = (Fin.natAdd n l).val from rfl, hinputs]
    ext t
    cases t with
    | inl e =>
      change decide (Fin.natAdd n l = Fin.castAdd n e.1 ∨ Fin.natAdd n l = Fin.natAdd n e.2) = true ↔ e.2 = l
      simp only [decide_eq_true_eq, (sep _ _).symm, false_or]
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hv
        apply Fin.ext
        omega
      · intro h
        rw [h]
    | inr B => simp only [Set.mem_ofPred_eq, Sum.elim, X, Fin.addCases_right, decide_eq_true_eq]
  · exact hsteps
  · intro p l h
    exact (houtput _).mpr (hpos p l h)
  · intro B hB ht
    have hsize : Fintype.card {l : Fin n // X (.inr B) (Fin.natAdd n l) = true} = B.card := by
      simp only [X, Sum.elim, Fin.addCases_right, decide_eq_true_eq]
      exact Fintype.card_coe B
    have hfree : ¬ ∃ p l : Fin n, R p l ∧ X (.inr B) (Fin.castAdd n p) = true ∧
        X (.inr B) (Fin.natAdd n l) = true := by
      rintro ⟨p, l, hpl, hp, hl⟩
      simp only [X, Sum.elim, Fin.addCases_left, decide_eq_true_eq] at hp
      simp only [X, Sum.elim, Fin.addCases_right, decide_eq_true_eq] at hl
      exact hp l hl hpl
    have hf := hneg (X (.inr B)) (hsize.le.trans hB) hfree
    have ht' := (houtput _).mp ht
    rw [hf] at ht'
    contradiction
