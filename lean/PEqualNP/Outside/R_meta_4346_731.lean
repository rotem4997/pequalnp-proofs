import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4346_731
    (lineOnceBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      1 ≤ q →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ∃ a : Fin 4, [a.val, 1] ∈ (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []}
        ≤ 8 * C.size + N)
    (residualBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      (∀ p l, I p l → circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      100 * C.size < N * q →
      42 * C.size < Fintype.card {e : Fin N × Fin N //
        let v := (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
        I e.1 e.2 ∧ [2, 2] ∉ v ∧ ∀ a : Fin 4, [a.val, 1] ∉ v} → False) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : ℕ :=     Fintype.card       { x6 : Fin x2 × Fin x2 //         have x7 : List (List ℕ) := (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x6.1, x2 + ↑x6.2] (2 : ℕ)).getD x5.output [];         x3 x6.1 x6.2 ∧ ([(2 : ℕ), (2 : ℕ)] ∈ x7 ∨ [(1 : ℕ), (1 : ℕ)] ∈ x7 ∨ [(2 : ℕ), (1 : ℕ)] ∈ x7) };   (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x6 < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C postedTraces hq shape degree joins ao accept reject few
  classical
  by_contra! small
  let vec (e : Fin N × Fin N) :=
    (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
  let traces := Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
    ([2, 2] ∈ vec e ∨ [1, 1] ∈ vec e ∨ [2, 1] ∈ vec e)}
  have hFew : 2 * traces < N * q := few
  have hOnce := lineOnceBound q N I C (by omega) joins ao reject
  let all : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  let twice : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => I e.1 e.2 ∧ [2, 2] ∈ vec e)
  let once : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ a : Fin 4, [a.val, 1] ∈ vec e)
  let residual : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => I e.1 e.2 ∧ [2, 2] ∉ vec e ∧ ∀ a : Fin 4, [a.val, 1] ∉ vec e)
  have total : all.card = N * (q + 1) := by
    let flag : {e : Fin N × Fin N // I e.1 e.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
      { toFun := fun e => ⟨e.val.2, e.val.1, e.property⟩
        invFun := fun e => ⟨(e.2.val, e.1), e.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have card := Fintype.card_congr flag
    rw [Fintype.card_sigma] at card
    simpa [all, Fintype.card_subtype, degree] using card
  have fewTwice : twice.card ≤ traces := by
    unfold traces
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro e he
    obtain ⟨hi, hv⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, Or.inl hv⟩
  have onceBudget : once.card ≤ 8 * C.size + N := by
    rw [Fintype.card_subtype] at hOnce
    exact hOnce
  have covered : all ⊆ (twice ∪ once) ∪ residual := by
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    by_cases hTwice : [2, 2] ∈ vec e
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hTwice⟩))
    by_cases hOncePair : ∃ a : Fin 4, [a.val, 1] ∈ vec e
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hOncePair⟩))
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hTwice,
      fun a ha => hOncePair ⟨a, ha⟩⟩)
  have coverBudget := (Finset.card_le_card covered).trans (Finset.card_union_le (twice ∪ once) residual)
  have unionBudget := Finset.card_union_le twice once
  rw [total, Nat.mul_add, Nat.mul_one] at coverBudget
  have many : 42 * C.size < residual.card := by omega
  apply residualBound q N I C hq shape degree joins ao accept reject small
  rw [Fintype.card_subtype]
  exact many
