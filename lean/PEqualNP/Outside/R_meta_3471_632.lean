import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3471_632
    (readOr : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → n ≤ C.output →
      C.output < n + C.size →
      (∃ g : Gate, C.gates[C.output - n]? = some g ∧ g.op = GateOp.or) →
      ∃ i j : ℕ, i < C.output ∧ j < C.output ∧
        ∀ x : List Bool, x.length = n → C.eval x =
          ((C.wires x).getD i false || (C.wires x).getD j false))
    (partialBound : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (i : ℕ),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p p' : Fin n, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      IsAO2 (n+n) C → i < C.output → C.output < n+n+C.size →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
        (C.wires (incidenceInput X Y)).getD i false = false) →
      n * (q+1) ≤ 2 * (∑ l, ((S l).filter fun p =>
        (C.wires (incidenceInput {p} {l})).getD i false).card) →
      n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C large order sizes unique basis lo hi gate yes no
  obtain ⟨i,j,ilt,jlt,read⟩ := readOr (n+n) C basis lo hi gate
  let accepted (w : ℕ) (l : Fin n) := (S l).filter fun p =>
    (C.wires (incidenceInput {p} {l})).getD w false
  have inputSize (X Y : Finset (Fin n)) : (incidenceInput X Y).length = n+n := by
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin n => decide (l ∈ Y))).length = n+n
    simp only [List.length_append, List.length_ofFn]
  have cover (l : Fin n) : S l ⊆ accepted i l ∪ accepted j l := by
    intro p hp
    have h := yes l p hp
    rw [read _ (inputSize _ _)] at h
    simpa only [accepted, Finset.mem_union, Finset.mem_filter, hp, true_and,
      Bool.or_eq_true] using h
  have count : (∑ l, (S l).card) ≤ (∑ l, ((accepted i l).card + (accepted j l).card)) :=
    Finset.sum_le_sum fun l _ => (Finset.card_le_card (cover l)).trans (Finset.card_union_le _ _)
  have total : n*(q+1) ≤ (∑ l, (accepted i l).card) + (∑ l, (accepted j l).card) := by
    simpa [sizes, Finset.sum_add_distrib] using count
  have half : n*(q+1) ≤ 2*(∑ l, (accepted i l).card) ∨
      n*(q+1) ≤ 2*(∑ l, (accepted j l).card) := by omega
  have sound (X Y : Finset (Fin n)) (hy : Y.card ≤ q) (hf : IsFalseInput S X Y) :=
    no X Y hy hf
  rcases half with h | h
  · apply partialBound q n S C i large order sizes unique basis ilt hi _ h
    intro X Y hy hf
    have both := sound X Y hy hf
    rw [read _ (inputSize _ _), Bool.or_eq_false_iff] at both
    exact both.1
  · apply partialBound q n S C j large order sizes unique basis jlt hi _ h
    intro X Y hy hf
    have both := sound X Y hy hf
    rw [read _ (inputSize _ _), Bool.or_eq_false_iff] at both
    exact both.2
