import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3469_73
    (extract : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ l, (S l).card = q+1) → IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ l, C.eval (incidenceInput (S l)ᶜ {l}) = false) →
      100*C.size < n*q → ∃ (pref tail : List Gate) (a b : ℕ) (lines : Finset (Fin n)),
        C.gates = pref ++ ⟨.or,[a,b]⟩ :: tail ∧ 101 ≤ lines.card ∧
        ∀ l ∈ lines, let v := fun (i : ℕ) (X : Finset (Fin n)) =>
          (⟨pref,i⟩ : Circuit).eval (incidenceInput X {l})
        v a (S l)ᶜ = false ∧ v b (S l)ᶜ = false ∧
        (∃ p ∈ S l, v a {p} = true ∧ v b {p} = false) ∧
        ∃ p ∈ S l, v a {p} = false ∧ v b {p} = true)
    (crossingBound : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2 + q + 1 →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → (∀ l, (S l).card = q+1) → IsAO2 (n+n) C → RightOnIncidentPairs S C →
      n+n ≤ C.output → (C.gates[C.output - (n+n)]?).map Gate.op = some .and →
      (∀ Y, Y.card ≤ q → C.eval (incidenceInput (zeroSet S Y) Y) = false) →
      (∃ (pref tail : List Gate) (a b : ℕ) (lines : Finset (Fin n)),
        C.gates = pref ++ ⟨.or,[a,b]⟩ :: tail ∧ 101 ≤ lines.card ∧
        ∀ l ∈ lines, let v := fun (i : ℕ) (X : Finset (Fin n)) =>
          (⟨pref,i⟩ : Circuit).eval (incidenceInput X {l})
        v a (S l)ᶜ = false ∧ v b (S l)ᶜ = false ∧
        (∃ p ∈ S l, v a {p} = true ∧ v b {p} = false) ∧
        ∃ p ∈ S l, v a {p} = false ∧ v b {p} = true) → n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hline hjoin hc hout _ ho hpos hneg
  classical
  have hs (l : Fin n) : C.eval (incidenceInput (S l)ᶜ {l}) = false := by
    apply hneg
    · simp; omega
    · intro m hm
      obtain rfl := Finset.mem_singleton.mp hm
      exact disjoint_compl_right
  have hmax (Y : Finset (Fin n)) (hy : Y.card ≤ q) :
      C.eval (incidenceInput (zeroSet S Y) Y) = false := by
    apply hneg _ _ hy
    intro l hl
    apply Finset.disjoint_left.mpr
    intro p hp hz
    exact (Finset.mem_filter.mp hz).2 l hl hp
  by_contra! hsmall
  obtain ⟨g,hg,hop⟩ := ho
  have htag : (C.gates[C.output - (n+n)]?).map Gate.op = some .and := by simp [hg,hop]
  have hx := extract q n S C hline hc hpos hs hsmall
  exact (Nat.not_lt_of_ge (crossingBound q n S C hq hn hjoin hline hc hpos hout htag hmax hx)) hsmall
