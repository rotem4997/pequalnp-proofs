import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_2984_68
    (geometry :
    ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)), 0 < q →
      N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p p', p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      (∀ p : Fin N, have T : Finset (Fin N) := Finset.univ.filter (fun l => p ∈ S l); T.card = q + 1) ∧
      (∀ l l' : Fin N, l ≠ l' → ∃! p, p ∈ S l ∧ p ∈ S l') ∧
      (∀ Y : Finset (Fin N), Y.card ≤ q →
        have U : Finset (Fin N) := Finset.univ.filter (fun p : Fin N => ∀ l ∈ Y, p ∉ S l); q ≤ U.card))
    (lower : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ p : Fin x2, have T : Finset (Fin x2) := Finset.univ.filter (fun l => p ∈ x3 l); T.card = x1 + 1) → (∀ l l' : Fin x2, l ≠ l' → ∃! p, p ∈ x3 l ∧ p ∈ x3 l') → (∀ Y : Finset (Fin x2), Y.card ≤ x1 → have U : Finset (Fin x2) := Finset.univ.filter (fun p : Fin x2 => ∀ l ∈ Y, p ∉ x3 l); x1 ≤ U.card) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ Y : Finset (Fin x2), Y.card ≤ x1 → x4.eval (incidenceInput (Finset.univ.filter (fun p : Fin x2 => ∀ l ∈ Y, p ∉ x3 l)) Y) = false) → x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN hCard hUnique hAO hOut hPos hNeg
  obtain ⟨hDegree, hDual, hAvoid⟩ := geometry q N S (by omega) hN hCard hUnique
  have hBig : 1 < N := by rw [hN]; omega
  let z : Fin N := ⟨0, by omega⟩
  let o : Fin N := ⟨1, hBig⟩
  have other (a : Fin N) : ∃ b : Fin N, b ≠ a := by
    by_cases ha : a = z
    · refine ⟨o, ?_⟩
      rw [ha]
      intro h
      have bad := congrArg Fin.val h
      change 1 = 0 at bad
      omega
    · exact ⟨z, Ne.symm ha⟩
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have retain (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hlen : (step w g).length = w.length + 1 := by simp [step]
      rw [List.foldl_cons, ih (step w g) (by omega)]
      exact List.getD_append _ _ _ _ hj
  have hGate : N + N ≤ C.output := by
    by_contra! hout
    have val (p l : Fin N) : C.eval (incidenceInput {p} {l}) =
          (incidenceInput {p} {l}).getD C.output false := by
      change (C.gates.foldl step _).getD C.output false = _
      apply retain
      change C.output < ((List.ofFn fun i : Fin N => decide (i ∈ ({p} : Finset (Fin N)))) ++
        List.ofFn fun j : Fin N => decide (j ∈ ({l} : Finset (Fin N)))).length
      simpa using hout
    rcases lt_or_ge C.output N with h | h
    · let p : Fin N := ⟨C.output, h⟩
      obtain ⟨p', hne⟩ := other p
      obtain ⟨l, hl⟩ := Finset.card_pos.mp (by rw [hDegree p']; omega :
        0 < (Finset.univ.filter (fun l => p' ∈ S l)).card)
      have hp : p' ∈ S l := (Finset.mem_filter.mp hl).2
      have v := hPos l p' hp
      rw [val] at v
      change ((List.ofFn fun i : Fin N => decide (i ∈ ({p'} : Finset (Fin N)))) ++
        List.ofFn fun j : Fin N => decide (j ∈ ({l} : Finset (Fin N)))).getD C.output false = true at v
      rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simpa using h)] at v
      have hpEq : p = p' := by simpa using v
      exact hne hpEq.symm
    · let l : Fin N := ⟨C.output - N, by omega⟩
      obtain ⟨l', hne⟩ := other l
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hCard l']; omega : 0 < (S l').card)
      have v := hPos l' p hp
      rw [val] at v
      change ((List.ofFn fun i : Fin N => decide (i ∈ ({p} : Finset (Fin N)))) ++
        List.ofFn fun j : Fin N => decide (j ∈ ({l'} : Finset (Fin N)))).getD C.output false = true at v
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h)] at v
      simp only [List.length_ofFn] at v
      rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; omega)] at v
      have hlEq : l = l' := by simpa using v
      exact hne hlEq.symm
  apply lower q N S C hq hN hCard hUnique hDegree hDual hAvoid hAO hGate hOut hPos
  intro Y hY
  apply hNeg _ Y hY
  intro l hl
  exact Finset.disjoint_left.mpr (fun p hp hmiss => (Finset.mem_filter.mp hmiss).2 l hl hp)
