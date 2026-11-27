import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK PEqualNP.GenericRejection
open PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_4704_1
    (h_line : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
      IsAO2 (N + N) C →
      C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ P L : Finset (Fin N), L.card ≤ q → IsFalseInput S P L → C.eval (incidenceInput P L) = false) →
      ((incidences S).filter fun e => lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = true).card ≤ 38 * C.size)
    (h_point : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
      IsAO2 (N + N) C →
      C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ P L : Finset (Fin N), L.card ≤ q → IsFalseInput S P L → C.eval (incidenceInput P L) = false) →
      ((incidences S).filter fun e => lineSingle C (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = true).card ≤ 38 * C.size)
    (h_dbl : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
      IsAO2 (N + N) C →
      ¬ IsReadK (N + N) C 2 →
      C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ P L : Finset (Fin N), L.card ≤ q → IsFalseInput S P L → C.eval (incidenceInput P L) = false) →
      (∀ D : Circuit, IsAO2 (N + N) D → D.output < N + N + D.size →
        (∀ P L : Finset (Fin N), D.eval (incidenceInput P L) = C.eval (incidenceInput P L)) →
        C.size ≤ D.size) →
      ((incidences S).filter fun e =>
        lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = false).card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 → x14.output < x2 + x2 + x14.size → (∀ (x17 x18 : Finset (Fin x2)), x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) = x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) → x4.size ≤ x14.size) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN hcard huniq hao hnotr2 hout hright hsound hmin
  let E_line := (incidences S).filter fun e =>
    lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = true
  let E_point := (incidences S).filter fun e =>
    lineSingle C (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = true
  let E_dbl := (incidences S).filter fun e =>
    lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = false
  have h1 : E_line.card ≤ 38 * C.size :=
    h_line q N S C hq hN hcard huniq hao hout hright hsound
  have h2 : E_point.card ≤ 38 * C.size :=
    h_point q N S C hq hN hcard huniq hao hout hright hsound
  have h3 : E_dbl.card ≤ 24 * C.size :=
    h_dbl q N S C hq hN hcard huniq hao hnotr2 hout hright hsound hmin
  have hinc : (incidences S).card = N * (q + 1) := by
    have heq : incidences S = Finset.univ.biUnion (fun l : Fin N => (S l).image (fun p => (p, l))) := by
      ext pl
      rcases pl with ⟨p, l⟩
      change (p, l) ∈ Finset.univ.filter (fun x : Fin N × Fin N => x.1 ∈ S x.2) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · intro hp
        exact ⟨l, p, hp, rfl, rfl⟩
      · rintro ⟨l', p', hp', rfl, rfl⟩
        exact hp'
    rw [heq, Finset.card_biUnion]
    · have hsum : (Finset.univ.sum fun l : Fin N => ((S l).image (fun p => (p, l))).card) =
          Finset.univ.sum fun _ : Fin N => q + 1 := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hcard l]
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · intro l1 _ l2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro pl hmem1 hmem2
      rcases Finset.mem_image.mp hmem1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp hmem2 with ⟨p2, _, hmem2'⟩
      exact hne (Prod.mk.inj hmem2').2.symm
  have hsub : incidences S ⊆ E_line ∪ (E_point ∪ E_dbl) := by
    intro e he
    cases hl : lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val)
    · cases hp : lineSingle C (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hl, hp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hl⟩)
  have hcov : (incidences S).card ≤ E_line.card + (E_point.card + E_dbl.card) := by
    calc (incidences S).card
        ≤ (E_line ∪ (E_point ∪ E_dbl)).card := Finset.card_le_card hsub
      _ ≤ E_line.card + (E_point ∪ E_dbl).card := Finset.card_union_le _ _
      _ ≤ E_line.card + (E_point.card + E_dbl.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
  have hmul : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
