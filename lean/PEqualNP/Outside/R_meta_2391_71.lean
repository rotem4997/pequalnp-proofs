import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2391_71
    (hsize : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨
          b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) →
      PEqualNP.TopForm.IsLeastAO G C → C.size ≤ 64)
    (hcover : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨
          b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.junk G C ≠ ∅ →
      ∃ K : Finset (Fin 26), (∀ a b, G.Adj a b → a ∈ K ∨ b ∈ K) ∧
        (∃ p : Fin 13, Fin.castAdd 13 p ∈ K) ∧
        (∃ l : Fin 13, Fin.natAdd 13 l ∈ K) ∧ 52 + K.card ≤ C.size + 1) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ := by
  classical
  intro G _ C hgraph hleast
  by_contra hjunk
  obtain ⟨K, hcov, ⟨p, hp⟩, ⟨l, hl⟩, hcost⟩ := hcover G C hgraph hleast hjunk
  have hsmall : K.card ≤ 13 := by
    have hbound := hsize G C hgraph hleast
    omega
  have hdisjoint (i j : Fin 13) : Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  have hexact (d : Fin 13) (hd : d = 0 ∨ d = 1) (i : Fin 13) :
      Fin.castAdd 13 (i + d) ∈ K ↔ Fin.natAdd 13 i ∉ K := by
    have hadj (j : Fin 13) : G.Adj (Fin.castAdd 13 (j + d)) (Fin.natAdd 13 j) := by
      apply (hgraph _ _).mpr
      refine ⟨j + d, j, ?_, Or.inl ⟨rfl, rfl⟩⟩
      rcases hd with rfl | rfl
      · exact Or.inl (Fin.add_zero j)
      · exact Or.inr (Or.inl rfl)
    let chooseVertex (j : Fin 13) : Fin 26 :=
      if Fin.castAdd 13 (j + d) ∈ K then Fin.castAdd 13 (j + d) else Fin.natAdd 13 j
    have hinj : Function.Injective chooseVertex := by
      intro a b hab
      by_cases ha : Fin.castAdd 13 (a + d) ∈ K <;>
        by_cases hb : Fin.castAdd 13 (b + d) ∈ K <;>
        simp only [chooseVertex, ha, hb, ite_eq_left, ite_eq_right] at hab
      · have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd] at hval
        simp only [Fin.val_add] at hval
        exact Fin.ext (by omega)
      · exact (hdisjoint _ _ hab).elim
      · exact (hdisjoint _ _ hab.symm).elim
      · have hval := congrArg Fin.val hab
        change 13 + _ = 13 + _ at hval
        exact Fin.ext (by omega)
    have hsub : Finset.univ.image chooseVertex ⊆ K := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      by_cases hh : Fin.castAdd 13 (j + d) ∈ K
      · simpa only [chooseVertex, ite_eq_left hh] using hh
      · simpa only [chooseVertex, ite_eq_right hh] using
          (hcov _ _ (hadj j)).resolve_left hh
    have hcard : (Finset.univ.image chooseVertex).card = 13 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have himage : Finset.univ.image chooseVertex = K :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hsmall)
    constructor
    · intro hpoint hline
      have hm : Fin.natAdd 13 i ∈ Finset.univ.image chooseVertex := by rw [himage]; exact hline
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      by_cases hjp : Fin.castAdd 13 (j + d) ∈ K
      · exact hdisjoint _ _ (by simpa only [chooseVertex, ite_eq_left hjp] using hj)
      · have hj' : Fin.natAdd 13 j = Fin.natAdd 13 i := by
          simpa only [chooseVertex, ite_eq_right hjp] using hj
        have hval := congrArg Fin.val hj'
        change 13 + _ = 13 + _ at hval
        have hji : j = i := Fin.ext (by omega)
        exact hjp (hji.symm ▸ hpoint)
    · intro hline
      exact (hcov _ _ (hadj i)).resolve_right hline
  have hstep (i : Fin 13) :
      Fin.castAdd 13 (i + 1) ∈ K ↔ Fin.castAdd 13 i ∈ K := by
    have hz : Fin.castAdd 13 i ∈ K ↔ Fin.natAdd 13 i ∉ K := by
      simpa only [Fin.add_zero] using hexact 0 (Or.inl rfl) i
    exact (hexact 1 (Or.inr rfl) i).trans hz.symm
  have hwalk (k : ℕ) : Fin.castAdd 13 (Fin.ofNat 13 k) ∈ K ↔ Fin.castAdd 13 (0 : Fin 13) ∈ K := by
    induction k with
    | zero => rfl
    | succ k ih =>
        have hone : (1 : Fin 13).val = (1 : ℕ) := rfl
        simpa only [Fin.ofNat_add, Nat.succ_eq_add_one, hone] using
          (hstep (Fin.ofNat 13 k)).trans ih
  have hall (i : Fin 13) : Fin.castAdd 13 i ∈ K ↔ Fin.castAdd 13 (0 : Fin 13) ∈ K := by
    simpa using hwalk i.val
  have hpoint := (hall l).mpr ((hall p).mp hp)
  have hnotline := (hexact 0 (Or.inl rfl) l).mp (by simpa only [Fin.add_zero] using hpoint)
  exact hnotline hl
