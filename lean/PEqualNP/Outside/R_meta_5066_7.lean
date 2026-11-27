import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5066_7 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D ∧
        PEqualNP.TopForm.TopForm G D ∧
        D.size ≤ C.size) →
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1))
       (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      (∀ a b : Fin (x1 + x1), G.Adj a b ↔ ∃ u v : Fin x1, (u, v) ∈ x2 ∧
        ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨ (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v))) →
      PEqualNP.TopForm.IsLeastAO G D →
      PEqualNP.TopForm.TopForm G D →
      PEqualNP.TopForm.junk G D = ∅ →
      x2.card + x1 ≤ D.size + (1 : ℕ)) →
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1))
       (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
      x1 < x2.card →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧
        ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) →
      (∀ a b : Fin (x1 + x1), G.Adj a b ↔ ∃ u v : Fin x1, (u, v) ∈ x2 ∧
        ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨ (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v))) →
      PEqualNP.TopForm.IsLeastAO G D →
      PEqualNP.TopForm.TopForm G D →
      PEqualNP.TopForm.junk G D = {g} →
      x2.card + x1 ≤ D.size + (1 : ℕ)) →
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1))
       (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧
        ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) →
      (∀ a b : Fin (x1 + x1), G.Adj a b ↔ ∃ u v : Fin x1, (u, v) ∈ x2 ∧
        ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨ (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v))) →
      PEqualNP.TopForm.IsLeastAO G D →
      PEqualNP.TopForm.TopForm G D →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk G D).card →
      x2.card + x1 ≤ D.size + (1 : ℕ)) →
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧ ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro hTopForm hZeroJunk hOneJunk hMultiJunk x1 x2 x3 x4 hcard _ hc4 hmatch hAO hfun hdeg
  let adj : Fin (x1 + x1) → Fin (x1 + x1) → Prop := fun a b =>
    ∃ u v : Fin x1, (u, v) ∈ x2 ∧
      ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨
       (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v))
  let G : SimpleGraph (Fin (x1 + x1)) :=
    { Adj := adj
      symm := ⟨by
        rintro a b ⟨u, v, huv, hor⟩
        exact ⟨u, v, huv, hor.symm⟩⟩
      loopless := ⟨by
        rintro a ⟨u, v, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega⟩ }
  have hG : ∀ a b : Fin (x1 + x1), G.Adj a b ↔
      ∃ u v : Fin x1, (u, v) ∈ x2 ∧
        ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨
         (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v)) := fun _ _ => Iff.rfl
  have hne : G.edgeFinset.Nonempty := by
    obtain ⟨⟨u, v⟩, huv⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hcard)
    refine ⟨s(Fin.castAdd x1 u, Fin.natAdd x1 v), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨u, v, huv, Or.inl ⟨rfl, rfl⟩⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hfun z]
    change decide (∃ u v : Fin x1, (u, v) ∈ x2 ∧ z (Fin.castAdd x1 u) = true ∧ z (Fin.natAdd x1 v) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x1))), z a = true) ||
       decide (∃ a b : Fin (x1 + x1), G.Adj a b ∧ z a = true ∧ z b = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨Fin.castAdd x1 u, Fin.natAdd x1 v, ⟨u, v, huv, Or.inl ⟨rfl, rfl⟩⟩, hu, hv⟩
    · rintro ⟨a, b, ⟨u, v, huv, hor⟩, ha, hb⟩
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, v, huv, ha, hb⟩
      · exact ⟨u, v, huv, hb, ha⟩
  obtain ⟨D, hLeast, hTF, hsize⟩ := hTopForm (x1 + x1) G x4 hne hAO hcfun
  have hD : x2.card + x1 ≤ D.size + 1 := by
    by_cases hj0 : (PEqualNP.TopForm.junk G D).card = 0
    · exact hZeroJunk x1 x2 x3 G D hcard hc4 hmatch hG hLeast hTF (Finset.card_eq_zero.mp hj0)
    · by_cases hj1 : (PEqualNP.TopForm.junk G D).card = 1
      · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
        exact hOneJunk x1 x2 x3 G D g hcard hc4 hmatch hdeg hG hLeast hTF hg
      · exact hMultiJunk x1 x2 x3 G D hcard hc4 hmatch hdeg hG hLeast hTF (by omega)
  omega
