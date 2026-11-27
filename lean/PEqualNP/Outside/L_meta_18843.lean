import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18843

private def inc (p l : Fin 13) : Bool :=
  decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)

private def linePts (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun p => inc p l = true

private def ptLines (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => inc p l = true

private theorem linePts_card (l : Fin 13) : (linePts l).card = 4 := by
  revert l
  decide

private theorem ptLines_card (p : Fin 13) : (ptLines p).card = 4 := by
  revert p
  decide

private theorem linePts_inter_card (l1 l2 : Fin 13) (h : l1 ≠ l2) :
    (linePts l1 ∩ linePts l2).card = 1 := by
  revert l1 l2 h
  decide

private theorem card_union4 (l1 l2 l3 l4 : Fin 13)
    (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h14 : l1 ≠ l4)
    (h23 : l2 ≠ l3) (h24 : l2 ≠ l4) (h34 : l3 ≠ l4) :
    10 ≤ (linePts l1 ∪ linePts l2 ∪ linePts l3 ∪ linePts l4).card := by
  have c1 := linePts_card l1
  have c2 := linePts_card l2
  have c3 := linePts_card l3
  have c4 := linePts_card l4
  have i12 := linePts_inter_card l1 l2 h12
  have i13 := linePts_inter_card l1 l3 h13
  have i23 := linePts_inter_card l2 l3 h23
  have i14 := linePts_inter_card l1 l4 h14
  have i24 := linePts_inter_card l2 l4 h24
  have i34 := linePts_inter_card l3 l4 h34
  have u12 : (linePts l1 ∪ linePts l2).card = 7 := by
    have := Finset.card_union_add_card_inter (linePts l1) (linePts l2)
    omega
  have inter12_3 : ((linePts l1 ∪ linePts l2) ∩ linePts l3).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have := Finset.card_union_le (linePts l1 ∩ linePts l3) (linePts l2 ∩ linePts l3)
    omega
  have u123 : 9 ≤ (linePts l1 ∪ linePts l2 ∪ linePts l3).card := by
    have := Finset.card_union_add_card_inter (linePts l1 ∪ linePts l2) (linePts l3)
    omega
  have inter123_4 : ((linePts l1 ∪ linePts l2 ∪ linePts l3) ∩ linePts l4).card ≤ 3 := by
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
    have hA := Finset.card_union_le ((linePts l1 ∩ linePts l4) ∪ (linePts l2 ∩ linePts l4)) (linePts l3 ∩ linePts l4)
    have hB := Finset.card_union_le (linePts l1 ∩ linePts l4) (linePts l2 ∩ linePts l4)
    omega
  have := Finset.card_union_add_card_inter (linePts l1 ∪ linePts l2 ∪ linePts l3) (linePts l4)
  omega

private theorem exists_four_mem {α : Type*} [DecidableEq α] (S : Finset α) (hS : 4 ≤ S.card) :
    ∃ a b c d : α, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have h1 : 3 ≤ (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase a).card)
  have h2 : 2 ≤ ((S.erase a).erase b).card := by rw [Finset.card_erase_of_mem hb]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase a).erase b).card)
  have h3 : 1 ≤ (((S.erase a).erase b).erase c).card := by rw [Finset.card_erase_of_mem hc]; omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (((S.erase a).erase b).erase c).card)
  rw [Finset.mem_erase] at hd
  obtain ⟨hdc, hd'⟩ := hd
  rw [Finset.mem_erase] at hd'
  obtain ⟨hdb, hd''⟩ := hd'
  rw [Finset.mem_erase] at hd''
  obtain ⟨hda, hdS⟩ := hd''
  rw [Finset.mem_erase] at hc
  obtain ⟨hcb, hc'⟩ := hc
  rw [Finset.mem_erase] at hc'
  obtain ⟨hca, hcS⟩ := hc'
  rw [Finset.mem_erase] at hb
  obtain ⟨hba, hbS⟩ := hb
  exact ⟨a, b, c, d, ha, hbS, hcS, hdS, hba.symm, hca.symm, hda.symm, hcb.symm, hdb.symm, hdc.symm⟩

theorem main_proof :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
      (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
        (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧
        (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
      ∀ (x4 : Finset (Fin (26 : ℕ))),
        (∀ (x5 x6 : Fin (26 : ℕ)), x1.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) →
        (∃ (x6 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x6 ∈ x4) →
        (∃ (x7 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x7 ∈ x4) →
        (14 : ℕ) ≤ x4.card) := by
  intro G _ hAdj K hCov ⟨p0, hp0⟩ ⟨l0, hl0⟩
  let A : Finset (Fin 13) := Finset.univ.filter fun p => Fin.castAdd 13 p ∈ K
  let B : Finset (Fin 13) := Finset.univ.filter fun l => Fin.natAdd 13 l ∈ K
  have hKcard : K.card = A.card + B.card := by
    let KA : Finset (Fin 26) := A.image (Fin.castAdd 13)
    let KB : Finset (Fin 26) := B.image (Fin.natAdd 13)
    have hKA : KA.card = A.card := Finset.card_image_of_injective _ (Fin.castAdd_injective 13 13)
    have hKB : KB.card = B.card := Finset.card_image_of_injective _ (Fin.natAdd_injective 13 13)
    have hDisj : Disjoint KA KB := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hxA
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hxB
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have := p.isLt
      omega
    have hUnion : KA ∪ KB = K := by
      ext x
      simp only [Finset.mem_union, KA, KB, A, B, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
        · exact hp
        · exact hl
      · intro hx
        by_cases hlt : x.val < 13
        · left
          refine ⟨⟨x.val, hlt⟩, ?_, Fin.ext (by simp)⟩
          have : Fin.castAdd 13 (⟨x.val, hlt⟩ : Fin 13) = x := Fin.ext (by simp)
          rwa [this]
        · right
          refine ⟨⟨x.val - 13, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
          have : Fin.natAdd 13 (⟨x.val - 13, by omega⟩ : Fin 13) = x := Fin.ext (by simp; omega)
          rwa [this]
    rw [← hUnion, Finset.card_union_of_disjoint hDisj, hKA, hKB]
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩⟩
  have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl0⟩⟩
  have hIncCov : ∀ p l : Fin 13, inc p l = true → p ∈ A ∨ l ∈ B := by
    intro p l hI
    have hIp : p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := of_decide_eq_true hI
    have hadj : G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) :=
      (hAdj _ _).mpr ⟨p, l, hIp, Or.inl ⟨rfl, rfl⟩⟩
    rcases hCov _ _ hadj with hp | hl
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  by_contra hlt14
  have hle13 : A.card + B.card ≤ 13 := by omega
  let Ac : Finset (Fin 13) := Finset.univ \ A
  let Bc : Finset (Fin 13) := Finset.univ \ B
  have hAc : Ac.card = 13 - A.card := by
    simp [Ac, Finset.card_sdiff]
  have hBc : Bc.card = 13 - B.card := by
    simp [Bc, Finset.card_sdiff]
  have hA4 : 4 ≤ A.card := by
    obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < Bc.card)
    have hlnot : l ∉ B := (Finset.mem_sdiff.mp hl).2
    have hsub : linePts l ⊆ A := by
      intro p hp
      have hI : inc p l = true := (Finset.mem_filter.mp hp).2
      exact (hIncCov p l hI).resolve_right hlnot
    have := Finset.card_le_card hsub
    rw [linePts_card l] at this
    exact this
  have hB4 : 4 ≤ B.card := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < Ac.card)
    have hpnot : p ∉ A := (Finset.mem_sdiff.mp hp).2
    have hsub : ptLines p ⊆ B := by
      intro l hl
      have hI : inc p l = true := (Finset.mem_filter.mp hl).2
      exact (hIncCov p l hI).resolve_left hpnot
    have := Finset.card_le_card hsub
    rw [ptLines_card p] at this
    exact this
  have hBc4 : 4 ≤ Bc.card := by omega
  obtain ⟨l1, l2, l3, l4, hl1, hl2, hl3, hl4, h12, h13, h14, h23, h24, h34⟩ := exists_four_mem Bc hBc4
  have hsubOf : ∀ l ∈ Bc, linePts l ⊆ A := by
    intro l hl p hp
    have hlnot : l ∉ B := (Finset.mem_sdiff.mp hl).2
    have hI : inc p l = true := (Finset.mem_filter.mp hp).2
    exact (hIncCov p l hI).resolve_right hlnot
  have hUsub : linePts l1 ∪ linePts l2 ∪ linePts l3 ∪ linePts l4 ⊆ A := by
    refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ ?_) ?_) ?_
    · exact hsubOf l1 hl1
    · exact hsubOf l2 hl2
    · exact hsubOf l3 hl3
    · exact hsubOf l4 hl4
  have hA10 : 10 ≤ A.card := (card_union4 l1 l2 l3 l4 h12 h13 h14 h23 h24 h34).trans (Finset.card_le_card hUsub)
  omega

end PEqualNP.Outside.L_meta_18843

theorem PEqualNP.Outside.L_meta_18843 : (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : Finset (Fin (26 : ℕ))), (∀ (x5 x6 : Fin (26 : ℕ)), x1.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → (∃ (x6 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x6 ∈ x4) → (∃ (x7 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x7 ∈ x4) → (14 : ℕ) ≤ x4.card) :=
  PEqualNP.Outside.L_meta_18843.main_proof
