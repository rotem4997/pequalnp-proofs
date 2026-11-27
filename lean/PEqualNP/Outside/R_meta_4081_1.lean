import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4081_1
    (lowCap : (let G : SimpleGraph (Fin 11) := (PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        3 ≤ (PEqualNP.TopForm.junk G C).card →
        ∀ g ∈ PEqualNP.TopForm.junk G C,
          ((PEqualNP.TopForm.Ustar G C).filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧
            PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
            ∀ h ∈ PEqualNP.TopForm.junk G C, h < g →
              PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = false).card ≤ 2))
    (doubleCharge : (let G : SimpleGraph (Fin 11) := (PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        3 ≤ (PEqualNP.TopForm.junk G C).card →
        (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G C →
          ∃ g ∈ PEqualNP.TopForm.junk G C,
            PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true) →
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
            2 * (PEqualNP.TopForm.Ustar G C).card →
        ((PEqualNP.TopForm.junk G C).filter fun g => 2 ≤
          ((PEqualNP.TopForm.Ustar G C).filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧
            PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
            ∀ h ∈ PEqualNP.TopForm.junk G C, h < g →
              PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = false).card).card ≤
          2 * (PEqualNP.TopForm.centreless G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C hs hL hT hj hcov _ hB
  set J := PEqualNP.TopForm.junk G C with hJ
  set U := PEqualNP.TopForm.Ustar G C with hU
  set c : ℕ → ℕ := fun g => (U.filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧
      PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      ∀ h ∈ J, h < g →
        PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = false).card
    with hc
  have hcap : ∀ g ∈ J, c g ≤ 2 := lowCap C hs hL hT hj
  have hdbl : (J.filter fun g => 2 ≤ c g).card ≤ 2 * (PEqualNP.TopForm.centreless G C).card +
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card :=
    doubleCharge C hs hL hT hj hcov hB
  have hsub : U ⊆ J.biUnion fun g => U.filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧
      PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      ∀ h ∈ J, h < g →
        PEqualNP.EdgeOwnership.gateVal 11 C h (PEqualNP.EdgeOwnership.pairInput u v) = false := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨g0, hg0, hv0⟩ := hcov u v he
      have hne : (J.filter fun g =>
          PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true).Nonempty :=
        ⟨g0, Finset.mem_filter.mpr ⟨hg0, hv0⟩⟩
      set m := (J.filter fun g =>
          PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true).min' hne
      have hm := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at hm
      refine Finset.mem_biUnion.mpr ⟨m, hm.1, Finset.mem_filter.mpr ⟨he, u, v, rfl, hm.2, ?_⟩⟩
      intro h hh hlt
      by_contra hf
      have hmem : h ∈ (J.filter fun g =>
          PEqualNP.EdgeOwnership.gateVal 11 C g (PEqualNP.EdgeOwnership.pairInput u v) = true) :=
        Finset.mem_filter.mpr ⟨hh, by simpa using hf⟩
      exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr hlt)
  have h1 : U.card ≤ ∑ g ∈ J, c g := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have h2 : ∑ g ∈ J, c g ≤ ∑ g ∈ J, (1 + if 2 ≤ c g then 1 else 0) := by
    apply Finset.sum_le_sum
    intro g hg
    have := hcap g hg
    split_ifs <;> omega
  have h3 : ∑ g ∈ J, (1 + if 2 ≤ c g then 1 else 0) = J.card + (J.filter fun g => 2 ≤ c g).card := by
    rw [Finset.sum_add_distrib, Finset.card_filter]
    simp
  omega
