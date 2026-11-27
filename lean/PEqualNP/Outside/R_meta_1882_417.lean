import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Every uncovered edge in Ustar must activate some junk AND gate.
-- Light junk gates (hitting at most 4 edges of Ustar) contribute at most 4 * C.size edges in total.
-- The remaining edges of Ustar split into those hit by bottom-level heavy junk gates (no junk gate
-- in their strict cone, hence pure OR-cones under TopForm) and upper-level (nested) heavy junk gates.
theorem PEqualNP.Outside.R_meta_1882_417
    (hCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C →
      ∀ e ∈ Ustar G C, ∃ g ∈ junk G C, e ∈ gammaE G C g)
    (hBottom : ∃ c1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5 ≤ w.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      2 ≤ (junk G C).card →
      (∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone n C i j) →
      ((Ustar G C).filter (fun e => ∃ g ∈ junk G C,
        (∀ i ∈ junk G C, ¬ InCone n C i g) ∧
        5 ≤ (gammaE G C g ∩ Ustar G C).card ∧ e ∈ gammaE G C g)).card ≤ c1 * (C.size + 1))
    (hUpper : ∃ c2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5 ≤ w.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      2 ≤ (junk G C).card →
      (∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone n C i j) →
      ((Ustar G C).filter (fun e => ∃ g ∈ junk G C,
        (∃ i ∈ junk G C, InCone n C i g) ∧
        5 ≤ (gammaE G C g ∩ Ustar G C).card ∧ e ∈ gammaE G C g)).card ≤ c2 * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  rcases hBottom with ⟨c1, hc1⟩
  rcases hUpper with ⟨c2, hc2⟩
  refine ⟨4 + c1 + c2, ?_⟩
  intro n G _ hg hne C hL hT hTwo hNest
  let U := Ustar G C
  let J := junk G C
  let lightJ := J.filter (fun g => (gammaE G C g ∩ U).card ≤ 4)
  let Ulight := U.filter (fun e => ∃ g ∈ lightJ, e ∈ gammaE G C g)
  let Ubot := U.filter (fun e => ∃ g ∈ J,
    (∀ i ∈ J, ¬ InCone n C i g) ∧ 5 ≤ (gammaE G C g ∩ U).card ∧ e ∈ gammaE G C g)
  let Uup := U.filter (fun e => ∃ g ∈ J,
    (∃ i ∈ J, InCone n C i g) ∧ 5 ≤ (gammaE G C g ∩ U).card ∧ e ∈ gammaE G C g)
  have hSub : U ⊆ Ulight ∪ (Ubot ∪ Uup) := by
    intro e he
    have hcov := hCover n G C hL hT e he
    rcases hcov with ⟨g, hgJ, hge⟩
    by_cases hle : (gammaE G C g ∩ U).card ≤ 4
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, g, Finset.mem_filter.mpr ⟨hgJ, hle⟩, hge⟩)
    · have hfive : 5 ≤ (gammaE G C g ∩ U).card := by omega
      by_cases hbot : ∀ i ∈ J, ¬ InCone n C i g
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, g, hgJ, hbot, hfive, hge⟩))
      · push Not at hbot
        exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, g, hgJ, hbot, hfive, hge⟩))
  have hLightSub : Ulight ⊆ lightJ.biUnion (fun g => gammaE G C g ∩ U) := by
    intro e he
    have h1 := Finset.mem_filter.mp he
    rcases h1.2 with ⟨g, hgL, hge⟩
    exact Finset.mem_biUnion.mpr ⟨g, hgL, Finset.mem_inter.mpr ⟨hge, h1.1⟩⟩
  have hLightBi : (lightJ.biUnion (fun g => gammaE G C g ∩ U)).card ≤
      ∑ g ∈ lightJ, (gammaE G C g ∩ U).card := Finset.card_biUnion_le
  have hLightSum : ∑ g ∈ lightJ, (gammaE G C g ∩ U).card ≤ lightJ.card * 4 := by
    have hle : ∀ g ∈ lightJ, (gammaE G C g ∩ U).card ≤ 4 := by
      intro g hg
      exact (Finset.mem_filter.mp hg).2
    have hsmul := Finset.sum_le_card_nsmul lightJ (fun g => (gammaE G C g ∩ U).card) 4 hle
    rw [smul_eq_mul] at hsmul
    exact hsmul
  have hLightCard : lightJ.card ≤ C.size := by
    have h1 : lightJ.card ≤ J.card := Finset.card_filter_le J _
    have h2 : J.card ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
    rw [Finset.card_range] at h2
    have h3 : C.gates.length = C.size := rfl
    omega
  have hLightBound : Ulight.card ≤ 4 * (C.size + 1) := by
    have h0 : Ulight.card ≤ (lightJ.biUnion (fun g => gammaE G C g ∩ U)).card :=
      Finset.card_le_card hLightSub
    omega
  have hBotBound : Ubot.card ≤ c1 * (C.size + 1) := hc1 n G hg hne C hL hT hTwo hNest
  have hUpBound : Uup.card ≤ c2 * (C.size + 1) := hc2 n G hg hne C hL hT hTwo hNest
  have hUnion1 : U.card ≤ (Ulight ∪ (Ubot ∪ Uup)).card := Finset.card_le_card hSub
  have hUnion2 : (Ulight ∪ (Ubot ∪ Uup)).card ≤ Ulight.card + (Ubot ∪ Uup).card :=
    Finset.card_union_le _ _
  have hUnion3 : (Ubot ∪ Uup).card ≤ Ubot.card + Uup.card := Finset.card_union_le _ _
  have hMul : (4 + c1 + c2) * (C.size + 1) =
      4 * (C.size + 1) + c1 * (C.size + 1) + c2 * (C.size + 1) := by
    rw [Nat.add_mul, Nat.add_mul]
  change U.card ≤ (4 + c1 + c2) * (C.size + 1)
  omega
