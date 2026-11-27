import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.R_meta_8071_317
    (triple : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let F := fun g => U ∩ gammaE G C g
        let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
        (∃ a b, a ∈ J ∧ b ∈ J ∧ a ≠ b ∧ ¬InCone 11 C a b ∧ ¬InCone 11 C b a) →
        U ⊆ J.biUnion F → 3 ≤ U.card →
        (∃ g ∈ J, 3 ≤ (F g).card) → U.card ≤ J.card + k)
    (pairs : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let F := fun g => U ∩ gammaE G C g
        let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
        (∃ a b, a ∈ J ∧ b ∈ J ∧ a ≠ b ∧ ¬InCone 11 C a b ∧ ¬InCone 11 C b a) →
        U ⊆ J.biUnion F → 3 ≤ U.card →
        (∀ g ∈ J, (F g).card ≤ 2) →
        (∃ D ⊆ J, k < D.card ∧ (∀ g ∈ D, (F g).card = 2) ∧
          ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Disjoint (F a) (F b)) → U.card ≤ J.card + k) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C hs least top _ independent covered three _
  let J := junk G C
  let U := Ustar G C
  let F := fun g => U ∩ gammaE G C g
  let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
  have hits : ∀ e ∈ U, ∃ g ∈ J, e ∈ F g := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨g, hj, hv⟩ := covered u v he
      exact ⟨g, hj, Finset.mem_inter.mpr ⟨he, Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hv⟩⟩⟩
  have hcover : U ⊆ J.biUnion F := fun e he => Finset.mem_biUnion.mpr (hits e he)
  suffices h : U.card ≤ J.card + k by
    dsimp [U, J, k, G] at h
    omega
  by_cases heavy : ∃ g ∈ J, 3 ≤ (F g).card
  · exact triple C hs least top independent hcover three heavy
  have small : ∀ g ∈ J, (F g).card ≤ 2 := by
    intro g hg
    by_contra! big
    exact heavy ⟨g, hg, big⟩
  by_contra! fail
  let owner := fun e => if he : e ∈ U then Classical.choose (hits e he) else 0
  have chosen : ∀ e ∈ U, owner e ∈ J ∧ e ∈ F (owner e) := by
    intro e he
    simpa only [owner, dif_pos he] using Classical.choose_spec (hits e he)
  let bin := fun g => U.filter (fun e => owner e = g)
  have sub : ∀ g, bin g ⊆ F g := by
    intro g e he
    obtain ⟨hu, rfl⟩ := Finset.mem_filter.mp he
    exact (chosen e hu).2
  have union : U ⊆ J.biUnion bin := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨owner e, (chosen e he).1, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  let D := J.filter (fun g => (bin g).card = 2)
  have dsub : D ⊆ J := Finset.filter_subset _ _
  have weight : ∀ g ∈ J, (bin g).card ≤ 1 + (if g ∈ D then 1 else 0) := by
    intro g hg
    have hb := (Finset.card_le_card (sub g)).trans (small g hg)
    by_cases hd : g ∈ D
    · simp [hd]; omega
    · have hn : (bin g).card ≠ 2 := fun he => hd (Finset.mem_filter.mpr ⟨hg, he⟩)
      simp [hd]; omega
  have cap : U.card ≤ J.card + D.card := calc
    U.card ≤ (J.biUnion bin).card := Finset.card_le_card union
    _ ≤ ∑ g ∈ J, (bin g).card := Finset.card_biUnion_le
    _ ≤ ∑ g ∈ J, (1 + (if g ∈ D then 1 else 0) : ℕ) := Finset.sum_le_sum weight
    _ = J.card + D.card := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr dsub]
  have eqbin : ∀ g ∈ D, bin g = F g := by
    intro g hg
    apply Finset.eq_of_subset_of_card_le (sub g)
    have hb := (Finset.mem_filter.mp hg).2
    have hf := small g (dsub hg)
    omega
  have two : ∀ g ∈ D, (F g).card = 2 := by
    intro g hg
    rw [← eqbin g hg]
    exact (Finset.mem_filter.mp hg).2
  have separate : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Disjoint (F a) (F b) := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [← eqbin a ha, ← eqbin b hb, Finset.disjoint_left]
    intro e ea eb
    exact hab ((Finset.mem_filter.mp ea).2.symm.trans (Finset.mem_filter.mp eb).2)
  have many : k < D.card := by omega
  exact (not_le.mpr fail) (pairs C hs least top independent hcover three small
    ⟨D, dsub, many, two, separate⟩)
