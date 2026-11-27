import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4867

open PEqualNP.HeptadCover

lemma sL_card : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide

lemma sL_inter_eq_one : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (singerLines3 l1 ∩ singerLines3 l2).card = 1 := by
  decide

lemma unique_line_of_ne :
    ∀ a b : Fin 13, a ≠ b → ∃ l : Fin 13, a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧
      ∀ l' : Fin 13, a ∈ singerLines3 l' → b ∈ singerLines3 l' → l' = l := by
  decide

lemma card_union_three_lines (l1 l2 l3 : Fin 13)
    (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3)
    (hnc : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3)) :
    (singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3).card = 9 := by
  have c1 := sL_card l1
  have c2 := sL_card l2
  have c3 := sL_card l3
  have i12 := sL_inter_eq_one l1 l2 h12
  have i13 := sL_inter_eq_one l1 l3 h13
  have i23 := sL_inter_eq_one l2 l3 h23
  have h12u : (singerLines3 l1 ∪ singerLines3 l2).card = 7 := by
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    omega
  have hdisj : Disjoint (singerLines3 l1 ∩ singerLines3 l3) (singerLines3 l2 ∩ singerLines3 l3) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_inter] at hp1 hp2
    exact hnc p ⟨hp1.1, hp2.1, hp1.2⟩
  have hi123 : ((singerLines3 l1 ∪ singerLines3 l2) ∩ singerLines3 l3).card = 2 := by
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj, i13, i23]
  have := Finset.card_union_add_card_inter (singerLines3 l1 ∪ singerLines3 l2) (singerLines3 l3)
  omega

lemma card_biUnion_lines_le (x2 : Finset (Fin 13))
    (hcard : x2.card ≤ 3)
    (hnc : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) :
    (x2.biUnion singerLines3).card ≤ 9 := by
  by_cases h0 : x2.card = 0
  · rw [Finset.card_eq_zero.mp h0]; simp
  by_cases h1 : x2.card = 1
  · obtain ⟨l1, rfl⟩ := Finset.card_eq_one.mp h1
    simp [sL_card]
  by_cases h2 : x2.card = 2
  · obtain ⟨l1, l2, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hbi : ({l1, l2} : Finset (Fin 13)).biUnion singerLines3 = singerLines3 l1 ∪ singerLines3 l2 := by
      ext p; simp
    rw [hbi]
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    have := sL_card l1; have := sL_card l2; have := sL_inter_eq_one l1 l2 hne
    omega
  · have h3 : x2.card = 3 := by omega
    obtain ⟨l1, l2, l3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp h3
    have hbi : ({l1, l2, l3} : Finset (Fin 13)).biUnion singerLines3 =
        singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3 := by
      ext p; simp [or_assoc]
    rw [hbi]
    have hnc3 : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hsub : ({l1, l2, l3} : Finset (Fin 13)) ⊆
          ({l1, l2, l3} : Finset (Fin 13)).filter (fun l => p ∈ singerLines3 l) := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        rcases hl with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, hp1⟩
        · exact ⟨Or.inr (Or.inl rfl), hp2⟩
        · exact ⟨Or.inr (Or.inr rfl), hp3⟩
      have hc := Finset.card_le_card hsub
      have h3c : ({l1, l2, l3} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have hle2 := hnc p
      omega
    rw [card_union_three_lines l1 l2 l3 h12 h13 h23 hnc3]

lemma mem_missLines_iff (X : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 X ↔ ∀ p ∈ X, p ∉ singerLines3 l := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  exact ⟨fun h p hp hpl => h hpl hp, fun h p hpl hp => h p hp hpl⟩

lemma extend_one (x1 x2 : Finset (Fin 13))
    (h1 : x1.card ≤ 3) (h2 : x2.card ≤ 3)
    (hcol : ∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2)
    (hcon : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2)
    (hmiss : x2 ⊆ missLines singerLines3 x1) :
    ∃ p : Fin 13, p ∉ x1 ∧
      (∀ l : Fin 13, (insert p x1 ∩ singerLines3 l).card ≤ 2) ∧
      x2 ⊆ missLines singerLines3 (insert p x1) := by
  let U := x2.biUnion singerLines3
  have hU9 : U.card ≤ 9 := card_biUnion_lines_le x2 h2 hcon
  have hU_miss : ∀ p : Fin 13, p ∉ U → x2 ⊆ missLines singerLines3 (insert p x1) := by
    intro p hpU l hl
    rw [mem_missLines_iff]
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hqx1
    · intro hpl
      exact hpU (Finset.mem_biUnion.mpr ⟨l, hl, hpl⟩)
    · exact (mem_missLines_iff x1 l).mp (hmiss hl) q hqx1
  by_cases hc0 : x1.card = 0
  · have hx1 : x1 = ∅ := Finset.card_eq_zero.mp hc0
    subst hx1
    have hlt : U.card < (Finset.univ : Finset (Fin 13)).card := by simp; omega
    obtain ⟨p, _, hpU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨p, by simp, ?_, hU_miss p hpU⟩
    intro l
    change ({p} ∩ singerLines3 l).card ≤ 2
    have hle : ({p} ∩ singerLines3 l).card ≤ ({p} : Finset (Fin 13)).card := Finset.card_le_card Finset.inter_subset_left
    rw [Finset.card_singleton] at hle
    omega
  by_cases hc1 : x1.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
    have hlt : (insert a U).card < (Finset.univ : Finset (Fin 13)).card := by
      have := Finset.card_insert_le a U; simp; omega
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, not_or] at hp
    refine ⟨p, by simp [hp.1], ?_, hU_miss p hp.2⟩
    intro l
    have hle : (insert p {a} ∩ singerLines3 l).card ≤ (insert p {a} : Finset (Fin 13)).card :=
      Finset.card_le_card Finset.inter_subset_left
    have hle2 : (insert p {a} : Finset (Fin 13)).card ≤ 2 := by
      have := Finset.card_insert_le p ({a} : Finset (Fin 13)); simp at this; omega
    omega
  by_cases hc2 : x1.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
    obtain ⟨lab, halab, hblab, hlab_uniq⟩ := unique_line_of_ne a b hab
    let F := singerLines3 lab ∪ U
    have hFlt : F.card < (Finset.univ : Finset (Fin 13)).card := by
      by_cases hx2e : x2 = ∅
      · have hUe : U = ∅ := by simp [U, hx2e]
        simp [F, hUe, sL_card]
      · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hx2e
        have hl0_ne : l0 ≠ lab := by
          intro heq; subst heq
          exact (mem_missLines_iff {a, b} l0).mp (hmiss hl0) a (by simp) halab
        have hi : (singerLines3 lab ∩ singerLines3 l0).card = 1 := sL_inter_eq_one lab l0 hl0_ne.symm
        have hsub : singerLines3 lab ∩ singerLines3 l0 ⊆ singerLines3 lab ∩ U := by
          intro q hq
          simp only [Finset.mem_inter] at hq ⊢
          exact ⟨hq.1, Finset.mem_biUnion.mpr ⟨l0, hl0, hq.2⟩⟩
        have hiU : 1 ≤ (singerLines3 lab ∩ U).card := by
          have := Finset.card_le_card hsub; omega
        have huc := Finset.card_union_add_card_inter (singerLines3 lab) U
        have hlc := sL_card lab
        change (singerLines3 lab ∪ U).card < (Finset.univ : Finset (Fin 13)).card
        rw [Finset.card_univ, Fintype.card_fin]
        omega
    obtain ⟨p, _, hpF⟩ := Finset.exists_mem_notMem_of_card_lt_card hFlt
    simp only [F, Finset.mem_union, not_or] at hpF
    have hpa : p ≠ a := fun h => hpF.1 (h ▸ halab)
    have hpb : p ≠ b := fun h => hpF.1 (h ▸ hblab)
    refine ⟨p, by simp [hpa, hpb], ?_, hU_miss p hpF.2⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne : l ≠ lab := fun h => hpF.1 (h ▸ hpl)
      have hnotboth : ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l) := fun ⟨ha, hb⟩ => hlne (hlab_uniq l ha hb)
      have hsub : insert p {a, b} ∩ singerLines3 l ⊆ insert p ({a, b} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inl rfl, hq.2⟩
        · exact Or.inr ⟨Or.inr rfl, hq.2⟩
      have hc1' : ({a, b} ∩ singerLines3 l).card ≤ 1 := by
        by_cases ha : a ∈ singerLines3 l
        · have hb : b ∉ singerLines3 l := fun hb => hnotboth ⟨ha, hb⟩
          have heq : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l = {a} := by
            ext q; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hq⟩
              · rfl
              · exact (hb hq).elim
            · rintro rfl; exact ⟨Or.inl rfl, ha⟩
          rw [heq]; simp
        · have hsubb : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l ⊆ {b} := by
            intro q hq
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
            rcases hq.1 with rfl | rfl
            · exact (ha hq.2).elim
            · rfl
          exact Nat.le_trans (Finset.card_le_card hsubb) (by simp)
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b} ∩ singerLines3 l = {a, b} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l
  · have hc3 : x1.card = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc3
    obtain ⟨l1, ha1, hb1, h1uniq⟩ := unique_line_of_ne a b hab
    obtain ⟨l2, hb2, hc2', h2uniq⟩ := unique_line_of_ne b c hbc
    obtain ⟨l3, ha3, hc3', h3uniq⟩ := unique_line_of_ne a c hac
    have hnotcol : ∀ l : Fin 13, ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧ c ∈ singerLines3 l) := by
      intro l ⟨ha, hb, hc⟩
      have hsub : ({a, b, c} : Finset (Fin 13)) ⊆ ({a, b, c} : Finset (Fin 13)) ∩ singerLines3 l := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, ha⟩
        · exact ⟨Or.inr (Or.inl rfl), hb⟩
        · exact ⟨Or.inr (Or.inr rfl), hc⟩
      have hle := hcol l
      have h3c : ({a, b, c} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hl12 : l1 ≠ l2 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc2'⟩
    have hl13 : l1 ≠ l3 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc3'⟩
    have hl23 : l2 ≠ l3 := fun h => hnotcol l2 ⟨h ▸ ha3, hb2, hc2'⟩
    have hnc_tri : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hpb : p = b := by
        by_contra hne
        exact hl12 ((h1uniq l2 (by
          -- wait: b is in both l1 and l2; unique point of l1 cap l2 is b!
          exfalso
          have hsub : ({p, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hp1, hp2⟩
            · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc
          omega) hb2).symm)
      subst hpb
      exact hnotcol l3 ⟨ha3, hp3, hc3'⟩
    let T := singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3
    have hTcard : T.card = 9 := card_union_three_lines l1 l2 l3 hl12 hl13 hl23 hnc_tri
    let R := Finset.univ \ T
    have hRcard : R.card = 4 := by
      dsimp only [R]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
    have hline_R : ∀ l ∈ x2, (R ∩ singerLines3 l).card ≤ 1 := by
      intro l hl
      have ha_not : a ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) a (by simp)
      have hb_not : b ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) b (by simp)
      have hc_not : c ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) c (by simp)
      have hll1 : l ≠ l1 := fun h => ha_not (h ▸ ha1)
      have hll2 : l ≠ l2 := fun h => hb_not (h ▸ hb2)
      have hll3 : l ≠ l3 := fun h => hc_not (h ▸ hc3')
      obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l1 hll1]; omega)
      obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l2 hll2]; omega)
      obtain ⟨p3, hp3⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l3 hll3]; omega)
      simp only [Finset.mem_inter] at hp1 hp2 hp3
      have hp12 : p1 ≠ p2 := by
        intro heq; subst heq
        have hsub : ({p1, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp2.2⟩
          · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
        have hne : p1 ≠ b := fun h => hb_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc; omega
      have hp13 : p1 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p1, a} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨ha1, ha3⟩
        have hne : p1 ≠ a := fun h => ha_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l3 hl13] at hc; omega
      have hp23 : p2 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p2, c} : Finset (Fin 13)) ⊆ singerLines3 l2 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp2.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨hc2', hc3'⟩
        have hne : p2 ≠ c := fun h => hc_not (h ▸ hp2.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l2 l3 hl23] at hc; omega
      have hsubT : ({p1, p2, p3} : Finset (Fin 13)) ⊆ T ∩ singerLines3 l := by
        intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hp1.2), hp1.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hp2.2), hp2.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hp3.2, hp3.1⟩
      have h3in : 3 ≤ (T ∩ singerLines3 l).card := by
        have h3c : ({p1, p2, p3} : Finset (Fin 13)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hp12, hp13]),
            Finset.card_insert_of_notMem (by simp [hp23]), Finset.card_singleton]
        have := Finset.card_le_card hsubT; omega
      have hdisjRT : Disjoint (R ∩ singerLines3 l) (T ∩ singerLines3 l) := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [R, Finset.mem_inter, Finset.mem_sdiff] at hq1 hq2
        exact hq1.1.2 hq2.1
      have hunion_sub : (R ∩ singerLines3 l) ∪ (T ∩ singerLines3 l) ⊆ singerLines3 l :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hle4 := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hdisjRT, sL_card l] at hle4
      omega
    have hRU_le : (R ∩ U).card ≤ 3 := by
      have hsub : R ∩ U ⊆ x2.biUnion (fun l => R ∩ singerLines3 l) := by
        intro q hq
        simp only [U, Finset.mem_inter, Finset.mem_biUnion] at hq ⊢
        rcases hq.2 with ⟨l, hl, hql⟩
        exact ⟨l, hl, hq.1, hql⟩
      calc (R ∩ U).card
          ≤ (x2.biUnion (fun l => R ∩ singerLines3 l)).card := Finset.card_le_card hsub
        _ ≤ ∑ l ∈ x2, (R ∩ singerLines3 l).card := Finset.card_biUnion_le
        _ ≤ ∑ _l ∈ x2, 1 := Finset.sum_le_sum hline_R
        _ = x2.card := by simp
        _ ≤ 3 := h2
    have hlt : (R ∩ U).card < R.card := by omega
    obtain ⟨p, hpR, hpnotRU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hpU : p ∉ U := fun h => hpnotRU (Finset.mem_inter.mpr ⟨hpR, h⟩)
    have hpT : p ∉ T := (Finset.mem_sdiff.mp hpR).2
    have hpa : p ≠ a := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ ha1))
    have hpb : p ≠ b := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hb1))
    have hpc : p ≠ c := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hc2'))
    refine ⟨p, by simp [hpa, hpb, hpc], ?_, hU_miss p hpU⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne1 : l ≠ l1 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_left _ (h ▸ hpl)))
      have hlne2 : l ≠ l2 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_right _ (h ▸ hpl)))
      have hlne3 : l ≠ l3 := fun h => hpT (Finset.mem_union_right _ (h ▸ hpl))
      have h1_le : ({a, b, c} ∩ singerLines3 l).card ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ ({a, b, c} ∩ singerLines3 l).card := by omega
        obtain ⟨u, v, huv, huvsub⟩ : ∃ u v, u ≠ v ∧ u ∈ ({a, b, c} ∩ singerLines3 l) ∧ v ∈ ({a, b, c} ∩ singerLines3 l) := by
          obtain ⟨S2, hS2sub, hS2card⟩ := Finset.exists_subset_card_eq hge2
          obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS2card
          exact ⟨u, v, huv, hS2sub (by simp), hS2sub (by simp)⟩
        rcases huvsub with ⟨hu, hv⟩
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu.1 with rfl | rfl | rfl <;> rcases hv.1 with rfl | rfl | rfl
        · exact huv rfl
        · exact hlne1 (h1uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hu.2 hv.2)
        · exact hlne1 (h1uniq l hv.2 hu.2)
        · exact huv rfl
        · exact hlne2 (h2uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hv.2 hu.2)
        · exact hlne2 (h2uniq l hv.2 hu.2)
        · exact huv rfl
      have hsub : insert p {a, b, c} ∩ singerLines3 l ⊆ insert p ({a, b, c} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | hq'
        · exact Or.inl rfl
        · exact Or.inr ⟨hq', hq.2⟩
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b, c} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b, c} ∩ singerLines3 l = {a, b, c} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l

lemma extend_to_quad :
    ∀ k : ℕ, ∀ x1 x2 : Finset (Fin 13),
      4 - x1.card = k → x1.card ≤ 4 → x2.card ≤ 3 →
      (∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2) →
      (∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) →
      x2 ⊆ missLines singerLines3 x1 →
      ∃ Q ∈ quadrangles singerLines3, x1 ⊆ Q ∧ x2 ⊆ missLines singerLines3 Q := by
  intro k
  induction k with
  | zero =>
    intro x1 x2 hk h1 _ hcol _ hmiss
    have h4 : x1.card = 4 := by omega
    refine ⟨x1, ?_, Finset.Subset.refl x1, hmiss⟩
    simp only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨h4, hcol⟩
  | succ k ih =>
    intro x1 x2 hk h1 h2 hcol hcon hmiss
    have hle3 : x1.card ≤ 3 := by omega
    obtain ⟨p, hpnot, hcol', hmiss'⟩ := extend_one x1 x2 hle3 h2 hcol hcon hmiss
    have hcard' : (insert p x1).card = x1.card + 1 := Finset.card_insert_of_notMem hpnot
    obtain ⟨Q, hQ, hsubQ, hmissQ⟩ := ih (insert p x1) x2 (by omega) (by omega) h2 hcol' hcon hmiss'
    exact ⟨Q, hQ, Finset.Subset.trans (Finset.subset_insert p x1) hsubQ, hmissQ⟩

end PEqualNP.Outside.L_meta_4867

theorem PEqualNP.Outside.L_meta_4867 :
  ∀ (x1 x2 : Finset (Fin (13 : ℕ))), x1.card ≤ (4 : ℕ) → x2.card ≤ (3 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), (x1 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x2 | x6 ∈ PEqualNP.HeptadCover.singerLines3 x7}.card ≤ (2 : ℕ)) → x2 ⊆ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1 → ∃ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x1 ⊆ x8 ∧ x2 ⊆ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8 := by
  intro x1 x2 h1 h2 hcol hcon hmiss
  exact PEqualNP.Outside.L_meta_4867.extend_to_quad (4 - x1.card) x1 x2 rfl h1 h2 hcol hcon hmiss
