import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17411

private def step (w : List Bool) (g : Finset ℕ × Finset ℕ) : List Bool :=
  w ++ [Decidable.decide (∀ k ∈ g.1, w.getD k Bool.false = Bool.true) ||
        Decidable.decide (∀ k ∈ g.2, w.getD k Bool.false = Bool.true)]

private def run (gs : List (Finset ℕ × Finset ℕ)) (v : Fin 21 → Bool) : List Bool :=
  List.foldl step (List.ofFn v ++ [Bool.false]) gs

private def pg24 (i j : Fin 21) : Bool :=
  [(i.val + 20) % 21, i.val, (i.val + 5) % 21, (i.val + 7) % 21, (i.val + 17) % 21].contains j.val

private def unitV (i : Fin 21) : Fin 21 → Bool := fun j => Decidable.decide (j = i)

private def nonNbrV (i : Fin 21) : Fin 21 → Bool := fun j => !pg24 i j

private def nbrs (i : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter fun j : Fin 21 => pg24 i j = Bool.true

private lemma nbrs_card (i : Fin 21) : (nbrs i).card = 5 := by
  revert i; decide

private lemma pg24_inter_le_one (i1 i2 : Fin 21) (hne : i1 ≠ i2) :
    (Finset.univ.filter fun j : Fin 21 => pg24 i1 j = Bool.true ∧ pg24 i2 j = Bool.true).card ≤ 1 := by
  revert i1 i2 hne; decide

private lemma run_concat (gs : List (Finset ℕ × Finset ℕ)) (g : Finset ℕ × Finset ℕ) (v : Fin 21 → Bool) :
    run (gs ++ [g]) v = step (run gs v) g := by
  simp [run, List.foldl_append]

private lemma run_len (gs : List (Finset ℕ × Finset ℕ)) (v : Fin 21 → Bool) :
    (run gs v).length = 22 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_concat]
    simp [step, ih]
    omega

private lemma getD_append_left (l : List Bool) (b : Bool) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k Bool.false = l.getD k Bool.false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma getD_append_last (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length Bool.false = b := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_of_ge (l : List Bool) (k : ℕ) (hk : l.length ≤ k) :
    l.getD k Bool.false = Bool.false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

private lemma getD_init_unit (i : Fin 21) (k : ℕ)
    (h : (List.ofFn (unitV i) ++ [Bool.false]).getD k Bool.false = Bool.true) :
    ∃ hk : k < 21, (⟨k, hk⟩ : Fin 21) = i := by
  by_cases hk : k < 21
  · refine ⟨hk, ?_⟩
    have hlt : k < (List.ofFn (unitV i)).length := by simp only [List.length_ofFn]; exact hk
    rw [getD_append_left _ _ _ hlt] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk] at h
    simpa [unitV] using h
  · exfalso
    by_cases h21 : k = 21
    · subst h21
      have hlast := getD_append_last (List.ofFn (unitV i)) Bool.false
      rw [List.length_ofFn] at hlast
      rw [hlast] at h
      exact Bool.false_ne_true h
    · have hge : (List.ofFn (unitV i) ++ [Bool.false]).length ≤ k := by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega
      rw [getD_of_ge _ _ hge] at h
      exact Bool.false_ne_true h

private lemma run_mono (gs : List (Finset ℕ × Finset ℕ)) (v w : Fin 21 → Bool)
    (hvw : ∀ j : Fin 21, v j = Bool.true → w j = Bool.true) :
    ∀ k : ℕ, (run gs v).getD k Bool.false = Bool.true → (run gs w).getD k Bool.false = Bool.true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    by_cases hlt : k < 21
    · have hlt' : k < (List.ofFn v).length := by simp only [List.length_ofFn]; exact hlt
      have hlt'' : k < (List.ofFn w).length := by simp only [List.length_ofFn]; exact hlt
      change (List.ofFn v ++ [Bool.false]).getD k Bool.false = Bool.true at hk
      change (List.ofFn w ++ [Bool.false]).getD k Bool.false = Bool.true
      rw [getD_append_left _ _ _ hlt'] at hk
      rw [getD_append_left _ _ _ hlt'']
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt] at hk ⊢
      exact hvw ⟨k, hlt⟩ hk
    · exfalso
      by_cases h21 : k = 21
      · subst h21
        change (List.ofFn v ++ [Bool.false]).getD 21 Bool.false = Bool.true at hk
        have hlast := getD_append_last (List.ofFn v) Bool.false
        rw [List.length_ofFn] at hlast
        rw [hlast] at hk
        exact Bool.false_ne_true hk
      · have hge : (run [] v).length ≤ k := by rw [run_len]; simp; omega
        rw [getD_of_ge _ _ hge] at hk
        exact Bool.false_ne_true hk
  | append_singleton gs g ih =>
    intro k hk
    set L := 22 + gs.length
    have hlv : (run gs v).length = L := run_len gs v
    have hlw : (run gs w).length = L := run_len gs w
    rcases lt_trichotomy k L with hlt | rfl | hgt
    · rw [run_concat, step, getD_append_left _ _ _ (by omega)] at hk ⊢
      exact ih k hk
    · rw [run_concat, step, ← hlv, getD_append_last] at hk
      rw [run_concat, step, ← hlw, getD_append_last]
      rw [Bool.or_eq_true] at hk ⊢
      rcases hk with h1 | h2
      · left
        exact decide_eq_true (fun a ha => ih a (of_decide_eq_true h1 a ha))
      · right
        exact decide_eq_true (fun b hb => ih b (of_decide_eq_true h2 b hb))
    · have hge : (run (gs ++ [g]) v).length ≤ k := by rw [run_len]; simp; omega
      rw [getD_of_ge _ _ hge] at hk
      exact absurd hk Bool.false_ne_true

private lemma unit_mem_nbr_of_nonNbr_false (gs : List (Finset ℕ × Finset ℕ)) (i j : Fin 21) (k : ℕ)
    (h0 : (run gs (nonNbrV i)).getD k Bool.false = Bool.false)
    (hj : (run gs (unitV j)).getD k Bool.false = Bool.true) :
    pg24 i j = Bool.true := by
  cases hval : pg24 i j
  · exfalso
    have hle : ∀ t : Fin 21, unitV j t = Bool.true → nonNbrV i t = Bool.true := by
      intro t ht
      have htj : t = j := of_decide_eq_true ht
      subst htj
      simp [nonNbrV, hval]
    have ht := run_mono gs (unitV j) (nonNbrV i) hle k hj
    rw [h0] at ht
    exact Bool.false_ne_true ht
  · rfl

private def owned (gs : List (Finset ℕ × Finset ℕ)) (i : Fin 21) : Finset ℕ :=
  (Finset.range gs.length).filter fun t =>
    (run gs (nonNbrV i)).getD (22 + t) Bool.false = Bool.false ∧
    2 ≤ (Finset.univ.filter fun j : Fin 21 => (run gs (unitV j)).getD (22 + t) Bool.false = Bool.true).card

private lemma owned_disjoint (gs : List (Finset ℕ × Finset ℕ)) (i1 i2 : Fin 21) (hne : i1 ≠ i2) :
    Disjoint (owned gs i1) (owned gs i2) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  simp only [owned, Finset.mem_filter] at ht1 ht2
  let S := Finset.univ.filter fun j : Fin 21 => (run gs (unitV j)).getD (22 + t) Bool.false = Bool.true
  have hsub : S ⊆ Finset.univ.filter fun j : Fin 21 => pg24 i1 j = Bool.true ∧ pg24 i2 j = Bool.true := by
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨unit_mem_nbr_of_nonNbr_false gs i1 j (22 + t) ht1.2.1 hj,
           unit_mem_nbr_of_nonNbr_false gs i2 j (22 + t) ht2.2.1 hj⟩
  have hle1 := pg24_inter_le_one i1 i2 hne
  have hge2 : 2 ≤ S.card := ht1.2.2
  have hle := Finset.card_le_card hsub
  omega

private lemma owned_sub_append (gs : List (Finset ℕ × Finset ℕ)) (g : Finset ℕ × Finset ℕ) (i : Fin 21) :
    owned gs i ⊆ owned (gs ++ [g]) i := by
  intro t ht
  simp only [owned, Finset.mem_filter, Finset.mem_range] at ht ⊢
  have hlt : 22 + t < 22 + gs.length := by omega
  have hstep : ∀ v : Fin 21 → Bool,
      (run (gs ++ [g]) v).getD (22 + t) Bool.false = (run gs v).getD (22 + t) Bool.false := by
    intro v
    rw [run_concat, step, getD_append_left]
    rw [run_len]
    exact hlt
  refine ⟨by simp; omega, ?_, ?_⟩
  · rw [hstep (nonNbrV i)]
    exact ht.2.1
  · have hEq : (Finset.univ.filter fun j : Fin 21 => (run (gs ++ [g]) (unitV j)).getD (22 + t) Bool.false = Bool.true) =
        (Finset.univ.filter fun j : Fin 21 => (run gs (unitV j)).getD (22 + t) Bool.false = Bool.true) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hstep (unitV j)]
    rw [hEq]
    exact ht.2.2

private def Inv (gs : List (Finset ℕ × Finset ℕ)) (i : Fin 21) (f : Fin 21 → ℕ) : Prop :=
  5 ≤ ((nbrs i).image f).card + (owned gs i).card ∧
  ∀ k : ℕ, (run gs (nonNbrV i)).getD k Bool.false = Bool.false →
    ∀ j1 j2 : Fin 21,
      (run gs (unitV j1)).getD k Bool.false = Bool.true →
      (run gs (unitV j2)).getD k Bool.false = Bool.true →
      f j1 = f j2

private lemma inv_exists (gs : List (Finset ℕ × Finset ℕ)) (i : Fin 21) :
    ∃ f : Fin 21 → ℕ, Inv gs i f := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun j => j.val, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective, nbrs_card i]
      omega
    · intro k _ j1 j2 h1 h2
      obtain ⟨hk1, rfl⟩ := getD_init_unit j1 k h1
      obtain ⟨hk2, rfl⟩ := getD_init_unit j2 k h2
      rfl
  | append_singleton gs g ih =>
    obtain ⟨f, hcard, hconst⟩ := ih
    set L : ℕ := 22 + gs.length with hLdef
    have hlen : ∀ v : Fin 21 → Bool, (run gs v).length = L := fun v => run_len gs v
    have hstep_lt : ∀ (v : Fin 21 → Bool) (k : ℕ), k < L →
        (run (gs ++ [g]) v).getD k Bool.false = (run gs v).getD k Bool.false := by
      intro v k hk
      rw [run_concat, step, getD_append_left]
      simpa [hlen v] using hk
    have hstep_eq : ∀ v : Fin 21 → Bool,
        (run (gs ++ [g]) v).getD L Bool.false =
          (Decidable.decide (∀ a ∈ g.1, (run gs v).getD a Bool.false = Bool.true) ||
           Decidable.decide (∀ b ∈ g.2, (run gs v).getD b Bool.false = Bool.true)) := by
      intro v
      rw [run_concat, step, ← hlen v, getD_append_last]
    have hstep_gt : ∀ (v : Fin 21 → Bool) (k : ℕ), L < k →
        (run (gs ++ [g]) v).getD k Bool.false = Bool.false := by
      intro v k hk
      rw [run_concat, step, getD_of_ge]
      simp [hlen v]
      omega
    have hown_le : (owned gs i).card ≤ (owned (gs ++ [g]) i).card :=
      Finset.card_le_card (owned_sub_append gs g i)
    by_cases h0 : (run (gs ++ [g]) (nonNbrV i)).getD L Bool.false = Bool.true
    · refine ⟨f, by omega, ?_⟩
      intro k hk0 j1 j2 h1 h2
      rcases lt_trichotomy k L with hlt | rfl | hgt
      · rw [hstep_lt (nonNbrV i) k hlt] at hk0
        rw [hstep_lt (unitV j1) k hlt] at h1
        rw [hstep_lt (unitV j2) k hlt] at h2
        exact hconst k hk0 j1 j2 h1 h2
      · rw [h0] at hk0
        exact absurd hk0 Bool.false_ne_true.symm
      · rw [hstep_gt (unitV j1) k hgt] at h1
        exact absurd h1 Bool.false_ne_true
    · have h0f : (run (gs ++ [g]) (nonNbrV i)).getD L Bool.false = Bool.false := by
        cases hval : (run (gs ++ [g]) (nonNbrV i)).getD L Bool.false
        · rfl
        · exact absurd hval h0
      let S := Finset.univ.filter fun j : Fin 21 => (run (gs ++ [g]) (unitV j)).getD L Bool.false = Bool.true
      by_cases hS2 : 2 ≤ S.card
      · have hmem : gs.length ∈ owned (gs ++ [g]) i := by
          simp only [owned, Finset.mem_filter, Finset.mem_range]
          exact ⟨by simp, h0f, hS2⟩
        have hnotmem : gs.length ∉ owned gs i := by
          simp only [owned, Finset.mem_filter, Finset.mem_range]
          intro h
          omega
        have hown_inc : (owned gs i).card + 1 ≤ (owned (gs ++ [g]) i).card := by
          have hsub : insert gs.length (owned gs i) ⊆ owned (gs ++ [g]) i :=
            Finset.insert_subset hmem (owned_sub_append gs g i)
          have hci := Finset.card_insert_of_notMem hnotmem
          have hle := Finset.card_le_card hsub
          omega
        have h0f' := h0f
        rw [hstep_eq (nonNbrV i), Bool.or_eq_false_iff] at h0f'
        have ha_ex : ∃ a ∈ g.1, (run gs (nonNbrV i)).getD a Bool.false = Bool.false := by
          have h1 : ¬(∀ a ∈ g.1, (run gs (nonNbrV i)).getD a Bool.false = Bool.true) := by
            intro hall
            have hd : Decidable.decide (∀ a ∈ g.1, (run gs (nonNbrV i)).getD a Bool.false = Bool.true) = Bool.true :=
              decide_eq_true hall
            rw [hd] at h0f'
            exact Bool.false_ne_true.symm h0f'.1
          classical
          push Not at h1
          obtain ⟨a, ha1, ha2⟩ := h1
          refine ⟨a, ha1, ?_⟩
          cases hval : (run gs (nonNbrV i)).getD a Bool.false
          · rfl
          · exact absurd hval ha2
        have hb_ex : ∃ b ∈ g.2, (run gs (nonNbrV i)).getD b Bool.false = Bool.false := by
          have h2 : ¬(∀ b ∈ g.2, (run gs (nonNbrV i)).getD b Bool.false = Bool.true) := by
            intro hall
            have hd : Decidable.decide (∀ b ∈ g.2, (run gs (nonNbrV i)).getD b Bool.false = Bool.true) = Bool.true :=
              decide_eq_true hall
            rw [hd] at h0f'
            exact Bool.false_ne_true.symm h0f'.2
          classical
          push Not at h2
          obtain ⟨b, hb1, hb2⟩ := h2
          refine ⟨b, hb1, ?_⟩
          cases hval : (run gs (nonNbrV i)).getD b Bool.false
          · rfl
          · exact absurd hval hb2
        obtain ⟨a, ha1, ha0⟩ := ha_ex
        obtain ⟨b, hb1, hb0⟩ := hb_ex
        have hL_hit : ∀ j : Fin 21, (run (gs ++ [g]) (unitV j)).getD L Bool.false = Bool.true →
            (run gs (unitV j)).getD a Bool.false = Bool.true ∨
            (run gs (unitV j)).getD b Bool.false = Bool.true := by
          intro j hj
          rw [hstep_eq (unitV j), Bool.or_eq_true] at hj
          rcases hj with h1 | h2
          · left
            exact of_decide_eq_true h1 a ha1
          · right
            exact of_decide_eq_true h2 b hb1
        by_cases hia : ∃ i0 : Fin 21, (run gs (unitV i0)).getD a Bool.false = Bool.true
        · by_cases hjb : ∃ j0 : Fin 21, (run gs (unitV j0)).getD b Bool.false = Bool.true
          · obtain ⟨i0, hi0⟩ := hia
            obtain ⟨j0, hj0⟩ := hjb
            let f' : Fin 21 → ℕ := fun x => if f x = f j0 then f i0 else f x
            refine ⟨f', ?_, ?_⟩
            · have hsub : (nbrs i).image f ⊆ insert (f j0) ((nbrs i).image f') := by
                intro y hy
                rw [Finset.mem_image] at hy
                obtain ⟨x, hx, rfl⟩ := hy
                by_cases hfx : f x = f j0
                · rw [hfx]
                  exact Finset.mem_insert_self _ _
                · apply Finset.mem_insert_of_mem
                  rw [Finset.mem_image]
                  exact ⟨x, hx, by simp [f', hfx]⟩
              have hc1 : ((nbrs i).image f).card ≤ ((nbrs i).image f').card + 1 := by
                calc ((nbrs i).image f).card
                    ≤ (insert (f j0) ((nbrs i).image f')).card := Finset.card_le_card hsub
                  _ ≤ ((nbrs i).image f').card + 1 := Finset.card_insert_le _ _
              omega
            · intro k hk0 j1 j2 h1 h2
              rcases lt_trichotomy k L with hlt | rfl | hgt
              · rw [hstep_lt (nonNbrV i) k hlt] at hk0
                rw [hstep_lt (unitV j1) k hlt] at h1
                rw [hstep_lt (unitV j2) k hlt] at h2
                have hij := hconst k hk0 j1 j2 h1 h2
                simp [f', hij]
              · have hf'eq : ∀ x : Fin 21, (run (gs ++ [g]) (unitV x)).getD L Bool.false = Bool.true →
                    f' x = f i0 := by
                  intro x hx
                  rcases hL_hit x hx with hxa | hxb
                  · have hfx := hconst a ha0 x i0 hxa hi0
                    simp [f', hfx]
                  · have hfx := hconst b hb0 x j0 hxb hj0
                    simp [f', hfx]
                rw [hf'eq j1 h1, hf'eq j2 h2]
              · rw [hstep_gt (unitV j1) k hgt] at h1
                exact absurd h1 Bool.false_ne_true
          · refine ⟨f, by omega, ?_⟩
            intro k hk0 j1 j2 h1 h2
            rcases lt_trichotomy k L with hlt | rfl | hgt
            · rw [hstep_lt (nonNbrV i) k hlt] at hk0
              rw [hstep_lt (unitV j1) k hlt] at h1
              rw [hstep_lt (unitV j2) k hlt] at h2
              exact hconst k hk0 j1 j2 h1 h2
            · have ha1' : (run gs (unitV j1)).getD a Bool.false = Bool.true := by
                rcases hL_hit j1 h1 with hm | hm
                · exact hm
                · exact absurd ⟨j1, hm⟩ hjb
              have ha2' : (run gs (unitV j2)).getD a Bool.false = Bool.true := by
                rcases hL_hit j2 h2 with hm | hm
                · exact hm
                · exact absurd ⟨j2, hm⟩ hjb
              exact hconst a ha0 j1 j2 ha1' ha2'
            · rw [hstep_gt (unitV j1) k hgt] at h1
              exact absurd h1 Bool.false_ne_true
        · refine ⟨f, by omega, ?_⟩
          intro k hk0 j1 j2 h1 h2
          rcases lt_trichotomy k L with hlt | rfl | hgt
          · rw [hstep_lt (nonNbrV i) k hlt] at hk0
            rw [hstep_lt (unitV j1) k hlt] at h1
            rw [hstep_lt (unitV j2) k hlt] at h2
            exact hconst k hk0 j1 j2 h1 h2
          · have hb1' : (run gs (unitV j1)).getD b Bool.false = Bool.true := by
              rcases hL_hit j1 h1 with hm | hm
              · exact absurd ⟨j1, hm⟩ hia
              · exact hm
            have hb2' : (run gs (unitV j2)).getD b Bool.false = Bool.true := by
              rcases hL_hit j2 h2 with hm | hm
              · exact absurd ⟨j2, hm⟩ hia
              · exact hm
            exact hconst b hb0 j1 j2 hb1' hb2'
          · rw [hstep_gt (unitV j1) k hgt] at h1
            exact absurd h1 Bool.false_ne_true
      · refine ⟨f, by omega, ?_⟩
        intro k hk0 j1 j2 h1 h2
        rcases lt_trichotomy k L with hlt | rfl | hgt
        · rw [hstep_lt (nonNbrV i) k hlt] at hk0
          rw [hstep_lt (unitV j1) k hlt] at h1
          rw [hstep_lt (unitV j2) k hlt] at h2
          exact hconst k hk0 j1 j2 h1 h2
        · have hj1S : j1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j1, h1⟩
          have hj2S : j2 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j2, h2⟩
          have hle1 : S.card ≤ 1 := by omega
          have heq : j1 = j2 := Finset.card_le_one.mp hle1 j1 hj1S j2 hj2S
          rw [heq]
        · rw [hstep_gt (unitV j1) k hgt] at h1
          exact absurd h1 Bool.false_ne_true

end PEqualNP.Outside.L_meta_17411

theorem PEqualNP.Outside.L_meta_17411 : have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → (Fin (21 : ℕ) → Bool) → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : Fin (21 : ℕ) → Bool) =>   have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (List.ofFn x3 ++ [Bool.false]) x1;   Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true); have x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x2 x3 : Fin (21 : ℕ)) => [(↑x2 + (20 : ℕ)) % (21 : ℕ), ↑x2, (↑x2 + (5 : ℕ)) % (21 : ℕ), (↑x2 + (7 : ℕ)) % (21 : ℕ), (↑x2 + (17 : ℕ)) % (21 : ℕ)].contains ↑x3; have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => Decidable.decide (x4 = x3); have x4 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x4 x5 : Fin (21 : ℕ)) => !x2 x4 x5; ∀ (x5 : List (Finset ℕ × Finset ℕ)) (x6 : Fin (21 : ℕ) → Finset ℕ), (∀ (x7 x8 : Fin (21 : ℕ)), x2 x7 x8 = Bool.true → x1 x5 (x6 x7) (x3 x8) = Bool.true) → (∀ (x8 : Fin (21 : ℕ)), x1 x5 (x6 x8) (x4 x8) = Bool.false) → (84 : ℕ) ≤ x5.length := by
  intro x1 x2 x3 x4 x5 x6 hpos hneg
  have hge4 : ∀ i : Fin 21, 4 ≤ (PEqualNP.Outside.L_meta_17411.owned x5 i).card := by
    intro i
    obtain ⟨f, hcard, hconst⟩ := PEqualNP.Outside.L_meta_17411.inv_exists x5 i
    have hnegi : ¬(∀ w ∈ x6 i, (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.nonNbrV i)).getD w Bool.false = Bool.true) := by
      intro hall
      have hd : Decidable.decide (∀ w ∈ x6 i, (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.nonNbrV i)).getD w Bool.false = Bool.true) = Bool.true :=
        decide_eq_true hall
      have hi := hneg i
      change Decidable.decide (∀ w ∈ x6 i, (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.nonNbrV i)).getD w Bool.false = Bool.true) = Bool.false at hi
      rw [hd] at hi
      exact Bool.false_ne_true.symm hi
    classical
    push Not at hnegi
    obtain ⟨w, hw6, hw0⟩ := hnegi
    have hw0f : (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.nonNbrV i)).getD w Bool.false = Bool.false := by
      cases hval : (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.nonNbrV i)).getD w Bool.false
      · rfl
      · exact absurd hval hw0
    have hwpos : ∀ j ∈ PEqualNP.Outside.L_meta_17411.nbrs i,
        (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.unitV j)).getD w Bool.false = Bool.true := by
      intro j hj
      have hpg : PEqualNP.Outside.L_meta_17411.pg24 i j = Bool.true := (Finset.mem_filter.mp hj).2
      have hp := hpos i j hpg
      change Decidable.decide (∀ u ∈ x6 i, (PEqualNP.Outside.L_meta_17411.run x5 (PEqualNP.Outside.L_meta_17411.unitV j)).getD u Bool.false = Bool.true) = Bool.true at hp
      exact of_decide_eq_true hp w hw6
    have hne : (PEqualNP.Outside.L_meta_17411.nbrs i).Nonempty := by
      rw [← Finset.card_pos, PEqualNP.Outside.L_meta_17411.nbrs_card i]
      omega
    obtain ⟨j0, hj0⟩ := hne
    have hsub : (PEqualNP.Outside.L_meta_17411.nbrs i).image f ⊆ {f j0} := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      rw [Finset.mem_singleton]
      exact hconst w hw0f j j0 (hwpos j hj) (hwpos j0 hj0)
    have hle1 : ((PEqualNP.Outside.L_meta_17411.nbrs i).image f).card ≤ 1 := by
      calc ((PEqualNP.Outside.L_meta_17411.nbrs i).image f).card
          ≤ ({f j0} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    omega
  have hsum : 84 ≤ ∑ i : Fin 21, (PEqualNP.Outside.L_meta_17411.owned x5 i).card := by
    calc 84 = ∑ _i : Fin 21, (4 : ℕ) := by decide
      _ ≤ ∑ i : Fin 21, (PEqualNP.Outside.L_meta_17411.owned x5 i).card :=
        Finset.sum_le_sum fun i _ => hge4 i
  have hbi : ∑ i : Fin 21, (PEqualNP.Outside.L_meta_17411.owned x5 i).card =
      (Finset.univ.biUnion (PEqualNP.Outside.L_meta_17411.owned x5)).card := by
    symm
    exact Finset.card_biUnion fun i1 _ i2 _ hne => PEqualNP.Outside.L_meta_17411.owned_disjoint x5 i1 i2 hne
  have hsubR : Finset.univ.biUnion (PEqualNP.Outside.L_meta_17411.owned x5) ⊆ Finset.range x5.length := by
    rw [Finset.biUnion_subset]
    intro i _
    exact Finset.filter_subset _ _
  have hleR : (Finset.univ.biUnion (PEqualNP.Outside.L_meta_17411.owned x5)).card ≤ x5.length := by
    calc (Finset.univ.biUnion (PEqualNP.Outside.L_meta_17411.owned x5)).card
        ≤ (Finset.range x5.length).card := Finset.card_le_card hsubR
      _ = x5.length := Finset.card_range _
  omega
