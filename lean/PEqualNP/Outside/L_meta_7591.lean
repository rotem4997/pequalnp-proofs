import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7591 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))), (0 : ℕ) < x1 → (∀ (x6 : Fin x2), x4 ↑x6 = {x7 : (Fin x2 → Bool) × (Fin x2 → Bool) | x7.1 x6 = Bool.true} ∧ x4 (x2 + ↑x6) = {x7 : (Fin x2 → Bool) × (Fin x2 → Bool) | x7.2 x6 = Bool.true}) → (∀ x7 < x3, ∃ (x9 : ℕ) (x10 : ℕ), Max.max x9 x10 < x2 + x2 + x7 ∧ x4 (x2 + x2 + x7) ∈ [x4 x9 ∪ x4 x10, x4 x9, ∅, x4 x9 ∩ x4 x10]) → ∃ (x8 : ℕ → Set (Finset (Fin x2) × Finset (Fin x2))), (∀ (x9 : Fin x2), x8 ↑x9 = {({x9}, ∅)} ∧ x8 (x2 + ↑x9) = {(∅, {x9})}) ∧ (∀ x9 < x3, ∃ (x11 : ℕ) (x12 : ℕ), Max.max x11 x12 < x2 + x2 + x9 ∧ x8 (x2 + x2 + x9) ∈ [x8 x11 ∪ x8 x12, x8 x11, ∅, {x13 : Finset (Fin x2) × Finset (Fin x2) | x13 ∈ Set.image2 (fun (x14 x15 : Finset (Fin x2) × Finset (Fin x2)) => x14 ⊔ x15) (x8 x11) (x8 x12) ∧ x13.2.card ≤ x1}]) ∧ ∀ x9 < x2 + x2 + x3, ∀ (x11 x12 : Fin x2 → Bool), Fintype.card { x13 : Fin x2 // x12 x13 = Bool.true } ≤ x1 → ((x11, x12) ∈ x4 x9 ↔ ∃ x14 ∈ x8 x9, (∀ x15 ∈ x14.1, x11 x15 = Bool.true) ∧ ∀ x15 ∈ x14.2, x12 x15 = Bool.true) := by
  intro x1 N x3
  induction x3 with
  | zero =>
    intro S hx1 hin _
    refine ⟨fun i => if h : i < N then {({⟨i, h⟩}, ∅)}
        else if h2 : i < N + N then {(∅, {⟨i - N, by omega⟩})} else ∅, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    · intro j
      constructor
      · simp only [dif_pos j.isLt]
      · have h1 : ¬ (N + (j : ℕ) < N) := by omega
        have h2 : N + (j : ℕ) < N + N := by omega
        simp only [dif_neg h1, dif_pos h2]
        congr 3
        exact Fin.ext (by simp)
    · intro i hi x11 x12 _
      by_cases h : i < N
      · have e := (hin ⟨i, h⟩).1
        simp only [Fin.val_mk] at e
        simp only [e, dif_pos h]
        simp
      · have hj : i - N < N := by omega
        have e := (hin ⟨i - N, hj⟩).2
        have hi' : N + (i - N) = i := by omega
        simp only [Fin.val_mk, hi'] at e
        simp only [e, dif_neg h, dif_pos (show i < N + N by omega)]
        simp
  | succ m ih =>
    intro S hx1 hin hS
    obtain ⟨F, hinF, hgate, hprop⟩ := ih S hx1 hin (fun k hk => hS k (by omega))
    obtain ⟨a, b, hab, hcase⟩ := hS m (by omega)
    have ha : a < N + N + m := lt_of_le_of_lt (le_max_left _ _) hab
    have hb : b < N + N + m := lt_of_le_of_lt (le_max_right _ _) hab
    classical
    obtain ⟨G0, hG0⟩ : ∃ G0 : Set (Finset (Fin N) × Finset (Fin N)), G0 =
        if S (N + N + m) = S a ∪ S b then F a ∪ F b
        else if S (N + N + m) = S a then F a
        else if S (N + N + m) = ∅ then ∅
        else {t : Finset (Fin N) × Finset (Fin N) | t ∈ Set.image2
          (fun (u v : Finset (Fin N) × Finset (Fin N)) => u ⊔ v) (F a) (F b) ∧ t.2.card ≤ x1} :=
      ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Finset (Fin N) × Finset (Fin N)),
        G = Function.update F (N + N + m) G0 := ⟨_, rfl⟩
    have hold : ∀ i, i < N + N + m → G i = F i := by
      intro i hi
      rw [hG]
      simp [show i ≠ N + N + m by omega]
    have hnew : G (N + N + m) = G0 := by
      rw [hG]
      simp
    refine ⟨G, ?_, ?_, ?_⟩
    · intro j
      rw [hold (j : ℕ) (by omega), hold (N + (j : ℕ)) (by omega)]
      exact hinF j
    · intro k hk
      rcases (show k < m ∨ k = m by omega) with hk | rfl
      · obtain ⟨c, d, hcd, h⟩ := hgate k hk
        have hc : c < N + N + k := lt_of_le_of_lt (le_max_left _ _) hcd
        have hd : d < N + N + k := lt_of_le_of_lt (le_max_right _ _) hcd
        refine ⟨c, d, hcd, ?_⟩
        rw [hold (N + N + k) (by omega), hold c (by omega), hold d (by omega)]
        exact h
      · refine ⟨a, b, hab, ?_⟩
        rw [hnew, hold a ha, hold b hb, hG0]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    · intro i hi x11 x12 hcard
      rcases (show i < N + N + m ∨ i = N + N + m by omega) with hi | rfl
      · rw [hold i hi]
        exact hprop i hi x11 x12 hcard
      · rw [hnew, hG0]
        have hpa := hprop a ha x11 x12 hcard
        have hpb := hprop b hb x11 x12 hcard
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcase
        split_ifs with h1 h2 h3
        · rw [h1, Set.mem_union, hpa, hpb]
          constructor
          · rintro (⟨u, hu, hs⟩ | ⟨u, hu, hs⟩)
            · exact ⟨u, Or.inl hu, hs⟩
            · exact ⟨u, Or.inr hu, hs⟩
          · rintro ⟨u, hu | hu, hs⟩
            · exact Or.inl ⟨u, hu, hs⟩
            · exact Or.inr ⟨u, hu, hs⟩
        · rw [h2]
          exact hpa
        · rw [h3]
          simp
        · have h4 : S (N + N + m) = S a ∩ S b := by
            rcases hcase with h | h | h | h
            · exact absurd h h1
            · exact absurd h h2
            · exact absurd h h3
            · exact h
          rw [h4, Set.mem_inter_iff, hpa, hpb]
          constructor
          · rintro ⟨⟨u, hu, hu1, hu2⟩, ⟨v, hv, hv1, hv2⟩⟩
            refine ⟨u ⊔ v, ⟨⟨u, hu, v, hv, rfl⟩, ?_⟩, ?_, ?_⟩
            · calc (u ⊔ v).2.card
                  ≤ (Finset.univ.filter (fun k => x12 k = true)).card := by
                    apply Finset.card_le_card
                    intro k hk
                    simp only [Prod.snd_sup, Finset.mem_union] at hk
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    rcases hk with hk | hk
                    · exact hu2 k hk
                    · exact hv2 k hk
                _ = Fintype.card { k : Fin N // x12 k = true } := (Fintype.card_subtype _).symm
                _ ≤ x1 := hcard
            · intro k hk
              simp only [Prod.fst_sup, Finset.mem_union] at hk
              rcases hk with hk | hk
              · exact hu1 k hk
              · exact hv1 k hk
            · intro k hk
              simp only [Prod.snd_sup, Finset.mem_union] at hk
              rcases hk with hk | hk
              · exact hu2 k hk
              · exact hv2 k hk
          · rintro ⟨_, ⟨⟨u, hu, v, hv, rfl⟩, _⟩, hs1, hs2⟩
            refine ⟨⟨u, hu, fun k hk => hs1 k ?_, fun k hk => hs2 k ?_⟩,
              ⟨v, hv, fun k hk => hs1 k ?_, fun k hk => hs2 k ?_⟩⟩
            · simp only [Prod.fst_sup, Finset.mem_union]; exact Or.inl hk
            · simp only [Prod.snd_sup, Finset.mem_union]; exact Or.inl hk
            · simp only [Prod.fst_sup, Finset.mem_union]; exact Or.inr hk
            · simp only [Prod.snd_sup, Finset.mem_union]; exact Or.inr hk
