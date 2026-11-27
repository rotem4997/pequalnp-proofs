import Mathlib
import PEqualNP.Defs

-- Complements of the wires of a set circuit, written as unions over finite sets of inputs,
-- built gate by gate by induction on the number of gates.
theorem PEqualNP.Outside.L_meta_2998 : ∀ (x1 : Type) (x2 x3 : ℕ) (x4 : ℕ → Set x1), (∀ x5 < x3, ∃ x7 < x2 + x5, ∃ x8 < x2 + x5, x4 (x2 + x5) = x4 x7 ∪ x4 x8 ∨ x4 (x2 + x5) = x4 x7 ∨ x4 (x2 + x5) = ∅ ∨ x4 (x2 + x5) = x4 x7 ∩ x4 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ x7 < x2, x6 x7 = {{x7}}) ∧ (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x6 (x2 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 x9) (x6 x10) ∨ x6 (x2 + x7) = x6 x9 ∨ x6 (x2 + x7) = {∅} ∨ x6 (x2 + x7) = x6 x9 ∪ x6 x10) ∧ ∀ x7 < x2 + x3, (∀ x9 ∈ x6 x7, ∀ x11 ∈ x9, x11 < x2) ∧ ∀ (x9 : x1), x9 ∉ x4 x7 ↔ ∃ x10 ∈ x6 x7, ∀ x11 ∈ x10, x9 ∉ x4 x11 := by
  intro X n m
  induction m with
  | zero =>
    intro S _
    refine ⟨fun i => {{i}}, fun i _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro i hi
    refine ⟨?_, ?_⟩
    · intro F hF k hk
      rw [Set.mem_singleton_iff] at hF
      subst hF
      rw [Finset.mem_singleton] at hk
      omega
    · intro x
      constructor
      · intro hx
        refine ⟨{i}, Set.mem_singleton _, fun k hk => ?_⟩
        rw [Finset.mem_singleton] at hk
        subst hk
        exact hx
      · rintro ⟨F, hF, hall⟩
        rw [Set.mem_singleton_iff] at hF
        subst hF
        exact hall i (Finset.mem_singleton_self i)
  | succ m ih =>
    intro S hS
    obtain ⟨F, hin, hgate, hprop⟩ := ih S (fun k hk => hS k (by omega))
    obtain ⟨a, ha, b, hb, hcase⟩ := hS m (by omega)
    classical
    obtain ⟨N, hN⟩ : ∃ N : Set (Finset ℕ), N =
        if S (n + m) = S a ∪ S b then Set.image2 (fun u v : Finset ℕ => u ∪ v) (F a) (F b)
        else if S (n + m) = S a then F a
        else if S (n + m) = ∅ then {∅}
        else F a ∪ F b := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Finset ℕ), G = Function.update F (n + m) N := ⟨_, rfl⟩
    have hold : ∀ i, i < n + m → G i = F i := by
      intro i hi
      rw [hG]
      simp [show i ≠ n + m by omega]
    have hnew : G (n + m) = N := by
      rw [hG]
      simp
    refine ⟨G, ?_, ?_, ?_⟩
    · intro i hi
      rw [hold i (by omega)]
      exact hin i hi
    · intro k hk
      rcases (show k < m ∨ k = m by omega) with hk | rfl
      · obtain ⟨c, hc, d, hd, h⟩ := hgate k hk
        refine ⟨c, hc, d, hd, ?_⟩
        rw [hold (n + k) (by omega), hold c (by omega), hold d (by omega)]
        exact h
      · refine ⟨a, ha, b, hb, ?_⟩
        rw [hnew, hold a ha, hold b hb, hN]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    · intro i hi
      rcases (show i < n + m ∨ i = n + m by omega) with hi | rfl
      · rw [hold i hi]
        exact hprop i hi
      · rw [hnew]
        obtain ⟨hba, hpa⟩ := hprop a ha
        obtain ⟨hbb, hpb⟩ := hprop b hb
        rw [hN]
        split_ifs with h1 h2 h3
        · refine ⟨?_, ?_⟩
          · rintro _ ⟨u, hu, v, hv, rfl⟩ k hk
            rcases Finset.mem_union.mp hk with hk | hk
            · exact hba u hu k hk
            · exact hbb v hv k hk
          · intro x
            rw [h1, Set.mem_union, not_or, hpa x, hpb x]
            constructor
            · rintro ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
              refine ⟨u ∪ v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
              intro k hk
              rcases Finset.mem_union.mp hk with hk | hk
              · exact hu' k hk
              · exact hv' k hk
            · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, hall⟩
              exact ⟨⟨u, hu, fun k hk => hall k (Finset.mem_union_left _ hk)⟩,
                ⟨v, hv, fun k hk => hall k (Finset.mem_union_right _ hk)⟩⟩
        · refine ⟨hba, ?_⟩
          intro x
          rw [h2]
          exact hpa x
        · refine ⟨?_, ?_⟩
          · intro u hu k hk
            rw [Set.mem_singleton_iff] at hu
            subst hu
            simp at hk
          · intro x
            rw [h3]
            simp
        · have h4 : S (n + m) = S a ∩ S b := by
            rcases hcase with h | h | h | h
            · exact absurd h h1
            · exact absurd h h2
            · exact absurd h h3
            · exact h
          refine ⟨?_, ?_⟩
          · intro u hu
            rcases hu with hu | hu
            · exact hba u hu
            · exact hbb u hu
          · intro x
            rw [h4, Set.mem_inter_iff, not_and_or, hpa x, hpb x]
            constructor
            · rintro (⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩)
              · exact ⟨u, Or.inl hu, hu'⟩
              · exact ⟨u, Or.inr hu, hu'⟩
            · rintro ⟨u, hu | hu, hu'⟩
              · exact Or.inl ⟨u, hu, hu'⟩
              · exact Or.inr ⟨u, hu, hu'⟩
