import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9429 : ∀ (x1 : Finset (Finset ℕ)) (x2 x3 : Finset ℕ) (x4 x5 : Finset (Finset ℕ)) (x6 x7 : Finset ℕ) (x8 x9 : ℕ), x8 ∉ x6 → x9 ∉ x6 → x7 ⊆ x6 → (∀ x13 ∈ x1, x13 ⊆ x6 ∧ ¬x13 ⊆ x7 ∧ ∀ x15 ∈ x1, x13 ≠ x15 → (x13 ∩ x15 ∩ x7).card ≤ (1 : ℕ)) → x4 ⊆ Insert.insert (Insert.insert x8 x2) (Insert.insert (Insert.insert x9 x3) x1) → x2 ∈ Finset.image₂ (fun (x15 x16 : Finset ℕ) => x15 ∩ x16) ({x15 ∈ x4 | x15 ⊆ x6}) ({x15 ∈ x4 | x15 ⊆ x6}) → x3 ∈ Finset.image₂ (fun (x16 x17 : Finset ℕ) => x16 ∩ x17) ({x16 ∈ x4 | x16 ⊆ x6}) ({x16 ∈ x4 | x16 ⊆ x6}) → x5 ⊆ Finset.image₂ (fun (x17 x18 : Finset ℕ) => x17 ∩ x18 ∩ x6 ∪ if {x8, x9} ⊆ x17 ∪ x18 then {x8} else ∅) x4 x4 → x5.biUnion id = Insert.insert x8 x7 → x7.card ≤ x5.card := by
  intro F x2 x3 W x5 X S a b ha hb hSX hF hW h2 h3 h5 hU
  have inF : ∀ P ∈ W, P ⊆ X → P ∈ F := by
    intro P hP hPX
    have := hW hP
    simp only [Finset.mem_insert] at this
    rcases this with h | h | h
    · rw [h] at hPX; exact absurd (hPX (Finset.mem_insert_self _ _)) ha
    · rw [h] at hPX; exact absurd (hPX (Finset.mem_insert_self _ _)) hb
    · exact h
  have im : ∀ y, y ∈ Finset.image₂ (fun u v : Finset ℕ => u ∩ v) ({u ∈ W | u ⊆ X}) ({u ∈ W | u ⊆ X}) →
      ∃ A ∈ F, ∃ B ∈ F, y = A ∩ B := by
    intro y hy
    rw [Finset.mem_image₂] at hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    rw [Finset.mem_filter] at hu hv
    exact ⟨u, inF u hu.1 hu.2, v, inF v hv.1 hv.2, rfl⟩
  have ins : ∀ (c : ℕ) (y : Finset ℕ), c ∉ X → ∀ A ∈ F, ∀ B ∈ F, y = A ∩ B → insert c y ∩ X = A ∩ B := by
    intro c y hc A hA B hB hy
    subst hy
    ext t
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ h2) hc
      · exact h1
    · intro h1
      exact ⟨Or.inr h1, (hF A hA).1 h1.1⟩
  have core : ∀ P ∈ W, ∃ A ∈ F, ∃ B ∈ F, P ∩ X = A ∩ B := by
    intro P hP
    have := hW hP
    simp only [Finset.mem_insert] at this
    rcases this with h | h | h
    · obtain ⟨A, hA, B, hB, e⟩ := im x2 h2
      exact ⟨A, hA, B, hB, by rw [h]; exact ins a x2 ha A hA B hB e⟩
    · obtain ⟨A, hA, B, hB, e⟩ := im x3 h3
      exact ⟨A, hA, B, hB, by rw [h]; exact ins b x3 hb A hA B hB e⟩
    · refine ⟨P, h, P, h, ?_⟩
      ext t
      simp only [Finset.mem_inter]
      exact ⟨fun h1 => ⟨h1.1, h1.1⟩, fun h1 => ⟨h1.1, (hF P h).1 h1.1⟩⟩
  have small : ∀ A ∈ F, ∀ B ∈ F, ∀ R : Finset ℕ, R ⊆ A → R ⊆ B → R ⊆ S → A ≠ B → R.card ≤ 1 := by
    intro A hA B hB R h1 h2 h3 hne
    refine le_trans (Finset.card_le_card ?_) ((hF A hA).2.2 B hB hne)
    intro t ht
    simp only [Finset.mem_inter]
    exact ⟨⟨h1 ht, h2 ht⟩, h3 ht⟩
  have bound : ∀ T ∈ x5, (T ∩ X).card ≤ 1 := by
    intro T hT
    have hTS : T ∩ X ⊆ S := by
      intro t ht
      rw [Finset.mem_inter] at ht
      have h : t ∈ x5.biUnion id := Finset.mem_biUnion.2 ⟨T, hT, ht.1⟩
      rw [hU, Finset.mem_insert] at h
      rcases h with h | h
      · exact absurd (h ▸ ht.2) ha
      · exact h
    have h := h5 hT
    rw [Finset.mem_image₂] at h
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := h
    obtain ⟨A, hA, B, hB, e1⟩ := core P hP
    obtain ⟨C, hC, D, hD, e2⟩ := core Q hQ
    have hsub : T ∩ X = (A ∩ B) ∩ (C ∩ D) := by
      rw [← e1, ← e2, ← hPQ]
      ext t
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hX⟩
        · exact ⟨⟨h.1.1, hX⟩, ⟨h.1.2, hX⟩⟩
        · split_ifs at h
          · rw [Finset.mem_singleton] at h; exact absurd (h ▸ hX) ha
          · simp at h
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inl ⟨⟨h1.1, h2.1⟩, h1.2⟩, h1.2⟩
    generalize T ∩ X = R at hsub hTS ⊢
    have rA : R ⊆ A := by intro t ht; rw [hsub] at ht; simp only [Finset.mem_inter] at ht; exact ht.1.1
    have rB : R ⊆ B := by intro t ht; rw [hsub] at ht; simp only [Finset.mem_inter] at ht; exact ht.1.2
    have rC : R ⊆ C := by intro t ht; rw [hsub] at ht; simp only [Finset.mem_inter] at ht; exact ht.2.1
    have rD : R ⊆ D := by intro t ht; rw [hsub] at ht; simp only [Finset.mem_inter] at ht; exact ht.2.2
    by_cases hAB : A = B
    · by_cases hAC : A = C
      · by_cases hAD : A = D
        · exfalso
          apply (hF A hA).2.1
          intro t ht
          apply hTS
          rw [hsub, ← hAB, ← hAC, ← hAD]
          simp only [Finset.mem_inter]
          exact ⟨⟨ht, ht⟩, ⟨ht, ht⟩⟩
        · exact small A hA D hD R rA rD hTS hAD
      · exact small A hA C hC R rA rC hTS hAC
    · exact small A hA B hB R rA rB hTS hAB
  calc S.card ≤ (x5.biUnion fun T => T ∩ X).card := by
        apply Finset.card_le_card
        intro s hs
        have h : s ∈ x5.biUnion id := by rw [hU]; exact Finset.mem_insert_of_mem hs
        obtain ⟨T, hT, hsT⟩ := Finset.mem_biUnion.1 h
        exact Finset.mem_biUnion.2 ⟨T, hT, Finset.mem_inter.2 ⟨hsT, hSX hs⟩⟩
    _ ≤ x5.card * 1 := Finset.card_biUnion_le_card_mul _ _ _ bound
    _ = x5.card := Nat.mul_one _
