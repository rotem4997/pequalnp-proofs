import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5942 : ∀ (x1 x2 : Type) [x3 : DecidableEq x1] [x4 : DecidableEq x2] (x5 : Finset x2) (x6 : x2 → x1 → Bool) (x7 : ℕ) (x8 : Finset x1),   have x9 : Finset x1 → Finset x2 := fun (x9 : Finset x1) => {x10 ∈ x5 | ∃ x11 ∈ x9, x6 x10 x11 = Bool.true};   x7 * (x9 x8).card < x8.card → ∃ x11 ⊆ x8, x11.card = x7 * (x9 x11).card + (1 : ℕ) ∧ ∀ x12 ⊆ x9 x11, x12.Nonempty → x7 * x12.card < {x15 ∈ x11 | ∃ x16 ∈ x12, x6 x16 x15 = Bool.true}.card := by
  intro A B _ _ S R k T N hT
  classical
  have hmemN : ∀ (P : Finset A) (b : B), b ∈ N P ↔ b ∈ S ∧ ∃ a ∈ P, R b a = true := by
    intro P b
    simp [N]
  have hNmono : ∀ P Q : Finset A, P ⊆ Q → N P ⊆ N Q := by
    intro P Q hPQ b hb
    rw [hmemN] at hb ⊢
    obtain ⟨hbS, a, ha, hR⟩ := hb
    exact ⟨hbS, a, hPQ ha, hR⟩
  have hex : ∃ m, ∃ U ⊆ T, U.card = m ∧ k * (N U).card < U.card :=
    ⟨T.card, T, Finset.Subset.refl _, rfl, hT⟩
  obtain ⟨U, hUT, hUm, hU⟩ := Nat.find_spec hex
  have hmin : ∀ U' ⊆ T, U'.card < U.card → U'.card ≤ k * (N U').card := by
    intro U' hU' hlt
    by_contra hc
    exact Nat.find_min hex (hUm ▸ hlt) ⟨U', hU', rfl, by omega⟩
  have hpos : 0 < U.card := by omega
  refine ⟨U, hUT, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    have h1 := hmin (U.erase a) ((Finset.erase_subset _ _).trans hUT) (Finset.card_erase_lt_of_mem ha)
    have h2 := Finset.card_le_card (hNmono _ _ (Finset.erase_subset a U))
    have h3 := Finset.card_erase_of_mem ha
    have h4 := Nat.mul_le_mul_left k h2
    omega
  · intro W hW hWne
    by_contra hc
    push_neg at hc
    have hsub : U.filter (fun a => ∃ b ∈ W, R b a = true) ⊆ U := Finset.filter_subset _ _
    have hUWne : (U.filter (fun a => ∃ b ∈ W, R b a = true)).Nonempty := by
      obtain ⟨b, hb⟩ := hWne
      obtain ⟨_, a, ha, hR⟩ := (hmemN U b).1 (hW hb)
      exact ⟨a, Finset.mem_filter.2 ⟨ha, b, hb, hR⟩⟩
    have hcard : (U \ U.filter (fun a => ∃ b ∈ W, R b a = true)).card
        = U.card - (U.filter (fun a => ∃ b ∈ W, R b a = true)).card := by
      first
        | exact Finset.card_sdiff_of_subset hsub
        | exact Finset.card_sdiff hsub
    have hp := Finset.card_pos.2 hUWne
    have hle := Finset.card_le_card hsub
    have h1 := hmin (U \ U.filter (fun a => ∃ b ∈ W, R b a = true))
      (Finset.sdiff_subset.trans hUT) (by omega)
    have hN : N (U \ U.filter (fun a => ∃ b ∈ W, R b a = true)) ⊆ N U \ W := by
      intro b hb
      obtain ⟨hbS, a, ha, hR⟩ := (hmemN _ b).1 hb
      rw [Finset.mem_sdiff] at ha ⊢
      exact ⟨(hmemN U b).2 ⟨hbS, a, ha.1, hR⟩,
        fun hbW => ha.2 (Finset.mem_filter.2 ⟨ha.1, b, hbW, hR⟩)⟩
    have h2 := Finset.card_le_card hN
    have h3 : (N U \ W).card = (N U).card - W.card := by
      first
        | exact Finset.card_sdiff_of_subset hW
        | exact Finset.card_sdiff hW
    have h4 := Finset.card_le_card hW
    have h6 := Nat.mul_le_mul_left k h2
    rw [h3, Nat.mul_sub] at h6
    have h7 := Nat.mul_le_mul_left k h4
    omega
