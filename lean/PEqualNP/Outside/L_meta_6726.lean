import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6726 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)) (x4 : Fin x1 × Fin x1 → Finset (Fin x2)), (44 : ℕ) * (x3.biUnion x4).card < x3.card → ∃ x6 ⊆ x3, x6.card = (44 : ℕ) * (x6.biUnion x4).card + (1 : ℕ) ∧ ∀ x7 ∈ x6.biUnion x4, (45 : ℕ) ≤ {x9 ∈ x6 | x7 ∈ x4 x9}.card := by
  intro n m T f hT
  classical
  have hmono : ∀ P Q : Finset (Fin n × Fin n), P ⊆ Q → P.biUnion f ⊆ Q.biUnion f :=
    fun P Q h => Finset.biUnion_subset_biUnion_of_subset_left f h
  have hex : ∃ k, ∃ U ⊆ T, U.card = k ∧ 44 * (U.biUnion f).card < U.card :=
    ⟨T.card, T, Finset.Subset.refl _, rfl, hT⟩
  obtain ⟨U, hUT, hUm, hU⟩ := Nat.find_spec hex
  have hmin : ∀ U' ⊆ T, U'.card < U.card → U'.card ≤ 44 * (U'.biUnion f).card := by
    intro U' hU' hlt
    by_contra hc
    exact Nat.find_min hex (hUm ▸ hlt) ⟨U', hU', rfl, by omega⟩
  have hpos : 0 < U.card := by omega
  refine ⟨U, hUT, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    have h1 := hmin (U.erase a) ((Finset.erase_subset _ _).trans hUT) (Finset.card_erase_lt_of_mem ha)
    have h2 := Finset.card_le_card (hmono _ _ (Finset.erase_subset a U))
    have h3 := Finset.card_erase_of_mem ha
    omega
  · intro b hb
    by_contra hc
    push_neg at hc
    have hsub : U.filter (fun a => b ∈ f a) ⊆ U := Finset.filter_subset _ _
    obtain ⟨a0, ha0, hba0⟩ := Finset.mem_biUnion.1 hb
    have hne : (U.filter (fun a => b ∈ f a)).Nonempty := ⟨a0, Finset.mem_filter.2 ⟨ha0, hba0⟩⟩
    have hcard : (U \ U.filter (fun a => b ∈ f a)).card
        = U.card - (U.filter (fun a => b ∈ f a)).card := by
      first
        | exact Finset.card_sdiff_of_subset hsub
        | exact Finset.card_sdiff hsub
    have hp := Finset.card_pos.2 hne
    have hle := Finset.card_le_card hsub
    have h1 := hmin (U \ U.filter (fun a => b ∈ f a)) (Finset.sdiff_subset.trans hUT) (by omega)
    have hN : (U \ U.filter (fun a => b ∈ f a)).biUnion f ⊆ (U.biUnion f).erase b := by
      intro c hc'
      obtain ⟨a, ha, hca⟩ := Finset.mem_biUnion.1 hc'
      rw [Finset.mem_sdiff] at ha
      refine Finset.mem_erase.2 ⟨fun hcb => ha.2 (Finset.mem_filter.2 ⟨ha.1, hcb ▸ hca⟩),
        Finset.mem_biUnion.2 ⟨a, ha.1, hca⟩⟩
    have h2 := Finset.card_le_card hN
    rw [Finset.card_erase_of_mem hb] at h2
    have hb1 := Finset.card_pos.2 ⟨b, hb⟩
    omega
