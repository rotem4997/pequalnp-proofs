import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

variable {n : ℕ}

def Av (L : List (Finset (Fin n))) (K : ℕ) (s : Finset (Fin n)) : Prop :=
  s.card ≤ 1 ∨ s ∈ List.take K L

def Ix (L : List (Finset (Fin n))) (X : Finset (Fin n)) (K : ℕ) : Finset (Fin L.length) :=
  Finset.univ.filter fun i => (i : ℕ) < K ∧ 1 < (L.get i).card ∧ L.get i ⊆ X

theorem core (L : List (Finset (Fin n)))
    (h : ∀ (j : ℕ) (s : Finset (Fin n)), L[j]? = some s →
      ∃ a b : Finset (Fin n), s = a ∪ b ∧ (a.card ≤ 1 ∨ a ∈ List.take j L) ∧
        (b.card ≤ 1 ∨ b ∈ List.take j L))
    (X : Finset (Fin n)) : ∀ K ≤ L.length, ∀ T : Finset (Finset (Fin n)),
      (∀ s ∈ T, Av L K s ∧ s ⊆ X) → (T.biUnion id).card ≤ (Ix L X K).card + T.card := by
  intro K
  induction K with
  | zero =>
    intro _ T hT
    have := Finset.card_biUnion_le_card_mul T id 1 (fun s hs => by
      rcases (hT s hs).1 with h1 | h1
      · exact h1
      · simp at h1)
    omega
  | succ K ih =>
    intro hK T hT
    have hK' : K < L.length := by omega
    have hsub : Ix L X K ⊆ Ix L X (K + 1) := by
      intro i hi
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨h1, by omega, h3⟩
    have hmono := Finset.card_le_card hsub
    have htake : List.take (K + 1) L = List.take K L ++ [L[K]] := by
      rw [List.take_succ_eq_append_getElem hK']
    have hav : ∀ s, Av L (K + 1) s → ¬ Av L K s → s = L[K] := by
      intro s h1 h2
      rcases h1 with h1 | h1
      · exact absurd (Or.inl h1) h2
      · rw [htake, List.mem_append, List.mem_singleton] at h1
        rcases h1 with h1 | h1
        · exact absurd (Or.inr h1) h2
        · exact h1
    by_cases hold : ∀ s ∈ T, Av L K s
    · have := ih (by omega) T fun s hs => ⟨hold s hs, (hT s hs).2⟩
      omega
    · push Not at hold
      obtain ⟨s, hsT, hs⟩ := hold
      have hsK := hav s (hT s hsT).1 hs
      obtain ⟨a, b, hab, ha, hb⟩ := h K s (by rw [List.getElem?_eq_getElem hK', hsK])
      have hsX := (hT s hsT).2
      have hbig : 1 < s.card := by
        by_contra hc
        exact hs (Or.inl (by omega))
      have hrest : ∀ t ∈ T.erase s, Av L K t ∧ t ⊆ X := by
        intro t ht
        obtain ⟨hne, htT⟩ := Finset.mem_erase.1 ht
        refine ⟨?_, (hT t htT).2⟩
        by_contra hc
        exact hne ((hav t (hT t htT).1 hc).trans hsK.symm)
      have key := ih (by omega) (insert a (insert b (T.erase s))) (by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨ha, (hab ▸ Finset.subset_union_left).trans hsX⟩
        · rcases Finset.mem_insert.1 ht with rfl | ht
          · exact ⟨hb, (hab ▸ Finset.subset_union_right).trans hsX⟩
          · exact hrest t ht)
      have hcov : T.biUnion id ⊆ (insert a (insert b (T.erase s))).biUnion id := by
        intro p hp
        obtain ⟨t, htT, htp⟩ := Finset.mem_biUnion.1 hp
        by_cases hts : t = s
        · rw [hts, hab] at htp
          rcases Finset.mem_union.1 htp with h1 | h1
          · exact Finset.mem_biUnion.2 ⟨a, by simp, h1⟩
          · exact Finset.mem_biUnion.2 ⟨b, by simp, h1⟩
        · exact Finset.mem_biUnion.2 ⟨t, by simp [hts, htT], htp⟩
      have c1 := Finset.card_le_card hcov
      have c2 := Finset.card_insert_le a (insert b (T.erase s))
      have c3 := Finset.card_insert_le b (T.erase s)
      have c4 := Finset.card_erase_add_one hsT
      have hnew : (Ix L X K).card + 1 ≤ (Ix L X (K + 1)).card := by
        have hnot : (⟨K, hK'⟩ : Fin L.length) ∉ Ix L X K := by
          intro hc
          have := (Finset.mem_filter.1 hc).2.1
          simp at this
        rw [← Finset.card_insert_of_notMem hnot]
        refine Finset.card_le_card fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp, ?_, ?_⟩
          · rw [List.get_eq_getElem]; simpa [← hsK] using hbig
          · rw [List.get_eq_getElem]; simpa [← hsK] using hsX
        · exact hsub hi
      omega

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n L h s hs
  have key := PEqualNP.Outside.L_meta_3574.core L h s L.length le_rfl {s} (by
    intro t ht
    rw [Finset.mem_singleton.1 ht]
    exact ⟨Or.inr (by rw [List.take_length]; exact hs), Finset.Subset.refl _⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at key
  refine key.trans (Nat.add_le_add_right ?_ 1)
  rw [Fintype.card_subtype]
  refine Finset.card_le_card fun i hi => ?_
  obtain ⟨h1, -, h2⟩ := Finset.mem_filter.1 hi
  exact Finset.mem_filter.2 ⟨h1, h2⟩
