import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7606_aux

def K {x1 : Type} (x5 : ℕ → Set x1) (j : ℕ) : Prop := x5 j ≠ ∅ ∧ ∀ k < j, x5 k ≠ x5 j

theorem take_mem (L : List ℕ) (hL : L.Pairwise (· < ·)) (i : Fin L.length) (m : ℕ)
    (hm : m ∈ L) (hlt : m < L.get i) : m ∈ L.take i := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
  rw [List.mem_take_iff_getElem]
  have hji : j < i := by
    by_contra hc
    have hle : (i : ℕ) ≤ j := by omega
    rcases Nat.eq_or_lt_of_le hle with h | h
    · subst h
      simp at hlt
    · have h2 := (List.pairwise_iff_getElem.mp hL) i j i.2 hj h
      simp only [List.get_eq_getElem] at hlt
      omega
  exact ⟨j, by omega, rfl⟩

theorem take_lt (L : List ℕ) (hL : L.Pairwise (· < ·)) (i : Fin L.length) (m : ℕ)
    (hm : m ∈ L.take i) : m < L.get i := by
  rw [List.mem_take_iff_getElem] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  exact (List.pairwise_iff_getElem.mp hL) j i (by omega) i.2 (by omega)

theorem rep {x1 : Type} (x5 : ℕ → Set x1) (k : ℕ) (hk : x5 k ≠ ∅) :
    ∃ m, m ≤ k ∧ x5 m = x5 k ∧ K x5 m := by
  classical
  have hex : ∃ m, x5 m = x5 k := ⟨k, rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex rfl, Nat.find_spec hex, ?_, ?_⟩
  · rw [Nat.find_spec hex]
    exact hk
  · intro q hq hqe
    exact Nat.find_min hex hq (hqe.trans (Nat.find_spec hex))

end PEqualNP.Outside.L_meta_7606_aux

open PEqualNP.Outside.L_meta_7606_aux in
theorem PEqualNP.Outside.L_meta_7606 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1),   x4 < x2 + x3 →     x5 x4 ≠ ∅ →       (∀ x8 < x3, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x2 + x8 ∧ x5 (x2 + x8) ∈ [x5 x10 ∪ x5 x11, x5 x10, ∅, x5 x10 ∩ x5 x11]) →         ∃ (x9 : List ℕ),           x9.length ≤ x3 ∧             (∀ x10 ∈ x9, x2 ≤ x10 ∧ x10 < x2 + x3) ∧               x5 x4 ∈ List.map x5 (List.range x2 ++ x9) ∧                 ∀ (x10 : Fin x9.length),                   have x11 : List ℕ := List.range x2 ++ List.take (↑x10) x9;                   have x12 : Set x1 := x5 (x9.get x10);                   (∀ x13 ∈ x11, x13 < x9.get x10) ∧ x12 ≠ ∅ ∧ x12 ∉ List.map x5 x11 ∧ ∃ x13 ∈ List.map x5 x11, ∃ x14 ∈ List.map x5 x11, ¬x13 ⊆ x14 ∧ ¬x14 ⊆ x13 ∧ (x12 = x13 ∪ x14 ∨ x12 = x13 ∩ x14) := by
  classical
  intro x1 x2 x3 x4 x5 h4 hne h
  obtain ⟨L, hLdef⟩ : ∃ L : List ℕ, L = ((List.range x3).filter (fun i => decide (K x5 (x2 + i)))).map (fun i => x2 + i) := ⟨_, rfl⟩
  have hmem : ∀ m, m ∈ L ↔ x2 ≤ m ∧ m < x2 + x3 ∧ K x5 m := by
    intro m
    simp only [hLdef, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨hi, hk⟩, rfl⟩
      exact ⟨by omega, by omega, hk⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨m - x2, ⟨by omega, by rwa [show x2 + (m - x2) = m by omega]⟩, by omega⟩
  have hpw : L.Pairwise (· < ·) := by
    rw [hLdef, List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp (by intro a b hab; omega)
  have hlen : L.length ≤ x3 := by
    rw [hLdef, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have rep3 : ∀ (i : Fin L.length) (k : ℕ), k < L.get i → x5 k ≠ ∅ →
      x5 k ∈ List.map x5 (List.range x2 ++ List.take i L) := by
    intro i k hk hke
    obtain ⟨m, hmk, hme, hK⟩ := rep x5 k hke
    have hi := (hmem (L.get i)).1 (List.get_mem L i)
    refine List.mem_map.2 ⟨m, ?_, hme⟩
    rw [List.mem_append]
    by_cases hm2 : m < x2
    · exact Or.inl (List.mem_range.2 hm2)
    · exact Or.inr (take_mem L hpw i m ((hmem m).2 ⟨by omega, by omega, hK⟩) (by omega))
  refine ⟨L, hlen, fun m hm => ⟨((hmem m).1 hm).1, ((hmem m).1 hm).2.1⟩, ?_, ?_⟩
  · obtain ⟨m, hmk, hme, hK⟩ := rep x5 x4 hne
    refine List.mem_map.2 ⟨m, ?_, hme⟩
    rw [List.mem_append]
    by_cases hm2 : m < x2
    · exact Or.inl (List.mem_range.2 hm2)
    · exact Or.inr ((hmem m).2 ⟨by omega, by omega, hK⟩)
  · intro i
    obtain ⟨h1, h2, hK1, hK2⟩ := (hmem (L.get i)).1 (List.get_mem L i)
    have p1 : ∀ m ∈ List.range x2 ++ List.take i L, m < L.get i := by
      intro m hm
      rcases List.mem_append.1 hm with a | a
      · have := List.mem_range.1 a
        omega
      · exact take_lt L hpw i m a
    refine ⟨p1, hK1, ?_, ?_⟩
    · intro hc
      obtain ⟨m, hm, hme⟩ := List.mem_map.1 hc
      exact hK2 m (p1 m hm) hme
    · obtain ⟨a, b, hab, hin⟩ := h (L.get i - x2) (by omega)
      have e : x2 + (L.get i - x2) = L.get i := by omega
      rw [e] at hab hin
      have ha : a < L.get i := by omega
      have hb : b < L.get i := by omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with hu | hc | he | hi
      · have hA : ¬ x5 a ⊆ x5 b := fun hs => hK2 b hb (by rw [hu, Set.union_eq_right.2 hs])
        have hB : ¬ x5 b ⊆ x5 a := fun hs => hK2 a ha (by rw [hu, Set.union_eq_left.2 hs])
        have hae : x5 a ≠ ∅ := fun e2 => hA (by rw [e2]; exact Set.empty_subset _)
        have hbe : x5 b ≠ ∅ := fun e2 => hB (by rw [e2]; exact Set.empty_subset _)
        exact ⟨x5 a, rep3 i a ha hae, x5 b, rep3 i b hb hbe, hA, hB, Or.inl hu⟩
      · exact absurd hc.symm (hK2 a ha)
      · exact absurd he hK1
      · have hA : ¬ x5 a ⊆ x5 b := fun hs => hK2 a ha (by rw [hi, Set.inter_eq_left.2 hs])
        have hB : ¬ x5 b ⊆ x5 a := fun hs => hK2 b hb (by rw [hi, Set.inter_eq_right.2 hs])
        have hae : x5 a ≠ ∅ := fun e2 => hA (by rw [e2]; exact Set.empty_subset _)
        have hbe : x5 b ≠ ∅ := fun e2 => hB (by rw [e2]; exact Set.empty_subset _)
        exact ⟨x5 a, rep3 i a ha hae, x5 b, rep3 i b hb hbe, hA, hB, Or.inr hi⟩
