import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9010_aux

open PEqualNP.HeptadCover

theorem through : ∀ x : Fin 13, x ∈ singerLines3 (x - 0) ∧ x ∈ singerLines3 (x - 1) ∧
    x ∈ singerLines3 (x - 3) ∧ x ∈ singerLines3 (x - 9) := by
  decide

theorem key : ∀ x : Fin 13, ∀ a ∈ (singerLines3 (x - 0)).erase x,
    ∀ b ∈ (singerLines3 (x - 1)).erase x, ∀ c ∈ (singerLines3 (x - 3)).erase x,
    ∀ d ∈ (singerLines3 (x - 9)).erase x, ∃ l : Fin 13,
    2 < (({a, b, c, d} : Finset (Fin 13)) ∩ singerLines3 l).card := by
  decide +kernel

end PEqualNP.Outside.L_meta_9010_aux

theorem PEqualNP.Outside.L_meta_9010 : ∀ x1 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, ∀ x3 ∉ x1, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5 := by
  intro Q hQ x hx
  by_contra h
  push_neg at h
  have hQ2 : ∀ l : Fin 13, (Q ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2 := by
    simp only [PEqualNP.HeptadCover.quadrangles, Finset.mem_filter] at hQ
    exact hQ.2
  have meet : ∀ k : Fin 13, x ∈ PEqualNP.HeptadCover.singerLines3 (x - k) →
      ∃ a ∈ (PEqualNP.HeptadCover.singerLines3 (x - k)).erase x, a ∈ Q := by
    intro k hk
    have h1 : x - k ∉ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q :=
      fun hm => h _ hm hk
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_disjoint_iff] at h1
    obtain ⟨a, ha1, ha2⟩ := h1
    exact ⟨a, Finset.mem_erase.2 ⟨fun e => hx (e ▸ ha2), ha1⟩, ha2⟩
  obtain ⟨t0, t1, t3, t9⟩ := PEqualNP.Outside.L_meta_9010_aux.through x
  obtain ⟨a, ha, haQ⟩ := meet 0 t0
  obtain ⟨b, hb, hbQ⟩ := meet 1 t1
  obtain ⟨c, hc, hcQ⟩ := meet 3 t3
  obtain ⟨d, hd, hdQ⟩ := meet 9 t9
  obtain ⟨l, hl⟩ := PEqualNP.Outside.L_meta_9010_aux.key x a ha b hb c hc d hd
  have hsub : ({a, b, c, d} : Finset (Fin 13)) ∩ PEqualNP.HeptadCover.singerLines3 l ⊆
      Q ∩ PEqualNP.HeptadCover.singerLines3 l := by
    apply Finset.inter_subset_inter_right
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  have := hQ2 l
  omega
