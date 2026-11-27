import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6654
open PEqualNP.CircuitLowerBounds



theorem plane (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (L l).card = q + 1) (huniq : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ L l ∧ b ∈ L l) :
    (∀ p : Fin N, (Finset.univ.filter fun l => p ∈ L l).card = q + 1) ∧
    ∀ l l' : Fin N, l ≠ l' → (L l ∩ L l').card = 1 := by
  classical
  have huq : ∀ a b l l', a ≠ b → a ∈ L l → b ∈ L l → a ∈ L l' → b ∈ L l' → l = l' := by
    intro a b l l' hab h1 h2 h3 h4
    obtain ⟨m, _, hm⟩ := huniq a b hab
    rw [hm l ⟨h1, h2⟩, hm l' ⟨h3, h4⟩]
  have hNc : (Finset.univ : Finset (Fin N)).card = q ^ 2 + q + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hN
  have he : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  have h1 : ∀ p : Fin N, (Finset.univ.filter fun l => p ∈ L l).card = q + 1 := by
    intro p
    have hdisj : ∀ l ∈ (Finset.univ.filter fun l => p ∈ L l),
        ∀ l' ∈ (Finset.univ.filter fun l => p ∈ L l), l ≠ l' →
        Disjoint ((L l).erase p) ((L l').erase p) := by
      intro l hl l' hl' hne
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact hne (huq x p l l' (Finset.mem_erase.1 hx).1 (Finset.mem_erase.1 hx).2
        (Finset.mem_filter.1 hl).2 (Finset.mem_erase.1 hx').2 (Finset.mem_filter.1 hl').2)
    have hU : (Finset.univ.filter fun l => p ∈ L l).biUnion (fun l => (L l).erase p)
        = Finset.univ.erase p := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · rintro ⟨l, _, hxp, _⟩
        exact hxp
      · intro hxp
        obtain ⟨l, ⟨hx, hp⟩, _⟩ := huniq x p hxp
        exact ⟨l, hp, hxp, hx⟩
    have hc := Finset.card_biUnion hdisj
    rw [hU, Finset.card_erase_of_mem (Finset.mem_univ p), hNc, he] at hc
    have hs : ∀ l ∈ (Finset.univ.filter fun l => p ∈ L l), ((L l).erase p).card = q := by
      intro l hl
      rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hl).2, hL l]
      omega
    rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul] at hc
    exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) hc).symm
  refine ⟨h1, ?_⟩
  intro l l' hne
  have hle : (L l ∩ L l').card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    exact hne (huq a b l l' hab (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 hb).1
      (Finset.mem_inter.1 ha).2 (Finset.mem_inter.1 hb).2)
  have hge : (L l ∩ L l').Nonempty := by
    have hdisj : ∀ p ∈ L l, ∀ p' ∈ L l, p ≠ p' →
        Disjoint ((Finset.univ.filter fun m => p ∈ L m).erase l)
          ((Finset.univ.filter fun m => p' ∈ L m).erase l) := by
      intro p hp p' hp' hpp
      rw [Finset.disjoint_left]
      intro m hm hm'
      have a1 := (Finset.mem_filter.1 (Finset.mem_erase.1 hm).2).2
      have a2 := (Finset.mem_filter.1 (Finset.mem_erase.1 hm').2).2
      exact (Finset.mem_erase.1 hm).1 (huq p p' m l hpp a1 a2 hp hp')
    have hc := Finset.card_biUnion hdisj
    have hs : ∀ p ∈ L l, ((Finset.univ.filter fun m => p ∈ L m).erase l).card = q := by
      intro p hp
      have hml : l ∈ (Finset.univ.filter fun m => p ∈ L m) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
      rw [Finset.card_erase_of_mem hml, h1 p]
      omega
    rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, hL l] at hc
    have hsubM : (L l).biUnion (fun p => (Finset.univ.filter fun m => p ∈ L m).erase l)
        ⊆ Finset.univ.erase l := by
      intro m hm
      obtain ⟨p, _, hm'⟩ := Finset.mem_biUnion.1 hm
      exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hm').1, Finset.mem_univ _⟩
    have hcard2 : (Finset.univ.erase l).card = (q + 1) * q := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ l), hNc, he]
    have heq := Finset.eq_of_subset_of_card_le hsubM (by rw [hcard2, hc])
    have hl' : l' ∈ Finset.univ.erase l := Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ _⟩
    rw [← heq] at hl'
    obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.1 hl'
    exact ⟨p, Finset.mem_inter.2 ⟨hp, (Finset.mem_filter.1 (Finset.mem_erase.1 hm).2).2⟩⟩
  have hpos := Finset.card_pos.2 hge
  omega

end PEqualNP.Outside.L_meta_6654

open PEqualNP.Outside.L_meta_6654 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6654 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x9 x10 } = x1 + (1 : ℕ)) ∧ ∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x12 x9 ∧ x3 x12 x10 := by
  intro q N R _ hq hN hL huniq
  have H := plane q N (fun l => Finset.univ.filter fun p => R p l) (by omega) hN
    (fun l => by rw [← Fintype.card_subtype]; exact hL l)
    (fun a b hab => by simpa using huniq a b hab)
  refine ⟨fun p => ?_, fun l l' hne => ?_⟩
  · rw [Fintype.card_subtype]
    have h := H.1 p
    simpa using h
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 (H.2 l l' hne)
    have hxm : x ∈ (Finset.univ.filter fun p => R p l) ∩ (Finset.univ.filter fun p => R p l') := by
      rw [hx]; exact Finset.mem_singleton_self x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hxm
    refine ⟨x, hxm, fun y hy => ?_⟩
    have hym : y ∈ (Finset.univ.filter fun p => R p l) ∩ (Finset.univ.filter fun p => R p l') := by
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy
    rw [hx] at hym
    exact Finset.mem_singleton.1 hym
