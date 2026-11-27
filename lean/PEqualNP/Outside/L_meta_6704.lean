import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6704

lemma lines_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (c : Fin N) :
    (Finset.univ.filter (fun l => I c l)).card = q + 1 := by
  have e : (Finset.univ.filter (fun l => I c l)).biUnion
      (fun l => (Finset.univ.filter (fun p => I p l)).erase c) = Finset.univ.erase c := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨l, _, hp, _⟩
      exact hp
    · intro hp
      obtain ⟨l, ⟨h1, h2⟩, _⟩ := hu p c hp
      exact ⟨l, h2, hp, h1⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I c l), ∀ l' ∈ Finset.univ.filter (fun l => I c l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p => I p l)).erase c)
        ((Finset.univ.filter (fun p => I p l')).erase c) := by
    intro l hl1 l' hl1' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hl1 hl1' hp hp'
    obtain ⟨l0, _, hun⟩ := hu p c hp.1
    exact hne ((hun l ⟨hp.2, hl1⟩).trans (hun l' ⟨hp'.2, hl1'⟩).symm)
  have hc := Finset.card_biUnion hd
  rw [e] at hc
  have hs : ∀ l ∈ Finset.univ.filter (fun l => I c l),
      ((Finset.univ.filter (fun p => I p l)).erase c).card = q := by
    intro l hl1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1
    rw [Finset.card_erase_of_mem (by simp [hl1]), hl l]
    rfl
  rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin] at hc
  have h3 : (Finset.univ.filter (fun l => I c l)).card * q = (q + 1) * q := by
    rw [← hc, hN]
    have : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
      rw [Nat.add_sub_cancel]
      ring
    exact this
  exact Nat.eq_of_mul_eq_mul_right (by omega) h3

lemma meet (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (L M : Fin N) (hLM : L ≠ M) :
    ∃ p, I p L ∧ I p M := by
  by_contra hno
  push_neg at hno
  have hpc := lines_card q N I hq hN hl hu
  set S := Finset.univ.filter (fun p => I p L) with hS
  have hT : ∀ p ∈ S, ((Finset.univ.filter (fun l => I p l)).erase L).card = q := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ L, hp.2⟩), hpc p]
    rfl
  have hdisj : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' →
      Disjoint ((Finset.univ.filter (fun l => I p l)).erase L)
        ((Finset.univ.filter (fun l => I p' l)).erase L) := by
    intro p hp p' hp' hne
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    rw [hS, Finset.mem_filter] at hp hp'
    rw [Finset.mem_erase, Finset.mem_filter] at hl1 hl2
    obtain ⟨m, _, hm⟩ := hu p p' hne
    exact hl1.1 ((hm l ⟨hl1.2.2, hl2.2.2⟩).trans (hm L ⟨hp.2, hp'.2⟩).symm)
  have hcard : (S.biUnion (fun p => (Finset.univ.filter (fun l => I p l)).erase L)).card
      = (q + 1) * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hT, hl L]
  have hsub : S.biUnion (fun p => (Finset.univ.filter (fun l => I p l)).erase L)
      ⊆ (Finset.univ.erase L).erase M := by
    intro l hl1
    rw [Finset.mem_biUnion] at hl1
    obtain ⟨p, hp, hl1⟩ := hl1
    rw [hS, Finset.mem_filter] at hp
    rw [Finset.mem_erase, Finset.mem_filter] at hl1
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, hl1.1, Finset.mem_univ l⟩
    rintro rfl
    exact hno p hp.2 hl1.2.2
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hLM.symm, Finset.mem_univ M⟩),
    Finset.card_erase_of_mem (Finset.mem_univ L), Finset.card_univ, Fintype.card_fin, hN] at h1
  have : (q + 1) * q = q ^ 2 + q := by ring
  omega

end PEqualNP.Outside.L_meta_6704

theorem PEqualNP.Outside.L_meta_6704 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x6 : Fin x2), (x3 x6).card = x1 + (1 : ℕ)) → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x7 ∈ x3 x10 ∧ x8 ∈ x3 x10) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x8 ∈ x3 x9 } = x1 + (1 : ℕ)) ∧ ∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card = (1 : ℕ) := by
  intro q N L hq hN hcard hu
  have hl : ∀ l : Fin N, (Finset.univ.filter (fun p => p ∈ L l)).card = q + 1 := by
    intro l
    have e : Finset.univ.filter (fun p => p ∈ L l) = L l := by
      ext r
      simp
    rw [e, hcard l]
  constructor
  · intro p
    rw [Fintype.card_subtype]
    exact PEqualNP.Outside.L_meta_6704.lines_card q N (fun p l => p ∈ L l) hq hN hl hu p
  · intro a b hab
    obtain ⟨p, hpa, hpb⟩ :=
      PEqualNP.Outside.L_meta_6704.meet q N (fun p l => p ∈ L l) hq hN hl hu a b hab
    rw [Finset.card_eq_one]
    refine ⟨p, ?_⟩
    ext r
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hra, hrb⟩
      by_contra hrp
      obtain ⟨m, _, hm⟩ := hu r p hrp
      exact hab ((hm a ⟨hra, hpa⟩).trans (hm b ⟨hrb, hpb⟩).symm)
    · rintro rfl
      exact ⟨hpa, hpb⟩
