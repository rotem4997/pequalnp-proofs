import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7471 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => Fin.castAdd (13 : ℕ) x2; have x3 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x3 : Fin (13 : ℕ)) => Fin.natAdd (13 : ℕ) x3; have x4 : (Fin (13 : ℕ) → Fin (26 : ℕ)) → Finset (Fin (26 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Fin (13 : ℕ) → Fin (26 : ℕ)) (x5 : Finset (Fin (26 : ℕ))) => {x6 : Fin (13 : ℕ) | x4 x6 ∉ x5}; have x5 : Finset (Fin (26 : ℕ)) → Prop := fun (x5 : Finset (Fin (26 : ℕ))) => ∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x6 ∈ x5 ∨ x3 x7 ∈ x5; have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x1 x8 x7}; ∀ (x7 : Set (Finset (Fin (26 : ℕ)))),   have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x8 x9 : Finset (Fin (13 : ℕ))) => ∃ x10 ∈ x7, (∀ x11 ∈ x8, x2 x11 ∉ x10) ∧ ∀ x11 ∈ x9, x3 x11 ∉ x10;   (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → ¬x8 {x9} {x10}) → (∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x8 x10 (x6 x10) ∧ x8 (x6 x10) x10) → (∀ x11 ∈ x7, x5 x11) ∧ ∀ (x11 : Finset (Fin (26 : ℕ))), Minimal x5 x11 → (x4 x2 x11).card ≤ (3 : ℕ) ∨ (x4 x3 x11).card ≤ (3 : ℕ) → x11 ∈ x7 := by
  intro x1
  simp only []
  intro x7 h1 h2
  have hsym : ∀ a b : Fin 13, x1 a b → x1 b a := by
    intro a b h
    simp only [x1] at h ⊢
    rwa [Nat.add_comm]
  have hcov : ∀ x11 ∈ x7, ∀ (a b : Fin 13), x1 a b → Fin.castAdd 13 a ∈ x11 ∨ Fin.natAdd 13 b ∈ x11 := by
    intro x11 hm a b hab
    by_contra hc
    rw [not_or] at hc
    exact h1 a b hab ⟨x11, hm, by simpa using hc.1, by simpa using hc.2⟩
  refine ⟨hcov, ?_⟩
  intro x11 hmin hc
  obtain ⟨hP, hle⟩ := hmin
  rcases hc with hc | hc
  · obtain ⟨⟨x10, hm, hL, hR⟩, _⟩ := h2 _ hc
    have hsub : ∀ z : Fin (13 + 13), z ∈ x10 → z ∈ x11 := by
      intro z
      induction z using Fin.addCases with
      | left a =>
        intro hz
        by_contra hn
        exact hL a (by simpa using hn) hz
      | right b =>
        intro hz
        by_contra hn
        apply hR b _ hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro a ha hab
        rcases hP a b hab with h | h
        · exact (by simpa using ha : Fin.castAdd 13 a ∉ x11) h
        · exact hn h
    have := le_antisymm (hle (hcov x10 hm) hsub) hsub
    rw [this]
    exact hm
  · obtain ⟨_, ⟨x10, hm, hL, hR⟩⟩ := h2 _ hc
    have hsub : ∀ z : Fin (13 + 13), z ∈ x10 → z ∈ x11 := by
      intro z
      induction z using Fin.addCases with
      | right b =>
        intro hz
        by_contra hn
        exact hR b (by simpa using hn) hz
      | left a =>
        intro hz
        by_contra hn
        apply hL a _ hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro b hb hba
        rcases hP a b (hsym b a hba) with h | h
        · exact hn h
        · exact (by simpa using hb : Fin.natAdd 13 b ∉ x11) h
    have := le_antisymm (hle (hcov x10 hm) hsub) hsub
    rw [this]
    exact hm
