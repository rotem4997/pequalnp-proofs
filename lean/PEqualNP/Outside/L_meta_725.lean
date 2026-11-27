import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_725 : ∀ (n t t1 : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t) → (∀ T : Finset (Fin n), (∀ c d : Fin n, G.Adj c d → c ∈ T ∨ d ∈ T) → t ≤ T.card) → (∃ U : Finset (Fin n), (∀ e f : Fin n, G.Adj e f → e ≠ v → f ≠ v → e ∈ U ∨ f ∈ U) ∧ U.card = t1) → (∀ W : Finset (Fin n), (∀ g h : Fin n, G.Adj g h → g ≠ v → h ≠ v → g ∈ W ∨ h ∈ W) → t1 ≤ W.card) → t ≤ t1 + 1 ∧ t1 ≤ t ∧ (t1 + 1 = t ↔ ∃ X : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ X ∨ j ∈ X) ∧ X.card = t ∧ v ∈ X) := by
  intro n t t1 G v ⟨S, hS, hSc⟩ hmin ⟨U, hU, hUc⟩ hmin1
  have hUv : ∀ a b : Fin n, G.Adj a b → a ∈ insert v U ∨ b ∈ insert v U := by
    intro a b hab
    by_cases ha : a = v
    · left; simp [ha]
    by_cases hb : b = v
    · right; simp [hb]
    rcases hU a b hab ha hb with h | h
    · left; exact Finset.mem_insert_of_mem h
    · right; exact Finset.mem_insert_of_mem h
  have h1 : t ≤ t1 + 1 := by
    have := hmin _ hUv
    have := Finset.card_insert_le v U
    omega
  have h2 : t1 ≤ t := by
    have := hmin1 S (fun a b hab _ _ => hS a b hab)
    omega
  refine ⟨h1, h2, ?_⟩
  constructor
  · intro heq
    refine ⟨insert v U, hUv, ?_, Finset.mem_insert_self v U⟩
    have := hmin _ hUv
    have := Finset.card_insert_le v U
    omega
  · rintro ⟨X, hX, hXc, hvX⟩
    have hE : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ X.erase v ∨ b ∈ X.erase v := by
      intro a b hab ha hb
      rcases hX a b hab with h | h
      · left; exact Finset.mem_erase.mpr ⟨ha, h⟩
      · right; exact Finset.mem_erase.mpr ⟨hb, h⟩
    have := hmin1 _ hE
    have := Finset.card_erase_of_mem hvX
    have : 0 < X.card := Finset.card_pos.mpr ⟨v, hvX⟩
    omega
