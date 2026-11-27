import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4239

def inc (p l : Fin 13) : Bool := (523 : ℕ).testBit ((p.val + 13 - l.val) % 13)

def ln (l : Fin 13) : Finset (Fin 13) := Finset.univ.filter fun p => inc p l = true

def pn (p : Fin 13) : Finset (Fin 13) := Finset.univ.filter fun l => inc p l = true

def ms (X : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ X, ¬ inc p l = true

def mp (Y : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => ∀ l ∈ Y, ¬ inc p l = true

theorem inc_iff : ∀ p l : Fin 13, inc p l = true ↔
    ∃ c ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + c := by
  decide +kernel

theorem c1 : ∀ l : Fin 13, (ln l).card = 4 ∧ (ms (ln l)).card = 0 := by
  decide +kernel

theorem c2 : ∀ p : Fin 13, (pn p).card = 4 ∧ (mp (pn p)).card = 0 := by
  decide +kernel

theorem c3 : ∀ p a : Fin 13, a ∈ pn p → (mp ((pn p).erase a)).card = 3 ∧
    ∃ l, ∀ q ∈ mp ((pn p).erase a), inc q l = true := by
  decide +kernel

theorem k1 (l : Fin 13) (X : Finset (Fin 13)) (hX : X ⊆ ln l) :
    X.card ≤ 2 ∨ (ms X).card ≤ 2 ∨ X.card = 3 := by
  have h := Finset.card_le_card hX
  have h4 := c1 l
  by_cases h' : X.card = 4
  · have e : X = ln l := Finset.eq_of_subset_of_card_le hX (by omega)
    rw [e, h4.2]
    simp
  · omega

theorem k2 (p : Fin 13) (Y : Finset (Fin 13)) (hY : Y ⊆ pn p) :
    (mp Y).card ≤ 2 ∨ Y.card ≤ 2 ∨ ((mp Y).card = 3 ∧ ∃ l, ∀ q ∈ mp Y, inc q l = true) := by
  have h := Finset.card_le_card hY
  have h4 := c2 p
  have h' : Y.card ≤ 2 ∨ Y.card = 3 ∨ Y.card = 4 := by omega
  rcases h' with h' | h' | h'
  · exact Or.inr (Or.inl h')
  · have hd : (pn p \ Y).card = 1 := by
      rw [Finset.card_sdiff_of_subset hY]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hd
    have ham : a ∈ pn p \ Y := by rw [ha]; exact Finset.mem_singleton_self a
    have e : Y = (pn p).erase a := by
      rw [← Finset.sdiff_singleton_eq_erase, ← ha, Finset.sdiff_sdiff_eq_self hY]
    have := c3 p a (Finset.mem_sdiff.1 ham).1
    rw [← e] at this
    exact Or.inr (Or.inr this)
  · have e : Y = pn p := Finset.eq_of_subset_of_card_le hY (by omega)
    rw [e, h4.2]
    simp

theorem k3 : ∀ a b : Fin 13, ∃ l, inc a l = true ∧ inc b l = true := by
  decide +kernel

theorem k4 : ∀ a b : Fin 13, ∃ p, inc p a = true ∧ inc p b = true := by
  decide +kernel

theorem two (X : Finset (Fin 13)) (h : X.card ≤ 2) : ∃ a b, ∀ q ∈ X, q = a ∨ q = b := by
  have h' : X.card = 0 ∨ X.card = 1 ∨ X.card = 2 := by omega
  rcases h' with h | h | h
  · rw [Finset.card_eq_zero] at h
    exact ⟨0, 0, fun q hq => by simp [h] at hq⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    exact ⟨a, a, fun q hq => Or.inl (Finset.mem_singleton.1 hq)⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.1 h
    exact ⟨a, b, fun q hq => by simpa using hq⟩

theorem main (X : Finset (Fin 13))
    (hX : ∀ p, p ∉ X → ∃ l, (∀ q ∈ X, ¬ inc q l = true) ∧ inc p l = true) :
    ((∃ l, ∀ p ∈ X, inc p l = true) ∨ ∃ p, ∀ l, (∀ q ∈ X, ¬ inc q l = true) → inc p l = true) ↔
    (X.card ≤ 2 ∨ (ms X).card ≤ 2 ∨ (X.card = 3 ∧ ∃ l, ∀ p ∈ X, inc p l = true)) := by
  have mem : ∀ l, l ∈ ms X ↔ ∀ q ∈ X, ¬ inc q l = true := fun l => by simp [ms]
  constructor
  · rintro (⟨l, hl⟩ | ⟨p, hp⟩)
    · rcases k1 l X (fun q hq => by simpa [ln] using hl q hq) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, l, hl⟩)
    · have hXY : mp (ms X) = X := by
        ext q
        simp only [mp, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          by_contra hq
          obtain ⟨l, h1, h2⟩ := hX q hq
          exact h l ((mem l).2 h1) h2
        · intro hq l hl
          exact (mem l).1 hl q hq
      have h := k2 p (ms X) (fun l hl => by
        simpa [pn] using hp l ((mem l).1 hl))
      rwa [hXY] at h
  · rintro (h | h | ⟨_, h⟩)
    · obtain ⟨a, b, hab⟩ := two X h
      obtain ⟨l, h1, h2⟩ := k3 a b
      exact Or.inl ⟨l, fun p hp => by rcases hab p hp with rfl | rfl <;> assumption⟩
    · obtain ⟨a, b, hab⟩ := two _ h
      obtain ⟨p, h1, h2⟩ := k4 a b
      exact Or.inr ⟨p, fun l hl => by rcases hab l ((mem l).2 hl) with rfl | rfl <;> assumption⟩
    · exact Or.inl h

end PEqualNP.Outside.L_meta_4239

open PEqualNP.Outside.L_meta_4239 in
theorem PEqualNP.Outside.L_meta_4239 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; ∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7) → (((∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x4 x7 → x2 x6 x7) ↔ x4.card ≤ (2 : ℕ) ∨ Nat.card { x6 : Fin (13 : ℕ) // x3 x4 x6 } ≤ (2 : ℕ) ∨ x4.card = (3 : ℕ) ∧ ∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x2 x7 x6) := by
  simp only [← inc_iff]
  intro X hX
  have e : Nat.card {l : Fin 13 // ∀ q ∈ X, ¬ inc q l = true} = (ms X).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [e]
  exact main X hX
