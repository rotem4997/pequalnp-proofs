import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_137_aux

theorem two (m : ℕ) (x y : Fin m → ℚ) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (hy : ∀ j, y j = 0 ∨ y j = 1) (hxy : x ≠ y) (hs : ∃ j, x j = 1 ∧ y j = 1)
    (p q : ℚ) (h : ∀ j, p * x j + q * y j = 0) : p = 0 ∧ q = 0 := by
  obtain ⟨j, hxj, hyj⟩ := hs
  have e1 := h j
  rw [hxj, hyj] at e1
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
    by_contra hc
    push Not at hc
    exact hxy (funext hc)
  have e2 := h k
  rcases hx k with h1 | h1 <;> rcases hy k with h2 | h2 <;> rw [h1, h2] at e2 hk
  · exact absurd rfl hk
  · constructor <;> linarith
  · constructor <;> linarith
  · exact absurd rfl hk

theorem one_zero (m : ℕ) (r1 r2 r3 : Fin m → ℚ) (h1 : ∀ j, r1 j = 0 ∨ r1 j = 1)
    (h2 : ∀ j, r2 j = 0 ∨ r2 j = 1) (h3 : ∀ j, r3 j = 0 ∨ r3 j = 1) (d12 : r1 ≠ r2)
    (s12 : ∃ j, r1 j = 1 ∧ r2 j = 1) (s13 : ∃ j, r1 j = 1 ∧ r3 j = 1)
    (s23 : ∃ j, r2 j = 1 ∧ r3 j = 1) (a b c : ℚ)
    (h : ∀ j, a * r1 j + b * r2 j + c * r3 j = 0) : a = 0 ∨ b = 0 ∨ c = 0 := by
  obtain ⟨j12, x12, y12⟩ := s12
  obtain ⟨j13, x13, z13⟩ := s13
  obtain ⟨j23, y23, z23⟩ := s23
  obtain ⟨k, hk⟩ : ∃ k, r1 k ≠ r2 k := by
    by_contra hc
    push Not at hc
    exact d12 (funext hc)
  have e12 := h j12
  have e13 := h j13
  have e23 := h j23
  have ek := h k
  rw [x12, y12] at e12
  rw [x13, z13] at e13
  rw [y23, z23] at e23
  rcases h3 j12 with t1 | t1 <;> rw [t1] at e12 <;>
  rcases h2 j13 with t2 | t2 <;> rw [t2] at e13 <;>
  rcases h1 j23 with t3 | t3 <;> rw [t3] at e23 <;>
  rcases h1 k with u1 | u1 <;> rcases h2 k with u2 | u2 <;> rw [u1, u2] at ek hk <;>
  rcases h3 k with u3 | u3 <;> rw [u3] at ek <;>
  first
    | exact absurd rfl hk
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; linarith)

end PEqualNP.Outside.L_meta_137_aux

open PEqualNP.Outside.L_meta_137_aux in
theorem PEqualNP.Outside.L_meta_137 : ∀ (m : ℕ) (r1 r2 r3 : Fin m → ℚ), (∀ j, r1 j = 0 ∨ r1 j = 1) → (∀ j, r2 j = 0 ∨ r2 j = 1) → (∀ j, r3 j = 0 ∨ r3 j = 1) → r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → (∃ j, r1 j = 1 ∧ r2 j = 1) → (∃ j, r1 j = 1 ∧ r3 j = 1) → (∃ j, r2 j = 1 ∧ r3 j = 1) → LinearIndependent ℚ ![r1, r2, r3] := by
  intro m r1 r2 r3 h1 h2 h3 d12 d13 d23 s12 s13 s23
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ j, g 0 * r1 j + g 1 * r2 j + g 2 * r3 j = 0 := by
    intro j
    have := congrFun hg j
    simpa [Fin.sum_univ_three, Finset.sum_apply] using this
  have hz : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
    rcases one_zero m r1 r2 r3 h1 h2 h3 d12 s12 s13 s23 _ _ _ h with ha | hb | hc
    · obtain ⟨hb, hc⟩ := two m r2 r3 h2 h3 d23 s23 (g 1) (g 2)
        (fun j => by have := h j; rw [ha] at this; linarith)
      exact ⟨ha, hb, hc⟩
    · obtain ⟨ha, hc⟩ := two m r1 r3 h1 h3 d13 s13 (g 0) (g 2)
        (fun j => by have := h j; rw [hb] at this; linarith)
      exact ⟨ha, hb, hc⟩
    · obtain ⟨ha, hb⟩ := two m r1 r2 h1 h2 d12 s12 (g 0) (g 1)
        (fun j => by have := h j; rw [hc] at this; linarith)
      exact ⟨ha, hb, hc⟩
  intro i
  fin_cases i
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2
