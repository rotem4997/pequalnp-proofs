import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7519

def Step (A : List ℕ) (w : ℕ) : Prop := ∃ a ∈ A, ∃ b ∈ A, w = a &&& b ∨ w = a ||| b

def Legal (A U : List ℕ) : Prop := ∀ i : Fin U.length, Step (A ++ U.take i.val) (U.get i)

theorem snoc_iff (A U : List ℕ) (w : ℕ) :
    Legal A (U ++ [w]) ↔ Legal A U ∧ Step (A ++ U) w := by
  constructor
  · intro h
    constructor
    · intro i
      have j : i.val < (U ++ [w]).length := by simp
      have hj := h ⟨i.val,j⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
        List.take_append_of_le_length (Nat.le_of_lt i.isLt)] using hj
    · have last : U.length < (U ++ [w]).length := by simp
      simpa [List.get_eq_getElem] using h ⟨U.length,last⟩
  · rintro ⟨ok,step⟩ i
    by_cases early : i.val < U.length
    · simpa only [List.get_eq_getElem,List.getElem_append_left early,
        List.take_append_of_le_length (Nat.le_of_lt early)] using ok ⟨_,early⟩
    · have h : i.val = U.length := by have := i.isLt; simp at this; omega
      simpa [List.get_eq_getElem,h] using step

theorem main (x2 x3 : List ℕ) (R : ℕ → ℕ → Prop)
    (hb : ∀ a ∈ x2, ∃ b ∈ x3, R a b)
    (hop : ∀ a b c d : ℕ, R a c → R b d → R (a &&& b) (c &&& d) ∧ R (a ||| b) (c ||| d))
    (xs : List ℕ) (hx : Legal x2 xs) :
    ∃ ys : List ℕ, ys.length = xs.length ∧ Legal x3 ys ∧ ∀ v ∈ xs, ∃ w ∈ ys, R v w := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[], rfl, fun i => i.elim0, by simp⟩
  | append_singleton xs v ih =>
    rw [snoc_iff] at hx
    obtain ⟨hx, a, ha, b, hb', hv⟩ := hx
    obtain ⟨ys, hlen, hys, hrel⟩ := ih hx
    have lift : ∀ u ∈ x2 ++ xs, ∃ w ∈ x3 ++ ys, R u w := by
      intro u hu
      rcases List.mem_append.1 hu with h | h
      · obtain ⟨w, hw, r⟩ := hb u h
        exact ⟨w, List.mem_append_left _ hw, r⟩
      · obtain ⟨w, hw, r⟩ := hrel u h
        exact ⟨w, List.mem_append_right _ hw, r⟩
    obtain ⟨c, hc, rac⟩ := lift a ha
    obtain ⟨d, hd, rbd⟩ := lift b hb'
    have old : ∀ e : ℕ, ∀ u ∈ xs, ∃ w ∈ ys ++ [e], R u w := by
      intro e u h
      obtain ⟨w, hw, r⟩ := hrel u h
      exact ⟨w, List.mem_append_left _ hw, r⟩
    rcases hv with hv | hv
    · refine ⟨ys ++ [c &&& d], by simp [hlen], ?_, ?_⟩
      · rw [snoc_iff]; exact ⟨hys, c, hc, d, hd, Or.inl rfl⟩
      · intro u hu
        rcases List.mem_append.1 hu with h | h
        · exact old _ u h
        · rw [List.mem_singleton] at h
          rw [h, hv]
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (hop a b c d rac rbd).1⟩
    · refine ⟨ys ++ [c ||| d], by simp [hlen], ?_, ?_⟩
      · rw [snoc_iff]; exact ⟨hys, c, hc, d, hd, Or.inr rfl⟩
      · intro u hu
        rcases List.mem_append.1 hu with h | h
        · exact old _ u h
        · rw [List.mem_singleton] at h
          rw [h, hv]
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (hop a b c d rac rbd).2⟩

end PEqualNP.Outside.L_meta_7519

theorem PEqualNP.Outside.L_meta_7519 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 : List ℕ) (x4 : ℕ → ℕ → Prop), (∀ x5 ∈ x2, ∃ x7 ∈ x3, x4 x5 x7) → (∀ (x6 x7 x8 x9 : ℕ), x4 x6 x8 → x4 x7 x9 → x4 (x6 &&& x7) (x8 &&& x9) ∧ x4 (x6 ||| x7) (x8 ||| x9)) → ∀ (x7 : List ℕ), x1 x2 x7 → ∃ (x9 : List ℕ), x9.length = x7.length ∧ x1 x3 x9 ∧ ∀ x10 ∈ x7, ∃ x12 ∈ x9, x4 x10 x12 :=
  fun x2 x3 x4 hb hop x7 h7 => PEqualNP.Outside.L_meta_7519.main x2 x3 x4 hb hop x7 h7
