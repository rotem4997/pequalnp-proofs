import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7744

def Step (A : List ℕ) (w : ℕ) := ∃ a ∈ A, ∃ b ∈ A, w = a &&& b ∨ w = a ||| b

def Legal (A U : List ℕ) := ∀ i : Fin U.length, Step (A ++ U.take i.val) (U.get i)

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

theorem legal_nil (A : List ℕ) : Legal A [] := fun i => Fin.elim0 i

theorem legal_prefix (B X : List ℕ) : ∀ Y : List ℕ, Legal B (X ++ Y) → Legal B X := by
  intro Y
  induction Y using List.reverseRecOn with
  | nil => intro h; simpa using h
  | append_singleton Y y ih =>
    intro h
    rw [← List.append_assoc] at h
    exact ih ((snoc_iff B (X ++ Y) y).mp h).1

theorem legal_suffix (B X : List ℕ) : ∀ Y : List ℕ, Legal B (X ++ Y) → Legal (B ++ X) Y := by
  intro Y
  induction Y using List.reverseRecOn with
  | nil => intro _; exact legal_nil _
  | append_singleton Y y ih =>
    intro h
    rw [← List.append_assoc] at h
    obtain ⟨h0, st⟩ := (snoc_iff B (X ++ Y) y).mp h
    refine (snoc_iff (B ++ X) Y y).mpr ⟨ih h0, ?_⟩
    simpa [List.append_assoc] using st

theorem filter_len (w : ℕ) : ∀ S : List ℕ, w ∈ S →
    (S.filter (fun z => decide (z ≠ w))).length + 1 ≤ S.length := by
  intro S
  induction S with
  | nil => intro h; simp at h
  | cons a S ih =>
    intro h
    rw [List.filter_cons]
    by_cases e : a = w
    · subst e
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
        List.length_cons]
      have := List.length_filter_le (fun z => decide ¬z = a) S
      omega
    · have hS : w ∈ S := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm e
        · exact h
      have := ih hS
      simp only [ne_eq] at this
      simp only [ne_eq, e, not_false_eq_true, decide_true, ite_true, List.length_cons]
      omega

theorem frontier (C : List ℕ) : ∀ R : List ℕ, Legal C R → ∀ S : List ℕ, (∀ z ∈ S, z ∈ C ++ R) →
    ∃ (B' L : List ℕ), (∀ z ∈ B', z ∈ C) ∧ L.length ≤ R.length ∧
      B'.length ≤ S.length + L.length ∧ Legal B' L ∧ ∀ z ∈ S, z ∈ B' ++ L := by
  intro R
  induction R using List.reverseRecOn with
  | nil =>
    intro _ S hS
    refine ⟨S, [], ?_, by simp, by simp, legal_nil _, ?_⟩
    · intro z hz; simpa using hS z hz
    · intro z hz; simpa using hz
  | append_singleton R0 w ih =>
    intro h S hS
    obtain ⟨h0, st⟩ := (snoc_iff C R0 w).mp h
    by_cases hw : w ∈ S
    · obtain ⟨x, hx, y, hy, op⟩ := st
      have hS' : ∀ z ∈ x :: y :: S.filter (fun z => decide (z ≠ w)), z ∈ C ++ R0 := by
        intro z hz
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hz
        rcases hz with rfl | rfl | ⟨hzS, hne⟩
        · exact hx
        · exact hy
        · have := hS z hzS
          simp only [List.mem_append, List.mem_singleton] at this
          rcases this with h1 | h1 | h1
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ h1
          · exact absurd h1 hne
      obtain ⟨B', L0, hB, hlen, hcard, hleg, hcov⟩ := ih h0 _ hS'
      have hxc : x ∈ B' ++ L0 := hcov x (by simp)
      have hyc : y ∈ B' ++ L0 := hcov y (by simp)
      refine ⟨B', L0 ++ [w], hB, ?_, ?_, (snoc_iff B' L0 w).mpr ⟨hleg, x, hxc, y, hyc, op⟩, ?_⟩
      · simp; omega
      · have e1 := filter_len w S hw
        simp only [List.length_cons] at hcard
        simp only [List.length_append, List.length_singleton]
        omega
      · intro z hz
        by_cases e : z = w
        · subst e; simp
        · have : z ∈ x :: y :: S.filter (fun z => decide (z ≠ w)) := by
            simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
            exact Or.inr (Or.inr ⟨hz, e⟩)
          have := hcov z this
          simp only [List.mem_append] at this ⊢
          tauto
    · have hS' : ∀ z ∈ S, z ∈ C ++ R0 := by
        intro z hz
        have := hS z hz
        simp only [List.mem_append, List.mem_singleton] at this
        rcases this with h1 | h1 | h1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ h1
        · subst h1; exact absurd hz hw
      obtain ⟨B', L0, hB, hlen, hcard, hleg, hcov⟩ := ih h0 S hS'
      exact ⟨B', L0, hB, by simp; omega, hcard, hleg, hcov⟩

theorem final : ∀ (x2 x3 : List ℕ) (x4 x5 x6 : ℕ), x3.length ≤ x4 + x5 → Legal x2 x3 →
    x6 ∈ x2 ++ x3 → ∃ (x10 : List ℕ), x10.length ≤ x4 ∧ Legal x2 x10 ∧
      ∃ (x11 : List ℕ) (x12 : List ℕ), x11.length ≤ x5 + (1 : ℕ) ∧ (∀ x13 ∈ x11, x13 ∈ x2 ++ x10) ∧
        x12.length ≤ x5 ∧ Legal x11 x12 ∧ x6 ∈ x11 ++ x12 := by
  intro B L a b v hlen hleg hv
  by_cases hk : L.length ≤ a
  · refine ⟨L, hk, hleg, [v], [], by simp, ?_, by simp, legal_nil _, by simp⟩
    intro z hz
    simp only [List.mem_singleton] at hz
    subst hz; exact hv
  · have htd := List.take_append_drop a L
    have hpre : Legal B (L.take a) := legal_prefix B (L.take a) (L.drop a) (by rw [htd]; exact hleg)
    have hsuf : Legal (B ++ L.take a) (L.drop a) :=
      legal_suffix B (L.take a) (L.drop a) (by rw [htd]; exact hleg)
    have hv' : ∀ z ∈ [v], z ∈ (B ++ L.take a) ++ L.drop a := by
      intro z hz
      simp only [List.mem_singleton] at hz
      subst hz
      rw [List.append_assoc, htd]; exact hv
    obtain ⟨B', L', hB, hlen', hcard, hleg', hcov⟩ := frontier _ _ hsuf [v] hv'
    refine ⟨L.take a, List.length_take_le _ _, hpre, B', L', ?_, hB, ?_, hleg', hcov v (by simp)⟩
    · simp only [List.length_singleton] at hcard
      simp only [List.length_drop] at hlen'
      omega
    · simp only [List.length_drop] at hlen'
      omega

end PEqualNP.Outside.L_meta_7744

theorem PEqualNP.Outside.L_meta_7744 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 : List ℕ) (x4 x5 x6 : ℕ), x3.length ≤ x4 + x5 → x1 x2 x3 → x6 ∈ x2 ++ x3 → ∃ (x10 : List ℕ), x10.length ≤ x4 ∧ x1 x2 x10 ∧ ∃ (x11 : List ℕ) (x12 : List ℕ), x11.length ≤ x5 + (1 : ℕ) ∧ (∀ x13 ∈ x11, x13 ∈ x2 ++ x10) ∧ x12.length ≤ x5 ∧ x1 x11 x12 ∧ x6 ∈ x11 ++ x12 :=
  PEqualNP.Outside.L_meta_7744.final
