import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8589

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8589

theorem PEqualNP.Outside.L_meta_8589 : ∀ (x1 : List (ℕ × ℕ)) (x2 : List (ℕ × ℕ → Bool)) (x3 : ℕ),   have x4 : (List (ℕ × ℕ → Bool) → Bool) → List (ℕ × ℕ → Bool) → Bool := fun (x4 : List (ℕ × ℕ → Bool) → Bool) (x5 : List (ℕ × ℕ → Bool)) => List.casesOn x5 Bool.true fun (x6 : ℕ × ℕ → Bool) (x7 : List (ℕ × ℕ → Bool)) => x1.any fun (x8 : ℕ × ℕ) => x6 x8 && x4 (List.filter (fun (x9 : ℕ × ℕ → Bool) => !x9 x8) x7);   x4^[x3] List.isEmpty x2 = Bool.true → ∃ (x6 : List (ℕ × ℕ)), x6.length ≤ x3 ∧ (∀ x7 ∈ x6, x7 ∈ x1) ∧ ∀ x7 ∈ x2, x6.any x7 = Bool.true := by
  intro P R k step h
  induction k generalizing R with
  | zero =>
    have hR : R = [] := by simpa using h
    subst hR
    exact ⟨[], by simp, by simp, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at h
    rcases R with _ | ⟨q, qs⟩
    · exact ⟨[], by simp, by simp, by simp⟩
    · have h' : (P.any fun p => q p && step^[k] List.isEmpty (qs.filter fun r => !r p)) = true := h
      rw [List.any_eq_true] at h'
      obtain ⟨p, hp, h1⟩ := h'
      rw [Bool.and_eq_true] at h1
      obtain ⟨l, l1, l2, l3⟩ := ih _ h1.2
      refine ⟨p :: l, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hp
        · exact l2 x hx
      · intro r hr
        rw [List.any_cons]
        rcases List.mem_cons.1 hr with rfl | hr
        · rw [h1.1, Bool.true_or]
        · cases hrp : r p
          · rw [Bool.false_or]
            exact l3 r (List.mem_filter.2 ⟨hr, by simp [hrp]⟩)
          · rw [Bool.true_or]
