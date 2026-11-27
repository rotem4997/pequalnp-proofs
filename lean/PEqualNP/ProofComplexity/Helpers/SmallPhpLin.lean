import PEqualNP.Defs
import Mathlib.Tactic

/-!
# The smallest pigeonhole formula has no one-line Res(+) refutation

Helper module (proofs only, no statement may use it). A derivation of one line is a single
axiom, and no clause of `PHP 2 1` is empty.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem php21_no_empty : (∅ : Clause (Fin 2 × Fin 1)) ∉ PHP 2 1 := by
  rintro (⟨i, h⟩ | ⟨i, i', j, -, h⟩)
  · have : ((i, (0 : Fin 1)), true) ∈ (∅ : Clause (Fin 2 × Fin 1)) := by
      rw [h]; simp
    simp at this
  · have : ((i, j), false) ∈ (∅ : Clause (Fin 2 × Fin 1)) := by
      rw [h]; simp
    simp at this

theorem php21_len (π : List (LinClause (Fin 2 × Fin 1)))
    (h : IsLinRefutation (PHP 2 1) π) : 1 < π.length := by
  obtain ⟨hd, hmem⟩ := h
  cases hd with
  | nil => simp at hmem
  | @ax π' C hπ hC =>
    cases π' with
    | nil =>
      simp only [List.mem_singleton] at hmem
      obtain ⟨C0, hC0, hEq⟩ := hC
      exfalso
      have hC0e : C0 = ∅ := by
        simp only [linOfClause] at hEq
        rw [← hmem] at hEq
        exact Finset.image_eq_empty.mp hEq
      exact php21_no_empty (hC0e ▸ hC0)
    | cons a t => simp
  | @res π' C D R hπ hC hD hR =>
    cases π' with
    | nil => simp at hC
    | cons a t => simp
  | @weak π' C D hπ hC hW =>
    cases π' with
    | nil => simp at hC
    | cons a t => simp

end PEqualNP.ProofComplexity.Helpers
