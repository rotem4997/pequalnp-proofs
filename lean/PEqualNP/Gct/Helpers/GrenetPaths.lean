import PEqualNP.Gct.Helpers.BorderedPerm

/-! Helper module, proofs only. The path sums of the subset graph: for weights `w s j` (step
number `s`, added element `j`), `pathSum w s S` is the sum over the ways to build the set `S`
in `s` steps of the product of the weights. It equals a permanent, by the expansion of the
permanent along its last row. -/

namespace PEqualNP.Gct.Helpers.Grenet

open Finset

variable {A : Type*} [CommRing A] {m : ℕ}

/-- The weighted number of ways to build `S` by adding one element at a time, in `s` steps. -/
def pathSum (w : ℕ → Fin m → A) : ℕ → Finset (Fin m) → A
  | 0, _ => 1
  | s + 1, S => ∑ j ∈ S, pathSum w s (S.erase j) * w s j

theorem pathSum_zero (w : ℕ → Fin m → A) (S : Finset (Fin m)) : pathSum w 0 S = 1 := rfl

theorem pathSum_succ (w : ℕ → Fin m → A) (s : ℕ) (S : Finset (Fin m)) :
    pathSum w (s + 1) S = ∑ j ∈ S, pathSum w s (S.erase j) * w s j := rfl

/-- The path sum of the image of an injection of `Fin s` is the permanent of the matrix of
weights with rows the steps and columns read through the injection. -/
theorem pathSum_eq_permanent (w : ℕ → Fin m → A) :
    ∀ (s : ℕ) (e : Fin s → Fin m), Function.Injective e →
      pathSum w s (univ.image e) =
        Matrix.permanent (Matrix.of fun (i k : Fin s) => w i (e k)) := by
  intro s
  induction s with
  | zero =>
    intro e _
    rw [pathSum_zero, Matrix.permanent_isEmpty]
  | succ s ih =>
    intro e he
    rw [pathSum_succ, Finset.sum_image (fun a _ b _ h => he h),
      BorderedPerm.permanent_succ_last_row]
    refine Finset.sum_congr rfl fun k _ => ?_
    have himg : (univ.image e).erase (e k) = univ.image (e ∘ k.succAbove) := by
      ext x
      simp only [mem_erase, mem_image, mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro ⟨hx, a, rfl⟩
        have hak : a ≠ k := fun h => hx (by rw [h])
        obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hak
        exact ⟨b, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨fun h => Fin.succAbove_ne k b (he h), _, rfl⟩
    rw [himg, ih _ (he.comp Fin.succAbove_right_injective), mul_comm]
    simp only [Matrix.of_apply, Fin.val_last]
    rfl

end PEqualNP.Gct.Helpers.Grenet
