import Mathlib
import PEqualNP.Defs

-- Coordinates come from directions 0 and 1: x5 inverts c ↦ (x3 0 c, x3 1 c). For a direction
-- x7 ≠ 0, the map x9 ↦ x3 x7 (x5 (0, x9)) is injective, hence a bijection, and x6 x7 is its
-- inverse; for x7 = 1 that map is the identity, so the coordinate conditions hold too.

namespace PEqualNP.Outside.L_meta_7420

end PEqualNP.Outside.L_meta_7420

theorem PEqualNP.Outside.L_meta_7420 : ∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x4 x5 : Fin (x1 + (1 : ℕ))), x4 ≠ x5 → Function.Bijective fun (x7 : Fin (x1 * x1)) => (x3 x4 x7, x3 x5 x7)) → ∃ (x5 : Fin x1 × Fin x1 ≃ Fin (x1 * x1)) (x6 : Fin (x1 + (1 : ℕ)) → Fin x1 ≃ Fin x1), (∀ (x7 : Fin x1 × Fin x1), (x6 (0 : Fin (x1 + (1 : ℕ)))) (x3 (0 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.1 ∧ (x6 (1 : Fin (x1 + (1 : ℕ)))) (x3 (1 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.2) ∧ ∀ (x7 : Fin (x1 + (1 : ℕ))), x7 ≠ (0 : Fin (x1 + (1 : ℕ))) → ∀ (x9 : Fin x1), (x6 x7) (x3 x7 (x5 ((0 : Fin x1), x9))) = x9 := by
  intro x1 _ x3 hb
  have h01 : (0 : Fin (x1 + 1)) ≠ 1 := by
    intro h
    have h2 := congrArg Fin.val h
    have hx : x1 ≠ 0 := NeZero.ne x1
    rw [Fin.val_zero, Fin.val_one', Nat.one_mod_eq_one.2 (by omega)] at h2
    omega
  let B := Equiv.ofBijective (fun c => (x3 0 c, x3 1 c)) (hb 0 1 h01)
  have hB : ∀ p, (x3 0 (B.symm p), x3 1 (B.symm p)) = p := fun p => B.apply_symm_apply p
  have hinj : ∀ x7 : Fin (x1 + 1), x7 ≠ 0 →
      Function.Bijective (fun x9 : Fin x1 => x3 x7 (B.symm ((0 : Fin x1), x9))) := by
    intro x7 hx
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    have ha := congrArg Prod.fst (hB ((0 : Fin x1), a))
    have hb' := congrArg Prod.fst (hB ((0 : Fin x1), b))
    have hc : B.symm ((0 : Fin x1), a) = B.symm ((0 : Fin x1), b) := by
      apply (hb 0 x7 (Ne.symm hx)).1
      simp only at ha hb' hab ⊢
      rw [ha, hb', hab]
    have := congrArg Prod.snd (B.symm.injective hc)
    exact this
  refine ⟨B.symm, fun x7 => if hx : x7 = 0 then Equiv.refl _ else
    (Equiv.ofBijective _ (hinj x7 hx)).symm, ?_, ?_⟩
  · intro p
    have h1 := congrArg Prod.fst (hB p)
    have h2 := congrArg Prod.snd (hB p)
    simp only at h1 h2
    refine ⟨by simp [h1], ?_⟩
    beta_reduce
    rw [dif_neg (Ne.symm h01), Equiv.symm_apply_eq, h2]
    simp only [Equiv.ofBijective_apply]
    have := congrArg Prod.snd (hB ((0 : Fin x1), p.2))
    exact this.symm
  · intro x7 hx x9
    beta_reduce
    rw [dif_neg hx, Equiv.symm_apply_eq]
    rfl
