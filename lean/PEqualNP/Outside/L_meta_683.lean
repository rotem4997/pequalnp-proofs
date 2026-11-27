import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_683

theorem main (F : Type) [Field F] [Fintype F] [CharP F 2] :
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  have h1 : ¬ Function.Surjective (fun s : F => s ^ 2 + s) := fun hs => by
    have hi := Finite.injective_iff_surjective.mpr hs
    have h01 : (0 : F) = 1 := hi (by simp [CharTwo.add_self_eq_zero])
    exact zero_ne_one h01
  have h2 : Function.Surjective (fun s : F => s ^ 2) :=
    Finite.injective_iff_surjective.mp (frobenius_inj F 2)
  simp only [Function.Surjective, not_forall, not_exists] at h1
  obtain ⟨c, hc⟩ := h1
  have hc0 : c ≠ 0 := fun h => hc 0 (by simp [h])
  obtain ⟨b, hb⟩ := h2 c⁻¹
  have hb' : b ^ 2 = c⁻¹ := hb
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb'
    exact inv_ne_zero hc0 (by simpa using hb'.symm)
  refine ⟨b, fun x hx => hc (x / b) ?_⟩
  have hcb : c = (b ^ 2)⁻¹ := by rw [hb', inv_inv]
  have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [hcb]
  field_simp
  linear_combination hx - h2'

end PEqualNP.Outside.L_meta_683

open PEqualNP.Outside.L_meta_683 in
theorem PEqualNP.Outside.L_meta_683 : ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  exact main F
