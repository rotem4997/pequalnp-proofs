import Mathlib

/-! Counting permutations with prescribed values on a finite set. Helper for L-gct-013. -/

namespace PEqualNP.Gct.Helpers

open Finset

/-- The permutations fixing every point of `s` number `(card α - #s)!`. -/
theorem card_perm_fix {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    #{σ : Equiv.Perm α | ∀ x ∈ s, σ x = x} = (Fintype.card α - #s).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ s)
  have h1 : #{σ : Equiv.Perm α | ∀ x ∈ s, σ x = x} =
      Fintype.card {f : Equiv.Perm α // ∀ a, ¬ (a ∉ s) → f a = a} := by
    rw [Fintype.card_subtype]
    congr 1
    ext σ
    simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype_compl,
    Fintype.card_coe]

/-- The permutations agreeing with a map injective on `s` number `(card α - #s)!`. -/
theorem card_perm_agree {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → α)
    (hf : Set.InjOn f s) :
    #{σ : Equiv.Perm α | ∀ x ∈ s, σ x = f x} = (Fintype.card α - #s).factorial := by
  let e : {x // x ∈ s} ≃ {x // x ∈ s.image f} :=
    Equiv.ofBijective (fun x => ⟨f x, mem_image_of_mem f x.2⟩)
      ⟨fun x y h => Subtype.ext (hf x.2 y.2 (congrArg Subtype.val h)), fun y => by
        obtain ⟨x, hx, hxy⟩ := mem_image.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let τ : Equiv.Perm α := e.extendSubtype
  have hτ : ∀ x ∈ s, τ x = f x := fun x hx => by
    simp only [τ, Equiv.extendSubtype_apply_of_mem e x hx]
    rfl
  rw [← card_perm_fix s]
  refine card_bij' (fun σ _ => τ⁻¹ * σ) (fun ρ _ => τ * ρ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro x hx
    rw [Equiv.Perm.mul_apply, hσ x hx, ← hτ x hx]; simp
  · intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ ⊢
    intro x hx
    rw [Equiv.Perm.mul_apply, hρ x hx, hτ x hx]
  · intro σ _; simp
  · intro ρ _; simp

end PEqualNP.Gct.Helpers
