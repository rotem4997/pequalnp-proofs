import PEqualNP.MetaComplexity.Helpers.ForestElim

/-!
The leaf step: fixing one input of an 8-input function to false costs a gate, and the
7-input function that remains is read through a renaming of the inputs.
-/

namespace PEqualNP.MetaComplexity.Helpers.N8b

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

theorem step (f : (Fin 8 → Bool) → Bool) (g : (Fin 7 → Bool) → Bool) (v : Fin 8)
    (π : Fin 8 → Fin 7) (b : ℕ) (hb : 0 < b) (hg : ∀ t : ℕ, HasCircuitSize 7 g t → b ≤ t)
    (hdep : ∃ x : Fin 8 → Bool, f (Function.update x v (!x v)) ≠ f x)
    (hnc : ∃ y z : Fin 7 → Bool, g y ≠ g z)
    (hr : ∀ y : Fin 7 → Bool, f (Function.update (y ∘ π) v false) = g y) :
    ∀ t : ℕ, HasCircuitSize 8 f t → b + 1 ≤ t := by
  have key : ∀ s : ℕ, HasCircuitSize 8 f (s + 1) → b ≤ s := by
    intro s h
    obtain ⟨y, z, hyz⟩ := hnc
    have h1 := Forest.one_gate_at 7 f v false s hdep
      ⟨y ∘ π, z ∘ π, by rw [hr, hr]; exact hyz⟩ h
    have h2 := relabel_size π _ s h1
    have e : (fun y : Fin 7 → Bool => f (Function.update (y ∘ π) v false)) = g := funext hr
    exact hg s (e ▸ h2)
  intro t h
  cases t with
  | succ s => exact Nat.succ_le_succ (key s h)
  | zero =>
    -- a circuit of size 0 also has size at most 1
    have h1 : HasCircuitSize 8 f 1 := by
      obtain ⟨C, h1, h2, h3⟩ := h
      exact ⟨C, h1, le_trans h2 (Nat.zero_le 1), h3⟩
    exact absurd (key 0 h1) (Nat.not_le.mpr hb)

/-- A statement about all 7-bit inputs, as seven Boolean quantifiers. -/
theorem all7 (P : (Fin 7 → Bool) → Prop)
    (h : ∀ a b c d e f g : Bool, P ![a, b, c, d, e, f, g]) : ∀ y, P y := by
  intro y
  have e : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6] := by
    funext i; fin_cases i <;> rfl
  rw [e]; exact h _ _ _ _ _ _ _

end PEqualNP.MetaComplexity.Helpers.N8b
