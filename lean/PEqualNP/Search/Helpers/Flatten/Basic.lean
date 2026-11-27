import PEqualNP.Defs.SearchQTree

/-!
# Flattening a tree-like Res(lin) derivation into a list derivation

A tree-like derivation is written out as a list, newest line first: the conclusion on top of
the flattened subtrees. The flattened list is a derivation, and its head is the conclusion.
-/

namespace PEqualNP.Search.Helpers.Flatten

open PEqualNP.Search

variable {V : Type} [Fintype V] [DecidableEq V]
  {F : Set (PEqualNP.ProofComplexity.Clause V)}

/-- Two derivations side by side, the first on top, form a derivation. -/
theorem append {π₁ π₂ : List (QLine V)} (h₁ : IsResLinQDerivation F π₁)
    (h₂ : IsResLinQDerivation F π₂) : IsResLinQDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax C _ hC hL ih => exact IsResLinQDerivation.ax C ih hC hL
  | res α β _ hm hm' ih =>
      exact IsResLinQDerivation.res α β ih (List.mem_append_left _ hm)
        (List.mem_append_left _ hm')
  | weaken _ hm himp ih =>
      exact IsResLinQDerivation.weaken ih (List.mem_append_left _ hm) himp

/-- The list of lines of a tree-like derivation, newest first. -/
def flatten : {L : QLine V} → ResLinQTree F L → List (QLine V)
  | L, .ax _ _ _ => [L]
  | _, .res (e := e) (e' := e') (C := C) (D := D) α β t t' =>
      ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) :: (flatten t' ++ flatten t)
  | D, .weaken t _ => D :: flatten t

/-- The flattened tree is a derivation whose head is the conclusion. -/
theorem flatten_spec : {L : QLine V} → (t : ResLinQTree F L) →
    IsResLinQDerivation F (flatten t) ∧ (flatten t).head? = some L
  | _, .ax C hC hL => ⟨IsResLinQDerivation.ax C IsResLinQDerivation.nil hC hL, rfl⟩
  | _, .res α β t t' => by
      obtain ⟨d, hd⟩ := flatten_spec t
      obtain ⟨d', hd'⟩ := flatten_spec t'
      refine ⟨?_, rfl⟩
      refine IsResLinQDerivation.res α β (append d' d) ?_ ?_
      · exact List.mem_append_right _ (List.mem_of_mem_head? hd)
      · exact List.mem_append_left _ (List.mem_of_mem_head? hd')
  | _, .weaken t himp => by
      obtain ⟨d, hd⟩ := flatten_spec t
      exact ⟨IsResLinQDerivation.weaken d (List.mem_of_mem_head? hd) himp, rfl⟩

/-- A tree-like refutation gives a list refutation. -/
theorem refutation (t : ResLinQTree F []) : IsResLinQRefutation F (flatten t) :=
  ⟨(flatten_spec t).1, List.mem_of_mem_head? (flatten_spec t).2⟩

end PEqualNP.Search.Helpers.Flatten
