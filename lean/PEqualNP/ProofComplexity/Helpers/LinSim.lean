import PEqualNP.ProofComplexity.Helpers.Lin

/-!
# Helpers: Res(⊕) simulates resolution line by line
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem linLit_injective {V : Type} :
    Function.Injective (fun l : Literal V => (({l.1} : Finset V), l.2)) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  simp only [Prod.mk.injEq, Finset.singleton_inj] at h
  exact Prod.ext h.1 h.2

theorem linOfClause_resolvent {V : Type} [DecidableEq V] {C D R : Clause V}
    (h : IsResolvent C D R) : IsLinResolvent (linOfClause D) (linOfClause C) (linOfClause R) := by
  obtain ⟨v, hC, hD, rfl⟩ := h
  refine ⟨{v}, Finset.mem_image.mpr ⟨(v, false), hD, rfl⟩,
    Finset.mem_image.mpr ⟨(v, true), hC, rfl⟩, ?_⟩
  unfold linOfClause
  rw [Finset.image_union, Finset.image_erase linLit_injective,
    Finset.image_erase linLit_injective, Finset.union_comm]

theorem lin_of_derivation {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)}
    (h : IsDerivation F π) :
    IsLinDerivation ((fun C => linOfClause C) '' F) (π.map linOfClause) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | ax _ hC ih => exact IsLinDerivation.ax ih ⟨_, hC, rfl⟩
  | res _ hC hD hR ih =>
    exact IsLinDerivation.res ih (List.mem_map_of_mem hD) (List.mem_map_of_mem hC)
      (linOfClause_resolvent hR)

end PEqualNP.ProofComplexity.Helpers
