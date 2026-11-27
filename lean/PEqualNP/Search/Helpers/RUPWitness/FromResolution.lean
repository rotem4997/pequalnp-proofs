import PEqualNP.Defs.SearchRUP

/-!
# Helpers: a resolution derivation, read as a run of clause learning, is a RUP run

Every line of a resolution derivation is RUP over the input and the lines before it: an axiom
is RUP since assuming its literals false falsifies it outright; a resolvent of `C` and `D` on
`v` is RUP since its literals false make `C` force `v` by unit propagation, and then every
literal of `D` is false.
-/

namespace PEqualNP.Search.Helpers.RUPWitness

open PEqualNP.ProofComplexity PEqualNP.Search

/-- An axiom is RUP over any set of clauses containing it. -/
theorem isRUP_of_mem {V : Type} {Γ : Set (Clause V)} {C : Clause V} (hC : C ∈ Γ) :
    IsRUP Γ C :=
  ⟨C, hC, fun l hl => UPForces.hyp ⟨l, hl, rfl⟩⟩

/-- A resolvent of two clauses of `Γ` is RUP over `Γ`. -/
theorem isRUP_of_resolvent {V : Type} [DecidableEq V] {Γ : Set (Clause V)}
    {C D R : Clause V} (hC : C ∈ Γ) (hD : D ∈ Γ) (hR : IsResolvent C D R) : IsRUP Γ R := by
  obtain ⟨v, hvC, hvD, rfl⟩ := hR
  refine ⟨D, hD, fun l hl => ?_⟩
  by_cases hlv : l = (v, false)
  · subst hlv
    refine UPForces.unit hC hvC fun l' hl' hne => UPForces.hyp ⟨l', ?_, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hl'⟩)
  · exact UPForces.hyp ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hlv, hl⟩), rfl⟩

/-- Every resolution derivation is a RUP run. -/
theorem isRUPRun_of_derivation {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (h : IsDerivation F π) : IsRUPRun F π := by
  induction h with
  | nil => exact IsRUPRun.nil
  | ax _ hC ih => exact IsRUPRun.learn ih (isRUP_of_mem (Or.inl hC))
  | res _ hC hD hR ih =>
    exact IsRUPRun.learn ih (isRUP_of_resolvent (Or.inr hC) (Or.inr hD) hR)

end PEqualNP.Search.Helpers.RUPWitness
