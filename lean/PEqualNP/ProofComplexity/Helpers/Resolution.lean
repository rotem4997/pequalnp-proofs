import PEqualNP.Defs

/-!
# Helpers: basic facts about resolution derivations

Used by the lemma files of the proof complexity program. Nothing here is a recorded statement.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- An assignment satisfying both premises satisfies the resolvent. -/
theorem resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, -, -, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst h
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩

/-- An assignment satisfying the axioms satisfies every clause of a derivation. -/
theorem derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {F : Set (Clause V)}
    {π : List (Clause V)} (h : IsDerivation F π) (ha : Satisfies a F) :
    ∀ C ∈ π, ClauseSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | res _ hC hD hR ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact resolvent_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE

end PEqualNP.ProofComplexity.Helpers
