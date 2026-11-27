import PEqualNP.Defs

/-!
# Helpers: a Duplicator strategy rules out narrow resolution refutations

Used by the refutation of `L-alg-002`. This is the easy direction of Atserias and Dalmau
(J. Comput. System Sci. 74(3), 2008): if Duplicator has a strategy in the existential
(k+1)-pebble game on a formula, the formula has no resolution refutation of width at most k.

A partial assignment is a consistent finite set of literals: `(v, b) ∈ ρ` means `ρ` sets `v`
to `b`. It falsifies a clause `C` when it sets every literal of `C` false.
-/

namespace PEqualNP.Search.Helpers


/-- The partial assignment `ρ` falsifies the clause `C`. -/
def Falsifies {V : Type} (ρ : Finset (PEqualNP.ProofComplexity.Literal V)) (C : PEqualNP.ProofComplexity.Clause V) : Prop :=
  ∀ l ∈ C, (l.1, !l.2) ∈ ρ

/-- A Duplicator strategy for width `k` on the clauses `F`: a family of consistent partial
assignments containing the empty one, closed under subsets, extendable by any one variable
while it has at most `k` literals, and never falsifying a clause of `F`. -/
structure DuplicatorStrategy {V : Type} [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (k : ℕ) where
  H : Set (Finset (PEqualNP.ProofComplexity.Literal V))
  consistent : ∀ ρ ∈ H, ∀ (v : V) (b : Bool), (v, b) ∈ ρ → (v, !b) ∉ ρ
  empty_mem : ∅ ∈ H
  restrict : ∀ ρ ∈ H, ∀ σ, σ ⊆ ρ → σ ∈ H
  extend : ∀ ρ ∈ H, ρ.card ≤ k → ∀ v : V, ∃ b : Bool, insert (v, b) ρ ∈ H
  no_falsify : ∀ ρ ∈ H, ∀ C ∈ F, ¬ Falsifies ρ C

end PEqualNP.Search.Helpers

namespace PEqualNP.Search.Helpers

/-- Every clause of a width-`k` derivation escapes every partial assignment of a Duplicator
strategy for width `k`. -/
theorem duplicator_not_falsified {V : Type} [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.Clause V)} {k : ℕ} (D : DuplicatorStrategy F k) :
    ∀ π : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsDerivation F π →
    (∀ C ∈ π, C.card ≤ k) → ∀ C ∈ π, ∀ ρ ∈ D.H, ¬ Falsifies ρ C := by
  intro π h
  induction h with
  | nil => intro _ C hC; simp at hC
  | @ax π C _ hCF ih =>
    intro hw C' hC' ρ hρ
    rcases List.mem_cons.mp hC' with rfl | hC'
    · exact D.no_falsify ρ hρ C' hCF
    · exact ih (fun E hE => hw E (List.mem_cons_of_mem _ hE)) C' hC' ρ hρ
  | @res π C E R _ hC hE hR ih =>
    intro hw C' hC' ρ hρ hfal
    have ih' := ih (fun X hX => hw X (List.mem_cons_of_mem _ hX))
    rcases List.mem_cons.mp hC' with rfl | hC'
    · obtain ⟨v, hv1, hv2, rfl⟩ := hR
      set R := C.erase (v, true) ∪ E.erase (v, false)
      -- the part of ρ that falsifies R
      set σ := ρ.filter fun l => (l.1, !l.2) ∈ R
      have hσH : σ ∈ D.H := D.restrict ρ hρ σ (Finset.filter_subset _ _)
      have hσcard : σ.card ≤ k := by
        have hinj : Set.InjOn (fun l : PEqualNP.ProofComplexity.Literal V => (l.1, !l.2)) σ := by
          intro x _ y _ hxy
          simp only [Prod.mk.injEq] at hxy
          exact Prod.ext hxy.1 (by simpa using hxy.2)
        have hmaps : ∀ l ∈ σ, (l.1, !l.2) ∈ R := fun l hl => (Finset.mem_filter.mp hl).2
        calc σ.card ≤ R.card := Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ k := hw _ List.mem_cons_self
      have hσfal : Falsifies σ R := by
        intro l hl
        have := hfal l hl
        refine Finset.mem_filter.mpr ⟨this, ?_⟩
        simpa using hl
      obtain ⟨b, hb⟩ := D.extend σ hσH hσcard v
      cases b with
      | false =>
        apply ih' C hC _ hb
        intro l hl
        by_cases hlv : l = (v, true)
        · subst hlv; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hσfal l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hl⟩)))
      | true =>
        apply ih' E hE _ hb
        intro l hl
        by_cases hlv : l = (v, false)
        · subst hlv; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hσfal l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hl⟩)))
    · exact ih' C' hC' ρ hρ hfal

/-- A Duplicator strategy for width `k` rules out every refutation of width at most `k`. -/
theorem duplicator_no_narrow_refutation {V : Type} [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.Clause V)} {k : ℕ} (D : DuplicatorStrategy F k)
    (π : List (PEqualNP.ProofComplexity.Clause V)) (hπ : PEqualNP.ProofComplexity.IsRefutation F π)
    (hw : ∀ C ∈ π, C.card ≤ k) : False :=
  duplicator_not_falsified D π hπ.1 hw ∅ hπ.2 ∅ D.empty_mem (by simp [Falsifies])

end PEqualNP.Search.Helpers
