import PEqualNP.ProofComplexity.Helpers.LiftQuadDefs

/-!
# Leg D of L-pcx-072: keeping local consistency (`StmtGoodStep`)

Conjecture until the checker accepts it.

Let `K' = insert j K₀`. A set `T` of at most `s` equations with unique neighbours in `K'` has
`δ * |T| ≤ |K'| ≤ |K₀| + 1`, so `2 * |T| ≤ s`. Take such a set `A` of largest size. For any
other such `T`, `T ∪ A` has at most `s` equations and its unique neighbours lie in `K'`
(`uniqueNbrs_ustar`), so by maximality `T ⊆ A`. `Good` solves `A` by some `x₀` agreeing with
`β` on `K₀`; put `b = x₀ j`. For any `U` of at most `s` equations, `peel` relative to `K'`
from `x₀` gives a solution agreeing with `x₀` on `K'`, that is with `update β j b` on `K'`.
No case split on `j ∈ K₀` is needed: then `x₀ j = β j`.
-/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily PEqualNP.ProofComplexity.LiftRank

/-- The unique neighbours of a union of two sets lie in `K` when those of each part do. -/
theorem uniqueNbrs_union_subset {m N : ℕ} (G : BipGraph m N) (K : Finset (Fin N))
    (T A : Finset (Fin m)) (hT : uniqueNbrs G T ⊆ K) (hA : uniqueNbrs G A ⊆ K) :
    uniqueNbrs G (T ∪ A) ⊆ K := by
  classical
  have heq : ustar G K (T ∪ A) = T ∪ A := by
    apply Finset.Subset.antisymm (ustar_subset G K (T ∪ A))
    exact Finset.union_subset
      (subset_ustar G K (T ∪ A) T Finset.subset_union_left hT)
      (subset_ustar G K (T ∪ A) A Finset.subset_union_right hA)
  have h := uniqueNbrs_ustar G K (T ∪ A)
  rwa [heq] at h

/-- On a boundary expander, a set of at most `s` equations with unique neighbours in a set of
at most `|K₀| + 1` blocks has at most `s / 2` equations. -/
theorem two_card_le {m N : ℕ} (G : BipGraph m N) (s δ : ℕ) (K' : Finset (Fin N))
    (hG : IsBdryExpander G s δ) (hδ : 1 ≤ δ) (k : ℕ) (hK' : K'.card ≤ k + 1)
    (hk : 2 * (k + 1) ≤ δ * s) (T : Finset (Fin m)) (hTs : T.card ≤ s)
    (hTK : uniqueNbrs G T ⊆ K') : 2 * T.card ≤ s := by
  have h1 := hG T hTs
  have h2 := Finset.card_le_card hTK
  have h3 : δ * (2 * T.card) ≤ δ * s := by
    calc δ * (2 * T.card) = 2 * (δ * T.card) := by ring
      _ ≤ 2 * (k + 1) := by omega
      _ ≤ δ * s := hk
  exact Nat.le_of_mul_le_mul_left h3 (by omega)

theorem good_step : StmtGoodStep := by
  classical
  intro m N G c s δ K₀ β j hG hδ hK hgood
  set K' := insert j K₀ with hK'def
  have hK'card : K'.card ≤ K₀.card + 1 := Finset.card_insert_le j K₀
  -- the family of admissible sets
  set F : Finset (Finset (Fin m)) :=
    Finset.univ.powerset.filter (fun T => T.card ≤ s ∧ uniqueNbrs G T ⊆ K') with hFdef
  have hmemF : ∀ T : Finset (Fin m), T ∈ F ↔ T.card ≤ s ∧ uniqueNbrs G T ⊆ K' := by
    intro T
    simp [hFdef]
  have hFne : F.Nonempty := by
    refine ⟨∅, (hmemF ∅).mpr ⟨by simp, ?_⟩⟩
    intro x hx
    simp [uniqueNbrs] at hx
  obtain ⟨A, hAF, hAmax⟩ := Finset.exists_max_image F Finset.card hFne
  obtain ⟨hAs, hAK⟩ := (hmemF A).mp hAF
  have hA2 := two_card_le G s δ K' hG hδ K₀.card hK'card hK A hAs hAK
  -- every admissible set lies in `A`
  have hsubA : ∀ T : Finset (Fin m), T.card ≤ s → uniqueNbrs G T ⊆ K' → T ⊆ A := by
    intro T hTs hTK
    have hT2 := two_card_le G s δ K' hG hδ K₀.card hK'card hK T hTs hTK
    have hUs : (T ∪ A).card ≤ s := by
      have := Finset.card_union_le T A
      omega
    have hUF : T ∪ A ∈ F :=
      (hmemF _).mpr ⟨hUs, uniqueNbrs_union_subset G K' T A hTK hAK⟩
    have hle := hAmax _ hUF
    have heq : A = T ∪ A := Finset.eq_of_subset_of_card_le Finset.subset_union_right hle
    rw [heq]
    exact Finset.subset_union_left
  obtain ⟨x₀, hx₀K, hx₀A⟩ := hgood A hAs
  refine ⟨x₀ j, fun hj => hx₀K j hj, ?_⟩
  intro U hU
  obtain ⟨x, hxK, hx⟩ := peel G c K' U x₀ (fun T hTU hTK i hi =>
    hx₀A i (hsubA T ((Finset.card_le_card hTU).trans hU) hTK hi)) U le_rfl
  refine ⟨x, fun j' hj' => ?_, hx⟩
  rw [hxK j' hj']
  by_cases hjj : j' = j
  · subst hjj
    simp
  · rw [Function.update_of_ne hjj]
    exact hx₀K j' ((Finset.mem_insert.mp hj').resolve_left hjj)

end PEqualNP.ProofComplexity.LiftQuad
