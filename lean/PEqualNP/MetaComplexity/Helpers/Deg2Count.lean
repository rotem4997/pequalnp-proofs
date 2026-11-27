import PEqualNP.MetaComplexity.Helpers.Deg2Circuit
import PEqualNP.MetaComplexity.Helpers.Deg2Forms

/-!
# The count for sound partial forms at degree two: card D2-14, from the missing cards

Conjecture until the checker accepts it. `card14_of` proves the statement of `card14_form_count`
of the skeleton plan (the degree-two card plan) from the cards on main
(D2-07 `card07_two_line`, D2-09 `card09_form_clean`, D2-10 E1 `card10_e1`, D2-11 `card11_cover`)
and three hypotheses: the exact statements of `card10_e0`, `card12_alpha`, `card13_beta` of the
plan, universally quantified.

Proof (builder sheet, card D2-14): clean the form (D2-09; no larger, keeps the counted edges);
every counted edge of the cleaned form is in `E0 ∪ E1 ∪ alpha ∪ beta` (D2-11), hence in
`E0 ∪ E1 ∪ F_2 ∪ (alpha \ ...) ∪ (beta \ ...)`. Counts: `2 s'' + |W|` (E0), `2 #X''` (E1),
`8 #X''` (D2-07 on the root cone, closed downward), `2 #M'' + |W|` (alpha), `2 #M''` (beta),
in total at most `12 s'' + 2 |W|` since `#X'' + #M'' ≤ s''`.
-/

namespace PEqualNP.MetaComplexity.Deg2

-- The hypotheses repeat the plan statements verbatim, binder names included.
set_option linter.unusedVariables false

open PEqualNP.MetaComplexity.Deg2.Api

/-- D2-14 (`card14_form_count`), from the statements of D2-10 (E0), D2-12 and D2-13. -/
theorem card14_of
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.countedEdges W R).card ≤ 12 * (D.rootCone W R).card + 2 * W.card := by
  obtain ⟨D', hs', hrc, hsub, hcl⟩ := Forms.card09_form_clean I D W R hs
  have h11 := Forms.card11_cover I D' W R hs'
  have hE0 := h10e0 I hI D' W R hs'
  have hE1 := Forms.card10_e1 I hI D' W R hs'
  have hA := h12 I hI D' W R hs' hcl
  have hB := h13 I hI D' W R hs' hcl
  have hF := card07_two_line I hI D' (D'.rootCone W R) (api_coneOf_down D' (W.image R))
  set A := D'.e0Set W R ∪ D'.e1Set I W R ∪ D'.fSet I (D'.rootCone W R) 2 with hAdef
  have hcov : D.countedEdges W R ⊆
      A ∪ (D'.alphaEdges I W R \ A) ∪ (D'.betaEdges I W R \ A) := by
    intro e he
    have he' := h11 (hsub he)
    by_cases hea : e ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hea)
    · simp only [Finset.mem_union] at he'
      rcases he' with ((h | h) | h) | h
      · exact absurd (Finset.mem_union_left _ (Finset.mem_union_left _ h)) hea
      · exact absurd (Finset.mem_union_left _ (Finset.mem_union_right _ h)) hea
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, hea⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, hea⟩)
  have hc := Finset.card_le_card hcov
  have u1 := Finset.card_union_le (A ∪ (D'.alphaEdges I W R \ A)) (D'.betaEdges I W R \ A)
  have u2 := Finset.card_union_le A (D'.alphaEdges I W R \ A)
  have hAc : A.card ≤ (D'.e0Set W R).card + (D'.e1Set I W R).card +
      (D'.fSet I (D'.rootCone W R) 2).card := by
    have u3 := Finset.card_union_le (D'.e0Set W R ∪ D'.e1Set I W R)
      (D'.fSet I (D'.rootCone W R) 2)
    have u4 := Finset.card_union_le (D'.e0Set W R) (D'.e1Set I W R)
    rw [hAdef]; omega
  have hdisj := card_filter_disj (s := D'.rootCone W R) (p := fun f => D'.deg f = 0)
    (q := fun f => D'.deg f = 1) (fun i h0 h1 => by omega)
  have hle := Finset.card_filter_le (D'.rootCone W R) (fun f => D'.deg f = 0 ∨ D'.deg f = 1)
  clear_value A
  omega

end PEqualNP.MetaComplexity.Deg2
