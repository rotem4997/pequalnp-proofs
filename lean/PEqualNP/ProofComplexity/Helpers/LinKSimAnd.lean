import PEqualNP.ProofComplexity.Helpers.LinKPlan

/-!
# Helper for L-pcx-054: the and-introduction step of the Res(k, ⊕) simulation

Helper module, proofs only. The statement proved is the `example : Prop` of `LinKPlan` whose
docstring begins "The and-introduction rule", with the transfer step of `LinKPlan` taken as a
hypothesis (`step_andIntro_of`).

With `P = ∏ j, (1 + qM j)`, `g₁ = termPoly T₁`, `g₂ = termPoly T₂`:

* `and_half`: `(1 + g₀) * P * f` is in the space, by transfer through a premise `L` all of
  whose terms other than `T₀` are in the conclusion. Budget `K + deg P + 2 * k ≤ D` beside
  the budget of the transfer itself;
* `step_andIntro_of`: `P * f = (1 + g₁) * P * f + g₁ * ((1 + g₂) * P * f) + g₁ * g₂ * P * f`
  in characteristic two, and the last summand is `P * termPoly (T₁ ∪ T₂) * f` modulo the
  space (`term_union_mul`).

Degree used: transfer `K + 2 * t * k + k`, the defects and absorptions `K + t * k + 2 * k`.
-/

namespace PEqualNP.ProofComplexity.LinKSim

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan

section Abstract

variable {σ : Type}

/-- A member of the span of polynomials of degree at most `k` has degree at most `k`. -/
theorem and_totalDegree_span_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx

/-- The approximator `∏ j, (1 + qs j)` has degree at most `t * k` when every `qs j` has degree
at most `k`. -/
theorem and_totalDegree_appr_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := Helpers.totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, mul_comm] at this
  exact this

end Abstract

section Lines

variable {V : Type}

/-- The inputs of a line whose terms have at most `k` equations have degree at most `k`. -/
theorem and_totalDegree_lineInputs_le {k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))

/-- The approximator of a line whose terms have at most `k` equations has degree at most
`t * k`. -/
theorem and_totalDegree_lineAppr_le {t k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  and_totalDegree_appr_le qs fun j =>
    and_totalDegree_span_le (and_totalDegree_lineInputs_le L hL) (hqs j)

variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}

/-- One half of the and-introduction rule. The premise `L` has every term other than `T₀` in
the conclusion `M`; `htr` is the transfer through `L` for multipliers of degree at most
`m + k`. Then `(1 + termPoly T₀) * P * f` is in the space. Budget `K + m + 2 * k ≤ D`. -/
theorem and_half (hC : DegClosed C D) (L M : LinKLine V) (T₀ : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) {K m k : ℕ}
    (hM : ∀ T ∈ M, T.card ≤ k) (hT₀ : T₀.card ≤ k)
    (hP : P.totalDegree ≤ m) (hf : f.totalDegree ≤ K) (hB : K + m + 2 * k ≤ D)
    (htr : ∀ R : MvPolynomial V (ZMod 2), R.totalDegree ≤ m + k →
      (∀ T ∈ L, termPoly T * R * f ∈ C) → R * f ∈ C)
    (hsub : ∀ T ∈ L, T ≠ T₀ → T ∈ M)
    (hHM : ∀ T ∈ M, P * termPoly T * f ∈ C) :
    (1 + termPoly T₀) * P * f ∈ C := by
  have hg0 : (termPoly T₀).totalDegree ≤ k := (totalDegree_termPoly_le T₀).trans hT₀
  have hd1 : (1 + termPoly T₀).totalDegree ≤ k :=
    (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg0)
  refine htr _ ((totalDegree_mul_le' hd1 hP).trans (by omega)) ?_
  intro T hT
  by_cases h0 : T = T₀
  · subst h0
    have h1 := idem_mul hC (termPoly T) (P * f) (totalDegree_mul_le' hP hf) hg0
      (by omega)
    have e : termPoly T * ((1 + termPoly T) * P) * f
        = P * f * (termPoly T * termPoly T + termPoly T) := by ring
    rw [e]
    exact h1
  · have hTM := hsub T hT h0
    have hmem := hHM T hTM
    have hd : (P * termPoly T * f).totalDegree ≤ m + k + K :=
      totalDegree_mul_le'
        (totalDegree_mul_le' hP ((totalDegree_termPoly_le T).trans (hM T hTM))) hf
    have h1 := DegSizeSim.absorb_le hC (1 + termPoly T₀) hmem hd1 hd (by omega)
    have e : termPoly T * ((1 + termPoly T₀) * P) * f
        = (1 + termPoly T₀) * (P * termPoly T * f) := by ring
    rw [e]
    exact h1

end Lines

/-- The and-introduction rule of the simulation, from the transfer step. Budget
`K + 2 * t * k + 2 * k ≤ D`. -/
theorem step_andIntro_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
      (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
      (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
      (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC hL1 hL2 hM hq1 hq2 hqM hf hB hand hP1 hP2 hHM
  obtain ⟨T₁, T₂, hT1, hT2, rfl⟩ := hand
  rw [mul_assoc] at hB
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    and_totalDegree_lineAppr_le _ hM qM hqM
  have hc1 : T₁.card ≤ k := hL1 T₁ hT1
  have hc2 : T₂.card ≤ k := hL2 T₂ hT2
  have hg1 : (termPoly T₁).totalDegree ≤ k := (totalDegree_termPoly_le T₁).trans hc1
  have hg2 : (termPoly T₂).totalDegree ≤ k := (totalDegree_termPoly_le T₂).trans hc2
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  -- Step 1: transfer through the first premise.
  have hA : (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₁ _ T₁ _ f hM hc1 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₁) q₁ f R hC
        (and_totalDegree_lineInputs_le L₁ hL1) hq1 hf hR (by omega) hP1 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  -- Step 2: transfer through the second premise.
  have hA2 : (1 + termPoly T₂) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₂ _ T₂ _ f hM hc2 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₂) q₂ f R hC
        (and_totalDegree_lineInputs_le L₂ hL2) hq2 hf hR (by omega) hP2 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  -- Step 3: the term `T₁ ∪ T₂` of the conclusion.
  have hU : (∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f ∈ C :=
    hHM _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hun := term_union_mul hC T₁ T₂ ((∏ j, (1 + qM j)) * f) hQ (by omega)
  -- Step 4: the middle summand by absorption, and the identity.
  have hd2 : ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f).totalDegree ≤ k + t * k + K := by
    have hd : (1 + termPoly T₂).totalDegree ≤ k :=
      (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg2)
    exact totalDegree_mul_le' (totalDegree_mul_le' hd hdM) hf
  have hmid := DegSizeSim.absorb_le hC (termPoly T₁) hA2 hg1 hd2 (by omega)
  have hsum := C.add_mem (C.add_mem hA hmid) (C.add_mem hU hun)
  have e : (∏ j, (1 + qM j)) * f
      = (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f
        + termPoly T₁ * ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f)
        + ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f
          + (∏ j, (1 + qM j)) * f * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂)) := by
    linear_combination
      (-1 : MvPolynomial V (ZMod 2)) * char2_add_self (termPoly T₁ * (∏ j, (1 + qM j)) * f)
      - char2_add_self (termPoly T₁ * termPoly T₂ * (∏ j, (1 + qM j)) * f)
      - char2_add_self ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f)
  rw [e]
  exact hsum

end PEqualNP.ProofComplexity.LinKSim
