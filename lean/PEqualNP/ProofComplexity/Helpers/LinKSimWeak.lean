import PEqualNP.ProofComplexity.Helpers.LinKPlan

/-!
# Helper module: the termwise weakening step of the Res(k, ⊕) simulation

Proofs only, no definitions. The statement proved is the "termwise weakening rule" of
`LinKPlan`, from the transfer step of `LinKPlan` taken as a hypothesis.

* `weak_span_degree_le`: a member of the span of polynomials of degree at most `k` has degree
  at most `k`;
* `weak_lineInputs_degree_le`: the inputs of a line whose terms have at most `k` equations
  have degree at most `k`;
* `weak_appr_degree_le`: the approximator `∏ j, (1 + qs j)` over `Fin t`, each `qs j` of
  degree at most `k`, has degree at most `t * k`;
* `weak_case_term`: case (a) of the rule for one term, budget `K + t * k + 2 * k`
  (stated with `r` in place of `t * k`);
* `weak_case_disj`: case (b) of the rule for one term, budget `K + t * k + k + 1`;
* `step_weak_of`: the rule, budget `K + 2 * t * k + 2 * k` with `1 ≤ k`.
-/

namespace PEqualNP.ProofComplexity.LinKSim

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan

section Degrees

variable {σ : Type}

/-- A member of the span of polynomials of degree at most `k` has degree at most `k`. -/
theorem weak_span_degree_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
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

/-- The inputs of a line whose terms have at most `k` equations have degree at most `k`. -/
theorem weak_lineInputs_degree_le {V : Type} {k : ℕ} (L : LinKLine V)
    (hL : ∀ T ∈ L, T.card ≤ k) : ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))

/-- The approximator `∏ j, (1 + qs j)`, each `qs j` of degree at most `k`, has degree at most
`t * k`. -/
theorem weak_appr_degree_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, Nat.mul_comm] at this
  exact this

end Degrees

section Cases

variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}

/-- Case (a) for one term: `T` implies the term `S`, and `P * termPoly S * f` is in the
space. Budget `K + r + 2 * k ≤ D`, `r` the degree bound of `P`. -/
theorem weak_case_term (hC : DegClosed C D) {K r k : ℕ} (T S : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k) (hS : S.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + 2 * k ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (hS' : P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  have h1 := weak_term_mul hC T S himp (P * f) (b := r + K) (totalDegree_mul_le' hP hf)
    (by omega)
  have hdS : (P * termPoly S * f).totalDegree ≤ r + k + K :=
    totalDegree_mul_le' (totalDegree_mul_le' hP ((totalDegree_termPoly_le S).trans hS)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hS'
    ((totalDegree_termPoly_le T).trans hT) hdS (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * termPoly S) + termPoly T * (P * termPoly S * f) := by
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * termPoly S * f))
  rw [e]
  exact C.add_mem h1 h2

/-- Case (b) for one term: `T` implies the disjunction of the one-equation terms of `M`, and
`P * termPoly S * f` is in the space for every term `S` of `M`. Budget `K + r + k + 1 ≤ D`,
`r` the degree bound of `P`. -/
theorem weak_case_disj [Fintype V] [DecidableEq V] (hC : DegClosed C D) {K r k : ℕ}
    (T : LinTerm V) (M : LinKLine V) (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + k + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)
    (hM : ∀ S ∈ M, P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_line (C := C) (D := D) hC T M himp
  have h1 := hmul (P * f) (r + K) (totalDegree_mul_le' hP hf) (by omega)
  have hsum : ∑ d ∈ J, P * eqPoly d * f ∈ C := by
    refine Submodule.sum_mem _ fun d hd => ?_
    have := hM {d} (hJ d hd)
    rwa [termPoly_singleton] at this
  have hds : (∑ d ∈ J, P * eqPoly d * f).totalDegree ≤ r + 1 + K :=
    totalDegree_finsetSum_le fun d _ =>
      totalDegree_mul_le' (totalDegree_mul_le' hP (totalDegree_eqPoly_le d)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hsum
    ((totalDegree_termPoly_le T).trans hT) hds (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)
        + termPoly T * ∑ d ∈ J, P * eqPoly d * f := by
    have e1 : ∑ d ∈ J, P * eqPoly d * f = P * (∑ d ∈ J, eqPoly d) * f := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1]
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * (∑ d ∈ J, eqPoly d) * f))
  rw [e]
  exact C.add_mem h1 h2

end Cases

/-- The termwise weakening rule of `LinKPlan`, from the transfer step of `LinKPlan`. -/
theorem step_weak_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
      (qL qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
      (∏ j, (1 + qL j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ _ C D K t k f L M qL qM hC hk hL hM hqL hqM hf hB hweak hPL hHM
  have h2 : 2 * t * k = t * k + t * k := by ring
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    weak_appr_degree_le qM fun j =>
      weak_span_degree_le (weak_lineInputs_degree_le M hM) (hqM j)
  refine htransfer V C D K t k (t * k) (lineInputs L) qL f _ hC
    (weak_lineInputs_degree_le L hL) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ L := Finset.mem_coe.mp hT
  rcases hweak T hT' with ⟨S, hS, himp⟩ | himp
  · exact weak_case_term hC T S _ f (hL T hT') (hM S hS) hdM hf (by omega) himp (hHM S hS)
  · exact weak_case_disj hC T M _ f (hL T hT') hdM hf (by omega) himp hHM

end PEqualNP.ProofComplexity.LinKSim
