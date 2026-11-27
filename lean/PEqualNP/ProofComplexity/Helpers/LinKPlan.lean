import PEqualNP.ProofComplexity.Helpers.DegSizeSim
import PEqualNP.ProofComplexity.Helpers.BoolVanish
import PEqualNP.Defs.ProofComplexityLinK
import PEqualNP.Defs.Expanders

/-!
# Plan for L-pcx-054: degree to size for Res(k, ⊕), and the weakening step proved

Part 1 (PROVED here). The one new mathematical fact of the extension of L-pcx-042 from Res(⊕)
to Res(k, ⊕) is the weakening step of the simulation for a term. With
`termPoly T = ∏ e ∈ T, eqPoly e` (the indicator of the term `T`, of degree at most `T.card`):

* `vanish_mem`: a degree-closed space holds every polynomial of degree at most `D` that
  vanishes on the Boolean cube. Everything below is this lemma plus a semantic check;
* `weak_term_mul`, `weak_term`: case (a) of `IsLinKWeakening`. If `T` implies `S` then
  `h * (termPoly T + termPoly T * termPoly S)` is in the space, budget
  `deg h + T.card + S.card ≤ D`;
* `term_alternative`: the linear algebra of case (b), `lin_alternative` relative to the affine
  space of `T`. If `T` implies the disjunction of the equations of `Q` then some `J ⊆ Q` and
  `I ⊆ T` have `∑ e ∈ I, (eqPoly e + 1) + ∑ d ∈ J, eqPoly d = 1` as polynomials. An
  inconsistent `T` is covered (then `J` may be anything the proof finds, and `I` alone
  certifies the inconsistency);
* `weak_disj_mul`, `weak_disj`, `weak_disj_line`: case (b). Some `J ⊆ Q`, chosen before the
  multiplier, has `h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)` in the space, budget
  `deg h + T.card + 1 ≤ D`;
* `unsat_term_mul`: an inconsistent term has `h * termPoly T` in the space, budget
  `deg h + T.card ≤ D`;
* `idem_mul`, `term_neg_mul`, `term_union_mul`: the three other cube identities the cut and
  the and-introduction steps use.

Part 2 (STATEMENTS only). Every `example : Prop` after the heading "The plan" is a statement
to be proved by a later leg, each with its degree budget and the checked helper of L-pcx-042
it generalizes. At `k = 1` each is the checked statement, with one exception that is flagged
(the final constant).
-/

namespace PEqualNP.ProofComplexity.LinKPlan

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

/-! ## Part 1: cube-vanishing polynomials and the weakening step -/

section Vanish

variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}

/-- A degree-closed space holds everything derivable from the Boolean axioms alone. -/
theorem mem_of_boolDerivable (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hp : PCDerivable (BoolVanish.boolAxioms σ) D p) : p ∈ C := by
  induction hp with
  | ax hp _ =>
    obtain ⟨v, rfl⟩ := hp
    exact hC.bool v
  | zero => exact C.zero_mem
  | add _ _ ih1 ih2 => exact C.add_mem ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases h0 : p = 0
    · subst h0
      simp
    · refine hC.mulX j p ih ?_
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) h0, totalDegree_X] at hdeg
      omega

/-- A degree-closed space holds every polynomial of degree at most `D` that vanishes on the
Boolean cube. -/
theorem vanish_mem (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hd : p.totalDegree ≤ D) (hv : ∀ x : σ → ZMod 2, eval x p = 0) : p ∈ C :=
  mem_of_boolDerivable hC
    (BoolVanish.vanish_derivable σ (BoolVanish.boolAxioms σ) D p (fun v => ⟨v, rfl⟩) hd hv)

/-- Idempotence of every polynomial, with a multiplier: budget `deg h + 2 * deg g ≤ D`. -/
theorem idem_mul (hC : DegClosed C D) (g h : MvPolynomial σ (ZMod 2)) {b e : ℕ}
    (hh : h.totalDegree ≤ b) (hg : g.totalDegree ≤ e) (hB : b + 2 * e ≤ D) :
    h * (g * g + g) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 : (g * g + g).totalDegree ≤ e + e :=
      (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hg hg) (by omega))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have : ∀ c : ZMod 2, c * c + c = 0 := by decide
    rw [this, mul_zero]

end Vanish

/-- The indicator polynomial of a term: the product of the affine forms of its equations. -/
noncomputable def termPoly {V : Type} (T : LinTerm V) : MvPolynomial V (ZMod 2) :=
  ∏ e ∈ T, eqPoly e

section Terms

variable {V : Type}

theorem termPoly_empty : termPoly (∅ : LinTerm V) = 1 := by
  simp [termPoly]

theorem termPoly_singleton (q : LinEq V) : termPoly ({q} : LinTerm V) = eqPoly q := by
  simp [termPoly]

theorem totalDegree_termPoly_le (T : LinTerm V) : (termPoly T).totalDegree ≤ T.card := by
  unfold termPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ e ∈ T, (eqPoly e).totalDegree ≤ ∑ _e ∈ T, 1 :=
        Finset.sum_le_sum fun e _ => totalDegree_eqPoly_le e
    _ = T.card := by simp

theorem eval_eqPoly (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = ∑ v ∈ q.1, x v + (if q.2 = true then 0 else 1) := by
  unfold eqPoly
  rw [map_add, map_sum, eval_C]
  simp only [eval_X]

/-- The affine form of an equation is `1` at a point of the cube exactly when the equation
holds there. -/
theorem eval_eqPoly_eq_one_iff (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = 1 ↔ LinEqSat (fun v => decide (x v = 1)) q := by
  rw [eval_eqPoly, linEqSat_iff_sum]

theorem eval_eqPoly_neg (x : V → ZMod 2) (e : LinEq V) :
    eval x (eqPoly (negLinEq e)) = eval x (eqPoly e) + 1 := by
  rw [eval_eqPoly, eval_eqPoly]
  rcases e with ⟨f, b⟩
  show ∑ v ∈ f, x v + (if (!b) = true then 0 else 1)
    = ∑ v ∈ f, x v + (if b = true then 0 else 1) + 1
  generalize ∑ v ∈ f, x v = s
  cases b
  · revert s
    decide
  · revert s
    decide

theorem eval_termPoly_of_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 1 := by
  unfold termPoly
  rw [map_prod]
  exact Finset.prod_eq_one fun e he => (eval_eqPoly_eq_one_iff x e).mpr (h e he)

theorem eval_termPoly_of_not_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : ¬ LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 0 := by
  obtain ⟨e, he, hne⟩ : ∃ e ∈ T, ¬ LinEqSat (fun v => decide (x v = 1)) e := by
    by_contra hcon
    exact h fun e he => by_contra fun hn => hcon ⟨e, he, hn⟩
  unfold termPoly
  rw [map_prod]
  refine Finset.prod_eq_zero he ?_
  rcases zmod2_cases (eval x (eqPoly e)) with h0 | h1
  · exact h0
  · exact absurd ((eval_eqPoly_eq_one_iff x e).mp h1) hne

variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}

/-- Weakening, case (a), multiplied form. If every assignment satisfying the term `T`
satisfies the term `S`, then `h * (termPoly T + termPoly T * termPoly S)` is in the space.
Budget `deg h + T.card + S.card ≤ D`. -/
theorem weak_term_mul (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T.card + S.card ≤ D) :
    h * (termPoly T + termPoly T * termPoly S) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have hT := totalDegree_termPoly_le T
    have hS := totalDegree_termPoly_le S
    have h1 : (termPoly T + termPoly T * termPoly S).totalDegree ≤ T.card + S.card :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hS))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [eval_termPoly_of_sat x T hT, eval_termPoly_of_sat x S (himp _ hT)]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp

/-- Weakening, case (a). Budget `T.card + S.card ≤ D`. -/
theorem weak_term (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S) (hB : T.card + S.card ≤ D) :
    termPoly T + termPoly T * termPoly S ∈ C := by
  have h := weak_term_mul hC T S himp 1 (b := 0) (by simp) (by omega)
  rwa [one_mul] at h

/-- A term that no assignment satisfies. Budget `deg h + T.card ≤ D`. -/
theorem unsat_term_mul (hC : DegClosed C D) (T : LinTerm V)
    (hT : ∀ a : V → Bool, ¬ LinTermSat a T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card ≤ D) :
    h * termPoly T ∈ C := by
  refine vanish_mem hC ((totalDegree_mul_le' hh (totalDegree_termPoly_le T)).trans hB) ?_
  intro x
  rw [map_mul, eval_termPoly_of_not_sat x T (hT _), mul_zero]

/-- The cut step: a term times the affine form of the complement of one of its equations.
Budget `deg h + T.card + 1 ≤ D`. -/
theorem term_neg_mul (hC : DegClosed C D) (T : LinTerm V) (e : LinEq V) (he : e ∈ T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card + 1 ≤ D) :
    h * (termPoly T * eqPoly (negLinEq e)) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_mul_le' (totalDegree_termPoly_le T)
      (totalDegree_eqPoly_le (negLinEq e))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_mul, eval_eqPoly_neg]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [(eval_eqPoly_eq_one_iff x e).mpr (hT e he)]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, mul_zero, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp

/-- The and-introduction step: the indicator of a union is the product of the indicators
modulo the space. Budget `deg h + T₁.card + T₂.card ≤ D`. -/
theorem term_union_mul [DecidableEq V] (hC : DegClosed C D) (T₁ T₂ : LinTerm V)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T₁.card + T₂.card ≤ D) :
    h * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_termPoly_le T₁
    have h2 := totalDegree_termPoly_le T₂
    have h3 := (totalDegree_termPoly_le (T₁ ∪ T₂)).trans (Finset.card_union_le T₁ T₂)
    have h4 : (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂).totalDegree
        ≤ T₁.card + T₂.card :=
      (totalDegree_add _ _).trans (max_le h3 (totalDegree_mul_le' h1 h2))
    exact (totalDegree_mul_le' hh h4).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have h11 : (1 : ZMod 2) + 1 * 1 = 0 := by decide
    by_cases h1 : LinTermSat (fun v => decide (x v = 1)) T₁
    · by_cases h2 : LinTermSat (fun v => decide (x v = 1)) T₂
      · have hu : LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := by
          intro q hq
          rcases Finset.mem_union.mp hq with hq | hq
          · exact h1 q hq
          · exact h2 q hq
        rw [eval_termPoly_of_sat x _ hu, eval_termPoly_of_sat x _ h1,
          eval_termPoly_of_sat x _ h2, h11, mul_zero]
      · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
          h2 fun q hq => hu q (Finset.mem_union_right _ hq)
        rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h2]
        simp
    · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
        h1 fun q hq => hu q (Finset.mem_union_left _ hq)
      rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h1]
      simp

end Terms

section Alternative

/-- A member of the span of the image of a finite set, over the two-element field, is the sum
over a subset. -/
theorem span_image_sum {ι M : Type} [AddCommGroup M] [Module (ZMod 2) M] (w : ι → M)
    (s : Finset ι) {y : M} (hy : y ∈ Submodule.span (ZMod 2) (w '' (↑s : Set ι))) :
    ∃ I : Finset ι, I ⊆ s ∧ y = ∑ i ∈ I, w i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hy
  obtain ⟨lc, hlc, rfl⟩ := hy
  refine ⟨lc.support, fun d hd => Finset.mem_coe.mp ((Finsupp.mem_supported _ _).mp hlc hd), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h1 : lc d = 1 := by
    generalize lc d = x at h0
    revert x
    decide
  rw [h1, one_smul]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The alternative behind termwise weakening, case (b): `lin_alternative` relative to the
affine space of a term. If every assignment satisfying the term `T` satisfies one of the
equations of `Q`, then the complements of some equations of `T` and the affine forms of some
equations of `Q` sum to `1`. At `T = {q}` this is `lin_alternative` (`I = ∅` or `I = {q}`).
No consistency of `T` is assumed. -/
theorem term_alternative (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ ∃ I : Finset (LinEq V), I ⊆ T ∧
      ∑ e ∈ I, (eqPoly e + 1) + ∑ d ∈ J, eqPoly d = 1 := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
        ∪ (eqVec '' (↑Q : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
          ∪ (eqVec '' (↑Q : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
            ∪ (eqVec '' (↑Q : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hT : LinTermSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) T := by
      intro e he
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Or.inl ⟨e, Finset.mem_coe.mpr he, rfl⟩))
      rw [map_add, h1] at this
      generalize φ (eqVec e) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hT
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Or.inr ⟨d, Finset.mem_coe.mpr hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.span_union, Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨I, hI, rfl⟩ := span_image_sum (fun e : LinEq V => eqVec e + (0, 1)) T hy
  obtain ⟨J, hJ, rfl⟩ := span_image_sum eqVec Q hz
  refine ⟨J, hJ, I, hI, ?_⟩
  have hP := congrArg affPoly hyz
  simp only [map_add, map_sum, affPoly_eqVec, affPoly_one] at hP
  exact hP

variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}

/-- Weakening, case (b), multiplied form. If every assignment satisfying the term `T`
satisfies one of the equations of `Q`, then some `J ⊆ Q`, chosen before the multiplier, has
`h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)` in the space for every `h` with
`deg h + T.card + 1 ≤ D`. The inconsistent case is included. -/
theorem weak_disj_mul (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, I, hI, hid⟩ := term_alternative T Q himp
  refine ⟨J, hJ, fun h b hh hB => vanish_mem hC ?_ ?_⟩
  · have hT := totalDegree_termPoly_le T
    have hs : (∑ d ∈ J, eqPoly d).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun d _ => totalDegree_eqPoly_le d
    have h1 : (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d).totalDegree ≤ T.card + 1 :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hs))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · have h0 : eval x (∑ e ∈ I, (eqPoly e + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [map_add, map_one, (eval_eqPoly_eq_one_iff x e).mpr (hT e (hI he))]
        decide
      have h1 : eval x (∑ d ∈ J, eqPoly d) = 1 := by
        have := congrArg (eval x) hid
        rw [map_add, h0, zero_add, map_one] at this
        exact this
      rw [eval_termPoly_of_sat x T hT, h1]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp

/-- Weakening, case (b). Budget `T.card + 1 ≤ D`. -/
theorem weak_disj (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) (hB : T.card + 1 ≤ D) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ termPoly T + termPoly T * ∑ d ∈ J, eqPoly d ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T Q himp
  refine ⟨J, hJ, ?_⟩
  have h := hmul 1 0 (by simp) (by omega)
  rwa [one_mul] at h

/-- Weakening, case (b), in the form of the rule: the hypothesis is the second disjunct of
`IsLinKWeakening` for the term `T` and the line `M`. -/
theorem weak_disj_line (hC : DegClosed C D) (T : LinTerm V) (M : LinKLine V)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q) :
    ∃ J : Finset (LinEq V), (∀ d ∈ J, ({d} : LinTerm V) ∈ M) ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T
    ((M.biUnion id).filter (fun q => ({q} : LinTerm V) ∈ M))
    (fun a ha => by
      obtain ⟨q, hq, hs⟩ := himp a ha
      exact ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩, hq⟩, hs⟩)
  exact ⟨J, fun d hd => (Finset.mem_filter.mp (hJ hd)).2, hmul⟩

end Alternative

/-! ## Part 2: the plan. Statements only from here on. -/

/-- The inputs of a line: the indicators of its terms. -/
noncomputable def lineInputs {V : Type} (L : LinKLine V) : Set (MvPolynomial V (ZMod 2)) :=
  (fun T => termPoly T) '' (↑L : Set (LinTerm V))

/-- The gain per factor when the level drops by `k`. At `k = 1` it is `eta`. -/
noncomputable def etaK (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)

theorem etaK_one (n K : ℕ) : etaK n K 1 = eta n K := rfl

section Abstract

/-- Idempotence of every polynomial. PROVED above as `idem_mul`; listed for the chain.
Budget `2 * deg g ≤ D` (with a multiplier, `deg h + 2 * deg g ≤ D`). Generalizes
`DegSizeSim.affine_idem` (degree one, budget `2 ≤ D`). -/
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ), DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), 2 * g.totalDegree ≤ D → g * g + g ∈ C

/-- The transfer step for inputs of degree at most `k`. Budget `K + t * k + deg R ≤ D`.
Generalizes `DegSizeSim.transfer` (`k = 1`: `K + t + r`). -/
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t * k + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C

/-- Rank retention for inputs of degree at most `k`, from `rank_retention_mul` (its `hmul`
costs `b + l + 2 * k`, its `hidem` costs `b + l + 2 * k`). Budget `b + l + 2 * k ≤ D`.
Generalizes `DegSizeRank.rankRetention_used` (`k = 1`: `b + l + 2`). -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b l k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ k) →
    b + l + 2 * k ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) l
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l

/-- Lemma 4.1 as used, inputs of degree at most `k`. Budget `a + K + k ≤ D`. Generalizes
`DegSizeRank.monoRank_used` (`k = 1`: `a + K + 1`); `MonoRank` is reused unchanged. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K k : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → a + K + k ≤ D →
    ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
      errRank C (zMul P G) l' * numMono (Fintype.card σ) l
        ≤ errRank C (zMul P G) l * numMono (Fintype.card σ) l'

/-- The gain lemma with level drop `k`: one more factor removes half of the rank `k` levels
lower. Budget `a + K + 2 * k ≤ D` and `k ≤ K` (the map `f ↦ q * f` must land in level `K`).
Generalizes `DegSizeGain.gain` (`k = 1`: `1 ≤ K`, `a + K + 2`). -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K k : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K →
    a + K + 2 * k ≤ D →
    ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
      2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - k)
        ≤ 2 * errRank C (zMul P ↑G) K

/-- Greedy: `t` factors bring the rank below `h_K * (1 - etaK) ^ t`. Budget
`K + (t + 1) * k ≤ D` (factor number `t + 1` is found with `a = t * k`). Generalizes
`DegSizeGain.greedy` (`k = 1`: `K + t + 1`). -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k : ℕ)
    (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K → K + (t + 1) * k ≤ D →
    ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
      (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
      (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
        ≤ hCodim C K * (1 - etaK (Fintype.card σ) K k) ^ t

/-- The common multiplier. Budget `K + (t + 1) * k ≤ D`. Generalizes `DegSizeGain.common`
(same proof: `codim_iInf` and the count). -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k : ℕ)
    (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
    (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ k) → k ≤ K → K + (t + 1) * k ≤ D →
    (S.card : ℝ) * (1 - etaK (Fintype.card σ) K k) ^ t < 1 →
    ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
      f.totalDegree ≤ K ∧ f ∉ C ∧
      (∀ ν ∈ S, ∀ j, qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
      ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C

end Abstract

/-! ### The simulation, rule by rule

The invariant of a line `L` with approximator `P = ∏ j, (1 + qs j)`, `qs j` in the span of
`lineInputs L`: from `P * termPoly T * f` in the space for every term `T` of `L`, get `P * f`
in the space. Every `P` has degree at most `t * k`. -/

/-- The axiom rule. Budget `K + t * k + w ≤ D` (the inputs of an axiom have degree one, so
`K + t + w` is what is used). Generalizes `DegSizeSim.step_ax`. -/
example : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C

/-- The cut rule. Budget `K + 2 * t * k + 2 * k ≤ D`: transfer through each premise costs
`K + 2 * t * k + k`, the defects (`idem_mul`, `term_neg_mul`) and the absorptions cost
`K + t * k + 2 * k`. Generalizes `DegSizeSim.step_res` (`k = 1`: `K + 2 * t + 2`). -/
example : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C

/-- The and-introduction rule. Budget `K + 2 * t * k + 2 * k ≤ D` (uses `idem_mul` and
`term_union_mul`). No counterpart at `k = 1`, where the rule is a weakening. -/
example : Prop :=
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
    (∏ j, (1 + qM j)) * f ∈ C

/-- The termwise weakening rule. Budget `K + 2 * t * k + 2 * k ≤ D` with `1 ≤ k`: transfer
`K + 2 * t * k`; case (a) by `weak_term_mul` at `K + t * k + 2 * k`; case (b) by
`weak_disj_line` at `K + t * k + k + 1`. Generalizes `DegSizeSim.step_weak` (`k = 1`:
`K + 2 * t` and `K + t + 1`, inside `K + 2 * t + 2`). -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
    (∏ j, (1 + qL j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C

/-- The simulation of a derivation. Budget `K + max (2 * t * k + 2 * k) (t * k + w) ≤ D`.
Generalizes `DegSizeSim.simulation` (`k = 1`: `K + max (2 * t + 2) (t + w)`). -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) →
    IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)

/-- Its consequence for a refutation: the common multiplier is derivable. Generalizes
`DegSizeSim.simulation_refutation`. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f

/-! ### Assembly and arithmetic -/

/-- The assembly inequality. Budget `k ≤ K` and
`K + max (2 * t * k + 2 * k) (t * k + w) ≤ D` (which covers `K + (t + 1) * k` of the common
multiplier). Generalizes `DegSizeAssembly.assembly`. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π → ¬ PCRefutable (cnfSystem F) D →
    k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t

/-- Soundness of Res(k, ⊕), needed to know `D < card V` through `DegSizeArith.complete_deg`.
Generalizes `lin_refutation_unsat`. -/
example : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (π : List (LinKLine V)),
    IsLinKRefutation k F π → ¬ Satisfiable F

/-- `etaK` is at most one (so `1 - etaK` is a nonnegative base). Generalizes
`DegSizeArith.eta_le_one`; needs no hypothesis because `numMono` is monotone. -/
example : Prop := ∀ n K k : ℕ, etaK n K k ≤ 1

/-- The binomial estimate: `k` applications of `DegSizeArith.numMono_ratio`. Generalizes
`DegSizeArith.eta_ge` (`k = 1`: `K / (2 * (n + 1))`). -/
example : Prop :=
  ∀ n K k : ℕ, k ≤ K → K ≤ n + 1 →
    (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k) ≤ etaK n K k

/-- The arithmetic: the final bound from the assembly inequality, with `K = D / 2` and
`t = D / (4 * k) - 1`. Then `t ≥ D / (8 k)`, `K - k + 1 ≥ 7 D / 16`, and `D < card V` gives
`7 / (16 (n + 1)) ≥ 1 / (4 n)`. Generalizes `DegSizeArith.final_of_assembly_256`. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t) →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)

/-! ### The general theorem and the corollary -/

/-- The general theorem: degree to size for Res(k, ⊕). At `k = 1` it reads
`exp (D ^ 2 / (64 v))` under `16 ≤ D` and `4 * w ≤ D`; the checked L-pcx-042 helper has
`exp (D ^ 2 / (256 v))` under `32 ≤ D` and `2 * w ≤ D`. The better constant comes from the
split `K = D / 2`, `t = D / 4 - 1` in place of `K = t = D / 4`, and is paid for by the
stronger width hypothesis. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)

/-- The explicit bound on the functional pigeonhole formula of the expanders of L-pcx-043,
from the general theorem and L-pcx-049. Generalizes `PhpFinal.php_exp`. -/
example : Prop :=
  ∃ b : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ ∀ n ≥ n₀,
    ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
      Fintype.card (PEqualNP.Expanders.GEdge G) ≤ (n + 1) * b ∧
      ∀ π : List (LinKLine (PEqualNP.Expanders.GEdge G)),
        IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π →
        Real.exp (c * n) ≤ (π.length : ℝ)

/-- The corollary L-pcx-054: for every `k ≥ 1`, Res(k, ⊕) is not polynomially bounded on
functional pigeonhole formulas. Generalizes `PhpFinal.php_not_poly`. -/
example : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), N < m ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length

end PEqualNP.ProofComplexity.LinKPlan
