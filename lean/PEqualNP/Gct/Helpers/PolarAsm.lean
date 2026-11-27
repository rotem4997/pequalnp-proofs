import Mathlib
import PEqualNP.Gct.Helpers.BezPoints
import PEqualNP.Gct.Helpers.PolarGeneric

/-!
Helpers for L-gct-049: the statements of L-gct-047 (independence of the gradients for some
directions `v`) and L-gct-048 (a covector `a` with no polar zeros on `a.x = 0`) give the
statement of L-gct-034, through count lemma B (L-gct-042).

The one non-formal point: none of the forms `G`, `a.x`, `D_{v_k} G` is the zero polynomial.
This follows from `polarAsm_nontrivial_zero`: `n` forms of positive degree in `n` variables,
one of them zero, have a nonzero common zero. Proof: otherwise `C[x]/(g)` is finite dimensional
of some dimension `K`; replacing each zero form by `X_0 ^ (K + 1)` keeps the only common zero
at `0` and gives a square system with `dim C[x]/(f) >= K + 1` by the dimension lower bound of
L-gct-042, while `C[x]/(f)` is a quotient of `C[x]/(g)`.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

theorem polarAsm_top_eq {n e : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p.IsHomogeneous e) :
    homogeneousComponent p.totalDegree p = p := by
  by_cases h0 : p = 0
  · simp [h0]
  · rw [hp.totalDegree h0]
    exact (homogeneousComponent_of_mem hp).trans (by simp)

/-- `n` forms of positive degree in `n` variables, one of them the zero polynomial, have a
nonzero common zero. -/
theorem polarAsm_nontrivial_zero {n : ℕ} (g : Fin n → MvPolynomial (Fin n) ℂ) (e : Fin n → ℕ)
    (he : ∀ i, 1 ≤ e i) (hg : ∀ i, (g i).IsHomogeneous (e i)) (i0 : Fin n) (hi0 : g i0 = 0)
    (hz : ∀ x : Fin n → ℂ, (∀ i, eval x (g i) = 0) → x = 0) : False := by
  classical
  have hinf : ∀ x : Fin n → ℂ,
      (∀ i, eval x (homogeneousComponent (g i).totalDegree (g i)) = 0) → x = 0 :=
    fun x hx => hz x fun i => by simpa [polarAsm_top_eq (hg i)] using hx i
  haveI := bez_finite_quotient g hinf
  set K := Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range g)) with hK
  let f : Fin n → MvPolynomial (Fin n) ℂ := fun i => if g i = 0 then X i0 ^ (K + 1) else g i
  have hftop : ∀ i, homogeneousComponent (f i).totalDegree (f i) = f i := by
    intro i
    by_cases h : g i = 0
    · simp only [f, h, ite_true]
      exact polarAsm_top_eq (isHomogeneous_X_pow i0 (K + 1))
    · simp only [f, h, ite_false]
      exact polarAsm_top_eq (hg i)
  have hfdeg : ∀ i, 1 ≤ (f i).totalDegree := by
    intro i
    by_cases h : g i = 0
    · simp only [f, h, ite_true, totalDegree_X_pow]
      omega
    · simp only [f, h, ite_false]
      rw [(hg i).totalDegree h]
      exact he i
  have hf0 : (f i0).totalDegree = K + 1 := by
    simp only [f, hi0, ite_true, totalDegree_X_pow]
  have hfinf : ∀ x : Fin n → ℂ,
      (∀ i, eval x (homogeneousComponent (f i).totalDegree (f i)) = 0) → x = 0 := by
    intro x hx
    refine hz x fun i => ?_
    by_cases h : g i = 0
    · simp [h]
    · have := hx i
      rw [hftop i] at this
      simpa [f, h] using this
  have hle := bez_finrank_ge f hfinf
  have hIJ : Ideal.span (Set.range g) ≤ Ideal.span (Set.range f) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases h : g i = 0
    · rw [SetLike.mem_coe, h]
      exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨i, by simp [f, h]⟩
  have hsurj := LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.factorₐ ℂ hIJ).toLinearMap) (Ideal.Quotient.factor_surjective hIJ)
  have hprod : K + 1 ≤ ∏ i, (f i).totalDegree := by
    rw [← hf0]
    exact Finset.single_le_prod (fun i _ => hfdeg i) (Finset.mem_univ i0)
  omega

theorem eval_affine_sub_one {n : ℕ} (a x : Fin n → ℂ) :
    eval x (∑ j, C (a j) * X j - 1 : MvPolynomial (Fin n) ℂ) = (∑ j, a j * x j) - 1 := by
  simp [map_sum]

/-- The assembly L-gct-049. -/
theorem polarAsm_holds : (∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ v : Fin h → Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, x ≠ 0 → MvPolynomial.eval x G = 0 → (∀ k, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → LinearIndependent ℂ (Fin.cons (fun j => MvPolynomial.eval x (MvPolynomial.pderiv j G)) (fun k j => MvPolynomial.eval x (MvPolynomial.pderiv j (∑ l, MvPolynomial.C (v k l) * MvPolynomial.pderiv l G))) : Fin (h + 1) → Fin (h + 2) → ℂ)) → (∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ) (v : Fin h → Fin (h + 2) → ℂ), G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, x ≠ 0 → MvPolynomial.eval x G = 0 → (∀ k, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → LinearIndependent ℂ (Fin.cons (fun j => MvPolynomial.eval x (MvPolynomial.pderiv j G)) (fun k j => MvPolynomial.eval x (MvPolynomial.pderiv j (∑ l, MvPolynomial.C (v k l) * MvPolynomial.pderiv l G))) : Fin (h + 1) → Fin (h + 2) → ℂ)) → ∃ a : Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, MvPolynomial.eval x G = 0 → ∑ j, a j * x j = 0 → (∀ k : Fin h, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → x = 0) → (∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (r - 1) ^ (h + 1) ≤ S.card ∧ ∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) := by
  classical
  intro H47 H48 h r G hr hG hsm
  obtain ⟨v, hv⟩ := H47 h r G hr hG hsm
  obtain ⟨a, ha⟩ := H48 h r G v hG hv
  have hLh : (∑ j, C (a j) * X j : MvPolynomial (Fin (h + 2)) ℂ).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℂ j).C_mul _
  let g : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ :=
    Fin.cons G (Fin.cons (∑ j, C (a j) * X j) (fun k => polarD G v k))
  let e : Fin (h + 2) → ℕ := Fin.cons r (Fin.cons 1 (fun _ => r - 1))
  have hge : ∀ i, (g i).IsHomogeneous (e i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · simpa [g, e] using hG
    · simpa [g, e] using hLh
    · simpa [g, e] using polarD_isHomogeneous hG v k
  have he : ∀ i, 1 ≤ e i := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · simp only [e, Fin.cons_zero]; omega
    · simp [e]
    · simp only [e, Fin.cons_succ]; omega
  have hgz : ∀ x : Fin (h + 2) → ℂ, (∀ i, eval x (g i) = 0) → x = 0 := by
    intro x hx
    refine ha x (by simpa [g] using hx 0) ?_ (fun k => by simpa [g, polarD] using hx k.succ.succ)
    have := hx 1
    simpa [g, map_sum] using this
  have hgne : ∀ i, g i ≠ 0 := fun i hi => polarAsm_nontrivial_zero g e he hge i hi hgz
  have hG0 : G ≠ 0 := by simpa [g] using hgne 0
  have hL0 : (∑ j, C (a j) * X j : MvPolynomial (Fin (h + 2)) ℂ) ≠ 0 := by
    simpa [g] using hgne 1
  have hD0 : ∀ k, polarD G v k ≠ 0 := fun k => by simpa [g] using hgne k.succ.succ
  have hcompL : homogeneousComponent 1 (∑ j, C (a j) * X j - 1 : MvPolynomial (Fin (h + 2)) ℂ) =
      ∑ j, C (a j) * X j := by
    have e1 : homogeneousComponent 1 (∑ j, C (a j) * X j : MvPolynomial (Fin (h + 2)) ℂ) =
        ∑ j, C (a j) * X j := (homogeneousComponent_of_mem hLh).trans (by simp)
    have e2 : homogeneousComponent 1 (1 : MvPolynomial (Fin (h + 2)) ℂ) = 0 :=
      homogeneousComponent_eq_zero _ _ (by simp)
    rw [map_sub, e1, e2, sub_zero]
  have hdegL : (∑ j, C (a j) * X j - 1 : MvPolynomial (Fin (h + 2)) ℂ).totalDegree = 1 := by
    apply le_antisymm
    · refine (totalDegree_sub _ _).trans ?_
      rw [hLh.totalDegree hL0]
      simp
    · by_contra hlt
      push Not at hlt
      apply hL0
      rw [← hcompL]
      exact homogeneousComponent_eq_zero _ _ hlt
  have hdegD : ∀ k, (polarD G v k).totalDegree = r - 1 := fun k =>
    (polarD_isHomogeneous hG v k).totalDegree (hD0 k)
  have hjac : ∀ x : Fin (h + 2) → ℂ, (∀ i, eval x ((Fin.cons G (Fin.cons
      (∑ j, C (a j) * X j - 1) (fun k : Fin h => polarD G v k)) :
        Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) →
      (Matrix.of fun i j : Fin (h + 2) => eval x (pderiv j ((Fin.cons G (Fin.cons
        (∑ j, C (a j) * X j - 1) (fun k : Fin h => polarD G v k)) :
          Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0 := by
    intro x hx
    have hGx : eval x G = 0 := by simpa using hx 0
    have hax : ∑ j, a j * x j = 1 := by
      have := hx 1
      change eval x (∑ j, C (a j) * X j - 1 : MvPolynomial (Fin (h + 2)) ℂ) = 0 at this
      rw [eval_affine_sub_one, sub_eq_zero] at this
      exact this
    have hDx : ∀ k, eval x (polarD G v k) = 0 := fun k => by simpa using hx k.succ.succ
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hax
    exact polar_jacobian_det_ne_zero G hG a v x hGx hax hDx
      (hv x hx0 hGx (fun k => by simpa [polarD] using hDx k))
  have htop : ∀ x : Fin (h + 2) → ℂ, (∀ i, eval x (homogeneousComponent
      ((Fin.cons G (Fin.cons (∑ j, C (a j) * X j - 1) (fun k : Fin h => polarD G v k)) :
        Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i).totalDegree
      ((Fin.cons G (Fin.cons (∑ j, C (a j) * X j - 1) (fun k : Fin h => polarD G v k)) :
        Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i)) = 0) → x = 0 := by
    intro x hx
    refine hgz x fun i => ?_
    have := hx i
    revert this
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · simp only [Fin.cons_zero, polarAsm_top_eq hG]
      intro h1
      simpa [g] using h1
    · rw [show (Fin.succ 0 : Fin (h + 2)) = 1 from rfl]
      simp only [show (1 : Fin (h + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero,
        hdegL, hcompL]
      intro h1
      simpa [g] using h1
    · simp only [Fin.cons_succ, polarAsm_top_eq (polarD_isHomogeneous hG v k)]
      intro h1
      simpa [g] using h1
  obtain ⟨S, hS, hSz⟩ := bezCountB_holds (h + 2) _ htop hjac
  refine ⟨a, v, S, ?_, fun x hx => ⟨hSz x hx, hjac x (hSz x hx)⟩⟩
  refine le_trans ?_ hS
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hdegL, hdegD, hG.totalDegree hG0,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul (by omega) le_rfl

end PEqualNP.Gct.Helpers
