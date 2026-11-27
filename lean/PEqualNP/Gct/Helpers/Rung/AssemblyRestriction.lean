import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.BorderSubst
import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# The superquadratic rung: assembly of L-gct-057 from its steps

Proves `AssemblyRestriction`: the step statements `RowSpaceExists`, `FewRows`, `GoodSubspace`,
`BlockPerm`, `Arith` and the recorded statement of L-gct-053 together give the recorded
statement of L-gct-057. Nothing here proves any of the steps.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial

/-- The gadget is homogeneous of degree `r`. -/
theorem gadgetPoly_isHomogeneous (a b r : ℕ) : (gadgetPoly a b r).IsHomogeneous r := by
  unfold gadgetPoly sumSubperm
  refine IsHomogeneous.sum _ _ _ fun S _ => IsHomogeneous.sum _ _ _ fun T _ => ?_
  unfold Matrix.permanent
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin r))
    (fun i : Fin r => (Matrix.of fun i j : Fin r =>
      Matrix.mvPolynomialX (Fin a) (Fin b) ℂ (S.1.orderEmbOfFin S.2 i) (T.1.orderEmbOfFin T.2 j))
      (σ i) i) (fun _ => 1) (fun i _ => by
        simp only [Matrix.of_apply, Matrix.mvPolynomialX_apply]
        exact isHomogeneous_X _ _)
  simpa using h

/-- The block sum is homogeneous of degree `r`. -/
theorem blockPoly_isHomogeneous (N a b r : ℕ) : (blockPoly N a b r).IsHomogeneous r := by
  unfold blockPoly
  exact IsHomogeneous.sum _ _ _ fun h _ => (gadgetPoly_isHomogeneous a b r).rename_isHomogeneous

/-- A linear form has total degree at most one. -/
theorem totalDegree_linForm_le {d : ℕ} (c : Fin d → ℂ) :
    (∑ t, C (c t) * X t : MvPolynomial (Fin d) ℂ).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun t _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (isHomogeneous_X ℂ t).totalDegree_le

/-- A linear form is homogeneous of degree one. -/
theorem linForm_isHomogeneous {d : ℕ} (c : Fin d → ℂ) :
    (∑ t, C (c t) * X t : MvPolynomial (Fin d) ℂ).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem assemblyRestriction : AssemblyRestriction := by
  intro hRow hFew hGood hBlock hArith h053 R m0
  -- parameters
  have hr2 : 2 ≤ 48 * R + 48 := by omega
  obtain ⟨P, hP⟩ := hRow (2 * (48 * R + 48)) (48 * R + 48) (48 * R + 48 + 1) hr2 (by omega)
  obtain ⟨M, hM⟩ := hFew (2 * (48 * R + 48)) (48 * R + 48) (48 * R + 48 + 1) P hr2 hP
  obtain ⟨N, hN1, hra, hm0, hm1, hd2, hbig⟩ := hArith R M m0 (48 * R + 48) le_rfl
  generalize hrdef : 48 * R + 48 = r at *
  obtain ⟨L, hL⟩ := hGood (2 * r) r (r + 1) P M hr2 hP hM (3 * r * N) N
  obtain ⟨c, g, hc, hg, hperm⟩ := hBlock N (3 * r * N) (2 * r) r hN1 (by omega) hra (by omega)
  -- reindex the variables of the block sum
  let σ := Fin N × Fin (3 * r * N) × Fin (2 * r)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let G0 : MvPolynomial (Fin (Fintype.card σ)) ℂ :=
    rename e (C c * blockPoly N (3 * r * N) (2 * r) r)
  have hG0 : G0.IsHomogeneous r := by
    have h1 : (C c * blockPoly N (3 * r * N) (2 * r) r).IsHomogeneous r :=
      (blockPoly_isHomogeneous N (3 * r * N) (2 * r) r).C_mul c
    exact h1.rename_isHomogeneous
  -- the gradient hypothesis of L-gct-053 on the transported subspace
  have hgrad : ∀ y : Fin (N * ((3 * r * N - M) * (r + 1))) → ℂ,
      (∀ i, eval (fun n => ∑ s, L (e.symm n) s * y s) (pderiv i G0) = 0) → y = 0 := by
    intro y hy
    refine hL y fun v => ?_
    have h1 := hy (e v)
    have h2 : pderiv (e v) G0 =
        rename e (C c * pderiv v (blockPoly N (3 * r * N) (2 * r) r)) := by
      show pderiv (e v) (rename e (C c * blockPoly N (3 * r * N) (2 * r) r)) = _
      rw [pderiv_rename e.injective, pderiv_C_mul]
    rw [h2, eval_rename] at h1
    have h3 : ((fun n => ∑ s, L (e.symm n) s * y s) ∘ e) = fun v => ∑ s, L v s * y s := by
      funext w
      simp
    rw [h3, map_mul, eval_C] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  obtain ⟨M', hM'⟩ := h053 (Fintype.card σ) (N * ((3 * r * N - M) * (r + 1))) r G0
    (fun n s => L (e.symm n) s) hG0 hgrad
  -- the section and the substitution
  let lin : Fin (Fintype.card σ) → MvPolynomial (Fin (N * ((3 * r * N - M) * (r + 1)))) ℂ :=
    fun n => ∑ t, C (M' n t) * X t
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin (N * ((3 * r * N - M) * (r + 1)))) ℂ :=
    (bind₁ lin).comp (rename e)
  refine ⟨3 * r * N + N * (2 * r + r) - r, r, N * ((3 * r * N - M) * (r + 1)),
    bind₁ lin G0, fun p => φ (g p), hm0, hm1, hr2, hd2, hbig, ?_, hM', ?_, ?_⟩
  · have h := hG0.aeval (n := 1) (S := ℂ) lin (fun i => linForm_isHomogeneous _)
    rw [one_mul] at h
    exact h
  · intro p
    show (bind₁ lin (rename e (g p))).totalDegree ≤ 1
    refine (PEqualNP.Gct.Helpers.totalDegree_bind₁_le_of_affine lin
      (fun i => totalDegree_linForm_le _) _).trans ?_
    exact (totalDegree_rename_le _ _).trans (hg p)
  · have hcomp : bind₁ (fun p => φ (g p)) = φ.comp (bind₁ g) := by
      apply algHom_ext
      intro p
      simp [bind₁_X_right]
    rw [hcomp, AlgHom.comp_apply, hperm]
    rfl

end PEqualNP.Gct.Rung
