import Mathlib

/-!
# Query evasion on the Boolean cube

Helper module for `PEqualNP.Library.L063` (Lemma 4.3 of Aaronson and Wigderson 2009,
"Algebrization"). For a finite set `Y` of points of `F ^ n`, all but at most `|Y|` points `w` of
the Boolean cube admit a polynomial of individual degree at most two that vanishes on `Y` and
restricts on the cube to the indicator of `w`.
-/

namespace PEqualNP.Library.Helpers.QueryEvasion

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- The point of `F ^ n` with `0/1` coordinates given by a cube point. -/
def pt (z : Fin n → Bool) : Fin n → F := fun i => if z i then (1 : F) else 0

/-- One factor of the cube indicator polynomial. -/
noncomputable def fac (z : Fin n → Bool) (j : Fin n) : MvPolynomial (Fin n) F :=
  if z j then X j else 1 - X j

/-- The multilinear indicator polynomial of a cube point. -/
noncomputable def delta (z : Fin n → Bool) : MvPolynomial (Fin n) F :=
  ∏ j, fac z j

theorem degreeOf_fac_le (z : Fin n → Bool) (i j : Fin n) :
    degreeOf i (fac (F := F) z j) ≤ if i = j then 1 else 0 := by
  classical
  unfold fac
  split_ifs with h1 h2 h2
  · rw [degreeOf_X]; simp [h2]
  · rw [degreeOf_X]; simp [h2]
  · refine (degreeOf_sub_le _ _ _).trans ?_
    rw [degreeOf_X]; simp [h2]
  · refine (degreeOf_sub_le _ _ _).trans ?_
    rw [degreeOf_X]; simp [h2]

theorem degreeOf_delta_le (z : Fin n → Bool) (i : Fin n) :
    degreeOf i (delta (F := F) z) ≤ 1 := by
  classical
  refine (degreeOf_prod_le i _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => degreeOf_fac_le (F := F) z i j).trans ?_
  simp

theorem eval_delta (z z' : Fin n → Bool) :
    eval (pt z') (delta (F := F) z) = if z' = z then 1 else 0 := by
  classical
  unfold delta
  rw [map_prod]
  split_ifs with h
  · subst h
    apply Finset.prod_eq_one
    intro i _
    unfold fac pt
    cases hz : z' i <;> simp [hz]
  · obtain ⟨i, hi⟩ : ∃ i, z' i ≠ z i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold fac pt
    cases hz : z i <;> cases hz' : z' i <;> simp_all

/-- Multilinear interpolation of a function on the cube, as a linear map. -/
noncomputable def interp (F : Type*) [Field F] (n : ℕ) :
    ((Fin n → Bool) → F) →ₗ[F] MvPolynomial (Fin n) F :=
  ∑ z, (LinearMap.proj z : ((Fin n → Bool) → F) →ₗ[F] F).smulRight (delta z)

theorem interp_apply (g : (Fin n → Bool) → F) :
    interp F n g = ∑ z, g z • delta z := by
  simp [interp]

theorem eval_interp (g : (Fin n → Bool) → F) (z' : Fin n → Bool) :
    eval (pt z') (interp F n g) = g z' := by
  classical
  rw [interp_apply, map_sum]
  simp [smul_eval, eval_delta]

theorem degreeOf_interp_le (g : (Fin n → Bool) → F) (i : Fin n) :
    degreeOf i (interp F n g) ≤ 1 := by
  rw [interp_apply]
  refine (degreeOf_sum_le i _ _).trans ?_
  refine Finset.sup_le fun z _ => ?_
  rw [smul_eq_C_mul]
  exact (degreeOf_C_mul_le _ _ _).trans (degreeOf_delta_le z i)

/-- Evaluation of the interpolant at the points of `Y`. -/
noncomputable def evalY (F : Type*) [Field F] (n : ℕ) (Y : Finset (Fin n → F)) :
    ((Fin n → Bool) → F) →ₗ[F] (Y → F) :=
  (LinearMap.pi fun y : Y => (MvPolynomial.aeval y.1).toLinearMap) ∘ₗ interp F n

theorem evalY_apply (Y : Finset (Fin n → F)) (g : (Fin n → Bool) → F) (y : Y) :
    evalY F n Y g y = eval y.1 (interp F n g) := by
  simp [evalY]

theorem main (F : Type) [Field F] (n : ℕ) (Y : Finset (Fin n → F)) :
    ∃ G : Finset (Fin n → Bool), 2 ^ n ≤ G.card + Y.card ∧ ∀ w ∈ G,
      ∃ p : MvPolynomial (Fin n) F, (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 2) ∧
        (∀ y ∈ Y, MvPolynomial.eval y p = 0) ∧
        ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : F) else 0) p =
          if z = w then 1 else 0 := by
  classical
  let G : Finset (Fin n → Bool) := Finset.univ.filter (fun w => ∃ g ∈ LinearMap.ker (evalY F n Y), g w ≠ 0)
  refine ⟨G, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker (evalY F n Y)
    rw [Module.finrank_fintype_fun_eq_card] at h1
    have hcard' : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
    rw [hcard'] at h1
    have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
    have h2 : Module.finrank F (LinearMap.range (evalY F n Y)) ≤ Y.card := by
      refine (Submodule.finrank_le _).trans ?_
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    let R : LinearMap.ker (evalY F n Y) →ₗ[F] (G → F) :=
      (LinearMap.pi fun w : G => (LinearMap.proj w.1 : ((Fin n → Bool) → F) →ₗ[F] F)) ∘ₗ
        (LinearMap.ker (evalY F n Y)).subtype
    have hR : Function.Injective R := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro g hg
      apply Subtype.ext
      funext w
      by_contra hw
      have hwG : w ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, g.1, g.2, hw⟩
      have := congrFun hg ⟨w, hwG⟩
      exact hw (by simpa [R] using this)
    have h3 := LinearMap.finrank_le_finrank_of_injective hR
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h3
    omega
  · intro w hw
    obtain ⟨g, hgK, hgw⟩ := (Finset.mem_filter.1 hw).2
    set g' := (g w)⁻¹ • g with hg'
    have hg'K : g' ∈ LinearMap.ker (evalY F n Y) := Submodule.smul_mem _ _ hgK
    have hg'w : g' w = 1 := by simp [hg', hgw]
    refine ⟨interp F n g' * delta w, ?_, ?_, ?_⟩
    · intro i
      refine (degreeOf_mul_le _ _ _).trans ?_
      have := degreeOf_interp_le g' i
      have := degreeOf_delta_le (F := F) w i
      omega
    · intro y hy
      have h0 : evalY F n Y g' ⟨y, hy⟩ = 0 := by
        rw [LinearMap.mem_ker.1 hg'K]; rfl
      rw [evalY_apply] at h0
      simp [h0]
    · intro z
      have h := eval_interp g' z
      have hd := eval_delta (F := F) w z
      unfold pt at h hd
      rw [map_mul, h, hd]
      split_ifs with hz
      · subst hz; simp [hg'w]
      · simp

end PEqualNP.Library.Helpers.QueryEvasion
