import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Sigma4Space

/-! Helper module for L-gct-169, the corner lemma. Let `W` be a linear space of `4 × 4` complex
matrices of dimension at least seven on which the permanent vanishes, and fix two rows `I` and
two columns `J`. The members of `W` vanishing on the block `I × J` form a space `W0` of
dimension at least three. On it the permanent is the product of the `2 × 2` permanents of the
blocks `I × J'` and `I' × J` (primes for complements), so one of the two factors vanishes on all
of `W0`. The `2 × 2` permanent `a d + b c` vanishes on no subspace of dimension three, so some
nonzero member of `W0` also vanishes on that block: it has two zero rows or two zero columns.
The indices are carried by permutations `σ`, `τ` of `Fin 4` with `σ 0, σ 1` the rows and
`τ 0, τ 1` the columns. -/

namespace PEqualNP.Gct.Helpers.Corner

open Finset

/-- Permuting rows and columns does not change the value of the permanent polynomial. -/
theorem eval_perm (σ τ : Equiv.Perm (Fin 4)) (w : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval (fun p : Fin 4 × Fin 4 => w (σ p.1, τ p.2)) (PEqualNP.Gct.permPoly ℂ 4) =
      MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) := by
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly, PEqualNP.Gct.MethodCeiling.eval_permPoly]
  have h : (Matrix.of fun i j => w (σ i, τ j)) =
      ((Matrix.of fun i j => w (i, j)).submatrix σ id).submatrix id τ := rfl
  rw [h, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

/-- The four entries of the block with rows `a, b` and columns `c, d`, as a linear map. -/
noncomputable def blk (a b c d : Fin 4) : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.funLeft ℂ ℂ ![(a, c), (a, d), (b, c), (b, d)]

theorem blk_apply (a b c d : Fin 4) (w : Fin 4 × Fin 4 → ℂ) :
    blk a b c d w = ![w (a, c), w (a, d), w (b, c), w (b, d)] := by
  funext k
  fin_cases k <;> rfl

theorem blk_eq_zero {a b c d : Fin 4} {w : Fin 4 × Fin 4 → ℂ} (h : blk a b c d w = 0) :
    w (a, c) = 0 ∧ w (a, d) = 0 ∧ w (b, c) = 0 ∧ w (b, d) = 0 := by
  rw [blk_apply] at h
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩

/-- The `2 × 2` permanent of the block with rows `a, b` and columns `c, d`. -/
def Q (a b c d : Fin 4) (w : Fin 4 × Fin 4 → ℂ) : ℂ := w (a, c) * w (b, d) + w (a, d) * w (b, c)

theorem Q_add_smul (a b c d : Fin 4) (u v : Fin 4 × Fin 4 → ℂ) (t : ℂ) :
    Q a b c d (u + t • v) = Q a b c d u +
      t * (u (a, c) * v (b, d) + v (a, c) * u (b, d) + u (a, d) * v (b, c) + v (a, d) * u (b, c)) +
      t ^ 2 * Q a b c d v := by
  simp only [Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- If the product of two quadratic functions vanishes on a subspace, one of them does. -/
theorem quad_split {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (q₁ q₂ : V → ℂ) (B₁ B₂ : V → V → ℂ)
    (h₁ : ∀ u v : V, ∀ t : ℂ, q₁ (u + t • v) = q₁ u + t * B₁ u v + t ^ 2 * q₁ v)
    (h₂ : ∀ u v : V, ∀ t : ℂ, q₂ (u + t • v) = q₂ u + t * B₂ u v + t ^ 2 * q₂ v)
    (h : ∀ w ∈ S, q₁ w * q₂ w = 0) : (∀ w ∈ S, q₁ w = 0) ∨ (∀ w ∈ S, q₂ w = 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨u, hu, hqu⟩, ⟨v, hv, hqv⟩⟩ := hc
  open Polynomial in
  let p₁ : ℂ[X] := C (q₁ u) + C (B₁ u v) * X + C (q₁ v) * X ^ 2
  open Polynomial in
  let p₂ : ℂ[X] := C (q₂ u) + C (B₂ u v) * X + C (q₂ v) * X ^ 2
  have hp : p₁ * p₂ = 0 := by
    apply Polynomial.funext
    intro r
    have e := h _ (S.add_mem hu (S.smul_mem r hv))
    rw [h₁, h₂] at e
    simp only [p₁, p₂, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero]
    linear_combination e
  rcases mul_eq_zero.1 hp with h0 | h0
  · apply hqu
    have e0 := congrArg (Polynomial.eval 0) h0
    simp only [p₁, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero] at e0
    linear_combination e0
  · apply hqv
    have e0 := congrArg (Polynomial.eval 0) h0
    have e1 := congrArg (Polynomial.eval 1) h0
    have e2 := congrArg (Polynomial.eval (-1)) h0
    simp only [p₂, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero] at e0 e1 e2
    linear_combination (e1 + e2) / 2 - e0

/-- The polar form of `x 0 * x 3 + x 1 * x 2`, as a map into the dual space. -/
noncomputable def polar : (Fin 4 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 4 → ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => x 3 * y 0 + x 0 * y 3 + x 2 * y 1 + x 1 * y 2)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem polar_apply (x y : Fin 4 → ℂ) :
    polar x y = x 3 * y 0 + x 0 * y 3 + x 2 * y 1 + x 1 * y 2 := rfl

theorem polar_injective : Function.Injective polar := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h : ∀ k, polar x (Pi.single k 1) = 0 := fun k => by rw [hx]; rfl
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [polar_apply, Pi.single_apply] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  funext k
  fin_cases k <;> simp [h0, h1, h2, h3]

/-- A subspace on which `x 0 * x 3 + x 1 * x 2` vanishes has dimension at most two. -/
theorem finrank_le_two (R : Submodule ℂ (Fin 4 → ℂ))
    (hR : ∀ x ∈ R, x 0 * x 3 + x 1 * x 2 = 0) : Module.finrank ℂ R ≤ 2 := by
  have hiso : ∀ x ∈ R, ∀ y ∈ R, polar x y = 0 := by
    intro x hx y hy
    have e1 := hR _ (R.add_mem hx hy)
    have e2 := hR x hx
    have e3 := hR y hy
    simp only [Pi.add_apply] at e1
    rw [polar_apply]
    linear_combination e1 - e2 - e3
  have hr : ∀ x : R, polar.domRestrict R x ∈ R.dualAnnihilator := fun x =>
    (Submodule.mem_dualAnnihilator _).2 fun y hy => hiso x x.2 y hy
  have hinj : Function.Injective ((polar.domRestrict R).codRestrict R.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (polar_injective (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq R
  have h3 : Module.finrank ℂ (Fin 4 → ℂ) = 4 := Module.finrank_fin_fun ℂ
  omega

/-- Cutting a space of dimension at least seven by four linear conditions leaves dimension at
least three. -/
theorem finrank_inf_ker (W : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (h7 : 7 ≤ Module.finrank ℂ W)
    (f : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) :
    3 ≤ Module.finrank ℂ (W ⊓ LinearMap.ker f : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  have e2 := LinearMap.finrank_range_add_finrank_ker f
  have e3 := Submodule.finrank_le (LinearMap.range f)
  have e4 := Submodule.finrank_le (W ⊔ LinearMap.ker f)
  have e5 : Module.finrank ℂ (Fin 4 → ℂ) = 4 := Module.finrank_fin_fun ℂ
  have e6 : Module.finrank ℂ (Fin 4 × Fin 4 → ℂ) = 16 := by
    rw [Module.finrank_fintype_fun_eq_card]; rfl
  omega

/-- A linear map that lowers the dimension of a subspace kills a nonzero member of it. -/
theorem exists_ker {S : Submodule ℂ (Fin 4 × Fin 4 → ℂ)} (g : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))
    (hlt : Module.finrank ℂ (S.map g) < Module.finrank ℂ S) : ∃ w ∈ S, w ≠ 0 ∧ g w = 0 := by
  by_contra hc
  push Not at hc
  have hinj : Function.Injective (g.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    exact hc x x.2 (fun h => hne (Subtype.ext h)) hx
  have e := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_domRestrict] at e
  omega

/-- The corner lemma with the two rows `σ 0, σ 1` and the two columns `τ 0, τ 1`. -/
theorem main_perm (W : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hW : ∀ w ∈ W, MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = 0)
    (h7 : 7 ≤ Module.finrank ℂ W) (σ τ : Equiv.Perm (Fin 4)) :
    (∃ w ∈ W, w ≠ 0 ∧ ∀ j : Fin 4, w (σ 0, j) = 0 ∧ w (σ 1, j) = 0) ∨
      (∃ w ∈ W, w ≠ 0 ∧ ∀ i : Fin 4, w (i, τ 0) = 0 ∧ w (i, τ 1) = 0) := by
  set W0 : Submodule ℂ (Fin 4 × Fin 4 → ℂ) :=
    W ⊓ LinearMap.ker (blk (σ 0) (σ 1) (τ 0) (τ 1)) with hW0
  have h3 : 3 ≤ Module.finrank ℂ W0 := finrank_inf_ker W h7 _
  have hmem : ∀ w ∈ W0, w ∈ W ∧ w (σ 0, τ 0) = 0 ∧ w (σ 0, τ 1) = 0 ∧ w (σ 1, τ 0) = 0 ∧
      w (σ 1, τ 1) = 0 := fun w hw => ⟨hw.1, blk_eq_zero hw.2⟩
  have hprod : ∀ w ∈ W0, Q (σ 0) (σ 1) (τ 2) (τ 3) w * Q (σ 2) (σ 3) (τ 0) (τ 1) w = 0 := by
    intro w hw
    obtain ⟨hw, a, b, c, d⟩ := hmem w hw
    have e := hW w hw
    rw [← eval_perm σ τ, PEqualNP.Gct.MethodCeiling.eval_permPoly,
      PEqualNP.Gct.Helpers.Sigma4Space.permanent_four] at e
    simp only [Matrix.of_apply, a, b, c, d, zero_mul, mul_zero, zero_add, add_zero] at e
    simp only [Q]
    linear_combination e
  rcases quad_split W0 _ _ _ _ (Q_add_smul _ _ _ _) (Q_add_smul _ _ _ _) hprod with hq | hq
  · left
    have hR : Module.finrank ℂ (W0.map (blk (σ 0) (σ 1) (τ 2) (τ 3))) ≤ 2 := by
      apply finrank_le_two
      rintro x ⟨w, hw, rfl⟩
      have := hq w hw
      simp only [blk_apply, Q] at this ⊢
      simpa using this
    obtain ⟨w, hw, hne, hk⟩ := exists_ker (S := W0) (blk (σ 0) (σ 1) (τ 2) (τ 3)) (by omega)
    obtain ⟨_, a, b, c, d⟩ := hmem w hw
    obtain ⟨e, f, g, h⟩ := blk_eq_zero hk
    refine ⟨w, (hmem w hw).1, hne, fun j => ?_⟩
    obtain ⟨k, rfl⟩ := τ.surjective j
    fin_cases k <;> simp_all
  · right
    have hR : Module.finrank ℂ (W0.map (blk (σ 2) (σ 3) (τ 0) (τ 1))) ≤ 2 := by
      apply finrank_le_two
      rintro x ⟨w, hw, rfl⟩
      have := hq w hw
      simp only [blk_apply, Q] at this ⊢
      simpa using this
    obtain ⟨w, hw, hne, hk⟩ := exists_ker (S := W0) (blk (σ 2) (σ 3) (τ 0) (τ 1)) (by omega)
    obtain ⟨_, a, b, c, d⟩ := hmem w hw
    obtain ⟨e, f, g, h⟩ := blk_eq_zero hk
    refine ⟨w, (hmem w hw).1, hne, fun i => ?_⟩
    obtain ⟨k, rfl⟩ := σ.surjective i
    fin_cases k <;> simp_all

/-- Two distinct elements of `Fin 4` are the images of `0` and `1` under a permutation. -/
theorem exists_perm (a b : Fin 4) (h : a ≠ b) : ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b := by
  refine ⟨Equiv.swap 0 a * Equiv.swap 1 (Equiv.swap 0 a b), ?_, ?_⟩ <;> revert h <;>
    fin_cases a <;> fin_cases b <;> decide

/-- The corner lemma. -/
theorem main : ∀ W : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
    (∀ w ∈ W, MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = 0) →
    7 ≤ Module.finrank ℂ W → ∀ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ → j₁ ≠ j₂ →
    (∃ w ∈ W, w ≠ 0 ∧ ∀ j : Fin 4, w (i₁, j) = 0 ∧ w (i₂, j) = 0) ∨
      (∃ w ∈ W, w ≠ 0 ∧ ∀ i : Fin 4, w (i, j₁) = 0 ∧ w (i, j₂) = 0) := by
  intro W hW h7 i₁ i₂ j₁ j₂ hi hj
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm i₁ i₂ hi
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm j₁ j₂ hj
  have := main_perm W hW h7 σ τ
  rwa [hσ0, hσ1, hτ0, hτ1] at this

end PEqualNP.Gct.Helpers.Corner
