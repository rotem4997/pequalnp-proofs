import PEqualNP.Gct.Helpers.Rung.Statements
import PEqualNP.Gct.Helpers.Rung.LemmaE
import PEqualNP.Gct.Helpers.Rung.RowSystem.Matching
import PEqualNP.Gct.Helpers.Rung.RowSystem.Bridge

/-!
# The superquadratic rung: proof of `RowSystem`

Helper module, proofs only. It proves the step `RowSystem` of `Statements.lean` (identity I2 of
the notes): at a point where the gradient of the gadget vanishes, all rows are common zeros of
one system of `b` polynomials whose top forms are the partials of `e_r`.

Route. Write the gadget as a sum over matchings (`Bridge.lean`) and expand along a row
(`Matching.lean`): `G_(s+1)(all rows, U) = G_(s+1)(rows without i, U)
+ ∑_{c ∈ U} x_ic G_s(rows without i, U without c)`. The polynomials `Q s U`, defined by
`Q 0 U = 1`, `Q (s+1) U = G_(s+1)(all rows, U) - ∑_{c ∈ U} y_c Q s (U without c)`, therefore
take the value `G_s(rows without i, U)` at row `i`, for every `i`, and their top form is
`(-1)^s s!` times the elementary symmetric polynomial of degree `s` in the variables of `U`.
With `U` the columns other than `j` and `s = r - 1`, the value at row `i` is the partial
derivative of the gadget in `x_ij`. Nothing here is a result until the lemma that rests on it
is checked.
-/

namespace PEqualNP.Gct.Rung.RowSys

open Finset MvPolynomial
open PEqualNP.Gct.Rung.LemE (esymmOn esymmOn_zero esymmOn_insert pderiv_esymm_succ)

variable {a b : ℕ}

theorem mpOn_zero {R : Type*} [CommRing R] (rows : Finset (Fin a)) (cols : Finset (Fin b))
    (W : Fin a × Fin b → R) : mpOn rows cols 0 W = 1 := by
  have : matchings rows cols 0 = {∅} := by
    ext M
    rw [mem_matchings, mem_singleton]
    constructor
    · rintro ⟨⟨_, h⟩, _⟩
      exact Finset.card_eq_zero.mp h
    · rintro rfl
      exact ⟨⟨Finset.empty_subset _, rfl⟩, by simp [IsMatch]⟩
  simp [mpOn, this]

/-- The polynomials of the row system, before normalization. -/
noncomputable def Q (W : Fin a × Fin b → ℂ) : ℕ → Finset (Fin b) → MvPolynomial (Fin b) ℂ
  | 0, _ => 1
  | s + 1, U => C (mpOn univ U (s + 1) W) - ∑ c ∈ U, X c * Q W s (U.erase c)

/-- At row `i` the polynomial `Q s U` takes the value of the matching sum without row `i`. -/
theorem eval_Q (W : Fin a × Fin b → ℂ) (i : Fin a) :
    ∀ (s : ℕ) (U : Finset (Fin b)),
      eval (fun c => W (i, c)) (Q W s U) = mpOn (univ.erase i) U s W := by
  intro s
  induction s with
  | zero => intro U; simp [Q, mpOn_zero]
  | succ s ih =>
    intro U
    rw [Q, map_sub, eval_C, map_sum, mpOn_row_expand (mem_univ i) W]
    simp only [map_mul, eval_X, ih]
    ring

/-- `∑_{c ∈ U} y_c e_s(U without c) = (s + 1) e_(s+1)(U)`. -/
theorem sum_X_mul_esymmOn_erase (U : Finset (Fin b)) :
    ∀ s : ℕ, ∑ c ∈ U, X c * esymmOn (U.erase c) s
      = ((s + 1 : ℕ) : MvPolynomial (Fin b) ℂ) * esymmOn U (s + 1) := by
  induction U using Finset.induction_on with
  | empty =>
    intro s
    have : (∅ : Finset (Fin b)).powersetCard (s + 1) = ∅ := Finset.powersetCard_eq_empty.mpr (by simp)
    simp [esymmOn, this]
  | insert x U hx ih =>
    intro s
    have hsum : ∀ t : ℕ, ∑ c ∈ U, X c * esymmOn ((insert x U).erase c) (t + 1)
        = ∑ c ∈ U, X c * esymmOn (U.erase c) (t + 1)
          + X x * ∑ c ∈ U, X c * esymmOn (U.erase c) t := by
      intro t
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hxc : x ≠ c := fun h => hx (h ▸ hc)
      rw [Finset.erase_insert_of_ne hxc,
        esymmOn_insert (fun h => hx (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.sum_insert hx, Finset.erase_insert hx]
    cases s with
    | zero =>
      have h0 : ∑ c ∈ U, X c * esymmOn ((insert x U).erase c) 0 = ∑ c ∈ U, X c * esymmOn (U.erase c) 0 := by
        simp [esymmOn_zero]
      rw [h0, ih 0, esymmOn_insert hx, esymmOn_zero]
      push_cast
      ring
    | succ t =>
      rw [hsum t, ih (t + 1), ih t, esymmOn_insert hx (t + 1)]
      push_cast
      ring

/-- The constant of the top form: `(-1)^s s!`. -/
noncomputable def kap (s : ℕ) : ℂ := (-1) ^ s * (s.factorial : ℂ)

theorem kap_ne_zero (s : ℕ) : kap s ≠ 0 := by
  unfold kap
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))

theorem kap_succ (s : ℕ) : kap (s + 1) = -((s + 1 : ℕ) : ℂ) * kap s := by
  unfold kap
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- `Q s U` minus its top form. -/
noncomputable def Rem (W : Fin a × Fin b → ℂ) (s : ℕ) (U : Finset (Fin b)) :
    MvPolynomial (Fin b) ℂ :=
  Q W s U - C (kap s) * esymmOn U s

theorem Rem_succ (W : Fin a × Fin b → ℂ) (s : ℕ) (U : Finset (Fin b)) :
    Rem W (s + 1) U = C (mpOn univ U (s + 1) W) - ∑ c ∈ U, X c * Rem W s (U.erase c) := by
  have h : ∑ c ∈ U, X c * Rem W s (U.erase c)
      = ∑ c ∈ U, X c * Q W s (U.erase c)
        - C (kap s) * (((s + 1 : ℕ) : MvPolynomial (Fin b) ℂ) * esymmOn U (s + 1)) := by
    rw [← sum_X_mul_esymmOn_erase U s, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold Rem
    ring
  rw [h]
  unfold Rem
  rw [Q, kap_succ]
  have hc : (C (-((s + 1 : ℕ) : ℂ) * kap s) : MvPolynomial (Fin b) ℂ)
      = -(((s + 1 : ℕ) : MvPolynomial (Fin b) ℂ) * C (kap s)) := by
    rw [C_mul, C_neg]
    simp
    ring
  rw [hc]
  ring

theorem totalDegree_Rem (W : Fin a × Fin b → ℂ) :
    ∀ (s : ℕ) (U : Finset (Fin b)), (Rem W (s + 1) U).totalDegree ≤ s := by
  intro s
  induction s with
  | zero =>
    intro U
    rw [Rem_succ]
    have : ∀ c ∈ U, X c * Rem W 0 (U.erase c) = 0 := by
      intro c _
      simp [Rem, Q, kap, esymmOn_zero]
    rw [Finset.sum_eq_zero this, sub_zero, totalDegree_C]
  | succ s ih =>
    intro U
    rw [Rem_succ]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_C]; exact Nat.zero_le _
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      have := ih (U.erase c)
      omega

/-- The gadget is the matching sum of the matrix of variables. -/
theorem gadgetPoly_eq_mpOn (a b r : ℕ) :
    gadgetPoly a b r = mpOn univ univ r (fun e : Fin a × Fin b => (X e : MvPolynomial (Fin a × Fin b) ℂ)) := by
  unfold gadgetPoly
  rw [sumSubperm_eq_mpOn]
  rfl

/-- The partial derivative of the gadget in `x_ij` is the matching sum of degree one less
without row `i` and column `j`. -/
theorem eval_pderiv_gadgetPoly (W : Fin a × Fin b → ℂ) (i : Fin a) (j : Fin b) (t : ℕ) :
    eval W (pderiv (i, j) (gadgetPoly a b (t + 1))) = mpOn (univ.erase i) (univ.erase j) t W := by
  rw [gadgetPoly_eq_mpOn]
  unfold mpOn
  rw [map_sum, map_sum, ← sum_erase_bij (mem_univ i) (mem_univ j) (fun M' => ∏ e ∈ M', W e),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [pderiv_prod_X]
  split_ifs
  · rw [map_prod]
    simp
  · simp

theorem rowSystem : RowSystem := by
  intro a b r W hr hgrad
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
  refine ⟨fun j => C (kap (t + 1))⁻¹ * Q W (t + 1) (univ.erase j), fun j => ?_, fun i j => ?_⟩
  · have h : C (kap (t + 1))⁻¹ * Q W (t + 1) (univ.erase j) - pderiv j (esymm (Fin b) ℂ (t + 2))
        = C (kap (t + 1))⁻¹ * Rem W (t + 1) (univ.erase j) := by
      rw [pderiv_esymm_succ]
      unfold Rem
      rw [mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (kap_ne_zero _), C_1, one_mul]
    rw [h]
    have h1 := totalDegree_Rem W t (univ.erase j)
    have h2 := totalDegree_mul (C (kap (t + 1))⁻¹) (Rem W (t + 1) (univ.erase j))
    rw [totalDegree_C] at h2
    omega
  · rw [map_mul, eval_C, eval_Q, ← eval_pderiv_gadgetPoly, hgrad (i, j), mul_zero]

end PEqualNP.Gct.Rung.RowSys

namespace PEqualNP.Gct.Rung

theorem rowSystem : RowSystem := RowSys.rowSystem

end PEqualNP.Gct.Rung
