import PEqualNP.Gct.Helpers.MethodCeiling

/-! Helper module, proofs only. The bordered expansion of the permanent: the expansion along
the last column, along the last row, and the two combined for a matrix written in blocks
`[[N, g], [r, c]]`; the corner coefficient of the permanent; and the identity comparing the
permanent on the all ones matrix with the permanent on `sigma4`, the all ones `4 × 4` matrix
with corner entry `-3`. Helper for L-gct-036. -/

namespace PEqualNP.Gct.Helpers.BorderedPerm

open Finset

section Matrix

variable {R : Type*} [CommRing R] {n k : ℕ}

/-- The permutation of `Fin (n + 1)` that sends `Fin.last n` to `i` and `Fin.castSucc j` to
`i.succAbove (τ j)`. -/
def insertLast (i : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr τ).trans (finSuccEquiv' i).symm)

@[simp]
theorem insertLast_last (i : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    insertLast i τ (Fin.last n) = i := by
  simp [insertLast]

@[simp]
theorem insertLast_castSucc (i : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    insertLast i τ (Fin.castSucc j) = i.succAbove (τ j) := by
  simp [insertLast]

/-- Every permutation of `Fin (n + 1)` is `insertLast i τ` for exactly one pair `(i, τ)`. -/
theorem insertLast_bijective :
    Function.Bijective fun x : Fin (n + 1) × Equiv.Perm (Fin n) => insertLast x.1 x.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have h' : insertLast i τ = insertLast i' τ' := h
    have hi : i = i' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n)) h'
      simpa using this
    subst hi
    have hτ : τ = τ' := by
      refine Equiv.ext fun j => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.castSucc j)) h'
      simpa using this
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

/-- Expansion of the permanent along the last column. -/
theorem permanent_succ_last (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    M.permanent =
      ∑ i, M i (Fin.last n) * (M.submatrix i.succAbove Fin.castSucc).permanent := by
  unfold Matrix.permanent
  refine (insertLast_bijective.sum_comp
    (fun σ : Equiv.Perm (Fin (n + 1)) => ∏ i, M (σ i) i)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_castSucc, mul_comm]
  simp

/-- Expansion of the permanent along the last row. -/
theorem permanent_succ_last_row (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    M.permanent =
      ∑ j, M (Fin.last n) j * (M.submatrix Fin.castSucc j.succAbove).permanent := by
  calc M.permanent = M.transpose.permanent := (Matrix.permanent_transpose M).symm
    _ = ∑ j, M.transpose j (Fin.last n) *
          (M.transpose.submatrix j.succAbove Fin.castSucc).permanent :=
        permanent_succ_last _
    _ = _ := by
        refine sum_congr rfl fun j _ => ?_
        rw [← Matrix.permanent_transpose (M.submatrix Fin.castSucc j.succAbove)]
        rfl

/-- The permanent of a matrix in blocks `[[N, g], [r, c]]`, expanded along the last column:
the corner term and the terms of the last column above the corner. -/
theorem permanent_corner_add (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    M.permanent =
      M (Fin.last k) (Fin.last k) * (M.submatrix Fin.castSucc Fin.castSucc).permanent +
        ∑ i : Fin k, M (Fin.castSucc i) (Fin.last k) *
          (M.submatrix (Fin.castSucc i).succAbove Fin.castSucc).permanent := by
  rw [permanent_succ_last M, Fin.sum_univ_castSucc, add_comm, Fin.succAbove_last]

/-- The corner coefficient: two matrices that agree off the last corner have permanents that
differ by the difference of the corners times the permanent of the top left block. -/
theorem permanent_sub_of_eq_off_corner (M M' : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (h : ∀ i j, i ≠ Fin.last k ∨ j ≠ Fin.last k → M' i j = M i j) :
    M'.permanent - M.permanent =
      (M' (Fin.last k) (Fin.last k) - M (Fin.last k) (Fin.last k)) *
        (M.submatrix Fin.castSucc Fin.castSucc).permanent := by
  have hsub : ∀ i : Fin (k + 1),
      M'.submatrix i.succAbove Fin.castSucc = M.submatrix i.succAbove Fin.castSucc := by
    intro i
    ext a b
    exact h _ _ (Or.inr (Fin.castSucc_lt_last b).ne)
  have hcol : ∀ i : Fin k, M' (Fin.castSucc i) (Fin.last k) = M (Fin.castSucc i) (Fin.last k) :=
    fun i => h _ _ (Or.inl (Fin.castSucc_lt_last i).ne)
  have hblock : M'.submatrix Fin.castSucc Fin.castSucc = M.submatrix Fin.castSucc Fin.castSucc := by
    have h0 := hsub (Fin.last k)
    rwa [Fin.succAbove_last] at h0
  rw [permanent_corner_add M', permanent_corner_add M]
  simp only [hsub, hcol, hblock]
  ring

/-- The bordered expansion: for a `(k + 2) × (k + 2)` matrix in blocks `[[N, g], [r, c]]`,
`perm = c * perm N + ∑ i j, g i * r j * perm (N with row i and column j removed)`. -/
theorem permanent_bordered (M : Matrix (Fin (k + 2)) (Fin (k + 2)) R) :
    M.permanent =
      M (Fin.last (k + 1)) (Fin.last (k + 1)) *
          (M.submatrix Fin.castSucc Fin.castSucc).permanent +
        ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          M (Fin.castSucc i) (Fin.last (k + 1)) * M (Fin.last (k + 1)) (Fin.castSucc j) *
            (M.submatrix (fun a => Fin.castSucc (i.succAbove a))
              (fun b => Fin.castSucc (j.succAbove b))).permanent := by
  rw [permanent_corner_add M]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [permanent_succ_last_row (M.submatrix (Fin.castSucc i).succAbove Fin.castSucc), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hlast : (Fin.castSucc i).succAbove (Fin.last k) = Fin.last (k + 1) :=
    Fin.succAbove_of_lt_succ _ _ (Fin.castSucc_lt_last i)
  have hminor : ((M.submatrix (Fin.castSucc i).succAbove Fin.castSucc).submatrix
      Fin.castSucc j.succAbove) =
      M.submatrix (fun a => Fin.castSucc (i.succAbove a))
        (fun b => Fin.castSucc (j.succAbove b)) := by
    ext a b
    simp [Fin.castSucc_succAbove_castSucc]
  rw [hminor, Matrix.submatrix_apply, hlast, mul_assoc]

end Matrix

section Eval

open PEqualNP.Gct.MethodCeiling

variable {k : ℕ}

/-- The top left block of a point of the `(k + 1) × (k + 1)` grid. -/
def topLeft (z : Fin (k + 1) × Fin (k + 1) → ℂ) : Fin k × Fin k → ℂ :=
  fun p => z (Fin.castSucc p.1, Fin.castSucc p.2)

@[simp]
theorem topLeft_apply (z : Fin (k + 1) × Fin (k + 1) → ℂ) (p : Fin k × Fin k) :
    topLeft z p = z (Fin.castSucc p.1, Fin.castSucc p.2) := rfl

theorem topLeft_add (z w : Fin (k + 1) × Fin (k + 1) → ℂ) :
    topLeft (z + w) = topLeft z + topLeft w := rfl

/-- The top left block of a point with row `i` and column `j` removed. -/
def topLeftMinor (z : Fin (k + 2) × Fin (k + 2) → ℂ) (i j : Fin (k + 1)) :
    Fin k × Fin k → ℂ :=
  fun p => z (Fin.castSucc (i.succAbove p.1), Fin.castSucc (j.succAbove p.2))

@[simp]
theorem topLeftMinor_apply (z : Fin (k + 2) × Fin (k + 2) → ℂ) (i j : Fin (k + 1))
    (p : Fin k × Fin k) :
    topLeftMinor z i j p = z (Fin.castSucc (i.succAbove p.1), Fin.castSucc (j.succAbove p.2)) :=
  rfl

/-- (I.a) The corner coefficient of the permanent: for points agreeing off the last corner, the
values of the permanent differ by the difference of the corners times the permanent of the top
left block. -/
theorem eval_permPoly_sub_of_eq_off_corner (z z' : Fin (k + 1) × Fin (k + 1) → ℂ)
    (h : ∀ p, p ≠ (Fin.last k, Fin.last k) → z' p = z p) :
    MvPolynomial.eval z' (PEqualNP.Gct.permPoly ℂ (k + 1)) -
        MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ (k + 1)) =
      (z' (Fin.last k, Fin.last k) - z (Fin.last k, Fin.last k)) *
        MvPolynomial.eval (topLeft z) (PEqualNP.Gct.permPoly ℂ k) := by
  rw [eval_permPoly, eval_permPoly, eval_permPoly]
  refine permanent_sub_of_eq_off_corner _ _ fun i j hij => ?_
  refine h (i, j) fun hp => ?_
  rw [Prod.mk.injEq] at hp
  rcases hij with hi | hj
  · exact hi hp.1
  · exact hj hp.2

/-- (I.a), update form: replacing the corner entry by `c` changes the permanent by
`(c - corner) * perm (top left block)`. -/
theorem eval_permPoly_update_corner (z : Fin (k + 1) × Fin (k + 1) → ℂ) (c : ℂ) :
    MvPolynomial.eval (Function.update z (Fin.last k, Fin.last k) c)
        (PEqualNP.Gct.permPoly ℂ (k + 1)) =
      MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ (k + 1)) +
        (c - z (Fin.last k, Fin.last k)) *
          MvPolynomial.eval (topLeft z) (PEqualNP.Gct.permPoly ℂ k) := by
  have h := eval_permPoly_sub_of_eq_off_corner z (Function.update z (Fin.last k, Fin.last k) c)
    fun p hp => Function.update_of_ne hp _ _
  rw [Function.update_self] at h
  rw [← h]
  ring

/-- (I), every size: for a point `z` of the `(k + 2) × (k + 2)` grid in blocks
`[[N, g], [r, c]]`,
`perm z = c * perm N + ∑ i j, g i * r j * perm (N without row i and column j)`. -/
theorem eval_permPoly_bordered (z : Fin (k + 2) × Fin (k + 2) → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ (k + 2)) =
      z (Fin.last (k + 1), Fin.last (k + 1)) *
          MvPolynomial.eval (topLeft z) (PEqualNP.Gct.permPoly ℂ (k + 1)) +
        ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          z (Fin.castSucc i, Fin.last (k + 1)) * z (Fin.last (k + 1), Fin.castSucc j) *
            MvPolynomial.eval (topLeftMinor z i j) (PEqualNP.Gct.permPoly ℂ k) := by
  rw [eval_permPoly, permanent_bordered]
  simp only [eval_permPoly]
  rfl

/-- The `2 × 2` permanent. -/
theorem eval_permPoly_two (w : Fin 2 × Fin 2 → ℂ) :
    MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 2) =
      w (0, 0) * w (1, 1) + w (0, 1) * w (1, 0) := by
  have h := eval_permPoly_bordered (k := 0) w
  rw [h]
  simp [eval_permPoly, Matrix.permanent]
  ring

/-- (I) for the `4 × 4` permanent, the `2 × 2` minors written out. -/
theorem eval_permPoly_four_bordered (z : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ 4) =
      z (Fin.last 3, Fin.last 3) * MvPolynomial.eval (topLeft z) (PEqualNP.Gct.permPoly ℂ 3) +
        ∑ i : Fin 3, ∑ j : Fin 3,
          z (Fin.castSucc i, Fin.last 3) * z (Fin.last 3, Fin.castSucc j) *
            (z (Fin.castSucc (i.succAbove 0), Fin.castSucc (j.succAbove 0)) *
                z (Fin.castSucc (i.succAbove 1), Fin.castSucc (j.succAbove 1)) +
              z (Fin.castSucc (i.succAbove 0), Fin.castSucc (j.succAbove 1)) *
                z (Fin.castSucc (i.succAbove 1), Fin.castSucc (j.succAbove 0))) := by
  rw [eval_permPoly_bordered (k := 2) z]
  simp only [eval_permPoly_two, topLeftMinor_apply]

/-- The permanent at the all ones point is `k!`. -/
theorem eval_permPoly_one (k : ℕ) :
    MvPolynomial.eval (fun _ => 1) (PEqualNP.Gct.permPoly ℂ k) = (k.factorial : ℂ) := by
  rw [eval_permPoly]
  simp [Matrix.permanent, Fintype.card_perm]

/-- The all ones `4 × 4` matrix with the last corner entry replaced by `-3`. -/
def sigma4 : Fin 4 × Fin 4 → ℂ :=
  fun p => if p = (Fin.last 3, Fin.last 3) then -3 else 1

theorem sigma4_corner : sigma4 (Fin.last 3, Fin.last 3) = -3 := by
  simp only [sigma4, ↓reduceIte]

theorem sigma4_of_ne {p : Fin 4 × Fin 4} (hp : p ≠ (Fin.last 3, Fin.last 3)) : sigma4 p = 1 := by
  simp only [sigma4, hp, ↓reduceIte]

theorem topLeft_sigma4 : topLeft sigma4 = fun _ => 1 := by
  funext p
  exact sigma4_of_ne fun hp => (Fin.castSucc_lt_last p.1).ne (Prod.mk.inj hp).1

/-- (II) The permanent on the all ones matrix plus `t` minus the permanent on `sigma4` plus `t`
is four times the `3 × 3` permanent on the all ones matrix plus the top left block of `t`. -/
theorem eval_permPoly_one_add_sub_sigma4_add (t : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval ((fun _ => 1) + t) (PEqualNP.Gct.permPoly ℂ 4) -
        MvPolynomial.eval (sigma4 + t) (PEqualNP.Gct.permPoly ℂ 4) =
      4 * MvPolynomial.eval ((fun _ => 1) + topLeft t) (PEqualNP.Gct.permPoly ℂ 3) := by
  have h := eval_permPoly_sub_of_eq_off_corner (k := 3) (sigma4 + t) ((fun _ => 1) + t)
    fun p hp => by simp [sigma4_of_ne hp]
  rw [h, topLeft_add, topLeft_sigma4]
  simp only [Pi.add_apply]
  rw [sigma4_corner]
  congr 1
  ring

/-- The permanent vanishes at `sigma4`. -/
theorem eval_permPoly_sigma4 : MvPolynomial.eval sigma4 (PEqualNP.Gct.permPoly ℂ 4) = 0 := by
  have h := eval_permPoly_one_add_sub_sigma4_add 0
  have h0 : topLeft (0 : Fin 4 × Fin 4 → ℂ) = 0 := rfl
  rw [h0, add_zero, add_zero, add_zero, eval_permPoly_one, eval_permPoly_one] at h
  have h24 : ((Nat.factorial 4 : ℕ) : ℂ) = 24 := by norm_num [Nat.factorial]
  have h6 : ((Nat.factorial 3 : ℕ) : ℂ) = 6 := by norm_num [Nat.factorial]
  rw [h24, h6] at h
  linear_combination -h

end Eval

end PEqualNP.Gct.Helpers.BorderedPerm
