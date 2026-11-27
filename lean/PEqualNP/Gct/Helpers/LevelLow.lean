import PEqualNP.Gct.Helpers.BorderedPerm

/-! Helper module, proofs only. A level space of the permanent of dimension `2 * n - 3`: the
matrices supported on the last row and the last column, whose last row sums to zero off the
corner and whose corner is minus the sum of the last column off the corner. On the all ones
matrix plus such a matrix the permanent is `n!`. -/

namespace PEqualNP.Gct.Helpers.LevelLow

open Finset PEqualNP.Gct.Helpers.BorderedPerm

variable {k : ℕ}

/-- The last row off the corner: the free entries `x`, then minus their sum. -/
def rowPart (x : Fin k → ℂ) : Fin (k + 1) → ℂ :=
  Fin.lastCases (-∑ j, x j) x

@[simp]
theorem rowPart_last (x : Fin k → ℂ) : rowPart x (Fin.last k) = -∑ j, x j := by
  simp [rowPart]

@[simp]
theorem rowPart_castSucc (x : Fin k → ℂ) (j : Fin k) : rowPart x (Fin.castSucc j) = x j := by
  simp [rowPart]

theorem sum_rowPart (x : Fin k → ℂ) : ∑ j, rowPart x j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- The matrix with last row `rowPart x`, last column `y`, corner minus the sum of `y`, and
zero elsewhere. -/
def pt (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) : Fin (k + 2) × Fin (k + 2) → ℂ :=
  fun p => Fin.lastCases (Fin.lastCases (-∑ i, y i) (rowPart x) p.2)
    (fun i => Fin.lastCases (y i) (fun _ => 0) p.2) p.1

@[simp]
theorem pt_last_last (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) :
    pt x y (Fin.last (k + 1), Fin.last (k + 1)) = -∑ i, y i := by
  simp [pt]

@[simp]
theorem pt_last_castSucc (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :
    pt x y (Fin.last (k + 1), Fin.castSucc j) = rowPart x j := by
  simp [pt]

@[simp]
theorem pt_castSucc_last (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    pt x y (Fin.castSucc i, Fin.last (k + 1)) = y i := by
  simp [pt]

@[simp]
theorem pt_castSucc_castSucc (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) (i j : Fin (k + 1)) :
    pt x y (Fin.castSucc i, Fin.castSucc j) = 0 := by
  simp [pt]

/-- The permanent of the all ones matrix plus `pt x y` is `(k + 2)!`. -/
theorem eval_one_add_pt (x : Fin k → ℂ) (y : Fin (k + 1) → ℂ) :
    MvPolynomial.eval (fun p => 1 + pt x y p) (PEqualNP.Gct.permPoly ℂ (k + 2)) =
      ((k + 2).factorial : ℂ) := by
  rw [eval_permPoly_bordered]
  have h1 : topLeft (fun p => 1 + pt x y p) = fun _ => 1 := by
    funext p
    simp
  have h2 : ∀ i j, topLeftMinor (fun p => 1 + pt x y p) i j = fun _ => 1 := by
    intro i j
    funext p
    simp
  simp only [h1, h2, eval_permPoly_one, pt_last_last, pt_castSucc_last, pt_last_castSucc]
  have h3 : ∀ i : Fin (k + 1), ∑ j : Fin (k + 1),
      (1 + y i) * (1 + rowPart x j) * (k.factorial : ℂ) =
        (1 + y i) * ((k + 1).factorial : ℂ) := by
    intro i
    rw [← sum_mul, ← mul_sum, sum_add_distrib, sum_rowPart]
    simp [Nat.factorial_succ]
    ring
  simp only [h3]
  rw [← sum_mul, sum_add_distrib]
  simp [Nat.factorial_succ]
  ring

/-- `pt` as a linear map. -/
def ptLin (k : ℕ) :
    ((Fin k → ℂ) × (Fin (k + 1) → ℂ)) →ₗ[ℂ] (Fin (k + 2) × Fin (k + 2) → ℂ) where
  toFun v := pt v.1 v.2
  map_add' v w := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [sum_add_distrib]; ring
      | cast j =>
        induction j using Fin.lastCases with
        | last => simp [sum_add_distrib]; ring
        | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simp
  map_smul' c v := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [mul_sum]
      | cast j =>
        induction j using Fin.lastCases with
        | last => simp [mul_sum]
        | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simp

theorem ptLin_injective (k : ℕ) : Function.Injective (ptLin k) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : pt x y = pt x' y' := h
  have hx : x = x' := by
    funext j
    have := congrFun h' (Fin.last (k + 1), Fin.castSucc (Fin.castSucc j))
    simpa using this
  have hy : y = y' := by
    funext i
    have := congrFun h' (Fin.castSucc i, Fin.last (k + 1))
    simpa using this
  rw [hx, hy]

theorem level_space_lower :
    ∀ n : ℕ, 2 ≤ n → ∃ L : Submodule ℂ (Fin n × Fin n → ℂ),
      (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        (Nat.factorial n : ℂ)) ∧ Module.finrank ℂ L = 2 * n - 3 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine ⟨LinearMap.range (ptLin k), ?_, ?_⟩
  · rintro t ⟨v, rfl⟩
    exact eval_one_add_pt v.1 v.2
  · rw [LinearMap.finrank_range_of_inj (ptLin_injective k), Module.finrank_prod,
      Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega

end PEqualNP.Gct.Helpers.LevelLow
