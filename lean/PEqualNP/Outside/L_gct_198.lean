import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

noncomputable section

/-- The first row is arbitrary with sum zero. The other rows use two pairs of columns,
  with the two nontrivial cube roots in opposite orders on the pairs. -/
private def entries (z : ℂ) (x : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  ![![x 0, x 1, x 2, x 3, x 4, -(x 0 + x 1 + x 2 + x 3 + x 4)],
    ![x 5, -x 5, x 6, -x 6, 0, 0],
    ![z * x 5, -(z * x 5), z ^ 2 * x 6, -(z ^ 2 * x 6), 0, 0],
    ![z ^ 2 * x 5, -(z ^ 2 * x 5), z * x 6, -(z * x 6), 0, 0]] p.1 p.2

private def family (z : ℂ) : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := entries z
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries, mul_add] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring

private theorem family_injective (z : ℂ) : Function.Injective (family z) := by
  intro x y h
  let positions : Fin 7 → Fin 4 × Fin 6 :=
    ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2)]
  funext k
  have hk := congrFun h (positions k)
  fin_cases k <;> exact hk

private theorem row_sum (z : ℂ) (x : Fin 7 → ℂ) (i : Fin 4) :
    ∑ j, entries z x (i, j) = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_six, entries]

private theorem quadratic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then entries z x (a, j) * entries z x (b, l) else 0) = 0 := by
  simp (config := { decide := true }) [Fin.sum_univ_six, Fin.sum_univ_four, entries]
  grobner

private theorem cubic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
        entries z x (a, j) * entries z x (b, l) * entries z x (c, m) else 0) = 0 := by
  simp (config := { decide := true }) [Fin.sum_univ_six, Fin.sum_univ_four, entries]
  grobner

private theorem quartic (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    (∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        entries z x (0, j) * entries z x (1, l) *
          entries z x (2, m) * entries z x (3, n)) = 0 := by
  simp (config := { decide := true }) [Fin.sum_univ_six, entries]
  grobner

theorem L_gct_198 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧
      (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
        if a < b then t (a, j) * t (b, l) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
          t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧
      (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ Module.finrank ℂ L = 7 := by
  obtain ⟨z, hprim⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ 3
  have hz : 1 + z + z ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hprim.geom_sum_eq_zero (by decide)
  refine ⟨LinearMap.range (family z), ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact ⟨row_sum z x, quadratic z hz x, cubic z hz x, quartic z hz x⟩
  · rw [LinearMap.finrank_range_of_inj (family_injective z), Module.finrank_fin_fun]

end

end PEqualNP.Outside
