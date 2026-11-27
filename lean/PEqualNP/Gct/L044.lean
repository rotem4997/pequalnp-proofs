import PEqualNP.Defs
import PEqualNP.Gct.Helpers.MethodCeiling

/-! L-gct-044 (ceiling of the subspace method): every zero `y` of `perm_m` lies on an affine
space `y + L` of zeros with `dim L ≥ 2m - 2`. If a row of `y` vanishes, `L` is the space of
matrices vanishing on that row. Otherwise row `i ≠ 0` of `t ∈ L` is a multiple of row `i` of
`y`, and row `0` of `t` lies in the kernel of `v ↦ perm (y with row 0 replaced by v)`. -/

open PEqualNP.Gct.MethodCeiling in
theorem PEqualNP.Gct.L044 :
    ∀ (m : ℕ) (y : Fin m × Fin m → ℂ),
      MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 →
        ∃ L : Submodule ℂ (Fin m × Fin m → ℂ), 2 * m - 2 ≤ Module.finrank ℂ L ∧
          ∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0 := by
  intro m y hy
  by_cases hz : ∃ r, ∀ j, y (r, j) = 0
  · obtain ⟨r, hr⟩ := hz
    let S : Fin m → Submodule ℂ (Fin m → ℂ) := fun i => if i = r then ⊥ else ⊤
    have hSr : S r = ⊥ := by simp [S]
    have hSi : ∀ i, i ≠ r → S i = ⊤ := fun i hi => by simp [S, hi]
    refine ⟨LinearMap.range (rowEmb S), ?_, ?_⟩
    · rw [finrank_range_rowEmb]
      have h1 := sum_lower (fun i => Module.finrank ℂ (S i)) r m 0
        (fun i hi => by rw [hSi i hi]; simp) (Nat.zero_le _)
      have h2 : 2 * m - 2 ≤ (m - 1) * m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m <;> simp
        · have := Nat.mul_le_mul_left (m - 1) h
          omega
      simp only [add_zero] at h1
      omega
    · rintro t ⟨x, rfl⟩
      rw [eval_permPoly]
      apply perm_eq_zero_of_row _ r
      intro j
      have hx : (x r : Fin m → ℂ) = 0 := by
        have h : ∀ v, v ∈ S r → v = 0 := by
          rw [hSr]
          simp
        exact h _ (x r).2
      simp [rowEmb_apply, hr, hx]
  · push Not at hz
    rcases m with _ | n
    · refine ⟨⊥, by simp, ?_⟩
      intro t ht
      rw [Submodule.mem_bot] at ht
      subst ht
      simpa using hy
    · set Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j => y (i, j) with hY
      let S : Fin (n + 1) → Submodule ℂ (Fin (n + 1) → ℂ) := fun i =>
        if i = 0 then LinearMap.ker (rowFun Y 0) else ℂ ∙ (fun j => y (i, j))
      have hS0 : S 0 = LinearMap.ker (rowFun Y 0) := by simp [S]
      have hSi : ∀ i, i ≠ 0 → S i = ℂ ∙ (fun j => y (i, j)) := fun i hi => by simp [S, hi]
      refine ⟨LinearMap.range (rowEmb S), ?_, ?_⟩
      · rw [finrank_range_rowEmb]
        have hk : n ≤ Module.finrank ℂ (LinearMap.ker (rowFun Y 0)) := by
          have h1 := LinearMap.finrank_range_add_finrank_ker (rowFun Y 0)
          have h2 : Module.finrank ℂ (LinearMap.range (rowFun Y 0)) ≤ 1 := by
            simpa using Submodule.finrank_le (LinearMap.range (rowFun Y 0))
          simp only [Module.finrank_fin_fun] at h1
          omega
        have h1 := sum_lower (fun i => Module.finrank ℂ (S i)) 0 1 n
          (fun i hi => by
            rw [hSi i hi, finrank_span_singleton]
            obtain ⟨j, hj⟩ := hz i
            intro h
            exact hj (congrFun h j))
          (by rw [hS0]; exact hk)
        simp only [add_tsub_cancel_right, mul_one] at h1
        omega
      · rintro t ⟨x, rfl⟩
        rw [eval_permPoly]
        have hc : ∀ i, ∃ a : ℂ, i ≠ 0 → a • (fun j => y (i, j)) = (x i : Fin (n + 1) → ℂ) := by
          intro i
          by_cases hi : i = 0
          · exact ⟨0, fun h => (h hi).elim⟩
          · have h : ∀ v, v ∈ S i → ∃ a : ℂ, a • (fun j => y (i, j)) = v := by
              rw [hSi i hi]
              intro v hv
              exact Submodule.mem_span_singleton.1 hv
            obtain ⟨a, ha⟩ := h _ (x i).2
            exact ⟨a, fun _ => ha⟩
        choose c hc using hc
        have hker : rowFun Y 0 (x 0) = 0 := by
          have h : ∀ v, v ∈ S 0 → rowFun Y 0 v = 0 := by
            rw [hS0]
            intro v hv
            exact hv
          exact h _ (x 0).2
        let d : Fin (n + 1) → ℂ := fun i => if i = 0 then 1 else 1 + c i
        have hM : (Matrix.of fun i j => (y + rowEmb S x) (i, j)) =
            Matrix.of fun i j => d i * (Y.updateRow 0 (Y 0 + x 0)) i j := by
          ext i j
          by_cases hi : i = 0
          · subst hi
            simp [d, rowEmb_apply, Y]
          · have := congrFun (hc i hi) j
            simp only [Pi.smul_apply, smul_eq_mul] at this
            simp only [Matrix.of_apply, Pi.add_apply, rowEmb_apply, d, hi, ite_false,
              Matrix.updateRow_ne hi, ← this, Y]
            ring
        have hY0 : Y.permanent = 0 := by
          rw [hY, ← eval_permPoly]
          exact hy
        rw [hM, perm_rowScale, ← rowFun_apply, map_add, hker, rowFun_apply,
          Matrix.updateRow_eq_self, hY0]
        simp
