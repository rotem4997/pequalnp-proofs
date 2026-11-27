import PEqualNP.Gct.Helpers.Rung.Chain
import PEqualNP.Gct.Helpers.Rung.BlockPerm
import PEqualNP.Gct.L023
import PEqualNP.Gct.L024

/-!
# The rung for every large size

The construction of L-gct-057 with a free number `a` of top rows: the permanent of every size
`a + 3 r N - r` restricts to a smooth section of the block sum. Since `a` is free, every large
size is reached, which gives the superquadratic bound for all large `m` (L-gct-074).
-/

namespace PEqualNP.Gct.Rung.AllM

open MvPolynomial PEqualNP.Gct.Rung

/-- The smooth restriction at a general number of top rows. -/
theorem restriction (r : ℕ) (P : Fin (2 * r) → Fin (r + 1) → ℂ) (M N a m : ℕ) (hr2 : 2 ≤ r)
    (hP : RowSpaceGood (2 * r) r (r + 1) P) (hM : RowsBounded (2 * r) r (r + 1) P M)
    (hN1 : 1 ≤ N) (hra : r ≤ a) (hm : m = a + N * (2 * r + r) - r) :
    ∃ (G : MvPolynomial (Fin (N * ((a - M) * (r + 1)))) ℂ)
      (g : Fin m × Fin m → MvPolynomial (Fin (N * ((a - M) * (r + 1)))) ℂ),
      G.IsHomogeneous r ∧
      (∀ x : Fin (N * ((a - M) * (r + 1))) → ℂ,
        (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) ∧
      (∀ i, (g i).totalDegree ≤ 1) ∧
      MvPolynomial.bind₁ g (PEqualNP.Gct.permPoly ℂ m) = G := by
  subst hm
  obtain ⟨L, hL⟩ := goodSubspace (2 * r) r (r + 1) P M hr2 hP hM a N
  obtain ⟨c, g, hc, hg, hperm⟩ := blockPerm N a (2 * r) r hN1 (by omega) hra (by omega)
  let σ := Fin N × Fin a × Fin (2 * r)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let G0 : MvPolynomial (Fin (Fintype.card σ)) ℂ :=
    rename e (C c * blockPoly N a (2 * r) r)
  have hG0 : G0.IsHomogeneous r := by
    have h1 : (C c * blockPoly N a (2 * r) r).IsHomogeneous r :=
      (blockPoly_isHomogeneous N a (2 * r) r).C_mul c
    exact h1.rename_isHomogeneous
  have hgrad : ∀ y : Fin (N * ((a - M) * (r + 1))) → ℂ,
      (∀ i, eval (fun n => ∑ s, L (e.symm n) s * y s) (pderiv i G0) = 0) → y = 0 := by
    intro y hy
    refine hL y fun v => ?_
    have h1 := hy (e v)
    have h2 : pderiv (e v) G0 =
        rename e (C c * pderiv v (blockPoly N a (2 * r) r)) := by
      show pderiv (e v) (rename e (C c * blockPoly N a (2 * r) r)) = _
      rw [pderiv_rename e.injective, pderiv_C_mul]
    rw [h2, eval_rename] at h1
    have h3 : ((fun n => ∑ s, L (e.symm n) s * y s) ∘ e) = fun v => ∑ s, L v s * y s := by
      funext w
      simp
    rw [h3, map_mul, eval_C] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  obtain ⟨M', hM'⟩ := PEqualNP.Gct.L053 (Fintype.card σ) (N * ((a - M) * (r + 1))) r G0
    (fun n s => L (e.symm n) s) hG0 hgrad
  let lin : Fin (Fintype.card σ) → MvPolynomial (Fin (N * ((a - M) * (r + 1)))) ℂ :=
    fun n => ∑ t, C (M' n t) * X t
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin (N * ((a - M) * (r + 1)))) ℂ :=
    (bind₁ lin).comp (rename e)
  refine ⟨bind₁ lin G0, fun p => φ (g p), ?_, hM', ?_, ?_⟩
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

/-- The arithmetic: with `r = 1584 R + 2`, `N ≥ M + 2`, `3 r N ≤ a < 3 r N + 6 r`. -/
theorem arithAll (R M N a r : ℕ) (hr : r = 1584 * R + 2) (hN : M + 2 ≤ N)
    (ha1 : 3 * r * N ≤ a) (ha2 : a < 3 * r * N + 6 * r) :
    2 ≤ N * ((a - M) * (r + 1)) ∧
    11 * (R * (a + N * (2 * r + r) - r) ^ 2) ≤ (r - 1) * (N * ((a - M) * (r + 1)) - 1) := by
  have hr2 : 2 ≤ r := by omega
  have hN2 : 2 ≤ N := by omega
  set p := r * N with hp
  have e1 : 3 * r * N = 3 * p := by rw [hp]; ring
  have e2 : N * (2 * r + r) = 3 * p := by rw [hp]; ring
  rw [e1] at ha1 ha2
  rw [e2]
  have hpN : N ≤ p := by rw [hp]; exact Nat.le_mul_of_pos_left N (by omega)
  have hpr : r ≤ p := by rw [hp]; exact Nat.le_mul_of_pos_right r (by omega)
  have h6 : 6 * r ≤ 3 * p := by rw [hp]; nlinarith
  have hm : a + 3 * p - r ≤ 12 * p := by omega
  have hA : 2 * p ≤ a - M := by omega
  have hd : N * (2 * p * (r + 1)) ≤ N * ((a - M) * (r + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)
  have hpp : p ≤ N * (r + 1) := by rw [hp]; nlinarith
  have hbig : 2 * (p * p) ≤ N * (2 * p * (r + 1)) := by
    calc 2 * (p * p) = 2 * p * p := by ring
      _ ≤ 2 * p * (N * (r + 1)) := Nat.mul_le_mul_left _ hpp
      _ = N * (2 * p * (r + 1)) := by ring
  have hp2 : 2 ≤ p := le_trans hr2 hpr
  have hpp1 : 1 ≤ p * p := by nlinarith
  set d := N * ((a - M) * (r + 1)) with hdd
  have hd1 : p * p ≤ d - 1 := by omega
  refine ⟨by nlinarith, ?_⟩
  have hr1 : r - 1 = 1584 * R + 1 := by omega
  calc 11 * (R * (a + 3 * p - r) ^ 2) ≤ 11 * (R * (12 * p) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 2))
    _ = 1584 * R * (p * p) := by ring
    _ ≤ (r - 1) * (p * p) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (r - 1) * (d - 1) := Nat.mul_le_mul_left _ hd1

/-- The superquadratic bound for all large sizes. -/
theorem allLarge : ∀ R : ℕ, ∃ m0 : ℕ, ∀ m n : ℕ, m0 ≤ m →
    PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → R * m ^ 2 ≤ n := by
  intro R
  obtain ⟨r, hr⟩ : ∃ r, r = 1584 * R + 2 := ⟨_, rfl⟩
  have hr2 : 2 ≤ r := by omega
  obtain ⟨P, hP⟩ := rowSpaceExists avoidance lemmaE (2 * r) r (r + 1) hr2 (by omega)
  obtain ⟨M, hM⟩ := fewRows rowSystem boundedZeros (2 * r) r (r + 1) P hr2 hP
  refine ⟨6 * r * (M + 2), fun m n hm hn => ?_⟩
  set N := (m + r) / (6 * r) with hNdef
  have h6r : 0 < 6 * r := by omega
  have hdiv1 : 6 * r * N ≤ m + r := Nat.mul_div_le _ _
  have hdiv2 : m + r < 6 * r * N + 6 * r := by
    have := Nat.lt_mul_div_succ (m + r) h6r
    rw [← hNdef] at this
    nlinarith
  have hN : M + 2 ≤ N := by
    rw [hNdef, Nat.le_div_iff_mul_le h6r]
    nlinarith
  have e3 : 6 * r * N = 3 * r * N + 3 * r * N := by ring
  have e4 : N * (2 * r + r) = 3 * r * N := by ring
  obtain ⟨a, ha⟩ : ∃ a, a = m + r - 3 * r * N := ⟨_, rfl⟩
  have ha1 : 3 * r * N ≤ a := by omega
  have ha2 : a < 3 * r * N + 6 * r := by omega
  have hrN : r ≤ 3 * r * N := by nlinarith
  have hmeq : m = a + N * (2 * r + r) - r := by omega
  obtain ⟨hd2, hbig⟩ := arithAll R M N a r hr hN ha1 ha2
  obtain ⟨G, g, hhom, hsm, hdeg, hG⟩ :=
    restriction r P M N a m hr2 hP hM (by omega) (by omega) hmeq
  have hGn : PEqualNP.Gct.HasBorderDetExpression G n := by
    rw [← hG]
    exact PEqualNP.Gct.L023 (Fin m × Fin m) _ (PEqualNP.Gct.permPoly ℂ m) g n hdeg hn
  have h := PEqualNP.Gct.L024 _ r n G hd2 hr2 hhom hsm hGn
  rw [← hmeq] at hbig
  omega

end PEqualNP.Gct.Rung.AllM
