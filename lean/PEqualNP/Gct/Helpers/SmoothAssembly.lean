import PEqualNP.Gct.L030

/-!
# Assembly of the smooth form bound

The bound `(r - 1) * (d - 1) ≤ 11 * n` for a smooth form of degree `r` in `d` variables with a
border determinantal expression of size `n`, from three statements taken as hypotheses (the
count of nondegenerate zeros of the polar system of a smooth form, the weighted count for the
polar system of a determinant of affine forms, and the arithmetic that turns the two into the
bound) and the checked persistence of nondegenerate zeros under coefficientwise limits.

The polar system of `f` with covector `a` and vectors `v` is
`Fin.cons f (Fin.cons (∑ j, C (a j) * X j - 1) (fun k => ∑ j, C (v k j) * pderiv j f))`.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- The determinant of an `n × n` matrix of polynomials of total degree at most one has total
degree at most `n`. -/
theorem totalDegree_det_le_size {σ : Type} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hA : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ n := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun τ _ => ?_
  have hprod : (∏ i, A (τ i) i).totalDegree ≤ n := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, (A (τ i) i).totalDegree ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hA _ _
      _ = n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul, totalDegree_neg]; exact hprod

/-- A partial derivative does not raise the total degree. -/
theorem totalDegree_pderiv_le_self {σ : Type} (j : σ) (f : MvPolynomial σ ℂ) :
    (pderiv j f).totalDegree ≤ f.totalDegree := by
  classical
  show (pderiv j f).support.sup (fun s => s.sum fun _ e => e) ≤ f.totalDegree
  refine Finset.sup_le fun s hs => ?_
  have hmem : s + Finsupp.single j 1 ∈ f.support := by
    rw [mem_support_iff] at hs ⊢
    intro h0
    apply hs
    rw [coeff_pderiv, h0, zero_mul]
  have hle := le_totalDegree hmem
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hle
  exact le_trans (Nat.le_add_right _ _) hle

/-- Every component of the polar system of `f` has total degree at most `D + 1` when `f` has
total degree at most `D`. -/
theorem polar_totalDegree_le {h : ℕ} (D : ℕ) (f : MvPolynomial (Fin (h + 2)) ℂ)
    (hf : f.totalDegree ≤ D) (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ)
    (i : Fin (h + 2)) :
    ((Fin.cons f (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j f)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i).totalDegree ≤ D + 1 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simp only [Fin.cons_zero]
    omega
  · simp only [Fin.cons_succ, Fin.cons_zero]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_one]
    refine max_le ?_ (Nat.zero_le _)
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
    omega
  · simp only [Fin.cons_succ]
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pderiv_le_self j f).trans (hf.trans (Nat.le_succ _))

/-- Coefficientwise convergence of `q k` to `G` gives coefficientwise convergence of the polar
systems, component by component. -/
theorem polar_tendsto {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (q : ℕ → MvPolynomial (Fin (h + 2)) ℂ)
    (hq : ∀ s, Filter.Tendsto (fun k => (q k).coeff s) Filter.atTop (nhds (G.coeff s)))
    (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (i : Fin (h + 2))
    (s : Fin (h + 2) →₀ ℕ) :
    Filter.Tendsto (fun m => ((Fin.cons (q m) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (q m))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i).coeff s) Filter.atTop
      (nhds (((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i).coeff s)) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simpa only [Fin.cons_zero] using hq s
  · simp only [Fin.cons_succ, Fin.cons_zero]
    exact tendsto_const_nhds
  · simp only [Fin.cons_succ, coeff_sum, coeff_C_mul, coeff_pderiv]
    refine tendsto_finsetSum _ fun j _ => ?_
    exact ((hq _).mul_const _).const_mul _

/-- The smooth form bound, assembled from the statements of the three lemmas it rests on and
the checked persistence of nondegenerate zeros. -/
theorem smooth_bound_of
    (h34 : ∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (r - 1) ^ (h + 1) ≤ S.card ∧ ∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0)
    (hC : ∀ (h n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)), (∀ i j, (A i j).totalDegree ≤ 1) → ∀ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) → ∀ p q : ℕ, S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n))
    (hD : ∀ (h n r K : ℕ), 2 ≤ r → (r - 1) ^ (h + 1) ≤ K → (∀ p q : ℕ, K * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) → (r - 1) * (h + 1) ≤ 11 * n) :
    ∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n := by
  intro d r n G hd hr hhom hsm hb
  obtain ⟨h, rfl⟩ : ∃ h, d = h + 2 := ⟨d - 2, by omega⟩
  obtain ⟨a, v, S, hcard, hS⟩ := h34 h r G hr hhom hsm
  obtain ⟨q, hq, hconv⟩ := hb
  choose A hA hdet using hq
  obtain ⟨K, hK⟩ := PEqualNP.Gct.L030 (h + 2) (n + 1)
    (Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ)
    (fun m => (Fin.cons (q m) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (q m))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ))
    (fun m i => polar_totalDegree_le n (q m)
      (by rw [← hdet m]; exact totalDegree_det_le_size _ (hA m)) a v i)
    (fun i s => polar_tendsto G q hconv a v i s) S hS
  obtain ⟨T, hTcard, hT⟩ := hK K le_rfl
  have hcount := hC h n (A K) (hA K) a v T (by rw [hdet K]; exact hT)
  have hfin : (r - 1) * (h + 1) ≤ 11 * n :=
    hD h n r T.card hr (by rw [hTcard]; exact hcard) hcount
  have e : h + 2 - 1 = h + 1 := by omega
  rw [e]
  exact hfin

end PEqualNP.Gct.Helpers
