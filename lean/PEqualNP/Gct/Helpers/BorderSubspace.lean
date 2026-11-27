import PEqualNP.Defs
import PEqualNP.Gct.L003
import PEqualNP.Gct.Helpers.SubspaceReduction
import PEqualNP.Gct.Helpers.MethodCeiling
import PEqualNP.Gct.Helpers.BorderSubspaceRoots

/-! Helpers for L-gct-069 (border subspace reduction). Let `q k → perm_m` coefficientwise, each
`q k` a determinant of an `n × n` matrix of affine forms, and `y` a zero of `perm_m`.
* On the line `y + s w` through a point where `perm_m` is nonzero, root persistence gives zeros
  `y k = y + s k • w` of `q k` tending to `y`.
* At each `y k` the argument of L-gct-035 gives a subspace of dimension at least `m ^ 2 - n` on
  which `q k (y k + ·)` vanishes; pick an orthonormal `(m ^ 2 - n)`-tuple in it.
* Orthonormal tuples form a compact set, so a subsequence converges to an orthonormal tuple,
  whose span `L` has dimension `m ^ 2 - n` and satisfies `perm_m (y + t) = 0` for `t ∈ L`, since
  evaluation is jointly continuous in (coefficients on a fixed finite support, point). -/

namespace PEqualNP.Gct.Helpers.BorderSubspace

open MvPolynomial Filter Topology Finset PEqualNP.Gct.Helpers.SubspaceReduction

section Zero

/-- The argument of L-gct-035 at any zero `z` of a polynomial with a determinantal expression
of size `n`: a subspace of dimension at least `m ^ 2 - n` on which `q (z + ·)` vanishes. -/
theorem exists_zero_subspace {m : ℕ} (n : ℕ) (q : MvPolynomial (Fin m × Fin m) ℂ)
    (hA : PEqualNP.Gct.HasDetExpression q n) (z : Fin m × Fin m → ℂ) (hz : eval z q = 0) :
    ∃ L : Submodule ℂ (Fin m × Fin m → ℂ), m ^ 2 ≤ Module.finrank ℂ L + n ∧
      ∀ t ∈ L, eval (z + t) q = 0 := by
  obtain ⟨A, hdeg, hdet⟩ := hA
  have heval : ∀ x : Fin m × Fin m → ℂ, eval x q = (A.map (eval x)).det := by
    intro x
    rw [← hdet, RingHom.map_det]
    rfl
  have h0 : (A.map (eval z)).det = 0 := by rw [← heval]; exact hz
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  let c : Fin n → Fin n → (Fin m × Fin m) → ℂ :=
    fun i j v => (A i j).coeff (Finsupp.single v 1)
  let Φ : (Fin m × Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi (fun i => ∑ j, ∑ v, (c i j v * u j) • LinearMap.proj v)
  have hΦ : ∀ t i, Φ t i = ∑ j, (∑ v, c i j v * t v) * u j := by
    intro t i
    simp only [Φ, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hzero : ∀ t ∈ LinearMap.ker Φ, eval (z + t) q = 0 := by
    intro t ht
    rw [heval]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨u, hu0, ?_⟩
    funext i
    have hti : Φ t i = 0 := by rw [LinearMap.mem_ker.mp ht]; rfl
    have hui : (A.map (eval z)).mulVec u i = 0 := by rw [hu]; rfl
    rw [hΦ] at hti
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hui ⊢
    rw [Pi.zero_apply]
    simp only [eval_add_of_totalDegree_le_one _ (hdeg _ _), add_mul, sum_add_distrib]
    rw [hui, zero_add]
    exact hti
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hdom : Module.finrank ℂ (Fin m × Fin m → ℂ) = m ^ 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, sq]
  have hran : Module.finrank ℂ (LinearMap.range Φ) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fin_fun] at this
  exact ⟨LinearMap.ker Φ, by omega, hzero⟩

end Zero

section Line

variable {σ : Type}

/-- The restriction of `q` to the line `s ↦ y + s • w`, as a univariate polynomial. -/
noncomputable def linePoly (y w : σ → ℂ) (q : MvPolynomial σ ℂ) : Polynomial ℂ :=
  aeval (fun v => Polynomial.C (y v) + Polynomial.C (w v) * Polynomial.X) q

theorem eval_linePoly (y w : σ → ℂ) (q : MvPolynomial σ ℂ) (s : ℂ) :
    (linePoly y w q).eval s = eval (y + s • w) q := by
  unfold linePoly
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, aeval_X, eval_X, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- A polynomial supported in `S` is the sum of its monomials over `S`. -/
theorem eq_sum_monomial (S : Finset (σ →₀ ℕ)) (q : MvPolynomial σ ℂ)
    (hS : ∀ s, s ∉ S → q.coeff s = 0) : q = ∑ s ∈ S, q.coeff s • monomial s (1 : ℂ) := by
  have hsub : q.support ⊆ S := fun s hs => by
    by_contra h
    exact (mem_support_iff.mp hs) (hS s h)
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub (fun s _ hs => by rw [notMem_support_iff.mp hs, monomial_zero])]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem linePoly_eq_sum (S : Finset (σ →₀ ℕ)) (q : MvPolynomial σ ℂ)
    (hS : ∀ s, s ∉ S → q.coeff s = 0) (y w : σ → ℂ) :
    linePoly y w q = ∑ s ∈ S, q.coeff s • linePoly y w (monomial s 1) := by
  conv_lhs => rw [eq_sum_monomial S q hS]
  simp only [linePoly, map_sum, map_smul]

/-- Coefficients converging on a fixed finite support and points converging: evaluations
converge. -/
theorem tendsto_eval (S : Finset (σ →₀ ℕ))
    (q : ℕ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ)
    (hq : ∀ k s, s ∉ S → (q k).coeff s = 0) (hp : ∀ s, s ∉ S → p.coeff s = 0)
    (hlim : ∀ s, Tendsto (fun k => (q k).coeff s) atTop (𝓝 (p.coeff s)))
    (x : ℕ → σ → ℂ) (y : σ → ℂ) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => eval (x k) (q k)) atTop (𝓝 (eval y p)) := by
  have e : ∀ (r : MvPolynomial σ ℂ), (∀ s, s ∉ S → r.coeff s = 0) → ∀ z : σ → ℂ,
      eval z r = ∑ s ∈ S, r.coeff s * eval z (monomial s 1) := by
    intro r hr z
    conv_lhs => rw [eq_sum_monomial S r hr]
    simp only [map_sum, smul_eval]
  have h1 : (fun k => eval (x k) (q k)) =
      fun k => ∑ s ∈ S, (q k).coeff s * eval (x k) (monomial s 1) :=
    funext fun k => e (q k) (hq k) (x k)
  rw [h1, e p hp]
  exact tendsto_finsetSum _ fun s _ =>
    (hlim s).mul (((continuous_eval _).tendsto y).comp hx)

end Line

section Compact

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem isCompact_orthonormal (d : ℕ) : IsCompact {b : Fin d → E | Orthonormal ℂ b} := by
  classical
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {b : Fin d → E | Orthonormal ℂ b} =
        ⋂ i, ⋂ j, {b : Fin d → E | inner ℂ (b i) (b j) = if i = j then (1 : ℂ) else 0} := by
      ext b
      simp [orthonormal_iff_ite]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin d → E)) (r := 1)).subset ?_
    intro b hb
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hb.1 i).le

/-- A subspace of dimension at least `d` contains an orthonormal `d`-tuple, read through a
linear equivalence with an inner product space. -/
theorem exists_orthonormal_tuple {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : E ≃ₗ[ℂ] V) (L : Submodule ℂ V) (d : ℕ) (hd : d ≤ Module.finrank ℂ L) :
    ∃ b : Fin d → E, Orthonormal ℂ b ∧ ∀ j, e (b j) ∈ L := by
  set L' : Submodule ℂ E := L.map (e.symm : V →ₗ[ℂ] E) with hL'
  have hr : Module.finrank ℂ L' = Module.finrank ℂ L := LinearEquiv.finrank_map_eq e.symm L
  have hd' : d ≤ Module.finrank ℂ L' := hr ▸ hd
  set ob := stdOrthonormalBasis ℂ L'
  refine ⟨fun j => (ob (Fin.castLE hd' j) : E), ?_, ?_⟩
  · have h1 := (ob.orthonormal.comp _ (Fin.castLE_injective hd')).comp_linearIsometry
      L'.subtypeₗᵢ
    exact h1
  · have hmem : ∀ x ∈ L', e x ∈ L := fun x hx => by
      rw [hL', Submodule.mem_map_equiv] at hx
      simpa using hx
    exact fun j => hmem _ (ob (Fin.castLE hd' j)).2

end Compact

section Main

/-- L-gct-069, the border form of L-gct-035. -/
theorem border_subspace (m n k : ℕ) (y : Fin m × Fin m → ℂ)
    (hy : eval y (PEqualNP.Gct.permPoly ℂ m) = 0)
    (hL : ∀ L : Submodule ℂ (Fin m × Fin m → ℂ),
      (∀ t ∈ L, eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → Module.finrank ℂ L ≤ k)
    (hB : PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n) :
    m ^ 2 ≤ k + n := by
  classical
  by_cases hmn : m ^ 2 ≤ n
  · omega
  obtain ⟨q, hq, hlim⟩ := hB
  set p := PEqualNP.Gct.permPoly ℂ m with hpdef
  -- a finite support for all the polynomials involved
  have hfin : {s : Fin m × Fin m →₀ ℕ |
      s ≤ Finsupp.equivFunOnFinite.symm (fun _ => n)}.Finite := Set.finite_Iic _
  set S := hfin.toFinset with hS
  have hqS : ∀ a s, s ∉ S → (q a).coeff s = 0 := by
    intro a s hs
    by_contra hne
    apply hs
    have hmem : s ∈ (q a).support := mem_support_iff.mpr hne
    have hdeg := (le_totalDegree hmem).trans (PEqualNP.Gct.L003 _ ℂ (q a) n (hq a))
    rw [hS, Set.Finite.mem_toFinset]
    intro i
    by_cases hi : i ∈ s.support
    · exact (Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) hi).trans hdeg
    · simp [Finsupp.notMem_support_iff.mp hi]
  have hpS : ∀ s, s ∉ S → p.coeff s = 0 := fun s hs =>
    tendsto_nhds_unique (hlim s) (by simp [hqS _ s hs])
  -- a point where the permanent is `1`
  set z1 : Fin m × Fin m → ℂ := fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2 with hz1def
  have hz1 : eval z1 p = 1 := by
    rw [hpdef, PEqualNP.Gct.MethodCeiling.eval_permPoly]
    have : (Matrix.of fun i j => z1 (i, j)) = 1 := by
      ext i j
      rfl
    rw [this, Matrix.permanent_one]
  set w := z1 - y with hw
  -- zeros of `q a` tending to `y`, on the line through `y` and `z1`
  set g := linePoly y w p with hg
  have hg0 : g.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hg, eval_linePoly]
    simpa using hy
  have hgne : g ≠ 0 := by
    intro h
    have h1 := eval_linePoly y w p 1
    rw [← hg, h, one_smul, hw, add_sub_cancel, hz1] at h1
    simp at h1
  set N := S.sup fun s => (linePoly y w (monomial s (1 : ℂ))).natDegree with hN
  have hdegN : ∀ a, (linePoly y w (q a)).natDegree ≤ N := by
    intro a
    rw [linePoly_eq_sum S (q a) (hqS a) y w]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    exact (Polynomial.natDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun s => (linePoly y w (monomial s (1 : ℂ))).natDegree) hs)
  have hcoef : ∀ i, Tendsto (fun a => (linePoly y w (q a)).coeff i) atTop (𝓝 (g.coeff i)) := by
    intro i
    have e : ∀ r : MvPolynomial (Fin m × Fin m) ℂ, (∀ s, s ∉ S → r.coeff s = 0) →
        (linePoly y w r).coeff i =
          ∑ s ∈ S, r.coeff s * (linePoly y w (monomial s 1)).coeff i := by
      intro r hr
      rw [linePoly_eq_sum S r hr y w, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_smul, smul_eq_mul]
    simp only [hg, e p hpS, e _ (hqS _)]
    exact tendsto_finsetSum _ fun s _ => (hlim s).mul_const _
  obtain ⟨sk, hsk, hroot⟩ := exists_roots_tendsto_zero (fun a => linePoly y w (q a)) g N hdegN
    hcoef hg0 hgne
  set yk : ℕ → Fin m × Fin m → ℂ := fun a => y + sk a • w with hykdef
  have hyk : Tendsto yk atTop (𝓝 y) := by
    have : Tendsto (fun a => y + sk a • w) atTop (𝓝 (y + (0 : ℂ) • w)) :=
      tendsto_const_nhds.add (hsk.smul_const w)
    simpa using this
  obtain ⟨K, hK⟩ := eventually_atTop.mp hroot
  have hzk : ∀ a, eval (yk (K + a)) (q (K + a)) = 0 := by
    intro a
    rw [hykdef, ← eval_linePoly]
    exact hK (K + a) (Nat.le_add_right K a)
  -- orthonormal tuples in the subspaces at the zeros
  set d := m ^ 2 - n with hd
  let E := EuclideanSpace ℂ (Fin m × Fin m)
  let e : E ≃L[ℂ] (Fin m × Fin m → ℂ) := EuclideanSpace.equiv (Fin m × Fin m) ℂ
  have hdata : ∀ a, ∃ b : Fin d → E, Orthonormal ℂ b ∧
      ∀ c : Fin d → ℂ, eval (yk (K + a) + e (∑ j, c j • b j)) (q (K + a)) = 0 := by
    intro a
    obtain ⟨La, hdim, hvan⟩ := exists_zero_subspace n (q (K + a)) (hq _) _ (hzk a)
    obtain ⟨b, hbo, hbm⟩ := exists_orthonormal_tuple e.toLinearEquiv La d (by omega)
    refine ⟨b, hbo, fun c => hvan _ ?_⟩
    rw [map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hbm j)
  choose B hBo hBz using hdata
  obtain ⟨b, hb, φ, hφ, hlimB⟩ := (isCompact_orthonormal (E := E) d).tendsto_subseq hBo
  -- the limit subspace
  set L : Submodule ℂ (Fin m × Fin m → ℂ) := Submodule.span ℂ (Set.range fun j => e (b j))
    with hLdef
  have hli : LinearIndependent ℂ (fun j => e (b j)) := by
    have := hb.linearIndependent.map' (e.toLinearEquiv : E →ₗ[ℂ] (Fin m × Fin m → ℂ))
      e.toLinearEquiv.ker
    exact this
  have hrank : Module.finrank ℂ L = d := by
    rw [hLdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hvanish : ∀ t ∈ L, eval (y + t) p = 0 := by
    intro t ht
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
    have hKφ : Tendsto (fun a => K + φ a) atTop atTop :=
      tendsto_atTop_mono (fun a => Nat.le_add_left (φ a) K) hφ.tendsto_atTop
    have hpts : Tendsto (fun a => yk (K + φ a) + e (∑ j, c j • B (φ a) j)) atTop
        (𝓝 (y + e (∑ j, c j • b j))) := by
      refine (hyk.comp hKφ).add ((e.continuous.tendsto _).comp ?_)
      exact tendsto_finsetSum _ fun j _ =>
        ((continuous_apply j).tendsto _ |>.comp hlimB).const_smul (c j)
    have hev := tendsto_eval S (fun a => q (K + φ a)) p (fun a => hqS _) hpS
      (fun s => (hlim s).comp hKφ) _ _ hpts
    have hz : (fun a => eval (yk (K + φ a) + e (∑ j, c j • B (φ a) j)) (q (K + φ a))) =
        fun _ => 0 := funext fun a => hBz (φ a) c
    rw [hz] at hev
    have ht' : e (∑ j, c j • b j) = t := by
      rw [← hc, map_sum]
      simp only [map_smul]
    rw [← ht']
    exact tendsto_nhds_unique hev tendsto_const_nhds
  have := hL L hvanish
  omega

end Main

end PEqualNP.Gct.Helpers.BorderSubspace
