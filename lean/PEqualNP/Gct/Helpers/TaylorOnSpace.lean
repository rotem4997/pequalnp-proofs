import PEqualNP.Defs
import PEqualNP.Gct.Helpers.MRPlusOne

/-! Helper module, proofs only. If a polynomial `p` vanishes on an affine subspace `y + L`, then
every iterated directional derivative of `p` along directions of `L` vanishes on `y + L`, and
therefore the `k`-th differential of `p` at `y`, written as a sum over index tuples of iterated
partial derivatives, vanishes on `L`. Valid for any polynomial over `ℂ` in finitely many
variables. -/

namespace PEqualNP.Gct.Helpers.TaylorSp

open MvPolynomial PEqualNP.Gct.Helpers

variable {σ : Type} [Fintype σ]

/-- The directional derivative of `p` along `t`, as a polynomial. -/
noncomputable def dirD (t : σ → ℂ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ a, C (t a) * pderiv a p

theorem eval_dirD (x t : σ → ℂ) (p : MvPolynomial σ ℂ) :
    eval x (dirD t p) = ∑ a, t a * eval x (pderiv a p) := by
  simp [dirD]

/-- If `p` vanishes on `y + L` and `t ∈ L`, the directional derivative of `p` along `t`
vanishes on `y + L`. -/
theorem dirD_vanish (p : MvPolynomial σ ℂ) (y : σ → ℂ) (L : Submodule ℂ (σ → ℂ))
    (h : ∀ u ∈ L, eval (y + u) p = 0) (t : σ → ℂ) (ht : t ∈ L) :
    ∀ u ∈ L, eval (y + u) (dirD t p) = 0 := by
  classical
  intro u hu
  have hin : HasDerivAt (fun s : ℂ => (y + u) + s • t) t 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const t).const_add (y + u)
    simpa using this
  have hout : HasFDerivAt (fun z : σ → ℂ => eval z p) (gradCLMg p (y + u)) (y + u) :=
    (hasStrictFDerivAt_eval_gen p (y + u)).hasFDerivAt
  have hg : HasDerivAt (fun s : ℂ => eval ((y + u) + s • t) p) (gradCLMg p (y + u) t) 0 :=
    hout.comp_hasDerivAt_of_eq (0 : ℂ) hin (by simp)
  have hz : (fun s : ℂ => eval ((y + u) + s • t) p) = fun _ => (0 : ℂ) := by
    funext s
    rw [add_assoc]
    exact h _ (L.add_mem hu (L.smul_mem s ht))
  rw [hz] at hg
  have h0 : gradCLMg p (y + u) t = 0 := hg.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  rw [eval_dirD, ← gradCLMg_apply]
  exact h0

/-- Iterated form: directional derivatives along a list of directions of `L`. -/
theorem foldr_dirD_vanish (p : MvPolynomial σ ℂ) (y : σ → ℂ) (L : Submodule ℂ (σ → ℂ))
    (h : ∀ u ∈ L, eval (y + u) p = 0) (l : List (σ → ℂ)) (hl : ∀ t ∈ l, t ∈ L) :
    ∀ u ∈ L, eval (y + u) (l.foldr dirD p) = 0 := by
  induction l with
  | nil => simpa using h
  | cons t l ih =>
    rw [List.foldr_cons]
    exact dirD_vanish _ y L (ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))) t
      (hl t List.mem_cons_self)

/-- The iterated directional derivative, expanded over index tuples. -/
theorem foldr_dirD_expand (p : MvPolynomial σ ℂ) (k : ℕ) (t : Fin k → σ → ℂ) :
    (List.ofFn t).foldr dirD p =
      ∑ a : Fin k → σ, C (∏ j, t j (a j)) * (List.ofFn a).foldr (fun i q => pderiv i q) p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.foldr_cons, ih (fun i => t i.succ)]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => σ)).sum_comp, Fintype.sum_prod_type]
    simp only [dirD, map_sum]
    refine Finset.sum_congr rfl fun a0 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hc : (Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (a0, b) = Fin.cons a0 b := rfl
    rw [hc, Fin.prod_univ_succ, List.ofFn_succ, List.foldr_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, Derivation.leibniz, pderiv_C,
      smul_eq_mul, map_mul]
    ring

/-- If `p` vanishes on `y + L`, the `k`-th differential of `p` at `y` vanishes on `L`. -/
theorem differential_vanish (p : MvPolynomial σ ℂ) (y : σ → ℂ) (L : Submodule ℂ (σ → ℂ))
    (h : ∀ u ∈ L, eval (y + u) p = 0) (k : ℕ) (t : Fin k → σ → ℂ) (ht : ∀ j, t j ∈ L) :
    ∑ a : Fin k → σ,
      eval y ((List.ofFn a).foldr (fun i q => pderiv i q) p) * ∏ j, t j (a j) = 0 := by
  have h1 := foldr_dirD_vanish p y L h (List.ofFn t)
    (fun s hs => by obtain ⟨j, rfl⟩ := (List.mem_ofFn' t s).1 hs; exact ht j) 0 L.zero_mem
  rw [add_zero, foldr_dirD_expand, map_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, eval_C, mul_comm]

end PEqualNP.Gct.Helpers.TaylorSp
