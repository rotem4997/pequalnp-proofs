import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Gct.Helpers.TaylorOnSpace
import PEqualNP.Gct.Helpers.OrderConditions
import PEqualNP.Gct.Helpers.SigmaSums
import PEqualNP.Gct.Helpers.SigmaThird

/-! Helper for L-gct-062, the reduction at the point of Mignon and Ressayre. For a direction `t`
of `L` that vanishes on the first row and column and has vanishing row and column sums, the
second and third order Taylor terms of the permanent along `t` are nonzero multiples of the power
sums of `t`; these directions form a subspace of codimension at most `4 n` in `L`, mapped
injectively to `n × n` matrices by restriction to the block. -/

namespace PEqualNP.Gct.SigmaRed

open Finset MvPolynomial PEqualNP.Gct.Helpers

/-- The second partial derivatives of the permanent at the point of Mignon and Ressayre, at two
positions off the first row and column. -/
theorem second_perm_block (p : ℕ) (a b : Fin (p + 2) × Fin (p + 2))
    (ha1 : a.1 ≠ 0) (ha2 : a.2 ≠ 0) (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) :
    eval (mrPoint p) (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ (p + 2)))) =
      if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then
        (p.factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 1).factorial : ℂ) else 0 := by
  rw [hess_perm_entry]
  unfold hessEntry
  have h4 : a.1 ≠ 0 ∧ b.1 ≠ 0 ∧ a.2 ≠ 0 ∧ b.2 ≠ 0 := ⟨ha1, hb1, ha2, hb2⟩
  by_cases h : a.1 ≠ b.1 ∧ a.2 ≠ b.2
  · simp [h, h4]
  · have h' : ¬ (a.2 ≠ b.2 ∧ a.1 ≠ b.1) := fun e => h ⟨e.2, e.1⟩
    simp [h, h']

theorem c2_ne (p : ℕ) (hp : 1 ≤ p) :
    (p.factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 1).factorial : ℂ) ≠ 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  intro h
  have h' : ((q + 1).factorial : ℂ) = (((q + 1 + 2) * q.factorial : ℕ) : ℂ) := by
    push_cast; simpa [sub_eq_zero] using h
  have := Nat.cast_injective h'
  rw [Nat.factorial_succ] at this
  have hq := Nat.factorial_pos q
  nlinarith

theorem c3_ne (p : ℕ) (hp : 1 ≤ p) :
    ((p - 1).factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 2).factorial : ℂ) ≠ 0 := by
  intro h
  have h' : ((p - 1).factorial : ℂ) = (((p + 2) * (p - 2).factorial : ℕ) : ℂ) := by
    push_cast; simpa [sub_eq_zero] using h
  have := Nat.cast_injective h'
  rcases Nat.lt_or_ge p 2 with h2 | h2
  · obtain rfl : p = 1 := by omega
    simp at this
  · obtain ⟨r, rfl⟩ : ∃ r, p = r + 2 := ⟨p - 2, by omega⟩
    simp only [show r + 2 - 1 = r + 1 by omega, show r + 2 - 2 = r by omega,
      Nat.factorial_succ] at this
    have hr := Nat.factorial_pos r
    nlinarith

/-- A function on `Fin (n+1) × Fin (n+1)` vanishing on the first row and column sums to the sum of
its block. -/
theorem sum_block {n : ℕ} (f : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hz : ∀ a : Fin (n + 1) × Fin (n + 1), a.1 = 0 ∨ a.2 = 0 → f a = 0) :
    ∑ q : Fin n × Fin n, f (q.1.succ, q.2.succ) = ∑ a, f a := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_succ]
  rw [sum_eq_zero (fun j _ => hz (0, j) (Or.inl rfl)), zero_add]
  refine sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succ, hz (i.succ, 0) (Or.inr rfl), zero_add]

/-- The border and sum conditions, as one linear map to a space of dimension `4 n`. -/
noncomputable def condMap (n : ℕ) :
    (Fin (n + 1) × Fin (n + 1) → ℂ) →ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ)) where
  toFun t := ((fun i => t (0, i.succ), fun i => t (i.succ, 0)),
    (fun i => ∑ j, t (i.succ, j), fun i => ∑ r, t (r, i.castSucc)))
  map_add' u v := by
    ext i <;> simp [sum_add_distrib]
  map_smul' c u := by
    ext i <;> simp [mul_sum]

theorem condMap_ker {p : ℕ} (t : Fin (p + 2) × Fin (p + 2) → ℂ) (h : condMap (p + 1) t = 0) :
    (∀ a : Fin (p + 2) × Fin (p + 2), a.1 = 0 ∨ a.2 = 0 → t a = 0) ∧
      (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0) := by
  have h1 : ∀ i : Fin (p + 1), t (0, i.succ) = 0 := fun i => congrFun (congrArg (·.1.1) h) i
  have h2 : ∀ i : Fin (p + 1), t (i.succ, 0) = 0 := fun i => congrFun (congrArg (·.1.2) h) i
  have h3 : ∀ i : Fin (p + 1), ∑ j, t (i.succ, j) = 0 := fun i => congrFun (congrArg (·.2.1) h) i
  have h4 : ∀ i : Fin (p + 1), ∑ r, t (r, i.castSucc) = 0 :=
    fun i => congrFun (congrArg (·.2.2) h) i
  have h00 : t (0, 0) = 0 := by
    have := h4 0
    rw [Fin.sum_univ_succ] at this
    simpa [h2] using this
  have hz : ∀ a : Fin (p + 2) × Fin (p + 2), a.1 = 0 ∨ a.2 = 0 → t a = 0 := by
    rintro ⟨r, c⟩ hrc
    rcases hrc with hr | hc
    · simp only at hr; subst hr
      cases c using Fin.cases with
      | zero => exact h00
      | succ c => exact h1 c
    · simp only at hc; subst hc
      cases r using Fin.cases with
      | zero => exact h00
      | succ r => exact h2 r
  have hrow : ∀ i, ∑ j, t (i, j) = 0 := by
    intro i
    cases i using Fin.cases with
    | zero => exact sum_eq_zero fun j _ => hz (0, j) (Or.inl rfl)
    | succ i => exact h3 i
  refine ⟨hz, hrow, fun j => ?_⟩
  cases j using Fin.lastCases with
  | cast j => exact h4 j
  | last =>
    have htot : ∑ j, ∑ i, t (i, j) = 0 := by
      rw [sum_comm]; exact sum_eq_zero fun i _ => hrow i
    rw [Fin.sum_univ_castSucc, sum_eq_zero (fun j _ => h4 j), zero_add] at htot
    exact htot

/-- The power sum conditions at the point of Mignon and Ressayre, for a direction of `L` that
vanishes on the border and has vanishing row and column sums. -/
theorem power_sums (p : ℕ) (hp : 1 ≤ p) (L : Submodule ℂ (Fin (p + 2) × Fin (p + 2) → ℂ))
    (hL : ∀ u ∈ L, eval (mrPoint p + u) (PEqualNP.Gct.permPoly ℂ (p + 2)) = 0)
    (t : Fin (p + 2) × Fin (p + 2) → ℂ) (ht : t ∈ L)
    (hz : ∀ a : Fin (p + 2) × Fin (p + 2), a.1 = 0 ∨ a.2 = 0 → t a = 0)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    ∑ a, t a ^ 2 = 0 ∧ ∑ a, t a ^ 3 = 0 := by
  have hline : ∀ (q : MvPolynomial (Fin (p + 2) × Fin (p + 2)) ℂ),
      (∀ u ∈ L, eval (mrPoint p + u) q = 0) → ∀ s : ℂ, eval (mrPoint p + s • t) q = 0 :=
    fun q hq s => hq _ (L.smul_mem s ht)
  have nz : ∀ a : Fin (p + 2) × Fin (p + 2), ¬ (a.1 ≠ 0 ∧ a.2 ≠ 0) → t a = 0 := by
    intro a ha
    apply hz
    by_contra hh
    exact ha ⟨fun e => hh (Or.inl e), fun e => hh (Or.inr e)⟩
  constructor
  · have h2 := (OrderCond.order_conditions_of_vanish_on_line _ _ t
      (hline _ hL)).2
    have pt : ∀ a b : Fin (p + 2) × Fin (p + 2),
        eval (mrPoint p) (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ (p + 2)))) * t a * t b =
          ((p.factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 1).factorial : ℂ)) *
            (if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then t a * t b else 0) := by
      intro a b
      by_cases ha : a.1 ≠ 0 ∧ a.2 ≠ 0
      · by_cases hb : b.1 ≠ 0 ∧ b.2 ≠ 0
        · rw [second_perm_block p a b ha.1 ha.2 hb.1 hb.2]
          split_ifs <;> ring
        · simp [nz b hb]
      · simp [nz a ha]
    simp only [pt, ← mul_sum] at h2
    rw [centred_two t hr hc] at h2
    exact (mul_eq_zero.mp h2).resolve_left (c2_ne p hp)
  · have hq := TaylorSp.dirD_vanish _ _ L hL t ht
    have h3 := (OrderCond.order_conditions_of_vanish_on_line _ _ t (hline _ hq)).2
    have ev : ∀ a b : Fin (p + 2) × Fin (p + 2),
        eval (mrPoint p) (pderiv a (pderiv b (TaylorSp.dirD t (PEqualNP.Gct.permPoly ℂ (p + 2))))) =
          ∑ c, t c * eval (mrPoint p)
            (pderiv a (pderiv b (pderiv c (PEqualNP.Gct.permPoly ℂ (p + 2))))) := by
      intro a b
      simp [TaylorSp.dirD, map_sum]
    have pt : ∀ a b c : Fin (p + 2) × Fin (p + 2),
        t c * eval (mrPoint p) (pderiv a (pderiv b (pderiv c (PEqualNP.Gct.permPoly ℂ (p + 2)))))
          * t a * t b =
          (((p - 1).factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 2).factorial : ℂ)) *
            (if (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) ∧ (a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2)
              then t a * t b * t c else 0) := by
      intro a b c
      by_cases ha : a.1 ≠ 0 ∧ a.2 ≠ 0
      · by_cases hb : b.1 ≠ 0 ∧ b.2 ≠ 0
        · by_cases hc' : c.1 ≠ 0 ∧ c.2 ≠ 0
          · rw [third_perm_block p a b c ha.1 ha.2 hb.1 hb.2 hc'.1 hc'.2]
            split_ifs <;> ring
          · simp [nz c hc']
        · simp [nz b hb]
      · simp [nz a ha]
    simp only [ev, sum_mul, pt, ← mul_sum] at h3
    rw [centred_three t hr hc] at h3
    have := (mul_eq_zero.mp h3).resolve_left (c3_ne p hp)
    simpa using this

theorem core (p k : ℕ) (hp : 1 ≤ p)
    (hW : ∀ W : Submodule ℂ (Fin (p + 1) × Fin (p + 1) → ℂ), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) →
      (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → Module.finrank ℂ W ≤ k)
    (L : Submodule ℂ (Fin (p + 2) × Fin (p + 2) → ℂ))
    (hL : ∀ u ∈ L, eval (mrPoint p + u) (PEqualNP.Gct.permPoly ℂ (p + 2)) = 0) :
    Module.finrank ℂ L ≤ 4 * (p + 1) + k := by
  let Ψ := condMap (p + 1) ∘ₗ L.subtype
  let ρ : (Fin (p + 2) × Fin (p + 2) → ℂ) →ₗ[ℂ] (Fin (p + 1) × Fin (p + 1) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun q : Fin (p + 1) × Fin (p + 1) => (q.1.succ, q.2.succ))
  let g := ρ ∘ₗ L.subtype ∘ₗ (LinearMap.ker Ψ).subtype
  have hker : ∀ y : LinearMap.ker Ψ, condMap (p + 1) (y : L) = 0 := fun y => y.2
  have hg : Function.Injective g := by
    intro y1 y2 hy
    obtain ⟨hz1, -, -⟩ := condMap_ker _ (hker y1)
    obtain ⟨hz2, -, -⟩ := condMap_ker _ (hker y2)
    have ht : ((y1 : L) : Fin (p + 2) × Fin (p + 2) → ℂ) = ((y2 : L) : _) := by
      funext ⟨r, c⟩
      cases r using Fin.cases with
      | zero => rw [hz1 _ (Or.inl rfl), hz2 _ (Or.inl rfl)]
      | succ r =>
        cases c using Fin.cases with
        | zero => rw [hz1 _ (Or.inr rfl), hz2 _ (Or.inr rfl)]
        | succ c => exact congrFun hy (r, c)
    exact Subtype.ext (Subtype.ext ht)
  have hW' := hW (LinearMap.range g) ?_ ?_
  · have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
    have e2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ 4 * (p + 1) := by
      refine (Submodule.finrank_le _).trans (le_of_eq ?_)
      simp [Module.finrank_prod]
      ring
    rw [LinearMap.finrank_range_of_inj hg] at hW'
    omega
  all_goals
    rintro x ⟨y, rfl⟩
    obtain ⟨hz, hr, hc⟩ := condMap_ker _ (hker y)
    obtain ⟨s2, s3⟩ := power_sums p hp L hL _ (y : L).2 hz hr hc
  · rw [← s2]
    exact sum_block (fun a => ((y : L) : Fin (p + 2) × Fin (p + 2) → ℂ) a ^ 2)
      (fun a ha => by simp [hz a ha])
  · rw [← s3]
    exact sum_block (fun a => ((y : L) : Fin (p + 2) × Fin (p + 2) → ℂ) a ^ 3)
      (fun a ha => by simp [hz a ha])

end PEqualNP.Gct.SigmaRed
