import Mathlib

namespace PEqualNP.Gct.Helpers.S2Reduction

open Finset

/-- (E2) Removing the diagonal from a double sum. -/
theorem e2 {q : ℕ} (f : Fin q → Fin q → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else f j l) = (∑ j, ∑ l, f j l) - ∑ j, f j j := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ l, (if j = l then 0 else f j l) = f j l - if j = l then f j l else 0 := by
    intro l; split_ifs <;> simp
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem dbl {q : ℕ} (a b : Fin q → ℂ) :
    (∑ j, ∑ l, a j * b l) = (∑ j, a j) * ∑ j, b j := by
  rw [Fintype.sum_mul_sum]

/-- (E3) in the special case of zero sums. -/
theorem e3 {q : ℕ} (a b x : Fin q → ℂ) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0)
    (hx : ∑ j, x j = 0) :
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else a j * b l * x m)
      = 2 * ∑ j, a j * b j * x j := by
  have h : ∀ j l m, (if j = l ∨ j = m ∨ l = m then 0 else a j * b l * x m)
      = a j * b l * x m - (if j = l then a j * b l * x m else 0)
        - (if j = m then a j * b l * x m else 0) - (if l = m then a j * b l * x m else 0)
        + 2 * (if j = l ∧ l = m then a j * b l * x m else 0) := by
    intro j l m
    by_cases h1 : j = l <;> by_cases h2 : j = m <;> by_cases h3 : l = m <;>
      simp_all <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have t1 : (∑ j, ∑ l, ∑ m, a j * b l * x m) = 0 := by
    simp [← Finset.mul_sum, ← Finset.sum_mul, ha, hb, hx]
  have t2 : (∑ j, ∑ l, ∑ m, if j = l then a j * b l * x m else 0) = 0 := by
    simp [Finset.sum_ite_irrel, ← Finset.mul_sum, hx]
  have t3 : (∑ j, ∑ l, ∑ m, if j = m then a j * b l * x m else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [← Finset.mul_sum, ← Finset.sum_mul, hb, mul_comm, mul_left_comm]
  have t4 : (∑ j, ∑ l, ∑ m, if l = m then a j * b l * x m else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [← Finset.mul_sum, ← Finset.sum_mul, ha, mul_assoc]
  have t5 : (∑ j, ∑ l, ∑ m, 2 * if j = l ∧ l = m then a j * b l * x m else 0)
      = 2 * ∑ j, a j * b j * x j := by
    simp only [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ite_and, Finset.sum_ite_eq]
  rw [t1, t2, t3, t4, t5]; ring

/-- D2 in closed form. -/
theorem d2 {q : ℕ} (a b : Fin q → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else a j * b l) = (∑ j, a j) * (∑ j, b j) - ∑ j, a j * b j := by
  rw [e2 (fun j l => a j * b l), dbl]

/-- Lemma S2 in the X-form of reduction.md, section 2. -/
def StmtS2 : Prop := ∀ (q : ℕ) (L : Submodule ℂ (Fin 2 × Fin q → ℂ)) (X : Submodule ℂ (Fin q → ℂ)),
  1 ≤ q → (∀ t ∈ L, ∑ j, t (0, j) = 0 ∧ ∑ j, t (1, j) = 0 ∧ ∑ j, t (0, j) * t (1, j) = 0) →
  (∀ x ∈ X, ∑ j, x j = 0) →
  (∀ t ∈ L, ∀ x ∈ X, ∑ j, (t (0, j) + t (1, j)) * x j = 0 ∧ ∑ j, t (0, j) * t (1, j) * x j = 0) →
  Module.finrank ℂ L + 1 + Module.finrank ℂ X ≤ q

/-- The literal term of notes/gct-086-S-p2-statement.txt. -/
def Target : Prop := ∀ (q : ℕ) (L : Submodule ℂ (Fin 2 × Fin q → ℂ)) (X : Submodule ℂ (Fin q → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)), 1 ≤ q → (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) → (∀ t ∈ L, ∀ x ∈ X, (∑ j, (t (0, j) + t (1, j) + x j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) = 0) → (∀ t ∈ L, ∀ y ∈ Y, (∑ j, (t (0, j) + t (1, j))) + y 0 + y 1 = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) + (∑ j, t (0, j)) * y 1 + y 0 * (∑ j, t (1, j)) = 0) → Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ q

/-- The row-0 sum functional A. -/
def rowSum (q : ℕ) : (Fin 2 × Fin q → ℂ) →ₗ[ℂ] ℂ where
  toFun t := ∑ j, t (0, j)
  map_add' s t := by simp [Finset.sum_add_distrib]
  map_smul' c t := by simp [Finset.mul_sum]

/-- Rank-nullity for a functional restricted to a subspace. -/
theorem finrank_le_inf_ker_add_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (L : Submodule ℂ V) (f : V →ₗ[ℂ] ℂ) :
    Module.finrank ℂ L ≤ Module.finrank ℂ ↥(L ⊓ LinearMap.ker f) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq L (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have h4 := Submodule.finrank_le (L ⊔ LinearMap.ker f)
  omega

theorem reduction : StmtS2 → Target := by
  intro hS q L X Y hq hL hX hY
  -- facts from hL
  have hL1 : ∀ t ∈ L, ∑ j, t (1, j) = - ∑ j, t (0, j) := by
    intro t ht
    have h := (hL t ht).1
    rw [Finset.sum_add_distrib] at h
    linear_combination h
  have hL2 : ∀ t ∈ L, (∑ j, t (0, j)) * (∑ j, t (1, j)) - ∑ j, t (0, j) * t (1, j) = 0 := by
    intro t ht
    have h := (hL t ht).2
    have e := d2 (fun j => t (0, j)) (fun l => t (1, l))
    rw [e] at h
    exact h
  -- facts on X
  have hx0 : ∀ x ∈ X, ∑ j, x j = 0 := by
    intro x hx
    have := (hX 0 L.zero_mem x hx).1
    simpa using this
  have hxab : ∀ t ∈ L, ∀ x ∈ X, ∑ j, (t (0, j) + t (1, j)) * x j = 0 := by
    intro t ht x hx
    have h := (hX t ht x hx).2.1
    have split : ∀ j l, (if j = l then (0 : ℂ) else t (0, j) * t (1, l) + t (0, j) * x l
        + t (1, j) * x l) = (if j = l then 0 else t (0, j) * t (1, l))
        + (if j = l then 0 else t (0, j) * x l) + (if j = l then 0 else t (1, j) * x l) := by
      intro j l; split_ifs <;> simp
    simp only [split, Finset.sum_add_distrib] at h
    have e1 := d2 (fun j => t (0, j)) (fun l => t (1, l))
    have e2' := d2 (fun j => t (0, j)) x
    have e3' := d2 (fun j => t (1, j)) x
    rw [e1, e2', e3'] at h
    have hab := hL2 t ht
    have hxs := hx0 x hx
    simp only [add_mul, Finset.sum_add_distrib]
    linear_combination -h + hab + ((∑ j, t (0, j)) + ∑ j, t (1, j)) * hxs
  -- the subspace L_A
  set A := rowSum q
  set LA := L ⊓ LinearMap.ker A with hLA
  have hLA0 : ∀ t ∈ LA, ∑ j, t (0, j) = 0 := fun t ht =>
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp ht).2
  have hLAL : ∀ t ∈ LA, t ∈ L := fun t ht => (Submodule.mem_inf.mp ht).1
  have hLA1 : ∀ t ∈ LA, ∑ j, t (1, j) = 0 := by
    intro t ht; rw [hL1 t (hLAL t ht), hLA0 t ht, neg_zero]
  have hLA2 : ∀ t ∈ LA, ∑ j, t (0, j) * t (1, j) = 0 := by
    intro t ht
    have h := hL2 t (hLAL t ht)
    rw [hLA0 t ht, zero_mul, zero_sub, neg_eq_zero] at h
    exact h
  have hxabc : ∀ t ∈ LA, ∀ x ∈ X, ∑ j, t (0, j) * t (1, j) * x j = 0 := by
    intro t ht x hx
    have h := (hX t (hLAL t ht) x hx).2.2
    have e := e3 (fun j => t (0, j)) (fun l => t (1, l)) x (hLA0 t ht) (hLA1 t ht) (hx0 x hx)
    rw [e] at h
    simpa using h
  -- step S
  have hSt : Module.finrank ℂ LA + 1 + Module.finrank ℂ X ≤ q :=
    hS q LA X hq (fun t ht => ⟨hLA0 t ht, hLA1 t ht, hLA2 t ht⟩) hx0
      (fun t ht x hx => ⟨hxab t (hLAL t ht) x hx, hxabc t ht x hx⟩)
  -- facts on Y
  have hy0 : ∀ y ∈ Y, y 0 + y 1 = 0 := by
    intro y hy
    have := (hY 0 L.zero_mem y hy).1
    simpa using this
  have hy1 : ∀ t ∈ L, ∀ y ∈ Y, (∑ j, t (0, j)) * (y 1 - y 0) = 0 := by
    intro t ht y hy
    have h := (hY t ht y hy).2
    have e := d2 (fun j => t (0, j)) (fun l => t (1, l))
    rw [e] at h
    linear_combination h - hL2 t ht - y 0 * hL1 t ht
  -- step U
  have hU1 : Module.finrank ℂ L ≤ Module.finrank ℂ LA + 1 :=
    finrank_le_inf_ker_add_one L A
  by_cases hc : ∃ t ∈ L, A t ≠ 0
  · obtain ⟨t0, ht0, hA0⟩ := hc
    have hYb : Y = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      have h1 := hy1 t0 ht0 y hy
      have h0 := hy0 y hy
      have hA0' : ∑ j, t0 (0, j) ≠ 0 := hA0
      have h2 : y 1 - y 0 = 0 := (mul_eq_zero.mp h1).resolve_left hA0'
      have hy00 : y 0 = 0 := by linear_combination (h0 - h2) / 2
      have hy11 : y 1 = 0 := by linear_combination (h0 + h2) / 2
      funext i; fin_cases i
      · exact hy00
      · exact hy11
    rw [hYb, finrank_bot]
    omega
  · push_neg at hc
    have hLAeq : LA = L := inf_eq_left.mpr fun t ht => LinearMap.mem_ker.mpr (hc t ht)
    have hYle : Y ≤ Submodule.span ℂ {(![1, -1] : Fin 2 → ℂ)} := by
      intro y hy
      rw [Submodule.mem_span_singleton]
      refine ⟨y 0, ?_⟩
      have h0 := hy0 y hy
      funext i; fin_cases i
      · simp
      · simp; linear_combination -h0
    have hY1 : Module.finrank ℂ Y ≤ 1 :=
      (Submodule.finrank_mono hYle).trans ((finrank_span_le_card _).trans (by simp))
    rw [hLAeq] at hSt
    omega

end PEqualNP.Gct.Helpers.S2Reduction
