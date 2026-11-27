import Mathlib
import PEqualNP.Defs

def vec (q : ℕ) (k : Fin (q - 1)) : Fin 2 × Fin q → ℂ :=
  fun (r, c) =>
    if r = 0 then
      if c.val = 0 then -1
      else if c.val = k.val + 1 then 1
      else 0
    else 0

lemma linearIndependent_vec (q : ℕ) (hq : 2 ≤ q) : LinearIndependent ℂ (vec q) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k'
  have hk_lt : k'.val + 1 < q := by omega
  let target : Fin 2 × Fin q := (0, ⟨k'.val + 1, hk_lt⟩)
  have h_eval := congr_fun hg target
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h_eval
  have h_term : ∀ i : Fin (q - 1), vec q i target = if i = k' then 1 else 0 := by
    intro i
    dsimp [vec, target]
    split_ifs with h_zero h_eq <;> try omega
    · have : i = k' := by ext; omega
      simp
    · have : i ≠ k' := by intro heq; subst heq; omega
      simp
  simp_rw [h_term] at h_eval
  simp at h_eval
  exact h_eval

lemma row1_zero (q : ℕ) (t : Fin 2 × Fin q → ℂ) (ht : t ∈ Submodule.span ℂ (Set.range (vec q))) (j : Fin q) :
    t (1, j) = 0 := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨k, rfl⟩
    dsimp [vec]
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

lemma vec_row0_sum (q : ℕ) (hq : 2 ≤ q) (k : Fin (q - 1)) :
    (∑ j : Fin q, vec q k (0, j)) = 0 := by
  have hk_lt : k.val + 1 < q := by omega
  have hq0 : 0 < q := by omega
  let j0 : Fin q := ⟨0, hq0⟩
  let j1 : Fin q := ⟨k.val + 1, hk_lt⟩
  have hj_id : ∀ j : Fin q, vec q k (0, j) = (if j = j1 then (1 : ℂ) else 0) - (if j = j0 then 1 else 0) := by
    intro j
    dsimp [vec, j0, j1]
    by_cases hj0 : j = ⟨0, hq0⟩
    · have hj_zero : j.val = 0 := congr_arg Fin.val hj0
      have : ¬ j = ⟨k.val + 1, hk_lt⟩ := by
        intro h
        have hk_eq : j.val = k.val + 1 := congr_arg Fin.val h
        omega
      simp [*]
    · have hj0_val : j.val ≠ 0 := by
        intro h
        apply hj0
        ext
        exact h
      by_cases hj1 : j = ⟨k.val + 1, hk_lt⟩
      · have : j.val = k.val + 1 := congr_arg Fin.val hj1
        simp [*]
      · have hj1_val : j.val ≠ k.val + 1 := by
          intro h
          apply hj1
          ext
          exact h
        simp [*]
  simp_rw [hj_id]
  rw [Finset.sum_sub_distrib]
  simp

lemma sum_rows_zero (q : ℕ) (hq : 2 ≤ q) (t : Fin 2 × Fin q → ℂ)
    (ht : t ∈ Submodule.span ℂ (Set.range (vec q))) :
    (∑ j, (t (0, j) + t (1, j))) = 0 := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨k, rfl⟩
    have h1 : ∀ j, (vec q k) (1, j) = 0 := by intro j; dsimp [vec]
    simp_rw [h1, add_zero]
    exact vec_row0_sum q hq k
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [Pi.add_apply]
    have : (∑ j, (x (0, j) + y (0, j) + (x (1, j) + y (1, j)))) =
        (∑ j, (x (0, j) + x (1, j))) + (∑ j, (y (0, j) + y (1, j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, ihx, ihy, add_zero]
  | smul a x hx ih =>
    simp only [Pi.smul_apply, smul_eq_mul]
    have : (∑ j, (a * x (0, j) + a * x (1, j))) = a * ∑ j, (x (0, j) + x (1, j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, ih, mul_zero]

lemma sum_prod_zero (q : ℕ) (t : Fin 2 × Fin q → ℂ)
    (ht : t ∈ Submodule.span ℂ (Set.range (vec q))) :
    (∑ j, ∑ l, if j = l then (0 : ℂ) else t (0, j) * t (1, l)) = 0 := by
  have h1 : ∀ l, t (1, l) = 0 := row1_zero q t ht
  have h2 : ∀ j l, (if j = l then (0 : ℂ) else t (0, j) * t (1, l)) = 0 := by
    intro j l
    rw [h1 l, mul_zero]
    split_ifs <;> rfl
  simp_rw [h2]
  simp

theorem PEqualNP.Outside.L_gct_108 : ∀ (q : ℕ), 2 ≤ q → ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ),
    (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧
    Module.finrank ℂ L + 1 = q := by
  intro q hq
  use Submodule.span ℂ (Set.range (vec q))
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ⟨sum_rows_zero q hq t ht, sum_prod_zero q t ht⟩
  · rw [finrank_span_eq_card (linearIndependent_vec q hq)]
    simp
    omega
