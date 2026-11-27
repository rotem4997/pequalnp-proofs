import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_202_aux

open Finset

variable {q : ℕ}
private abbrev I (q : ℕ) := Fin q

private def pairs (f : I q → I q → ℂ) :=
  ∑ j, ∑ l, if j = l then 0 else f j l

private def triples (f : I q → I q → I q → ℂ) :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else f j l m

private def quads (f : I q → I q → I q → I q → ℂ) :=
  ∑ j, ∑ l, ∑ m, ∑ n,
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else f j l m n

/-- Once a set of columns is used, every remaining column contributes the same value. -/
private theorem unused (S : Finset (I q)) (z : ℂ) :
    (∑ i, if i ∈ S then 0 else z) = ((q - S.card : ℕ) : ℂ) * z := by
  classical
  have h : Sᶜ = univ.filter (fun i => i ∉ S) := by ext; simp
  calc
    _ = ∑ i ∈ Sᶜ, z := by rw [h, sum_filter]; simp
    _ = _ := by simp [Finset.card_compl, I]

private theorem pairs_step (c : ℂ) (f : I q → ℂ) (g : I q → I q → ℂ) :
    pairs (fun j l => c * f l + g j l) =
      ((q - 1 : ℕ) : ℂ) * c * (∑ l, f l) + pairs g := by
  classical
  unfold pairs
  have split (j l : I q) :
      (if j = l then 0 else c * f l + g j l) =
      (if j = l then 0 else c * f l) + (if j = l then 0 else g j l) := by split_ifs <;> simp
  simp_rw [split, sum_add_distrib]
  congr 1
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro l _
  simpa [mul_assoc] using unused {l} (c * f l)

private theorem triples_step (c : ℂ) (f : I q → I q → ℂ) (g : I q → I q → I q → ℂ) :
    triples (fun j l m => c * f l m + g j l m) =
      ((q - 2 : ℕ) : ℂ) * c * pairs f + triples g := by
  classical
  unfold pairs triples
  have split (j l m : I q) :
      (if j = l ∨ j = m ∨ l = m then 0 else c * f l m + g j l m) =
      (if j = l ∨ j = m ∨ l = m then 0 else c * f l m) +
      (if j = l ∨ j = m ∨ l = m then 0 else g j l m) := by split_ifs <;> simp
  simp_rw [split, sum_add_distrib]
  congr 1
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  by_cases e : l = m
  · simp [e]
  · simpa [e, mul_assoc] using unused {l, m} (c * f l m)

private theorem quads_step (c : ℂ) (f : I q → I q → I q → ℂ) :
    quads (fun _ l m n => c * f l m n) = ((q - 3 : ℕ) : ℂ) * c * triples f := by
  classical
  unfold quads triples
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hlm : l = m
  · simp [hlm]
  by_cases hln : l = n
  · simp [hln]
  by_cases hmn : m = n
  · simp [hmn]
  simpa [hlm, hln, hmn, mul_assoc] using unused {l, m, n} (c * f l m n)

end PEqualNP.Outside.L_gct_202_aux

open Finset PEqualNP.Outside.L_gct_202_aux

theorem PEqualNP.Outside.L_gct_202 : ∀ (q : ℕ) (t : Fin 4 × Fin q → ℂ) (c : ℂ), 4 ≤ q → (∀ j, t (0, j) = c) → (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0 → c = 0 := by
  classical
  intro q t c hq hrow ⟨h1, h2, h3, h4⟩
  let f (j : Fin q) := t (1, j) + t (2, j) + t (3, j)
  let g (j l : Fin q) := t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)
  let h (j l m : Fin q) := t (1, j) * t (2, l) * t (3, m)
  have first : (q : ℂ) * c + (∑ j, f j) = 0 := by
    simpa [Fin.sum_univ_four, f, hrow, sum_add_distrib, add_assoc] using h1
  have pair_entry (j l : Fin q) :
      (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a,j) * t (b,l) else 0) = c * f l + g j l := by
    norm_num [Fin.sum_univ_four, hrow, f, g]
    ring
  have triple_entry (j l m : Fin q) :
      (∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
        if a < b ∧ b < d then t (a,j) * t (b,l) * t (d,m) else 0) = c * g l m + h j l m := by
    norm_num [Fin.sum_univ_four, hrow, g, h]
    ring
  simp_rw [pair_entry] at h2
  simp_rw [triple_entry] at h3
  change pairs (fun j l => c * f l + g j l) = 0 at h2
  change triples (fun j l m => c * g l m + h j l m) = 0 at h3
  rw [pairs_step] at h2
  rw [triples_step] at h3
  simp_rw [hrow, mul_assoc] at h4
  change quads (fun _ l m n => c * (t (1,l) * (t (2,m) * t (3,n)))) = 0 at h4
  rw [quads_step] at h4
  have last : ((q - 3 : ℕ) : ℂ) * c * triples h = 0 := by simpa [h, mul_assoc] using h4
  by_contra hc
  have hn (k : ℕ) (hk : k < q) : ((q - k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  have z3 := (mul_eq_zero.mp last).resolve_left (mul_ne_zero (hn 3 (by omega)) hc)
  rw [z3, add_zero] at h3
  have z2 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (hn 2 (by omega)) hc)
  rw [z2, add_zero] at h2
  have z1 := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (hn 1 (by omega)) hc)
  rw [z1, add_zero] at first
  exact mul_ne_zero (by exact_mod_cast (show q ≠ 0 by omega)) hc first
