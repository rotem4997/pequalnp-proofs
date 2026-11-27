import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Helpers: a CNF formula of weight below one is satisfiable

Used by the proof of `L-lib-028`. The weight of a formula is the sum over its clauses of
`2^-(length)`. If every clause mentions each variable at most once and the weight is below
one, then splitting on a variable gives two formulas whose weights add up to at most twice the
weight, so one of them has weight below one; induction on a bound for the variables.
-/

namespace PEqualNP.Library.SearchHelpers

open PEqualNP.Search

/-- The weight of a formula: the sum of `2^-|c|` over its clauses. -/
def wt (φ : CNF) : ℚ := (φ.map fun c => (2 : ℚ)⁻¹ ^ c.length).sum

/-- The formula after setting variable `x` to `v`: clauses made true are deleted, and the
literals on `x` are removed from the others. -/
def restrict (x : ℕ) (v : Bool) (φ : CNF) : CNF :=
  (φ.filter fun c => decide ((x, v) ∉ c)).map fun c => c.filter fun l => decide (l.1 ≠ x)

theorem wt_nonneg (φ : CNF) : 0 ≤ wt φ := by
  unfold wt
  induction φ with
  | nil => simp
  | cons c φ ih => simp only [List.map_cons, List.sum_cons]; positivity

theorem wt_cons (c : Clause) (φ : CNF) : wt (c :: φ) = (2 : ℚ)⁻¹ ^ c.length + wt φ := by
  simp [wt]

theorem wt_restrict_cons (x : ℕ) (v : Bool) (c : Clause) (φ : CNF) :
    wt (restrict x v (c :: φ)) =
      (if (x, v) ∈ c then 0 else (2 : ℚ)⁻¹ ^ (c.filter fun l => decide (l.1 ≠ x)).length) +
        wt (restrict x v φ) := by
  by_cases h : (x, v) ∈ c
  · simp [restrict, h]
  · simp [restrict, h, wt]

theorem length_le_filter_succ (x : ℕ) (c : Clause) (hc : (c.map Prod.fst).Nodup) :
    c.length ≤ (c.filter fun l => decide (l.1 ≠ x)).length + 1 := by
  have hsplit := List.length_eq_length_filter_add (l := c) (fun l : Literal => decide (l.1 ≠ x))
  have hsub : ((c.filter fun l => !decide (l.1 ≠ x)).map Prod.fst).Sublist (c.map Prod.fst) :=
    (List.filter_sublist).map _
  have hnd := hc.sublist hsub
  have hsubset : (c.filter fun l => !decide (l.1 ≠ x)).map Prod.fst ⊆ [x] := by
    intro y hy
    simp only [List.mem_map, List.mem_filter, decide_not, Bool.not_not, decide_eq_true_eq] at hy
    obtain ⟨l, ⟨-, hl⟩, rfl⟩ := hy
    simpa using hl
  have := (hnd.subperm hsubset).length_le
  simp only [List.length_map, List.length_singleton] at this
  omega

theorem clause_bound (x : ℕ) (c : Clause) (hc : (c.map Prod.fst).Nodup) :
    ((if (x, true) ∈ c then 0 else (2 : ℚ)⁻¹ ^ (c.filter fun l => decide (l.1 ≠ x)).length) +
      (if (x, false) ∈ c then 0 else (2 : ℚ)⁻¹ ^ (c.filter fun l => decide (l.1 ≠ x)).length))
      ≤ 2 * (2 : ℚ)⁻¹ ^ c.length := by
  have hlen := length_le_filter_succ x c hc
  have key : (2 : ℚ)⁻¹ ^ (c.filter fun l => decide (l.1 ≠ x)).length ≤ 2 * (2 : ℚ)⁻¹ ^ c.length := by
    have h1 : (2 : ℚ)⁻¹ ^ ((c.filter fun l => decide (l.1 ≠ x)).length + 1) ≤ (2 : ℚ)⁻¹ ^ c.length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlen
    rw [pow_succ] at h1
    linarith
  by_cases ht : (x, true) ∈ c <;> by_cases hf : (x, false) ∈ c <;> simp only [ht, hf, if_true, if_false]
  · have : (0 : ℚ) ≤ 2 * (2 : ℚ)⁻¹ ^ c.length := by positivity
    linarith
  · simpa using key
  · simpa using key
  · have : (c.filter fun l => decide (l.1 ≠ x)) = c := by
      rw [List.filter_eq_self]
      intro l hl
      obtain ⟨i, b⟩ := l
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl
      cases b <;> simp_all
    rw [this]
    ring_nf
    exact le_refl _

theorem wt_restrict_le (x : ℕ) : ∀ φ : CNF, (∀ c ∈ φ, (c.map Prod.fst).Nodup) →
    wt (restrict x true φ) + wt (restrict x false φ) ≤ 2 * wt φ := by
  intro φ
  induction φ with
  | nil => intro _; simp [restrict, wt]
  | cons c φ ih =>
    intro h
    rw [wt_restrict_cons, wt_restrict_cons, wt_cons]
    have h1 := clause_bound x c (h c (by simp))
    have h2 := ih (fun c' hc' => h c' (by simp [hc']))
    linarith

theorem satisfiable_of_wt_lt_one : ∀ (N : ℕ) (φ : CNF), (∀ c ∈ φ, ∀ l ∈ c, l.1 < N) →
    (∀ c ∈ φ, (c.map Prod.fst).Nodup) → wt φ < 1 → Satisfiable φ := by
  intro N
  induction N with
  | zero =>
    intro φ hvar _ hw
    cases φ with
    | nil => exact ⟨fun _ => true, rfl⟩
    | cons c φ =>
      exfalso
      have hc : c = [] := by
        cases c with
        | nil => rfl
        | cons l c => exact absurd (hvar (l :: c) List.mem_cons_self l List.mem_cons_self) (Nat.not_lt_zero _)
      rw [wt_cons, hc] at hw
      have := wt_nonneg φ
      simp at hw
      linarith
  | succ N ih =>
    intro φ hvar hnd hw
    have hle := wt_restrict_le N φ hnd
    have hvar' : ∀ v, ∀ c ∈ restrict N v φ, ∀ l ∈ c, l.1 < N := by
      intro v c hc l hl
      simp only [restrict, List.mem_map, List.mem_filter] at hc
      obtain ⟨c0, ⟨hc0, -⟩, rfl⟩ := hc
      simp only [List.mem_filter, ne_eq, decide_eq_true_eq] at hl
      have := hvar c0 hc0 l hl.1
      omega
    have hnd' : ∀ v, ∀ c ∈ restrict N v φ, (c.map Prod.fst).Nodup := by
      intro v c hc
      simp only [restrict, List.mem_map, List.mem_filter] at hc
      obtain ⟨c0, ⟨hc0, -⟩, rfl⟩ := hc
      exact (hnd c0 hc0).sublist (List.filter_sublist.map _)
    have lift : ∀ v, Satisfiable (restrict N v φ) → Satisfiable φ := by
      rintro v ⟨σ, hσ⟩
      refine ⟨Function.update σ N v, ?_⟩
      simp only [CNF.eval, List.all_eq_true] at hσ ⊢
      intro c hc
      simp only [Clause.eval, List.any_eq_true, Literal.eval, beq_iff_eq] at hσ ⊢
      by_cases hin : (N, v) ∈ c
      · exact ⟨(N, v), hin, by simp⟩
      · have hmem : (c.filter fun l => decide (l.1 ≠ N)) ∈ restrict N v φ := by
          simp only [restrict, List.mem_map, List.mem_filter]
          exact ⟨c, ⟨hc, by simpa using hin⟩, rfl⟩
        obtain ⟨l, hl, hlv⟩ := hσ _ hmem
        simp only [List.mem_filter, ne_eq, decide_eq_true_eq] at hl
        exact ⟨l, hl.1, by rw [Function.update_of_ne hl.2]; exact hlv⟩
    by_cases ht : wt (restrict N true φ) < 1
    · exact lift true (ih _ (hvar' true) (hnd' true) ht)
    · have hf : wt (restrict N false φ) < 1 := by linarith
      exact lift false (ih _ (hvar' false) (hnd' false) hf)

end PEqualNP.Library.SearchHelpers
