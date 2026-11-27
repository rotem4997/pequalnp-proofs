import PEqualNP.Defs
import Mathlib.Data.Nat.Log

/-!
# Helpers: splitting the clauses of a CNF formula into clauses of width at most three

Helper module (proofs only, no statement may use it).

The transformation is a uniform variant of the one of Karp (1972). The items of a formula are
its literal occurrences and its clause ends, numbered `0, 1, 2, ...` in the order of the
encoding. An old variable `i` becomes the odd number `2 * i + 1`. The fresh variable of the
item `m` is the even number `2 ^ (m + 1)`, written `y m` here. The new formula has

* the unit clause `(y 0)`,
* for a literal `l` at item `m` the clause `(¬ y m ∨ l ∨ y (m + 1))`,
* for a clause end at item `m` the two unit clauses `(¬ y m)` and `(y (m + 1))`.

So `y` is true at the first item of every clause, stays true along a clause as long as no
literal is true, and must be false at the end of the clause. Every item of the old formula
produces its clauses of the new one from the item and its number alone.

Main results: `isKCNF_split` and `satisfiable_split`.
-/

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search

/-- The new name of the old variable `i`. -/
def X (i : ℕ) : ℕ := 2 * i + 1

/-- The fresh variable of the item `m`. -/
def Y (m : ℕ) : ℕ := 2 ^ (m + 1)

/-- The clauses of one old clause whose first item has the number `m`. -/
def chain (m : ℕ) : Clause → CNF
  | [] => [[(Y m, false)], [(Y (m + 1), true)]]
  | l :: c => [(Y m, false), (X l.1, l.2), (Y (m + 1), true)] :: chain (m + 1) c

/-- The clauses of a formula whose first item has the number `m`. -/
def splitFrom (m : ℕ) : CNF → CNF
  | [] => []
  | c :: φ => chain m c ++ splitFrom (m + c.length + 1) φ

/-- The transformed formula. -/
def split (φ : CNF) : CNF := [(Y 0, true)] :: splitFrom 0 φ

/-! ### Width -/

theorem isKCNF_chain (m : ℕ) (c : Clause) : IsKCNF 3 (chain m c) := by
  induction c generalizing m with
  | nil =>
    intro d hd
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp
  | cons l c ih =>
    intro d hd
    simp only [chain, List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp
    · exact ih _ d hd

theorem isKCNF_splitFrom (m : ℕ) (φ : CNF) : IsKCNF 3 (splitFrom m φ) := by
  induction φ generalizing m with
  | nil => intro d hd; simp [splitFrom] at hd
  | cons c φ ih =>
    intro d hd
    simp only [splitFrom, List.mem_append] at hd
    rcases hd with hd | hd
    · exact isKCNF_chain _ _ d hd
    · exact ih _ d hd

theorem isKCNF_split (φ : CNF) : IsKCNF 3 (split φ) := by
  intro d hd
  simp only [split, List.mem_cons] at hd
  rcases hd with rfl | hd
  · simp
  · exact isKCNF_splitFrom _ _ d hd

/-! ### Evaluation -/

theorem eval_append (σ : Assignment) (φ ψ : CNF) :
    CNF.eval σ (φ ++ ψ) = (CNF.eval σ φ && CNF.eval σ ψ) := by
  simp [CNF.eval]

theorem eval_cons (σ : Assignment) (c : Clause) (φ : CNF) :
    CNF.eval σ (c :: φ) = (Clause.eval σ c && CNF.eval σ φ) := by
  simp [CNF.eval]

theorem ceval_cons (σ : Assignment) (l : Literal) (c : Clause) :
    Clause.eval σ (l :: c) = (Literal.eval σ l || Clause.eval σ c) := by
  simp [Clause.eval]

/-! ### From the new formula to the old one -/

/-- The fresh variable after the end of a clause is true. -/
theorem chain_end (τ : Assignment) (c : Clause) : ∀ m : ℕ,
    CNF.eval τ (chain m c) = true → τ (Y (m + c.length + 1)) = true := by
  induction c with
  | nil =>
    intro m h
    simp only [chain, CNF.eval, Clause.eval, Literal.eval, List.all_cons, List.any_cons,
      List.any_nil, List.all_nil, Bool.or_false, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq] at h
    simpa using h.2
  | cons l c ih =>
    intro m h
    rw [chain, eval_cons, Bool.and_eq_true] at h
    rw [show m + (l :: c).length + 1 = (m + 1) + c.length + 1 by
      simp only [List.length_cons]; omega]
    exact ih (m + 1) h.2

theorem chain_sound (τ : Assignment) (c : Clause) : ∀ m : ℕ,
    CNF.eval τ (chain m c) = true → τ (Y m) = true →
      Clause.eval (fun i => τ (X i)) c = true := by
  induction c with
  | nil =>
    intro m h hm
    simp [chain, CNF.eval, Clause.eval, Literal.eval, hm] at h
  | cons l c ih =>
    intro m h hm
    rw [chain, eval_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [ceval_cons]
    by_cases hl : τ (X l.1) = l.2
    · simp [Literal.eval, hl]
    · have hy : τ (Y (m + 1)) = true := by
        simpa [Clause.eval, Literal.eval, hm, hl] using h1
      simp [ih (m + 1) h2 hy]

theorem splitFrom_sound (τ : Assignment) (φ : CNF) : ∀ m : ℕ,
    CNF.eval τ (splitFrom m φ) = true → τ (Y m) = true →
      CNF.eval (fun i => τ (X i)) φ = true := by
  induction φ with
  | nil => intro m _ _; rfl
  | cons c φ ih =>
    intro m h hm
    rw [splitFrom, eval_append, Bool.and_eq_true] at h
    rw [eval_cons, chain_sound τ c m h.1 hm, ih _ h.2 (chain_end τ c m h.1)]
    rfl

/-! ### From the old formula to the new one -/

/-- The assignment of the new formula: `σ` on the old variables, `t` on the fresh ones. -/
def mk (σ : Assignment) (t : ℕ → Bool) : Assignment :=
  fun v => if v % 2 = 1 then σ (v / 2) else t (Nat.log 2 v - 1)

theorem mk_X (σ : Assignment) (t : ℕ → Bool) (i : ℕ) : mk σ t (X i) = σ i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [mk, X, h1, h2]

theorem mk_Y (σ : Assignment) (t : ℕ → Bool) (m : ℕ) : mk σ t (Y m) = t m := by
  have h1 : 2 ^ (m + 1) % 2 = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
  have h2 : Nat.log 2 (2 ^ (m + 1)) = m + 1 := Nat.log_pow (by norm_num) _
  simp [mk, Y, h1, h2]

/-- The values of the fresh variables along one clause, relative to its first item. -/
def cv (σ : Assignment) : Clause → ℕ → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | l :: c, j + 1 => !Literal.eval σ l && cv σ c j

/-- The values of the fresh variables along a formula, relative to its first item. -/
def tv (σ : Assignment) : CNF → ℕ → Bool
  | [], _ => true
  | c :: φ, j => if j ≤ c.length then cv σ c j else tv σ φ (j - c.length - 1)

theorem cv_zero (σ : Assignment) (c : Clause) : cv σ c 0 = true := by
  cases c <;> rfl

theorem tv_zero (σ : Assignment) (φ : CNF) : tv σ φ 0 = true := by
  cases φ with
  | nil => rfl
  | cons c φ => simp [tv, cv_zero]

theorem chain_complete (σ : Assignment) (c : Clause) : ∀ (m : ℕ) (t : ℕ → Bool) (a : Bool),
    (∀ j ≤ c.length, t (m + j) = (a && cv σ c j)) → t (m + c.length + 1) = true →
    (a = true → Clause.eval σ c = true) → CNF.eval (mk σ t) (chain m c) = true := by
  induction c with
  | nil =>
    intro m t a ht hend ha
    have h0 := ht 0 (le_refl _)
    have ha' : a = false := by
      cases a
      · rfl
      · simpa [Clause.eval] using ha rfl
    rw [ha'] at h0
    simp only [Nat.add_zero, Bool.false_and] at h0
    simp only [List.length_nil, Nat.add_zero] at hend
    simp [chain, CNF.eval, Clause.eval, Literal.eval, mk_Y, h0, hend]
  | cons l c ih =>
    intro m t a ht hend ha
    have h0 := ht 0 (Nat.zero_le _)
    simp only [Nat.add_zero, cv, Bool.and_true] at h0
    have h1 := ht 1 (by simp)
    simp only [cv, cv_zero, Bool.and_true] at h1
    rw [chain, eval_cons, Bool.and_eq_true]
    constructor
    · simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval, mk_Y,
        mk_X, h0, h1]
      cases a <;> cases hl : (σ l.1 == l.2) <;> simp
    · refine ih (m + 1) t (a && !Literal.eval σ l) ?_ ?_ ?_
      · intro j hj
        have := ht (j + 1) (by simpa using hj)
        rw [show m + 1 + j = m + (j + 1) by omega, this, cv, Bool.and_assoc]
      · rw [show m + 1 + c.length + 1 = m + (l :: c).length + 1 by
          simp only [List.length_cons]; omega]
        exact hend
      · intro h
        rw [Bool.and_eq_true] at h
        have := ha h.1
        rw [ceval_cons] at this
        cases hl : Literal.eval σ l
        · simpa [hl] using this
        · simp [hl] at h

theorem splitFrom_complete (σ : Assignment) (φ : CNF) : ∀ (m : ℕ) (t : ℕ → Bool),
    (∀ j, t (m + j) = tv σ φ j) → CNF.eval σ φ = true →
      CNF.eval (mk σ t) (splitFrom m φ) = true := by
  induction φ with
  | nil => intro m t _ _; rfl
  | cons c φ ih =>
    intro m t ht h
    rw [eval_cons, Bool.and_eq_true] at h
    rw [splitFrom, eval_append, Bool.and_eq_true]
    constructor
    · refine chain_complete σ c m t true ?_ ?_ (fun _ => h.1)
      · intro j hj
        rw [ht j, tv]
        simp only [hj, ↓reduceIte, Bool.true_and]
      · have e : ¬ c.length + 1 ≤ c.length := by omega
        rw [show m + c.length + 1 = m + (c.length + 1) by omega, ht, tv]
        simp only [e, ↓reduceIte]
        rw [show c.length + 1 - c.length - 1 = 0 by omega, tv_zero]
    · refine ih _ t ?_ h.2
      intro j
      have e : ¬ c.length + 1 + j ≤ c.length := by omega
      rw [show m + c.length + 1 + j = m + (c.length + 1 + j) by omega, ht, tv]
      simp only [e, ↓reduceIte]
      rw [show c.length + 1 + j - c.length - 1 = j by omega]

/-- The transformed formula is satisfiable exactly when the formula is. -/
theorem satisfiable_split (φ : CNF) : Satisfiable (split φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨τ, h⟩
    rw [split, eval_cons, Bool.and_eq_true] at h
    refine ⟨fun i => τ (X i), splitFrom_sound τ φ 0 h.2 ?_⟩
    simpa [Clause.eval, Literal.eval] using h.1
  · rintro ⟨σ, h⟩
    refine ⟨mk σ (tv σ φ), ?_⟩
    rw [split, eval_cons, Bool.and_eq_true]
    refine ⟨?_, splitFrom_complete σ φ 0 _ (fun j => by rw [Nat.zero_add]) h⟩
    simp [Clause.eval, Literal.eval, mk_Y, tv_zero]

end PEqualNP.Library.SearchHelpers.KSat.Hard
