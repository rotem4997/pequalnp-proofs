import PEqualNP.Library.Machines.Run
import PEqualNP.Library.Helpers.OracleTranslate

/-!
# One step of a stack machine only looks at the tops of the stacks

Helper module (proofs only, no statement may use it).

* `pops q`: the largest number of pops and peeks along one run of the statement `q`.
* `stepAux_split`: running `q` on stacks `P k ++ R k` is running it on `P` and putting `R` back
  underneath, as long as each `P k` holds at least `pops q` symbols or `R k` is empty.
* `good_stepAux`: a statement that only pushes symbols of `T` keeps every stack inside `T`.
* `stepT`: the step function made total (a halted configuration stays put), and
  `iterate_stepT`: a run that halts within `s` steps is reached by `stepT^[m]` for every
  `m ≥ s`.
-/

open Turing

namespace PEqualNP.Library.Helpers.Tableau

section stmt

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- The largest number of pops and peeks one run of a statement can make. -/
def pops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pops q
  | .peek _ _ q => pops q + 1
  | .pop _ _ q => pops q + 1
  | .load _ q => pops q
  | .branch _ q₁ q₂ => max (pops q₁) (pops q₂)
  | .goto _ => 0
  | .halt => 0

theorem update_append (P R : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    Function.update (fun k => P k ++ R k) k (l ++ R k) =
      fun k' => Function.update P k l k' ++ R k' := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem head_append_of (P R : List α) (h : 1 ≤ P.length ∨ R = []) :
    (P ++ R).head? = P.head? := by
  rcases h with h | h
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · subst h; simp

theorem tail_append_of (P R : List α) (h : 1 ≤ P.length ∨ R = []) :
    (P ++ R).tail = P.tail ++ R := by
  rcases h with h | h
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · subst h; simp

theorem stepAux_split (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (P R : ∀ k, List (Γ k)),
    (∀ k, pops q ≤ (P k).length ∨ R k = []) →
    TM2.stepAux q v (fun k => P k ++ R k) =
      ⟨(TM2.stepAux q v P).l, (TM2.stepAux q v P).var,
        fun k => (TM2.stepAux q v P).stk k ++ R k⟩ := by
  induction q with
  | push k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have e : Function.update (fun k => P k ++ R k) k (f v :: (P k ++ R k)) =
        fun k' => Function.update P k (f v :: P k) k' ++ R k' := by
      rw [← update_append]; rfl
    rw [e]
    apply ih
    intro k'
    rcases h k' with h | h
    · left
      by_cases hk : k' = k
      · subst hk; simp only [Function.update_self, List.length_cons]; simp only [pops] at h; omega
      · rw [Function.update_of_ne hk]; exact h
    · right; exact h
  | peek k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have e : (P k ++ R k).head? = (P k).head? := by
      apply head_append_of
      rcases h k with h | h
      · left; simp only [pops] at h; omega
      · right; exact h
    rw [e]
    apply ih
    intro k'
    rcases h k' with h | h
    · left; simp only [pops] at h; omega
    · right; exact h
  | pop k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have h1 : 1 ≤ (P k).length ∨ R k = [] := by
      rcases h k with h | h
      · left; simp only [pops] at h; omega
      · right; exact h
    rw [head_append_of _ _ h1, tail_append_of _ _ h1, update_append]
    apply ih
    intro k'
    rcases h k' with h | h
    · left
      by_cases hk : k' = k
      · subst hk; simp only [Function.update_self, List.length_tail]; simp only [pops] at h
        omega
      · rw [Function.update_of_ne hk]; simp only [pops] at h; omega
    · right; exact h
  | load a q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    exact ih _ P R (fun k => by simpa [pops] using h k)
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v P R h
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ v P R (fun k => by
        rcases h k with h | h
        · left; simp only [pops] at h; omega
        · right; exact h)
    · exact ih₁ v P R (fun k => by
        rcases h k with h | h
        · left; simp only [pops] at h; omega
        · right; exact h)
  | goto f => intro v P R h; rfl
  | halt => intro v P R h; rfl

/-- Running a statement on the stacks is running it on the top `d` symbols of each stack,
for `d` at least `pops q`. -/
theorem stepAux_take (q : TM2.Stmt Γ Λ σ) (d : ℕ) (hd : pops q ≤ d) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux q v S =
      ⟨(TM2.stepAux q v (fun k => (S k).take d)).l,
        (TM2.stepAux q v (fun k => (S k).take d)).var,
        fun k => (TM2.stepAux q v (fun k => (S k).take d)).stk k ++ (S k).drop d⟩ := by
  have e : S = fun k => (S k).take d ++ (S k).drop d := by
    funext k; simp
  conv_lhs => rw [e]
  apply stepAux_split
  intro k
  by_cases h : d ≤ (S k).length
  · left; rw [List.length_take]; omega
  · right; rw [List.drop_eq_nil_iff]; omega

open PEqualNP.Library.Helpers.Enum in
theorem good_stepAux (T : Set (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ) (hq : pushSet q ⊆ T) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)), Good T S → Good T (TM2.stepAux q v S).stk := by
  induction q with
  | push k f q ih =>
    intro v S hS
    simp only [TM2.stepAux]
    apply ih (fun x hx => hq (Or.inr hx))
    intro k' s hs
    by_cases hk : k' = k
    · subst hk
      rw [Function.update_self] at hs
      rcases List.mem_cons.1 hs with hs | hs
      · subst hs; exact hq (Or.inl ⟨v, rfl⟩)
      · exact hS k' s hs
    · rw [Function.update_of_ne hk] at hs; exact hS k' s hs
  | peek k f q ih => intro v S hS; exact ih hq _ S hS
  | pop k f q ih =>
    intro v S hS
    simp only [TM2.stepAux]
    apply ih hq
    intro k' s hs
    by_cases hk : k' = k
    · subst hk
      rw [Function.update_self] at hs
      exact hS k' s (List.mem_of_mem_tail hs)
    · rw [Function.update_of_ne hk] at hs; exact hS k' s hs
  | load a q ih => intro v S hS; exact ih hq _ S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S hS
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ (fun x hx => hq (Or.inr hx)) v S hS
    · exact ih₁ (fun x hx => hq (Or.inl hx)) v S hS
  | goto f => intro v S hS; exact hS
  | halt => intro v S hS; exact hS

end stmt

section run

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- The step function made total: a halted configuration stays put. -/
def stepT (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => TM2.stepAux (M l) c.var c.stk

theorem stepT_of_step (M : Λ → TM2.Stmt Γ Λ σ) (c c' : TM2.Cfg Γ Λ σ)
    (h : TM2.step M c = some c') : stepT M c = c' := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa [TM2.step, stepT] using h

theorem stepT_none (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (h : c.l = none) :
    stepT M c = c := by
  simp [stepT, h]

theorem iterate_stepT (M : Λ → TM2.Stmt Γ Λ σ) :
    ∀ (s : ℕ) (a b : TM2.Cfg Γ Λ σ), (flip bind (TM2.step M))^[s] (some a) = some b →
      b.l = none → ∀ m, s ≤ m → (stepT M)^[m] a = b := by
  intro s
  induction s with
  | zero =>
    intro a b hab hb m _
    have : a = b := Option.some.inj hab
    subst this
    exact Function.iterate_fixed (stepT_none M a hb) m
  | succ s ih =>
    intro a b hab hb m hm
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step M a with
    | none =>
      have e : flip bind (TM2.step M) (some a) = none := hfa
      rw [e, PEqualNP.Library.Machines.iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step M) (some a) = some c := hfa
      rw [e] at hab
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Function.iterate_succ_apply, stepT_of_step M a c hfa]
      exact ih c b hab hb m' (by omega)

/-- Every configuration of a total run: also the configurations of the real run. -/
theorem iterate_stepT_mem (M : Λ → TM2.Stmt Γ Λ σ) :
    ∀ (j : ℕ) (a : TM2.Cfg Γ Λ σ), ∃ s ≤ j,
      (flip bind (TM2.step M))^[s] (some a) = some ((stepT M)^[j] a) := by
  intro j
  induction j with
  | zero => intro a; exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    intro a
    cases hfa : TM2.step M a with
    | none =>
      have hl : a.l = none := by
        obtain ⟨l, v, S⟩ := a
        cases l with
        | none => rfl
        | some l => simp [TM2.step] at hfa
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [Function.iterate_fixed (stepT_none M a hl)]; rfl
    | some c =>
      obtain ⟨s, hs, h⟩ := ih c
      refine ⟨s + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepT_of_step M a c hfa]
      have e : flip bind (TM2.step M) (some a) = some c := hfa
      rw [e]; exact h

end run

end PEqualNP.Library.Helpers.Tableau
