import PEqualNP.Library.Helpers.OracleClock
import PEqualNP.Library.Machines.Run

/-!
# Oracle queries are short

Helper module (proofs only, no statement may use it). One oracle step grows a stack by at most
`maxPush` symbols (the oracle step only empties the query stack), so every query asked during
the first `n` steps from a configuration whose query stack has at most `B` symbols has length at
most `B + maxPush * n`. Hence two oracles that agree on all strings up to that length give the
same run, and on input `x` within `t` steps the bound is `|x| + maxPush * t`.
-/

open Turing

namespace PEqualNP.Library.Helpers.Enum

open PEqualNP.Library.Machines (maxPush)

variable (M : OracleTM2) (A : Language Bool)

theorem oracle_step_length (c c' : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (h : M.step A c = some c')
    (k : M.tm.K) : (c'.stk k).length ≤ (c.stk k).length + maxPush M.tm := by
  unfold OracleTM2.step at h
  by_cases hc : c.l = some M.ask
  · rw [if_pos hc] at h
    cases h
    by_cases hk : k = M.kq
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  · rw [if_neg hc] at h
    exact Machines.step_length M.tm c c' h k

theorem queries_length (n : ℕ) : ∀ (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (B : ℕ),
    (c.stk M.kq).length ≤ B → ∀ y ∈ queries M A c n, y.length ≤ B + maxPush M.tm * n := by
  induction n with
  | zero => intro c B _ y hy; simp [queries] at hy
  | succ n ih =>
    intro c B hc y hy
    simp only [queries, Finset.mem_union] at hy
    rcases hy with hy | hy
    · unfold query at hy
      split_ifs at hy
      · simp only [Option.toFinset_some, Finset.mem_singleton] at hy
        subst hy
        simp only [List.length_map, List.length_reverse]
        omega
      · simp at hy
    · cases hs : M.step A c with
      | none => rw [hs] at hy; simp at hy
      | some c' =>
        rw [hs] at hy
        have h1 := oracle_step_length M A c c' hs M.kq
        have h2 := ih c' (B + maxPush M.tm) (by omega) y hy
        rw [Nat.mul_succ]
        omega

/-- Oracles agreeing on all strings of length at most `B + maxPush * n` give the same first
`n` steps, from any configuration whose query stack has at most `B` symbols. -/
theorem runFrom_congr_short (A' : Language Bool) (n : ℕ) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ)
    (B : ℕ) (hc : (c.stk M.kq).length ≤ B)
    (h : ∀ y : List Bool, y.length ≤ B + maxPush M.tm * n → (y ∈ A ↔ y ∈ A')) :
    ∀ s ≤ n, runFrom M A c s = runFrom M A' c s :=
  runFrom_congr M A A' n c (fun y hy => h y (queries_length M A n c B hc y hy))

theorem initList_kq_length {α : Type} (ιin : α → M.tm.Γ M.tm.k₀) (x : List α) :
    ((initList M.tm (x.map ιin)).stk M.kq).length ≤ x.length := by
  rw [Machines.initList_eq]
  by_cases hk : M.kq = M.tm.k₀
  · show (Function.update (fun _ => []) M.tm.k₀ (x.map ιin) M.kq).length ≤ x.length
    rw [hk, Function.update_self, List.length_map]
  · show (Function.update (fun _ => []) M.tm.k₀ (x.map ιin) M.kq).length ≤ x.length
    rw [Function.update_of_ne hk]
    exact Nat.zero_le _

/-- Every query asked within `t` steps on input `x` has length at most `|x| + maxPush * t`. -/
theorem accepts_queries_length {α : Type} (ιin : α → M.tm.Γ M.tm.k₀) (t : ℕ) (x : List α) :
    ∀ y ∈ queries M A (initList M.tm (x.map ιin)) t, y.length ≤ x.length + maxPush M.tm * t :=
  queries_length M A t _ _ (initList_kq_length M ιin x)

/-- Oracles agreeing on all strings of length at most `|x| + maxPush * t` accept `x` alike
within `t` steps. -/
theorem accepts_congr_short {α : Type} (ιin : α → M.tm.Γ M.tm.k₀) (o : M.tm.Γ M.tm.k₁) (t : ℕ)
    (x : List α) (A' : Language Bool)
    (h : ∀ y : List Bool, y.length ≤ x.length + maxPush M.tm * t → (y ∈ A ↔ y ∈ A')) :
    Accepts M A ιin o t x ↔ Accepts M A' ιin o t x := by
  have e := runFrom_congr_short M A A' t _ x.length (initList_kq_length M ιin x) h
  unfold Accepts
  constructor
  · rintro ⟨s, hs, r⟩; exact ⟨s, hs, (e s hs) ▸ r⟩
  · rintro ⟨s, hs, r⟩; exact ⟨s, hs, (e s hs).symm ▸ r⟩

end PEqualNP.Library.Helpers.Enum
