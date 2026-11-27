import PEqualNP.Defs
import Mathlib.Tactic

/-!
# A machine must erase its input

Helper module (proofs only, no statement may use it). One labelled statement pops a bounded
number of symbols from any one stack, so after `m` steps a stack has lost at most `m * d`
symbols, where `d` is the largest pop count over the finitely many labels. A halted machine
holds on each stack at most its output.
-/

open Turing

namespace PEqualNP.Library.Helpers
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- The most pops a statement can do on any run. -/
def pops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pops q
  | .peek _ _ q => pops q
  | .pop _ _ q => pops q + 1
  | .load _ q => pops q
  | .branch _ q₁ q₂ => max (pops q₁) (pops q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_len (k : K) (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (S : ∀ k, List (Γ k)),
    (S k).length ≤ ((TM2.stepAux q v S).stk k).length + pops q := by
  induction q with
  | push k' f q ih =>
    intro v S
    refine le_trans ?_ (ih v _)
    by_cases h : k = k'
    · subst h; simp
    · simp [Function.update_of_ne h]
  | peek k' f q ih => intro v S; exact ih _ _
  | pop k' f q ih =>
    intro v S
    have := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    simp only [TM2.stepAux, pops]
    by_cases h : k = k'
    · subst h; simp at this; omega
    · simp [Function.update_of_ne h] at this; omega
  | load a q ih => intro v S; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    have h1 := ih₁ v S
    have h2 := ih₂ v S
    simp only [TM2.stepAux, pops]
    cases f v <;> simp <;> omega
  | goto f => intro v S; simp [pops, TM2.stepAux]
  | halt => intro v S; simp [pops, TM2.stepAux]

theorem iter_len [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (k : K) :
    ∀ (m : ℕ) (c c' : TM2.Cfg Γ Λ σ), (flip bind (TM2.step M))^[m] (some c) = some c' →
      (c.stk k).length ≤ (c'.stk k).length + m * (Finset.univ.sup fun l => pops (M l)) := by
  intro m
  induction m with
  | zero => intro c c' h; simp at h; subst h; simp
  | succ m ih =>
    intro c c' h
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      exfalso
      have : ∀ n, (flip bind (TM2.step M))^[n] none = none := by
        intro n; induction n with
        | zero => rfl
        | succ n ihn => rw [Function.iterate_succ_apply]; exact ihn
      have h0 : (flip bind (TM2.step M)) (some ⟨none, v, S⟩) = none := rfl
      rw [h0, this] at h
      cases h
    | some l =>
      have h' : (flip bind (TM2.step M))^[m] (some (TM2.stepAux (M l) v S)) = some c' := by
        simpa [flip, TM2.step] using h
      have h1 := ih _ _ h'
      have h2 := stepAux_len k (M l) v S
      have h3 : pops (M l) ≤ Finset.univ.sup fun l => pops (M l) :=
        Finset.le_sup (f := fun l => pops (M l)) (Finset.mem_univ l)
      simp only at h1 h2 ⊢
      rw [Nat.succ_mul]
      omega

theorem halt_len (tm : FinTM2) (s : List (tm.Γ tm.k₁)) (k : tm.K) :
    ((haltList tm s).stk k).length ≤ s.length := by
  unfold haltList
  dsimp only
  split
  · rename_i e; subst e; simp
  · simp

/-- A language decided within `t` forces `n ≤ d * t n + 1` for some constant `d`. -/
theorem dtime_linear (t : ℕ → ℕ) (L : Language Bool) (hL : L ∈ DTIME t) :
    ∃ d : ℕ, ∀ n : ℕ, n ≤ d * t n + 1 := by
  obtain ⟨f, -, c, hc⟩ := hL
  let _ := c.tm.ΛFin
  let _ := c.tm.kDecidableEq
  refine ⟨Finset.univ.sup fun l => pops (c.tm.m l), fun n => ?_⟩
  have h := c.outputsFun (List.replicate n false)
  have key := iter_len c.tm.m c.tm.k₀ h.steps _ _ h.evals_in_steps
  have hle : h.steps ≤ t n := by
    have := h.steps_le_m.trans (hc _); simpa using this
  have hinit : ((initList c.tm (List.map c.inputAlphabet.invFun (List.replicate n false))).stk c.tm.k₀).length = n := by
    simp [initList]
  have hhalt : ((haltList c.tm (List.map c.outputAlphabet.invFun (Computability.encodeBool (f (List.replicate n false))))).stk c.tm.k₀).length ≤ 1 := by
    exact (halt_len _ _ _).trans (by cases f (List.replicate n false) <;> simp [Computability.encodeBool])
  rw [hinit] at key
  have : (Finset.univ.sup fun l => pops (c.tm.m l)) * h.steps ≤ (Finset.univ.sup fun l => pops (c.tm.m l)) * t n :=
    Nat.mul_le_mul_left _ hle
  rw [Nat.mul_comm] at this
  omega
end PEqualNP.Library.Helpers
