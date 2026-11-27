import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Clocked runs of oracle machines and their locality

Helper module (proofs only, no statement may use it).

* `runFrom M A c n`: the configuration after `n` steps of `M.step A` from `c` (as Mathlib's
  `EvalsTo` iterates it).
* `Accepts M A ιin o t x`: within `t` steps, the run on `x` (written with `ιin`) reaches the
  halting configuration with output `[o]`.
* `queries M A c n`: the query strings asked during the first `n` steps; at most `n` of them,
  and an oracle agreeing with `A` on them gives the same run (`runFrom_congr`).
* `decides_iff_accepts`: a machine deciding `L` relative to `A` within time `t` accepts exactly
  `L` in the sense of `Accepts`.
-/

open Turing

namespace PEqualNP.Library.Helpers.Enum

variable (M : OracleTM2) (A : Language Bool)

/-- The configuration after `n` steps from `c`, or `none` if the run stopped before. -/
noncomputable def runFrom (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (n : ℕ) :
    Option (TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) :=
  (flip bind (M.step A))^[n] (some c)

theorem runFrom_zero (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : runFrom M A c 0 = some c := rfl

theorem runFrom_succ (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (n : ℕ) :
    runFrom M A c (n + 1) = (M.step A c).bind (fun c' => runFrom M A c' n) := by
  unfold runFrom
  rw [Function.iterate_succ_apply]
  show (flip bind (M.step A))^[n] (M.step A c) = _
  cases M.step A c with
  | none =>
    show (flip bind (M.step A))^[n] none = none
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply]; exact ih
  | some c' => rfl

open Classical in
/-- The query asked at configuration `c`, if any. -/
noncomputable def query (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : Option (List Bool) :=
  if c.l = some M.ask then some ((c.stk M.kq).reverse.map M.queryBit) else none

theorem step_congr (A' : Language Bool) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ)
    (h : ∀ y ∈ (query M c).toFinset, y ∈ A ↔ y ∈ A') : M.step A c = M.step A' c := by
  unfold OracleTM2.step
  by_cases hc : c.l = some M.ask
  · have hy := h ((c.stk M.kq).reverse.map M.queryBit) (by simp [query, hc])
    rw [if_pos hc, if_pos hc]
    by_cases hA : (c.stk M.kq).reverse.map M.queryBit ∈ A
    · rw [if_pos hA, if_pos (hy.mp hA)]
    · rw [if_neg hA, if_neg (fun h' => hA (hy.mpr h'))]
  · rw [if_neg hc, if_neg hc]

/-- The query strings asked during the first `n` steps from `c`. -/
noncomputable def queries : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ → ℕ → Finset (List Bool)
  | _, 0 => ∅
  | c, n + 1 => (query M c).toFinset ∪ ((M.step A c).elim ∅ (fun c' => queries c' n))

theorem queries_card (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (n : ℕ) :
    (queries M A c n).card ≤ n := by
  induction n generalizing c with
  | zero => simp [queries]
  | succ n ih =>
    simp only [queries]
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (query M c).toFinset.card ≤ 1 := by
      cases query M c <;> simp
    have h2 : ((M.step A c).elim ∅ (fun c' => queries M A c' n)).card ≤ n := by
      cases M.step A c with
      | none => simp
      | some c' => exact ih c'
    omega

theorem runFrom_congr (A' : Language Bool) (n : ℕ) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ)
    (h : ∀ y ∈ queries M A c n, y ∈ A ↔ y ∈ A') :
    ∀ s ≤ n, runFrom M A c s = runFrom M A' c s := by
  induction n generalizing c with
  | zero =>
    intro s hs
    obtain rfl : s = 0 := by omega
    rfl
  | succ n ih =>
    intro s hs
    cases s with
    | zero => rfl
    | succ s =>
      rw [runFrom_succ, runFrom_succ]
      have hstep : M.step A c = M.step A' c :=
        step_congr M A A' c (fun y hy => h y (by simp only [queries]; exact Finset.mem_union_left _ hy))
      rw [← hstep]
      cases hc : M.step A c with
      | none => rfl
      | some c' =>
        simp only [Option.bind_some]
        refine ih c' (fun y hy => h y ?_) s (by omega)
        simp only [queries, hc, Option.elim_some]
        exact Finset.mem_union_right _ hy

/-- The halting configuration with output `s`, typed as a configuration of `M.tm`'s stacks. -/
def haltC (s : List (M.tm.Γ M.tm.k₁)) : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ := haltList M.tm s

/-- Within `t` steps, the run on `x` reaches the halting configuration with output `[o]`. -/
def Accepts {α : Type} (ιin : α → M.tm.Γ M.tm.k₀) (o : M.tm.Γ M.tm.k₁) (t : ℕ) (x : List α) :
    Prop :=
  ∃ s ≤ t, runFrom M A (initList M.tm (x.map ιin)) s = some (haltC M [o])

theorem accepts_local {α : Type} (ιin : α → M.tm.Γ M.tm.k₀) (o : M.tm.Γ M.tm.k₁) (t : ℕ)
    (x : List α) : ∃ Q : Finset (List Bool), Q.card ≤ t ∧ ∀ A' : Language Bool,
      (∀ y ∈ Q, y ∈ A ↔ y ∈ A') → (Accepts M A ιin o t x ↔ Accepts M A' ιin o t x) := by
  refine ⟨queries M A (initList M.tm (x.map ιin)) t, queries_card _ _ _ _, fun A' hA' => ?_⟩
  have h := runFrom_congr M A A' t _ hA'
  unfold Accepts
  constructor
  · rintro ⟨s, hs, e⟩; exact ⟨s, hs, (h s hs) ▸ e⟩
  · rintro ⟨s, hs, e⟩; exact ⟨s, hs, (h s hs).symm ▸ e⟩

theorem step_halt (s : List (M.tm.Γ M.tm.k₁)) : M.step A (haltC M s) = none := by
  unfold OracleTM2.step
  have : (haltC M s).l ≠ some M.ask := by simp [haltC, haltList]
  rw [if_neg this]
  rfl

theorem runFrom_halt (s : List (M.tm.Γ M.tm.k₁)) (n : ℕ) :
    runFrom M A (haltC M s) (n + 1) = none := by
  refine (runFrom_succ M A _ n).trans ?_
  rw [step_halt]; rfl

/-- Runs reaching a halting configuration: the step count and the configuration are unique. -/
theorem runFrom_halt_unique (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (s₁ s₂ : List (M.tm.Γ M.tm.k₁))
    (n₁ n₂ : ℕ) (h₁ : runFrom M A c n₁ = some (haltC M s₁))
    (h₂ : runFrom M A c n₂ = some (haltC M s₂)) : s₁ = s₂ := by
  induction n₁ generalizing c n₂ with
  | zero =>
    cases n₂ with
    | zero =>
      rw [runFrom_zero] at h₁ h₂
      have := (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
      have hk := congrArg (fun c => c.stk M.tm.k₁) this
      simpa [haltC, haltList] using hk
    | succ n₂ =>
      rw [runFrom_zero] at h₁
      rw [Option.some.inj h₁, runFrom_halt] at h₂
      cases h₂
  | succ n₁ ih =>
    cases n₂ with
    | zero =>
      rw [runFrom_zero] at h₂
      rw [Option.some.inj h₂, runFrom_halt] at h₁
      cases h₁
    | succ n₂ =>
      rw [runFrom_succ] at h₁ h₂
      cases hc : M.step A c with
      | none => rw [hc] at h₁; cases h₁
      | some c' =>
        rw [hc] at h₁ h₂
        exact ih c' n₂ h₁ h₂

/-- A machine deciding `L` relative to `A` within time `t` accepts exactly `L`. -/
theorem decides_iff_accepts {α : Type} (f : List α → Bool) (ein : M.tm.Γ M.tm.k₀ ≃ α)
    (eout : M.tm.Γ M.tm.k₁ ≃ Bool) (t : ℕ → ℕ)
    (h : ∀ x, Nonempty (StateTransition.EvalsToInTime (M.step A)
      (initList M.tm (x.map ein.symm))
      (some (haltList M.tm ((Computability.encodeBool (f x)).map eout.symm))) (t x.length)))
    (x : List α) :
    f x = true ↔ Accepts M A ein.symm (eout.symm true) (t x.length) x := by
  obtain ⟨⟨⟨n, hn⟩, hle⟩⟩ := h x
  have hn' : runFrom M A (initList M.tm (x.map ein.symm)) n =
      some (haltC M [eout.symm (f x)]) := hn
  constructor
  · intro hf
    rw [hf] at hn'
    exact ⟨n, hle, hn'⟩
  · rintro ⟨s, _, hs⟩
    have := runFrom_halt_unique M A _ _ _ _ _ hn' hs
    simp only [List.cons.injEq, and_true] at this
    exact eout.symm.injective this

end PEqualNP.Library.Helpers.Enum
