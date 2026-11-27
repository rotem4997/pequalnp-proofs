import PEqualNP.Library.Helpers.OracleLift
import PEqualNP.Library.Helpers.OracleQueryLength

/-!
# The empty oracle gives the plain classes

Helper module (proofs only, no statement may use it).

Relative to the empty oracle, a step at label `ask` empties the query stack and goes to label
`no`. A plain machine does the same in (length of the query stack) + 1 steps: `plainFin M` is
`M.tm` with one more bit of internal state, where the statement of `ask` is "pop one symbol of
the query stack, remember in the bit whether there was one; if so go to `ask`, else go to `no`".
When the loop ends the bit is `false` again, so outside the loop the bit is always `false` and
the halting configuration is the expected one. The query stack has at most
(input length) + `maxPush` * (steps so far) symbols, so a run of `n` oracle steps is matched by
at most `n * (input length + maxPush * n + 1)` plain steps.

* `decidable_of_oracle_empty`: decided in polynomial time relative to the empty oracle implies
  decided in polynomial time, for any input encoding.
* `oracle_of_decidable`: the converse, relative to any oracle.
* `oracleP_empty`, `oracleNP_empty`: the two classes relative to the empty oracle are P and NP.
-/

open Turing

namespace PEqualNP.Library.Helpers.OracleEmpty

open PEqualNP.Library.Machines (maxPush iterate_none)

section flag

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- A statement run on internal states carrying one more bit, which it leaves alone. -/
def addFlag : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × Bool)
  | .push k f q => .push k (fun s => f s.1) (addFlag q)
  | .peek k f q => .peek k (fun s o => (f s.1 o, s.2)) (addFlag q)
  | .pop k f q => .pop k (fun s o => (f s.1 o, s.2)) (addFlag q)
  | .load a q => .load (fun s => (a s.1, s.2)) (addFlag q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (addFlag q₁) (addFlag q₂)
  | .goto f => .goto (fun s => f s.1)
  | .halt => .halt

/-- A configuration with the extra bit set to `b`. -/
def embCfg (b : Bool) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × Bool) :=
  ⟨c.l, (c.var, b), c.stk⟩

/-- Pop one symbol of stack `kq`; go to `ask` if there was one, to `no` otherwise. -/
def drain (kq : K) (ask no : Λ) : TM2.Stmt Γ Λ (σ × Bool) :=
  .pop kq (fun s o => (s.1, o.isSome)) (.goto (fun s => if s.2 then ask else no))

theorem stepAux_addFlag [DecidableEq K] (q : TM2.Stmt Γ Λ σ) (v : σ) (b : Bool)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux (addFlag q) (v, b) S = embCfg b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [addFlag, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

end flag

open Classical in
/-- The statements of the plain machine: `drain` at `ask`, the old statement elsewhere. -/
noncomputable def pm (M : OracleTM2) (l : M.tm.Λ) : TM2.Stmt M.tm.Γ M.tm.Λ (M.tm.σ × Bool) :=
  if l = M.ask then drain M.kq M.ask M.no else addFlag (M.tm.m l)

/-- The plain machine simulating `M` relative to the empty oracle. -/
noncomputable def plainFin (M : OracleTM2) : FinTM2 :=
  @FinTM2.mk M.tm.K M.tm.kDecidableEq M.tm.kFin M.tm.k₀ M.tm.k₁ M.tm.Γ M.tm.Λ M.tm.main
    M.tm.ΛFin (M.tm.σ × Bool) (M.tm.initialState, false)
    (@instFintypeProd _ _ M.tm.σFin _) M.tm.Γk₀Fin (pm M)

/-- The step function of `plainFin M`. -/
noncomputable def pstep (M : OracleTM2) (c : TM2.Cfg M.tm.Γ M.tm.Λ (M.tm.σ × Bool)) :
    Option (TM2.Cfg M.tm.Γ M.tm.Λ (M.tm.σ × Bool)) :=
  TM2.step (pm M) c

variable (M : OracleTM2)

theorem fb_some {τ : Type} (f : τ → Option τ) (a : τ) : flip bind f (some a) = f a := rfl

theorem pstep_ask (v : M.tm.σ) (b : Bool) (S : ∀ k, List (M.tm.Γ k)) :
    pstep M ⟨some M.ask, (v, b), S⟩ =
      some ⟨some (if (S M.kq).head?.isSome then M.ask else M.no), (v, (S M.kq).head?.isSome),
        Function.update S M.kq (S M.kq).tail⟩ := by
  show some (TM2.stepAux (pm M M.ask) (v, b) S) = _
  have e : pm M M.ask = drain M.kq M.ask M.no := by simp [pm]
  rw [e]
  rfl

theorem pstep_other (l : M.tm.Λ) (hl : l ≠ M.ask) (v : M.tm.σ) (S : ∀ k, List (M.tm.Γ k)) :
    pstep M (embCfg false ⟨some l, v, S⟩) =
      some (embCfg false (TM2.stepAux (M.tm.m l) v S)) := by
  show some (TM2.stepAux (pm M l) (v, false) S) = _
  have e : pm M l = addFlag (M.tm.m l) := by simp [pm, hl]
  rw [e, stepAux_addFlag]

/-- The loop at `ask` empties the query stack and ends at `no` with the bit `false`. -/
theorem drain_run (v : M.tm.σ) : ∀ (n : ℕ) (S : ∀ k, List (M.tm.Γ k)) (b : Bool),
    (S M.kq).length = n →
    (flip bind (pstep M))^[n + 1] (some ⟨some M.ask, (v, b), S⟩) =
      some ⟨some M.no, (v, false), Function.update S M.kq []⟩ := by
  intro n
  induction n with
  | zero =>
    intro S b hS
    have hnil : S M.kq = [] := List.length_eq_zero_iff.mp hS
    rw [Function.iterate_succ_apply, Function.iterate_zero_apply, fb_some, pstep_ask, hnil]
    rfl
  | succ n ih =>
    intro S b hS
    rw [Function.iterate_succ_apply]
    have e : flip bind (pstep M) (some ⟨some M.ask, (v, b), S⟩) =
        some ⟨some M.ask, (v, true),
          Function.update S M.kq (S M.kq).tail⟩ := by
      rw [fb_some, pstep_ask]
      cases hq : S M.kq with
      | nil => rw [hq] at hS; simp at hS
      | cons x t => rfl
    rw [e, ih _ true (by
      rw [Function.update_self, List.length_tail, hS]; rfl)]
    rw [Function.update_idem]

/-- One oracle step relative to the empty oracle is matched by at most
(length of the query stack) + 1 plain steps. -/
theorem sim_step (c c' : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ)
    (h : M.step (∅ : Set (List Bool)) c = some c') :
    ∃ m, m ≤ (c.stk M.kq).length + 1 ∧
      (flip bind (pstep M))^[m] (some (embCfg false c)) = some (embCfg false c') := by
  obtain ⟨l, v, S⟩ := c
  unfold OracleTM2.step at h
  by_cases hc : l = some M.ask
  · subst hc
    rw [if_pos rfl] at h
    refine ⟨(S M.kq).length + 1, le_refl _, ?_⟩
    have hr := drain_run M v (S M.kq).length S false rfl
    rw [← Option.some.inj h]
    refine hr.trans ?_
    refine congrArg some ?_
    simp only [embCfg]
    congr 1
    exact congrArg some (if_neg (fun hx => hx)).symm
  · rw [if_neg hc] at h
    cases l with
    | none => exact absurd h (by simp [TM2.step])
    | some l =>
      have hl : l ≠ M.ask := fun e => hc (by rw [e])
      refine ⟨1, by omega, ?_⟩
      have h' : some (TM2.stepAux (M.tm.m l) v S) = some c' := h
      rw [← Option.some.inj h']
      exact pstep_other M l hl v S

/-- A run of `n` oracle steps relative to the empty oracle, from a configuration whose query
stack has at most `B` symbols, is matched by at most `n * (B + maxPush * n + 1)` plain steps. -/
theorem sim_run : ∀ (n : ℕ) (a b : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) (B : ℕ),
    (a.stk M.kq).length ≤ B →
    (flip bind (M.step (∅ : Set (List Bool))))^[n] (some a) = some b →
    ∃ m, m ≤ n * (B + maxPush M.tm * n + 1) ∧
      (flip bind (pstep M))^[m] (some (embCfg false a)) = some (embCfg false b) := by
  intro n
  induction n with
  | zero =>
    intro a b B _ hab
    have : a = b := Option.some.inj hab
    exact ⟨0, by simp, by rw [this]; rfl⟩
  | succ n ih =>
    intro a b B hB hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : M.step (∅ : Set (List Bool)) a with
    | none =>
      have e : flip bind (M.step (∅ : Set (List Bool))) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (M.step (∅ : Set (List Bool))) (some a) = some c := hfa
      rw [e] at hab
      obtain ⟨m1, hm1, r1⟩ := sim_step M a c hfa
      have hlen := Enum.oracle_step_length M (∅ : Set (List Bool)) a c hfa M.kq
      obtain ⟨m2, hm2, r2⟩ := ih c b (B + maxPush M.tm) (by omega) hab
      refine ⟨m2 + m1, ?_, ?_⟩
      · have e1 : B + maxPush M.tm * (n + 1) + 1 = B + maxPush M.tm + maxPush M.tm * n + 1 := by
          ring
        rw [e1, Nat.succ_mul]
        have : m1 ≤ B + maxPush M.tm + maxPush M.tm * n + 1 := by omega
        exact Nat.add_le_add hm2 this
      · rw [Function.iterate_add_apply, r1, r2]

/-- Decided in polynomial time relative to the empty oracle implies decided in polynomial
time, for any input encoding. -/
theorem decidable_of_oracle_empty {α αΓ : Type} (ea : α → List αΓ) (S : Set α)
    (h : OracleDecidableInPolyTime (∅ : Set (List Bool)) ea S) : DecidableInPolyTime ea S := by
  obtain ⟨p, f, M, ein, eout, hf, hrun⟩ := h
  have key : ∀ a, Nonempty (TM2OutputsInTime (plainFin M) ((ea a).map ein.invFun)
      (some ((Computability.encodeBool (f a)).map eout.invFun))
      ((p * (Polynomial.X + Polynomial.C (maxPush M.tm) * p + 1)).eval (ea a).length)) := by
    intro a
    obtain ⟨⟨⟨n, hn⟩, hle⟩⟩ := hrun a
    obtain ⟨m, hm, r⟩ := sim_run M n _ _ (ea a).length
      (Enum.initList_kq_length M ein.symm (ea a)) hn
    have e1 : (plainFin M).step = pstep M := rfl
    have e2 : initList (plainFin M) ((ea a).map ein.invFun) =
        embCfg false (initList M.tm ((ea a).map ein.symm)) := rfl
    have e3 : haltList (plainFin M) ((Computability.encodeBool (f a)).map eout.invFun) =
        embCfg false (haltList M.tm ((Computability.encodeBool (f a)).map eout.symm)) := rfl
    refine ⟨⟨⟨m, ?_⟩, ?_⟩⟩
    · rw [e1, e2, Option.map_some, e3]; exact r
    refine hm.trans ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one]
    exact Nat.mul_le_mul hle (by gcongr)
  exact ⟨f, hf, ⟨{
    tm := plainFin M
    inputAlphabet := ein
    outputAlphabet := eout
    time := p * (Polynomial.X + Polynomial.C (maxPush M.tm) * p + 1)
    outputsFun := fun a => Classical.choice (key a) }⟩⟩

/-- Decided in polynomial time implies decided in polynomial time relative to any oracle, for
any input encoding. -/
theorem oracle_of_decidable {α αΓ : Type} (A : Language Bool) (ea : α → List αΓ) (S : Set α)
    (h : DecidableInPolyTime ea S) : OracleDecidableInPolyTime A ea S := by
  obtain ⟨f, hf, ⟨c⟩⟩ := h
  refine ⟨c.time, f, liftTM c.tm, c.inputAlphabet, c.outputAlphabet, hf, fun a => ?_⟩
  obtain ⟨⟨n, hn⟩, hle⟩ := c.outputsFun a
  refine ⟨⟨⟨n, ?_⟩, hle⟩⟩
  have := liftTM_iter c.tm A n (some (initList c.tm ((ea a).map c.inputAlphabet.invFun)))
  rw [hn] at this
  exact this

/-- Relative to the empty oracle, P^A is P. -/
theorem oracleP_empty :
    PEqualNP.Library.OracleP (∅ : Set (List Bool)) = PEqualNP.Library.P := by
  ext L
  exact ⟨decidable_of_oracle_empty _ L, oracle_of_decidable _ _ L⟩

/-- Relative to the empty oracle, NP^A is NP. -/
theorem oracleNP_empty :
    PEqualNP.Library.OracleNP (∅ : Set (List Bool)) = PEqualNP.Library.NP := by
  ext L
  constructor
  · rintro ⟨R, p, hR, hL⟩
    exact ⟨R, p, decidable_of_oracle_empty _ R hR, hL⟩
  · rintro ⟨R, p, hR, hL⟩
    exact ⟨R, p, oracle_of_decidable _ _ R hR, hL⟩

end PEqualNP.Library.Helpers.OracleEmpty
