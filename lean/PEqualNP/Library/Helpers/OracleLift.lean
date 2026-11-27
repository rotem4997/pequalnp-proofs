import PEqualNP.Defs
import Mathlib.Tactic

/-!
# A machine as an oracle machine that never asks

Helper module (proofs only, no statement may use it). Given a machine `tm`, `liftTM tm` has
labels `Option tm.Λ`: label `some l` runs the statement of `l` with every jump relabelled by
`some`, and the fresh label `none` serves as `ask`, `yes` and `no`. No run from a configuration
whose label is `some` reaches `none`, so relative to any oracle the oracle machine runs exactly
as `tm`, in the same number of steps, to the same halting configuration.
-/

open Turing

namespace PEqualNP.Library.Helpers

section relabel

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- A statement with every jump target wrapped in `some`. -/
def relabelSome : TM2.Stmt Γ Λ σ → TM2.Stmt Γ (Option Λ) σ
  | .push k f q => .push k f (relabelSome q)
  | .peek k f q => .peek k f (relabelSome q)
  | .pop k f q => .pop k f (relabelSome q)
  | .load a q => .load a (relabelSome q)
  | .branch f q₁ q₂ => .branch f (relabelSome q₁) (relabelSome q₂)
  | .goto f => .goto (fun s => some (f s))
  | .halt => .halt

/-- A configuration with its label wrapped in `some`. -/
def embCfg (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ (Option Λ) σ :=
  ⟨c.l.map some, c.var, c.stk⟩

theorem stepAux_relabelSome (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (relabelSome q) v S = embCfg (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [relabelSome, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

end relabel

/-- The machine `tm` with labels `Option tm.Λ`. -/
def liftFin (tm : FinTM2) : FinTM2 :=
  @FinTM2.mk tm.K tm.kDecidableEq tm.kFin tm.k₀ tm.k₁ tm.Γ (Option tm.Λ) (some tm.main)
    (@instFintypeOption _ tm.ΛFin) tm.σ tm.initialState tm.σFin tm.Γk₀Fin
    (fun l => l.elim TM2.Stmt.halt (fun l => relabelSome (tm.m l)))

/-- The oracle machine that never asks. -/
def liftTM (tm : FinTM2) : OracleTM2 where
  tm := liftFin tm
  kq := tm.k₀
  queryBit := fun _ => true
  ask := none
  yes := none
  no := none

theorem liftTM_step (tm : FinTM2) (A : Language Bool) (c : tm.Cfg) :
    (liftTM tm).step A (embCfg c) =
      (tm.step c).map embCfg := by
  let := tm.kDecidableEq
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
    unfold OracleTM2.step
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h; cases h))]
    show some (TM2.stepAux (relabelSome (tm.m l)) v S) = some (embCfg (TM2.stepAux (tm.m l) v S))
    rw [stepAux_relabelSome]

theorem liftTM_iter (tm : FinTM2) (A : Language Bool) (n : ℕ) (o : Option tm.Cfg) :
    (flip bind ((liftTM tm).step A))^[n] (o.map embCfg) =
      ((flip bind tm.step)^[n] o).map embCfg := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    cases o with
    | none => rfl
    | some c => exact liftTM_step tm A c

theorem P_subset_OracleP (A : Language Bool) : P ⊆ OracleP A := by
  rintro L ⟨f, hf, ⟨c⟩⟩
  refine ⟨c.time, f, liftTM c.tm, c.inputAlphabet, c.outputAlphabet, hf, fun a => ?_⟩
  obtain ⟨⟨n, hn⟩, hle⟩ := c.outputsFun a
  refine ⟨⟨⟨n, ?_⟩, hle⟩⟩
  have := liftTM_iter c.tm A n (some (initList c.tm (a.map c.inputAlphabet.invFun)))
  rw [hn] at this
  exact this

end PEqualNP.Library.Helpers
