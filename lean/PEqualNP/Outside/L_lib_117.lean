import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open Turing PEqualNP.Library

private inductive Stack | input | output
  deriving DecidableEq

private instance : Fintype Stack :=
  ⟨{.input, .output}, by intro k; cases k <;> simp⟩

private inductive Label | ask | yes | no
  deriving DecidableEq

private instance : Fintype Label :=
  ⟨{.ask, .yes, .no}, by intro l; cases l <;> simp⟩

private abbrev Alphabet : Stack → Type := fun _ => Bool

private def program : Label → TM2.Stmt Alphabet Label Unit
  | .ask => .halt
  | .yes => .push Stack.output (fun _ => true) .halt
  | .no => .push Stack.output (fun _ => false) .halt

private abbrev bitMachine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .ask
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

/- The oracle reads the input stack from bottom to top and clears it in one step. -/
private abbrev inputOracle : OracleTM2 where
  tm := bitMachine
  kq := .input
  queryBit := id
  ask := .ask
  yes := .yes
  no := .no

private def stackContents (x y : List Bool) : ∀ k, List (Alphabet k)
  | .input => x
  | .output => y

private abbrev Cfg := TM2.Cfg Alphabet Label Unit

private def answerLabel : Bool → Label
  | true => .yes
  | false => .no

private noncomputable def step (A : Language Bool) : Cfg → Option Cfg :=
  inputOracle.step A

private theorem startCfg (x : List Bool) :
    initList inputOracle.tm x = (⟨some .ask, (), stackContents x []⟩ : Cfg) := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [inputOracle, bitMachine, stackContents]

private theorem stopCfg (b : Bool) :
    haltList inputOracle.tm [b] = (⟨none, (), stackContents [] [b]⟩ : Cfg) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [inputOracle, bitMachine, stackContents]

open Classical in
private theorem askStep (A : Language Bool) (x : List Bool) :
    step A ⟨some .ask, (), stackContents x []⟩ =
      some ⟨some (answerLabel (decide (x.reverse ∈ A))), (), stackContents [] []⟩ := by
  have clearInput :
      Function.update (stackContents x []) Stack.input [] = stackContents [] [] := by
    funext k
    cases k <;> simp [stackContents]
  unfold step OracleTM2.step
  rw [ite_eq_left rfl]
  change some (⟨some (if x.reverse.map id ∈ A then .yes else .no), (),
    Function.update (stackContents x []) Stack.input []⟩ : Cfg) = _
  rw [List.map_id, clearInput]
  by_cases hx : x.reverse ∈ A <;> simp [hx, answerLabel]

private theorem answerStep (A : Language Bool) (b : Bool) :
    step A ⟨some (answerLabel b), (), stackContents [] []⟩ =
      some ⟨none, (), stackContents [] [b]⟩ := by
  have writeOutput (v : Bool) :
      Function.update (stackContents [] []) Stack.output [v] = stackContents [] [v] := by
    funext k
    cases k <;> simp [stackContents]
  cases b <;>
    (unfold step OracleTM2.step
     rw [ite_eq_right (by simp [inputOracle, answerLabel])]
     change TM2.step program _ = _
     simp only [answerLabel, TM2.step, program, TM2.stepAux, stackContents, writeOutput])

open Classical in
theorem L_lib_117 :
    (∃ c : ℕ, ∀ A : Language Bool, PEqualNP.Library.OracleDecidableInTime A (fun x : List Bool => x) {x : List Bool | x ∈ A} (fun _ : ℕ => c)) ∨ (∃ c : ℕ, ∀ A : Language Bool, PEqualNP.Library.OracleDecidableInTime A (fun x : List Bool => x) {x : List Bool | x.reverse ∈ A} (fun _ : ℕ => c)) := by
  refine Or.inr ⟨2, fun A => ?_⟩
  refine ⟨fun x => decide (x.reverse ∈ A), inputOracle, Equiv.refl Bool, Equiv.refl Bool, ?_, ?_⟩
  · intro x
    simp
  · intro x
    have hInput : x.map (Equiv.refl Bool).symm = x := by simp
    have hOutput :
        (Computability.encodeBool (decide (x.reverse ∈ A))).map (Equiv.refl Bool).symm =
          [decide (x.reverse ∈ A)] := by simp [Computability.encodeBool]
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    dsimp only
    rw [hInput, hOutput, startCfg, stopCfg, Function.iterate_succ_apply, Function.iterate_one]
    change (step A ⟨some .ask, (), stackContents x []⟩).bind (step A) = _
    rw [askStep]
    exact answerStep A _

end PEqualNP.Outside
