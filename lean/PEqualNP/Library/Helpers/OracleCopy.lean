import PEqualNP.Library.Machines.Run

/-!
# An oracle machine deciding its own oracle

Helper module (proofs only, no statement may use it).

The oracle machine `ocM` pops each input symbol and pushes it on the query stack, so that the
query stack read bottom to top is the input. It then asks the oracle and writes `true` on a yes
answer, `false` on a no answer. On an input of length `n` it halts after `n + 3` steps.
-/

namespace PEqualNP.Library.Helpers.OracleCopy

open Turing PEqualNP.Library.Machines

/-- Stacks: input, output, query. -/
inductive CK | inp | out | qry
  deriving DecidableEq

instance : Fintype CK :=
  ⟨{.inp, .out, .qry}, by intro x; cases x <;> simp⟩

/-- Stack alphabets: bits everywhere. -/
abbrev CΓ : CK → Type := fun _ => Bool

/-- Labels. -/
inductive CL | main | ask | yes | no
  deriving DecidableEq

instance : Fintype CL :=
  ⟨{.main, .ask, .yes, .no}, by intro x; cases x <;> simp⟩

/-- Internal state: the last symbol read. -/
abbrev CS : Type := Option Bool

/-- The program. -/
def ocProg : CL → TM2.Stmt CΓ CL CS
  | .main =>
    .pop CK.inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push CK.qry (fun s => s.getD false) (.load (fun _ => none) (.goto fun _ => .main)))
        (.goto fun _ => .ask))
  | .ask => .halt
  | .yes => .push CK.out (fun _ => true) .halt
  | .no => .push CK.out (fun _ => false) .halt

/-- The machine. -/
def ocTM : FinTM2 where
  K := CK
  k₀ := CK.inp
  k₁ := CK.out
  Γ := CΓ
  Λ := CL
  main := .main
  σ := CS
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := ocProg

/-- The oracle machine. -/
def ocM : OracleTM2 where
  tm := ocTM
  kq := CK.qry
  queryBit := id
  ask := .ask
  yes := .yes
  no := .no

/-- The stacks, given by their contents. -/
def stks (l u q : List Bool) : ∀ k, List (CΓ k)
  | .inp => l
  | .out => u
  | .qry => q

theorem set_inp (l l' u q : List Bool) :
    Function.update (stks l u q) CK.inp l' = stks l' u q := by
  funext k; cases k <;> rfl

theorem set_out (l u u' q : List Bool) :
    Function.update (stks l u q) CK.out u' = stks l u' q := by
  funext k; cases k <;> rfl

theorem set_qry (l u q q' : List Bool) :
    Function.update (stks l u q) CK.qry q' = stks l u q' := by
  funext k; cases k <;> rfl

/-- Configurations. -/
abbrev CCfg : Type := TM2.Cfg CΓ CL CS

theorem main_nil (q : List Bool) :
    TM2.step ocProg (⟨some .main, none, stks [] [] q⟩ : CCfg) =
      some ⟨some .ask, none, stks [] [] q⟩ := by
  simp only [TM2.step, ocProg, TM2.stepAux, stks, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, set_inp]

theorem main_cons (a : Bool) (l q : List Bool) :
    TM2.step ocProg (⟨some .main, none, stks (a :: l) [] q⟩ : CCfg) =
      some ⟨some .main, none, stks l [] (a :: q)⟩ := by
  simp only [TM2.step, ocProg, TM2.stepAux, stks, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, set_inp, set_qry, Option.getD_some]

/-- Step functions agreeing with the machine away from the label `ask`. -/
def Agrees (f : CCfg → Option CCfg) : Prop :=
  ∀ c : CCfg, c.l ≠ some .ask → f c = TM2.step ocProg c

theorem step_main {f : CCfg → Option CCfg} (hf : Agrees f) (l q : List Bool) :
    (flip bind f)^[l.length + 1] (some (⟨some .main, none, stks l [] q⟩ : CCfg)) =
      some ⟨some .ask, none, stks [] [] (l.reverse ++ q)⟩ := by
  induction l generalizing q with
  | nil => exact (hf _ (by simp)).trans (main_nil q)
  | cons x l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind f)^[l.length + 1] (f _) = _
    rw [hf _ (by simp), main_cons, ih]
    simp

theorem agrees_oracle (A : Language Bool) : Agrees (ocM.step A) := by
  intro c hc
  unfold OracleTM2.step
  split
  · exact absurd ‹_› hc
  · rfl

theorem yes_step :
    TM2.step ocProg (⟨some .yes, none, stks [] [] []⟩ : CCfg) =
      some ⟨none, none, stks [] [true] []⟩ := by
  simp only [TM2.step, ocProg, TM2.stepAux, stks, set_out]

theorem no_step :
    TM2.step ocProg (⟨some .no, none, stks [] [] []⟩ : CCfg) =
      some ⟨none, none, stks [] [false] []⟩ := by
  simp only [TM2.step, ocProg, TM2.stepAux, stks, set_out]

/-- The oracle step, typed on configurations of the machine. -/
noncomputable def F (A : Language Bool) : CCfg → Option CCfg := ocM.step A

open Classical in
theorem ask_step (A : Language Bool) (q : List Bool) :
    F A (⟨some .ask, none, stks [] [] q⟩ : CCfg) =
      some ⟨some (if q.reverse ∈ A then .yes else .no), none, stks [] [] []⟩ := by
  unfold F OracleTM2.step
  split
  swap
  · exact absurd rfl ‹_›
  show some (⟨some (if (q.reverse.map id) ∈ A then CL.yes else CL.no), none,
    Function.update (stks [] [] q) CK.qry []⟩ : CCfg) = _
  rw [set_qry, List.map_id]

open Classical in
/-- The run on configurations. -/
theorem oc_iter (A : Language Bool) (x : List Bool) :
    (flip bind (F A))^[1 + 1 + (x.length + 1)]
      (some (⟨some .main, none, stks x [] []⟩ : CCfg)) =
      some (⟨none, none, stks [] [decide (x ∈ A)] []⟩ : CCfg) := by
  have hf : Agrees (F A) := agrees_oracle A
  rw [Function.iterate_add_apply, step_main hf, List.append_nil]
  show (flip bind (F A))^[1] ((F A) (⟨some .ask, _, _⟩ : CCfg)) = _
  rw [ask_step, List.reverse_reverse]
  show (F A) _ = _
  rw [hf _ (by split <;> simp)]
  by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte]
    rw [yes_step]
    simp
  · simp only [hx, ↓reduceIte]
    rw [no_step]
    simp

theorem map_refl {α : Type} (l : List α) : l.map (Equiv.refl α).symm = l := by simp

open Classical in
/-- The run of the oracle machine. -/
theorem oc_run (A : Language Bool) (x : List Bool) :
    Nonempty (StateTransition.EvalsToInTime (ocM.step A)
      (initList ocM.tm (x.map (Equiv.refl Bool).symm))
      (some (haltList ocM.tm ((Computability.encodeBool (decide (x ∈ A))).map
        (Equiv.refl Bool).symm)))
      (x.length + 3)) := by
  have hi : initList ocM.tm (x.map (Equiv.refl Bool).symm) =
      (⟨some .main, none, stks x [] []⟩ : CCfg) := by
    refine (congrArg (fun l => initList ocM.tm l) (map_refl _)).trans ?_
    refine (initList_eq ocM.tm _).trans ?_
    show (⟨some .main, none, _⟩ : CCfg) = _
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList ocM.tm ((Computability.encodeBool (decide (x ∈ A))).map
        (Equiv.refl Bool).symm) =
      (⟨none, none, stks [] [decide (x ∈ A)] []⟩ : CCfg) := by
    refine (congrArg (fun l => haltList ocM.tm l) (map_refl _)).trans ?_
    refine (haltList_eq ocM.tm _).trans ?_
    show (⟨none, none, _⟩ : CCfg) = _
    congr 1
    funext k; cases k <;> rfl
  rw [hi, ho]
  refine ⟨⟨_, oc_iter A x⟩, ?_⟩
  dsimp only
  omega

end PEqualNP.Library.Helpers.OracleCopy
