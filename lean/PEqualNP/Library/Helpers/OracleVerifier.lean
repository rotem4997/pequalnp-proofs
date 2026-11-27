import PEqualNP.Library.Machines.Run

/-!
# An oracle verifier for "some string of the same length is in the oracle"

Helper module (proofs only, no statement may use it).

The oracle machine `ovM` reads an encoded pair `x.map inl ++ w.map inr` from its input stack.
For each `inl` it pushes a marker on a counter stack; for each `inr b` it pushes `b` on the
query stack and pops a marker (remembering a mismatch when there is none). Leftover markers are
then popped, also recording a mismatch. It asks the oracle about the query stack, which holds `w`
bottom to top, and writes `true` iff the answer is yes and there was no mismatch.
-/

namespace PEqualNP.Library.Helpers.OracleVerifier

open Turing PEqualNP.Library.Machines

/-- Stacks: input, output, counter, query. -/
inductive OK | inp | out | cnt | qry
  deriving DecidableEq

instance : Fintype OK :=
  ⟨{.inp, .out, .cnt, .qry}, by intro x; cases x <;> simp⟩

/-- Stack alphabets. -/
@[reducible] def OΓ : OK → Type
  | .inp => Bool ⊕ Bool
  | .out => Bool
  | .cnt => Unit
  | .qry => Bool

/-- Labels. -/
inductive OL | main | drain | ask | yes | no
  deriving DecidableEq

instance : Fintype OL :=
  ⟨{.main, .drain, .ask, .yes, .no}, by intro x; cases x <;> simp⟩

/-- Internal state: mismatch flag and the last symbol read. -/
abbrev OS : Type := Bool × Option (Bool ⊕ Bool)

/-- The bit carried by an `inr` symbol. -/
def bitOf : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inr b) => b
  | _ => false

/-- Is the symbol an `inl`. -/
def isInl : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

/-- The program. -/
def ovProg : OL → TM2.Stmt OΓ OL OS
  | .main =>
    .pop OK.inp (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isInl s.2)
          (.push OK.cnt (fun _ => ()) (.goto fun _ => .main))
          (.push OK.qry (fun s => bitOf s.2)
            (.pop OK.cnt (fun s o => (s.1 || o.isNone, s.2)) (.goto fun _ => .main))))
        (.goto fun _ => .drain))
  | .drain =>
    .pop OK.cnt (fun s o => (s.1 || o.isSome, o.map fun _ => Sum.inl true))
      (.branch (fun s => s.2.isSome) (.goto fun _ => .drain) (.goto fun _ => .ask))
  | .ask => .halt
  | .yes => .push OK.out (fun s => !s.1) (.load (fun _ => (false, none)) .halt)
  | .no => .push OK.out (fun _ => false) (.load (fun _ => (false, none)) .halt)

/-- The machine. -/
def ovTM : FinTM2 where
  K := OK
  k₀ := OK.inp
  k₁ := OK.out
  Γ := OΓ
  Λ := OL
  main := .main
  σ := OS
  initialState := (false, none)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := ovProg

/-- The oracle machine. -/
def ovM : OracleTM2 where
  tm := ovTM
  kq := OK.qry
  queryBit := id
  ask := .ask
  yes := .yes
  no := .no

/-- The stacks, given by their contents. -/
def stks (l : List (Bool ⊕ Bool)) (u : List Bool) (c : List Unit) (q : List Bool) :
    ∀ k, List (OΓ k)
  | .inp => l
  | .out => u
  | .cnt => c
  | .qry => q

theorem set_inp (l l' : List (Bool ⊕ Bool)) u c q :
    Function.update (stks l u c q) OK.inp l' = stks l' u c q := by
  funext k; cases k <;> rfl

theorem set_out (l : List (Bool ⊕ Bool)) u u' c q :
    Function.update (stks l u c q) OK.out u' = stks l u' c q := by
  funext k; cases k <;> rfl

theorem set_cnt (l : List (Bool ⊕ Bool)) u c c' q :
    Function.update (stks l u c q) OK.cnt c' = stks l u c' q := by
  funext k; cases k <;> rfl

theorem set_qry (l : List (Bool ⊕ Bool)) u c q q' :
    Function.update (stks l u c q) OK.qry q' = stks l u c q' := by
  funext k; cases k <;> rfl

/-- Configurations. -/
abbrev OCfg : Type := TM2.Cfg OΓ OL OS

/-- The scan of the input: mismatch flag, counter, query stack. -/
def scan : List (Bool ⊕ Bool) → Bool → List Unit → List Bool → Bool × List Unit × List Bool
  | [], m, c, q => (m, c, q)
  | Sum.inl _ :: l, m, c, q => scan l m (() :: c) q
  | Sum.inr b :: l, m, c, q => scan l (m || c.isEmpty) c.tail (b :: q)

theorem fb (c : OCfg) : flip bind (TM2.step ovProg) (some c) = TM2.step ovProg c := rfl

theorem main_nil (m : Bool) (o : Option (Bool ⊕ Bool)) (c : List Unit) (q : List Bool) :
    TM2.step ovProg (⟨some .main, (m, o), stks [] [] c q⟩ : OCfg) =
      some ⟨some .drain, (m, none), stks [] [] c q⟩ := by
  simp only [TM2.step, ovProg, TM2.stepAux, stks, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, set_inp]

theorem main_inl (a : Bool) (l : List (Bool ⊕ Bool)) (m : Bool) (o : Option (Bool ⊕ Bool))
    (c : List Unit) (q : List Bool) :
    TM2.step ovProg (⟨some .main, (m, o), stks (Sum.inl a :: l) [] c q⟩ : OCfg) =
      some ⟨some .main, (m, some (Sum.inl a)), stks l [] (() :: c) q⟩ := by
  simp only [TM2.step, ovProg, TM2.stepAux, stks, List.head?_cons, List.tail_cons,
    Option.isSome_some, isInl, Bool.cond_true, set_inp, set_cnt]

theorem main_inr (b : Bool) (l : List (Bool ⊕ Bool)) (m : Bool) (o : Option (Bool ⊕ Bool))
    (c : List Unit) (q : List Bool) :
    TM2.step ovProg (⟨some .main, (m, o), stks (Sum.inr b :: l) [] c q⟩ : OCfg) =
      some ⟨some .main, (m || c.isEmpty, some (Sum.inr b)), stks l [] c.tail (b :: q)⟩ := by
  simp only [TM2.step, ovProg, TM2.stepAux, stks, List.head?_cons, List.tail_cons,
    Option.isSome_some, isInl, Bool.cond_true, Bool.cond_false, set_inp, set_qry, set_cnt, bitOf]
  cases c <;> rfl

/-- Step functions agreeing with the machine away from the label `ask`. -/
def Agrees (f : OCfg → Option OCfg) : Prop :=
  ∀ c : OCfg, c.l ≠ some .ask → f c = TM2.step ovProg c

theorem step_main {f : OCfg → Option OCfg} (hf : Agrees f) (l : List (Bool ⊕ Bool)) (m : Bool)
    (o : Option (Bool ⊕ Bool)) (c : List Unit) (q : List Bool) :
    (flip bind f)^[l.length + 1]
        (some (⟨some .main, (m, o), stks l [] c q⟩ : OCfg)) =
      some ⟨some .drain, ((scan l m c q).1, none), stks [] [] (scan l m c q).2.1
        (scan l m c q).2.2⟩ := by
  induction l generalizing m o c q with
  | nil => exact (hf _ (by simp)).trans (main_nil m o c q)
  | cons x l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind f)^[l.length + 1] (f _) = _
    rw [hf _ (by simp)]
    cases x with
    | inl a => rw [main_inl, ih]; rfl
    | inr b => rw [main_inr, ih]; rfl

theorem step_drain {f : OCfg → Option OCfg} (hf : Agrees f) (m : Bool)
    (o : Option (Bool ⊕ Bool)) (c : List Unit) (q : List Bool) :
    (flip bind f)^[c.length + 1]
        (some (⟨some .drain, (m, o), stks [] [] c q⟩ : OCfg)) =
      some ⟨some .ask, (m || !c.isEmpty, none), stks [] [] [] q⟩ := by
  induction c generalizing m o with
  | nil =>
    show f (⟨some .drain, (m, o), stks [] [] [] q⟩ : OCfg) = _
    rw [hf _ (by simp)]
    simp only [TM2.step, ovProg, TM2.stepAux, stks, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, Option.map_none, Bool.or_false, set_cnt,
      List.isEmpty_nil, Bool.not_true]
  | cons x c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind f)^[c.length + 1] (f _) = _
    rw [hf _ (by simp)]
    have e : TM2.step ovProg (⟨some .drain, (m, o), stks [] [] (x :: c) q⟩ : OCfg) =
        some ⟨some .drain, (true, some (Sum.inl true)), stks [] [] c q⟩ := by
      simp only [TM2.step, ovProg, TM2.stepAux, stks, List.head?_cons, List.tail_cons,
        Option.isSome_some, Option.map_some, Bool.cond_true, Bool.or_true, set_cnt]
    rw [e, ih]
    simp

theorem agrees_oracle (A : Language Bool) : Agrees (ovM.step A) := by
  intro c hc
  unfold OracleTM2.step
  split
  · exact absurd ‹_› hc
  · rfl

theorem yes_step (m : Bool) (o : Option (Bool ⊕ Bool)) :
    TM2.step ovProg (⟨some .yes, (m, o), stks [] [] [] []⟩ : OCfg) =
      some ⟨none, (false, none), stks [] [!m] [] []⟩ := by
  simp only [TM2.step, ovProg, TM2.stepAux, stks, set_out]

theorem no_step (m : Bool) (o : Option (Bool ⊕ Bool)) :
    TM2.step ovProg (⟨some .no, (m, o), stks [] [] [] []⟩ : OCfg) =
      some ⟨none, (false, none), stks [] [false] [] []⟩ := by
  simp only [TM2.step, ovProg, TM2.stepAux, stks, set_out]

/-- The oracle step, typed on configurations of the machine. -/
noncomputable def F (A : Language Bool) : OCfg → Option OCfg := ovM.step A

open Classical in
theorem ask_step (A : Language Bool) (m : Bool) (o : Option (Bool ⊕ Bool)) (q : List Bool) :
    F A (⟨some .ask, (m, o), stks [] [] [] q⟩ : OCfg) =
      some ⟨some (if q.reverse ∈ A then .yes else .no), (m, o), stks [] [] [] []⟩ := by
  unfold F OracleTM2.step
  split
  swap
  · exact absurd rfl ‹_›
  show some (⟨some (if (q.reverse.map id) ∈ A then OL.yes else OL.no), (m, o),
    Function.update (stks [] [] [] q) OK.qry []⟩ : OCfg) = _
  rw [set_qry, List.map_id]

theorem unit_list_eq : ∀ a b : List Unit, a.length = b.length → a = b
  | [], [], _ => rfl
  | () :: a, () :: b, h => by rw [unit_list_eq a b (by simpa using h)]

theorem scan_inl (x : List Bool) (l : List (Bool ⊕ Bool)) (m : Bool) (c : List Unit)
    (q : List Bool) :
    scan (x.map Sum.inl ++ l) m c q = scan l m (List.replicate x.length () ++ c) q := by
  induction x generalizing c with
  | nil => rfl
  | cons a x ih =>
    show scan (x.map Sum.inl ++ l) m (() :: c) q = _
    rw [ih]
    congr 1
    apply unit_list_eq
    simp; omega

theorem scan_inr (w : List Bool) (m : Bool) (c : List Unit) (q : List Bool) :
    scan (w.map Sum.inr) m c q =
      (m || decide (c.length < w.length), c.drop w.length, w.reverse ++ q) := by
  induction w generalizing m c q with
  | nil => simp [scan]
  | cons b w ih =>
    show scan (w.map Sum.inr) (m || c.isEmpty) c.tail (b :: q) = _
    rw [ih]
    cases c with
    | nil => simp
    | cons u c =>
      simp only [List.isEmpty_cons, Bool.or_false, List.tail_cons, List.length_cons,
        List.drop_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        Prod.mk.injEq, and_true]
      congr 1

theorem map_refl {α : Type} (l : List α) : l.map (Equiv.refl α).symm = l := by simp

open Classical in
/-- The run on configurations. -/
theorem ov_iter (A : Language Bool) (x w : List Bool) :
    (flip bind (F A))^[1 + 1 + (x.length - w.length + 1) +
        ((encodePair (x, w)).length + 1)]
      (some (⟨some .main, (false, none), stks (encodePair (x, w)) [] [] []⟩ : OCfg)) =
      some (⟨none, (false, none), stks [] [decide (w.length = x.length ∧ w ∈ A)] [] []⟩ :
        OCfg) := by
  have hs : scan (encodePair (x, w)) false [] [] =
      (decide (x.length < w.length), List.replicate (x.length - w.length) (), w.reverse) := by
    simp only [encodePair]
    rw [scan_inl, scan_inr]
    simp
  have hf : Agrees (F A) := agrees_oracle A
  rw [Function.iterate_add_apply, step_main hf, hs, Function.iterate_add_apply,
    show x.length - w.length + 1 = (List.replicate (x.length - w.length) ()).length + 1 by simp]
  dsimp only
  rw [step_drain hf]
  show (flip bind (F A))^[1]
    ((F A) (⟨some .ask, _, _⟩ : OCfg)) = _
  rw [ask_step, List.reverse_reverse]
  show (F A) _ = _
  rw [hf _ (by split <;> simp)]
  by_cases hw : w ∈ A
  · simp only [hw, ↓reduceIte]
    rw [yes_step]
    congr 4
    by_cases h : w.length = x.length
    · simp [h]
    · simp only [List.isEmpty_replicate]
      simp [h]; omega
  · simp only [hw, ↓reduceIte]
    rw [no_step]
    simp

open Classical in
/-- The run of the oracle verifier. -/
theorem ov_run (A : Language Bool) (x w : List Bool) :
    Nonempty (StateTransition.EvalsToInTime (ovM.step A)
      (initList ovM.tm ((encodePair (x, w)).map (Equiv.refl (Bool ⊕ Bool)).symm))
      (some (haltList ovM.tm ((Computability.encodeBool
        (decide (w.length = x.length ∧ w ∈ A))).map (Equiv.refl Bool).symm)))
      (2 * (encodePair (x, w)).length + 4)) := by
  have hl : (encodePair (x, w)).length = x.length + w.length := by simp [encodePair]
  have hi : initList ovM.tm ((encodePair (x, w)).map (Equiv.refl (Bool ⊕ Bool)).symm) =
      (⟨some .main, (false, none), stks (encodePair (x, w)) [] [] []⟩ : OCfg) := by
    refine (congrArg (fun l => initList ovM.tm l) (map_refl _)).trans ?_
    refine (initList_eq ovM.tm _).trans ?_
    show (⟨some .main, (false, none), _⟩ : OCfg) = _
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList ovM.tm ((Computability.encodeBool
        (decide (w.length = x.length ∧ w ∈ A))).map (Equiv.refl Bool).symm) =
      (⟨none, (false, none), stks [] [decide (w.length = x.length ∧ w ∈ A)] [] []⟩ : OCfg) := by
    refine (congrArg (fun l => haltList ovM.tm l) (map_refl _)).trans ?_
    refine (haltList_eq ovM.tm _).trans ?_
    show (⟨none, (false, none), _⟩ : OCfg) = _
    congr 1
    funext k; cases k <;> rfl
  rw [hi, ho]
  refine ⟨⟨_, ov_iter A x w⟩, ?_⟩
  dsimp only
  omega

end PEqualNP.Library.Helpers.OracleVerifier
