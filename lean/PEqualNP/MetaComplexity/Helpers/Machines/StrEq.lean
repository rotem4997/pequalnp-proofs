import PEqualNP.Library.Machines.FirstGRun

/-!
# A machine that decides whether the two strings of a pair are equal

Helper module (proofs only, no statement may use it). The alphabet `A` is any finite type with
decidable equality; the input is the generic pair over `A ⊕ A`. Four stacks: the input, one
store for each component and the output (one bit). The first loop moves the input onto the two
stores, by tag; this reverses both components, which does not change whether they are equal.
The second loop pops one symbol from each store, and keeps a flag that stays true as long as the
two popped symbols agree (a symbol against an empty store disagrees). When both stores are empty
the flag is written to the output. On an input of length `n` the machine halts after at most
`2 * n + 2` steps.

The stores hold optional symbols, so that a push never needs a default symbol of `A`.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open Turing PEqualNP.Library.Machines

namespace StrEq

/-- Stack alphabets: input, first store, second store, output. -/
@[reducible] def SΓ (A : Type) : Bool × Bool → Type
  | (false, false) => A ⊕ A
  | (false, true) => Option A
  | (true, false) => Option A
  | (true, true) => Bool

/-- Labels: split the input, compare the stores. -/
inductive SL : Type
  | split
  | cmp
  deriving DecidableEq

instance : Fintype SL :=
  Fintype.ofList [SL.split, SL.cmp] (fun x => by cases x <;> simp)

/-- Internal state: two symbols in transit and the flag. -/
abbrev Sσ (A : Type) : Type := Option A × Option A × Bool

variable {A : Type}

/-- The program. -/
def eqProg [DecidableEq A] : SL → TM2.Stmt (SΓ A) SL (Sσ A)
  | .split =>
    .pop (false, false)
      (fun _ (o : Option (A ⊕ A)) => (o.bind Sum.getLeft?, o.bind Sum.getRight?, true))
      (.branch (fun s => s.1.isSome)
        (.push (false, true) (fun s => s.1) (.goto fun _ => .split))
        (.branch (fun s => s.2.1.isSome)
          (.push (true, false) (fun s => s.2.1) (.goto fun _ => .split))
          (.goto fun _ => .cmp)))
  | .cmp =>
    .pop (false, true) (fun s (o : Option (Option A)) => (o.join, s.2.1, s.2.2))
      (.pop (true, false) (fun s (o : Option (Option A)) => (s.1, o.join, s.2.2))
        (.branch (fun s => s.1.isSome || s.2.1.isSome)
          (.load (fun s => (none, none, s.2.2 && decide (s.1 = s.2.1))) (.goto fun _ => .cmp))
          (.push (true, true) (fun s => s.2.2) (.load (fun _ => (none, none, false)) .halt))))

/-- The machine. -/
def eqM (A : Type) [Fintype A] [DecidableEq A] : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := SΓ A
  Λ := SL
  main := .split
  σ := Sσ A
  initialState := (none, none, false)
  Γk₀Fin := inferInstanceAs (Fintype (A ⊕ A))
  m := eqProg

/-- The stacks: input, the two stores, output. -/
def lst (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) : ∀ k, List (SΓ A k)
  | (false, false) => l
  | (false, true) => u
  | (true, false) => v
  | (true, true) => o

theorem lst_in (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (false, false) = l := rfl

theorem lst_a (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (false, true) = u := rfl

theorem lst_b (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (true, false) = v := rfl

theorem lst_out (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (true, true) = o := rfl

theorem lst_set_in (l l' : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (false, false) l' = lst l' u v o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (A ⊕ A)) (u u' v : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (false, true) u' = lst l u' v o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (A ⊕ A)) (u v v' : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (true, false) v' = lst l u v' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_out (l : List (A ⊕ A)) (u v : List (Option A)) (o o' : List Bool) :
    Function.update (lst l u v o) (true, true) o' = lst l u v o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (A ⊕ A)) :
    lst l [] [] [] = Function.update (fun _ => [] : ∀ k, List (SΓ A k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst ([] : List (A ⊕ A)) [] [] o =
      Function.update (fun _ => [] : ∀ k, List (SΓ A k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

/-- Configurations of the machine. -/
abbrev SCfg (A : Type) : Type := TM2.Cfg (SΓ A) SL (Sσ A)

variable [DecidableEq A]

/-- The step function on optional configurations. -/
abbrev eqStep : Option (SCfg A) → Option (SCfg A) := flip bind (TM2.step eqProg)

theorem split_inl (s : Sσ A) (a : A) (l : List (A ⊕ A)) (u v : List (Option A))
    (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst (Sum.inl a :: l) u v o⟩ : SCfg A) =
      some ⟨some .split, (some a, none, true), lst l (some a :: u) v o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inl,
    Sum.getRight?_inl, Option.isSome_some, Bool.cond_true]
  rw [lst_set_in, lst_a, lst_set_a]

theorem split_inr (s : Sσ A) (a : A) (l : List (A ⊕ A)) (u v : List (Option A))
    (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst (Sum.inr a :: l) u v o⟩ : SCfg A) =
      some ⟨some .split, (none, some a, true), lst l u (some a :: v) o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inr,
    Sum.getRight?_inr, Option.isSome_some, Option.isSome_none, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_b, lst_set_b]

theorem split_nil (s : Sσ A) (u v : List (Option A)) (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst [] u v o⟩ : SCfg A) =
      some ⟨some .cmp, (none, none, true), lst [] u v o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.bind_none, Option.isSome_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_step (s : Sσ A) (x y : List A) (o : List Bool) (h : x ≠ [] ∨ y ≠ []) :
    TM2.step eqProg (⟨some .cmp, s, lst [] (x.map some) (y.map some) o⟩ : SCfg A) =
      some ⟨some .cmp, (none, none, s.2.2 && decide (x.head? = y.head?)),
        lst [] (x.tail.map some) (y.tail.map some) o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_a, lst_set_a, lst_b, lst_set_b]
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp at h ⊢

theorem cmp_nil (s : Sσ A) (o : List Bool) :
    TM2.step eqProg (⟨some .cmp, s, lst [] [] [] o⟩ : SCfg A) =
      some ⟨none, (none, none, false), lst [] [] [] (s.2.2 :: o)⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_a, lst_set_a, lst_b, lst_set_b]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none, Bool.or_self,
    Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (A ⊕ A)) (u v : List (Option A)) (s : Sσ A),
      eqStep^[l.length + 1] (some (⟨some .split, s, lst l u v []⟩ : SCfg A)) =
        some ⟨some .cmp, (none, none, true),
          lst [] ((l.filterMap Sum.getLeft?).reverse.map some ++ u)
            ((l.filterMap Sum.getRight?).reverse.map some ++ v) []⟩ := by
  intro l
  induction l with
  | nil => intro u v s; exact split_nil s u v []
  | cons x l ih =>
    intro u v s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : eqStep (some (⟨some .split, s, lst (Sum.inl a :: l) u v []⟩ : SCfg A)) =
          some ⟨some .split, (some a, none, true), lst l (some a :: u) v []⟩ :=
        split_inl s a l u v []
      rw [e, ih]
      simp [List.filterMap_cons]
    | inr a =>
      have e : eqStep (some (⟨some .split, s, lst (Sum.inr a :: l) u v []⟩ : SCfg A)) =
          some ⟨some .split, (none, some a, true), lst l u (some a :: v) []⟩ :=
        split_inr s a l u v []
      rw [e, ih]
      simp [List.filterMap_cons]

theorem flag_step (f : Bool) (x y : List A) :
    (f && decide (x.head? = y.head?) && decide (x.tail = y.tail)) = (f && decide (x = y)) := by
  rw [Bool.eq_iff_iff]
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp [and_assoc]
  intro _ _
  exact decide_eq_true_iff

theorem cmpLoop :
    ∀ (n : ℕ) (x y : List A) (s : Sσ A), max x.length y.length = n →
      eqStep^[n + 1] (some (⟨some .cmp, s, lst [] (x.map some) (y.map some) []⟩ : SCfg A)) =
        some ⟨none, (none, none, false), lst [] [] [] [s.2.2 && decide (x = y)]⟩ := by
  intro n
  induction n with
  | zero =>
    intro x y s h
    have hx : x = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : y = [] := List.length_eq_zero_iff.mp (by omega)
    subst hx hy
    rw [show (s.2.2 && decide (([] : List A) = [])) = s.2.2 by simp]
    exact cmp_nil s []
  | succ n ih =>
    intro x y s h
    rw [Function.iterate_succ_apply]
    have hne : x ≠ [] ∨ y ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rw [hc.1, hc.2] at h
      simp at h
    have e : eqStep (some (⟨some .cmp, s, lst [] (x.map some) (y.map some) []⟩ : SCfg A)) =
        some ⟨some .cmp, (none, none, s.2.2 && decide (x.head? = y.head?)),
          lst [] (x.tail.map some) (y.tail.map some) []⟩ := cmp_step s x y [] hne
    rw [e, ih x.tail y.tail _ (by simp only [List.length_tail]; omega)]
    exact congrArg (fun b => some (⟨none, (none, none, false), lst [] [] [] [b]⟩ : SCfg A))
      (flag_step s.2.2 x y)

theorem eq_run [Fintype A] (p : List A × List A) :
    ∃ n, n ≤ 2 * (Gen.gpair (p.1, p.2)).length + 2 ∧
      eqStep^[n] (some (initList (eqM A) (Gen.gpair (p.1, p.2)))) =
        some (haltList (eqM A) [decide (p.1 = p.2)]) := by
  have hs := splitLoop (Gen.gpair (p.1, p.2)) [] [] (none, none, false)
  rw [Gen.gpair_left, Gen.gpair_right, List.append_nil, List.append_nil] at hs
  have hc := cmpLoop (max p.1.reverse.length p.2.reverse.length) p.1.reverse p.2.reverse
    (none, none, true) rfl
  have hd : (true && decide (p.1.reverse = p.2.reverse)) = decide (p.1 = p.2) := by simp
  rw [hd] at hc
  refine ⟨(max p.1.reverse.length p.2.reverse.length + 1) +
    ((Gen.gpair (p.1, p.2)).length + 1), ?_, ?_⟩
  · rw [Gen.gpair_length, List.length_reverse, List.length_reverse]
    omega
  · refine (congrArg (fun c => eqStep^[_] (some c)) (initList_eq (eqM A) _)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq (eqM A) [decide (p.1 = p.2)])).symm)
    show eqStep^[_]
      (some (⟨some .split, (none, none, false),
        Function.update (fun _ => []) (false, false) (Gen.gpair (p.1, p.2))⟩ : SCfg A)) =
      some (⟨none, (none, none, false),
        Function.update (fun _ => []) (true, true) [decide (p.1 = p.2)]⟩ : SCfg A)
    rw [← lst_start, ← lst_end, Function.iterate_add_apply, hs, hc]

end StrEq

open StrEq in
/-- Whether the two strings of a pair are equal is decidable in at most `2 * n + 2` steps. -/
theorem strEq_polyTime {A : Type} [Fintype A] [DecidableEq A] :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : List A × List A => PEqualNP.Library.Machines.Gen.gpair (p.1, p.2))
      Computability.encodeBool (fun p : List A × List A => decide (p.1 = p.2))) :=
  ⟨{
    tm := eqM A
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun p =>
      { steps := Classical.choose (eq_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.1 = p.2)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.1 = p.2))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => eqStep^[Classical.choose (eq_run p)]
            (some (initList (eqM A) x))) (hm _ (Gen.gpair (p.1, p.2)))).trans
            ((Classical.choose_spec (eq_run p)).2.trans
              (congrArg (fun x => some (haltList (eqM A) x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (eq_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.MetaComplexity.Helpers.Machines
