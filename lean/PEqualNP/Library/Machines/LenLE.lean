import PEqualNP.Library.Machines.Run

/-!
# A machine that decides whether the second string of a pair is no longer than the first

Helper module (proofs only, no statement may use it). It lives in its own namespace `LenCmp`, so
that it can be imported together with the multiplication machine. Four stacks: the input (tagged bits), two
unary counters and the output (one bit). The first loop moves the input onto the counters, one
mark per symbol of the first and of the second component. The second loop pops one mark from each
counter until one of them is empty: if the second counter is empty the answer is true, otherwise
the answer is false. An erasing loop then empties the other counter, writes the answer and halts.
On an input of length `n` it halts after at most `2 * n + 3` steps.
-/

namespace PEqualNP.Library.Machines.LenCmp

open Turing

/-- Stack alphabets: input, first counter, second counter, output. -/
@[reducible] def LΓ : Bool × Bool → Type
  | (false, false) => Bool ⊕ Bool
  | (false, true) => Unit
  | (true, false) => Unit
  | (true, true) => Bool

/-- Labels: split the input, compare the counters, erase the first or the second counter. -/
inductive LL : Type
  | split
  | cmp
  | eraseA
  | eraseB
  deriving DecidableEq

instance : Fintype LL :=
  Fintype.ofList [LL.split, LL.cmp, LL.eraseA, LL.eraseB] (fun x => by cases x <;> simp)

/-- The program. -/
def lenProg : LL → TM2.Stmt LΓ LL (Bool × Bool)
  | .split =>
    .pop (false, false) (fun _ o => (o.isSome, (o.map Sum.isRight).getD false))
      (.branch (fun s => s.1)
        (.branch (fun s => s.2)
          (.push (true, false) (fun _ => ()) (.goto fun _ => .split))
          (.push (false, true) (fun _ => ()) (.goto fun _ => .split)))
        (.goto fun _ => .cmp))
  | .cmp =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.pop (true, false) (fun s o => (s.1, o.isSome))
        (.branch (fun s => s.2)
          (.branch (fun s => s.1)
            (.goto fun _ => .cmp)
            (.load (fun _ => (false, false)) (.goto fun _ => .eraseB)))
          (.load (fun _ => (false, false)) (.goto fun _ => .eraseA))))
  | .eraseA =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseA)
        (.push (true, true) (fun _ => true) (.load (fun _ => (false, false)) .halt)))
  | .eraseB =>
    .pop (true, false) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseB)
        (.push (true, true) (fun _ => false) (.load (fun _ => (false, false)) .halt)))

/-- The machine. -/
def lenM : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := LΓ
  Λ := LL
  main := .split
  σ := Bool × Bool
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := lenProg

/-- The stacks: input, the two counters (as numbers), output. -/
def lst (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) : ∀ k, List (LΓ k)
  | (false, false) => l
  | (false, true) => List.replicate a ()
  | (true, false) => List.replicate b ()
  | (true, true) => o

theorem lst_in (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, false) = l := rfl

theorem lst_a (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, true) = List.replicate a () := rfl

theorem lst_b (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, false) = List.replicate b () := rfl

theorem lst_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, true) = o := rfl

theorem lst_set_in (l l' : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, false) l' = lst l' a b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (Bool ⊕ Bool)) (a a' b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, true) (List.replicate a' ()) = lst l a' b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (Bool ⊕ Bool)) (a b b' : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) (List.replicate b' ()) = lst l a b' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b0 (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) [] = lst l a 0 o :=
  lst_set_b l a b 0 o

theorem lst_set_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o o' : List Bool) :
    Function.update (lst l a b o) (true, true) o' = lst l a b o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (Bool ⊕ Bool)) :
    lst l 0 0 [] = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst [] 0 0 o = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

/-- Configurations of the machine. -/
abbrev LCfg : Type := TM2.Cfg LΓ LL (Bool × Bool)

/-- The step function on optional configurations. -/
abbrev lenStep : Option LCfg → Option LCfg := flip bind (TM2.step lenProg)

theorem split_inl (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inl x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, false), lst l (a + 1) b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inl, Option.getD_some, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_a, ← List.replicate_succ, lst_set_a]

theorem split_inr (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inr x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, true), lst l a (b + 1) o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inr, Option.getD_some, Bool.cond_true]
  rw [lst_set_in, lst_b, ← List.replicate_succ, lst_set_b]

theorem split_nil (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst [] a b o⟩ : LCfg) =
      some ⟨some .cmp, (false, false), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Option.map_none,
    Option.getD_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_ss (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] (a + 1) (b + 1) o⟩ : LCfg) =
      some ⟨some .cmp, (true, true), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
  rw [lst_set_a, lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem cmp_b0 (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] a 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (false, false), lst [] (a - 1) 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_b0]

theorem cmp_a0 (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (false, false), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.replicate_succ, List.head?_nil, List.head?_cons,
    List.tail_cons, Option.isSome_none, Option.isSome_some, Bool.cond_false, Bool.cond_true]
  rw [lst_set_b]

theorem eraseA_s (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] (a + 1) 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (true, s.2), lst [] a 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_a]

theorem eraseA_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (true :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem eraseB_s (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (true, s.2), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem eraseB_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (false :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b, List.tail_replicate, lst_set_b]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (Bool ⊕ Bool)) (a b : ℕ) (s : Bool × Bool),
      lenStep^[l.length + 1] (some (⟨some .split, s, lst l a b []⟩ : LCfg)) =
        some ⟨some .cmp, (false, false),
          lst [] (a + l.countP Sum.isLeft) (b + l.countP Sum.isRight) []⟩ := by
  intro l
  induction l with
  | nil => intro a b s; exact split_nil s a b []
  | cons x l ih =>
    intro a b s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inl x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, false), lst l (a + 1) b []⟩ := split_inl s x l a b []
      have h1 : a + 1 + l.countP Sum.isLeft =
          a + (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isRight =
          (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]
    | inr x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inr x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, true), lst l a (b + 1) []⟩ := split_inr s x l a b []
      have h1 : b + 1 + l.countP Sum.isRight =
          b + (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isLeft =
          (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]

theorem cmpLoopT :
    ∀ (b c : ℕ) (s : Bool × Bool),
      lenStep^[b + 1] (some (⟨some .cmp, s, lst [] (b + c) b []⟩ : LCfg)) =
        some ⟨some .eraseA, (false, false), lst [] (c - 1) 0 []⟩ := by
  intro b
  induction b with
  | zero =>
    intro c s
    rw [Nat.zero_add c]
    exact cmp_b0 s c []
  | succ b ih =>
    intro c s
    rw [Function.iterate_succ_apply]
    have hbc : b + 1 + c = b + c + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (b + 1 + c) (b + 1) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] (b + c) b []⟩ := by
      rw [hbc]; exact cmp_ss s (b + c) b []
    rw [e, ih]

theorem cmpLoopF :
    ∀ (a d : ℕ) (s : Bool × Bool),
      lenStep^[a + 1] (some (⟨some .cmp, s, lst [] a (a + 1 + d) []⟩ : LCfg)) =
        some ⟨some .eraseB, (false, false), lst [] 0 d []⟩ := by
  intro a
  induction a with
  | zero =>
    intro d s
    have h : 0 + 1 + d = d + 1 := by omega
    rw [h]
    exact cmp_a0 s d []
  | succ a ih =>
    intro d s
    rw [Function.iterate_succ_apply]
    have had : a + 1 + 1 + d = a + 1 + d + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (a + 1) (a + 1 + 1 + d) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] a (a + 1 + d) []⟩ := by
      rw [had]; exact cmp_ss s a (a + 1 + d) []
    rw [e, ih]

theorem eraseALoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseA, s, lst [] n 0 []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [true]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseA_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseA, s, lst [] (n + 1) 0 []⟩ : LCfg)) =
        some ⟨some .eraseA, (true, s.2), lst [] n 0 []⟩ := eraseA_s s n []
    rw [e, ih]

theorem eraseBLoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseB, s, lst [] 0 n []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [false]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseB_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseB, s, lst [] 0 (n + 1) []⟩ : LCfg)) =
        some ⟨some .eraseB, (true, s.2), lst [] 0 n []⟩ := eraseB_s s n []
    rw [e, ih]

theorem len_run (l : List (Bool ⊕ Bool)) (a b : ℕ) (ha : l.countP Sum.isLeft = a)
    (hb : l.countP Sum.isRight = b) (hab : a + b ≤ l.length) :
    ∃ n, n ≤ 2 * l.length + 3 ∧
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
  have hs := splitLoop l 0 0 (false, false)
  rw [Nat.zero_add, Nat.zero_add, ha, hb] at hs
  have key : ∀ n : ℕ,
      lenStep^[n] (some (⟨some .split, (false, false), lst l 0 0 []⟩ : LCfg)) =
        some (⟨none, (false, false), lst [] 0 0 [decide (b ≤ a)]⟩ : LCfg) →
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
    intro n h
    refine (congrArg (fun c => lenStep^[n] (some c)) (initList_eq lenM l)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq lenM [decide (b ≤ a)])).symm)
    show lenStep^[n]
      (some (⟨some .split, (false, false), Function.update (fun _ => []) (false, false) l⟩ :
        LCfg)) =
      some (⟨none, (false, false),
        Function.update (fun _ => []) (true, true) [decide (b ≤ a)]⟩ : LCfg)
    rw [← lst_start, ← lst_end]
    exact h
  by_cases h : b ≤ a
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨(c - 1 + 1) + ((b + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (b ≤ b + c) = true := by simp
    rw [Function.iterate_add_apply _ (c - 1 + 1) _, Function.iterate_add_apply _ (b + 1) _, hs,
      cmpLoopT, eraseALoop, hd]
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    refine ⟨(d + 1) + ((a + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (a + 1 + d ≤ a) = false := decide_eq_false h
    rw [Function.iterate_add_apply _ (d + 1) _, Function.iterate_add_apply _ (a + 1) _, hs,
      cmpLoopF, eraseBLoop, hd]

theorem countP_isLeft_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isLeft = p.1.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isLeft =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isLeft = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.add_zero]

theorem countP_isRight_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isRight = p.2.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isRight =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isRight = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.zero_add]

theorem lenLE_run (p : List Bool × List Bool) :
    ∃ n, n ≤ 2 * (PEqualNP.Library.encodePair p).length + 3 ∧
      lenStep^[n] (some (initList lenM (PEqualNP.Library.encodePair p))) =
        some (haltList lenM [decide (p.2.length ≤ p.1.length)]) :=
  len_run (PEqualNP.Library.encodePair p) p.1.length p.2.length
    (countP_isLeft_encodePair p) (countP_isRight_encodePair p)
    (by simp [PEqualNP.Library.encodePair])

/-- Whether the second component of a pair is no longer than the first is decidable in at most
`2 * n + 3` steps. -/
theorem lenLE_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length))) :=
  ⟨{
    tm := lenM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := Classical.choose (lenLE_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.2.length ≤ p.1.length)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.2.length ≤ p.1.length))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => lenStep^[Classical.choose (lenLE_run p)]
            (some (initList lenM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((Classical.choose_spec (lenLE_run p)).2.trans
              (congrArg (fun x => some (haltList lenM x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (lenLE_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.Library.Machines.LenCmp
