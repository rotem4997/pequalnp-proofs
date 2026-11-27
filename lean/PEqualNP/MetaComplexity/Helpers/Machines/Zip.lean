import PEqualNP.Library.Machines.FirstGRun

/-!
# A machine that zips the two strings of a pair, padding the shorter one

Helper module (proofs only, no statement may use it). The input is the generic pair over
`A ⊕ B`; the output is the list of pairs of optional symbols, where a missing symbol marks the
end of the shorter string. Seven stacks: the input, a store for each component, a second store
for each component, a stack of pairs and the output.

1. `split`: empty the input; first components go to one store, second components to the other
   (both reversed).
2. `revA`, `revB`: move each store onto its second store (order restored).
3. `zip`: pop one symbol from each second store and push the pair, until both are empty (the
   pairs come out reversed).
4. `out`: move the pairs to the output (order restored).

On an input of length `n` the machine halts after at most `4 * n + 5` steps. The stores hold
optional symbols, so that a push never needs a default symbol.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open Turing PEqualNP.Library.Machines

namespace Zip

/-- The stacks. -/
inductive ZK : Type
  | I | SA | SB | TA | TB | P | O
  deriving DecidableEq

instance : Fintype ZK :=
  Fintype.ofList [ZK.I, ZK.SA, ZK.SB, ZK.TA, ZK.TB, ZK.P, ZK.O] (fun x => by cases x <;> simp)

/-- Stack alphabets. -/
@[reducible] def ZΓ (A B : Type) : ZK → Type
  | .I => A ⊕ B
  | .SA => Option A
  | .SB => Option B
  | .TA => Option A
  | .TB => Option B
  | .P => Option A × Option B
  | .O => Option A × Option B

/-- Labels. -/
inductive ZL : Type
  | split | revA | revB | zip | out
  deriving DecidableEq

instance : Fintype ZL :=
  Fintype.ofList [ZL.split, ZL.revA, ZL.revB, ZL.zip, ZL.out] (fun x => by cases x <;> simp)

/-- Internal state: two symbols in transit and a flag. -/
abbrev Zσ (A B : Type) : Type := Option A × Option B × Bool

variable {A B : Type}

/-- The program. -/
def zProg : ZL → TM2.Stmt (ZΓ A B) ZL (Zσ A B)
  | .split =>
    .pop .I (fun _ (o : Option (A ⊕ B)) => (o.bind Sum.getLeft?, o.bind Sum.getRight?, false))
      (.branch (fun s => s.1.isSome)
        (.push .SA (fun s => s.1) (.goto fun _ => .split))
        (.branch (fun s => s.2.1.isSome)
          (.push .SB (fun s => s.2.1) (.goto fun _ => .split))
          (.goto fun _ => .revA)))
  | .revA =>
    .pop .SA (fun s (o : Option (Option A)) => (o.join, s.2))
      (.branch (fun s => s.1.isSome)
        (.push .TA (fun s => s.1) (.goto fun _ => .revA))
        (.goto fun _ => .revB))
  | .revB =>
    .pop .SB (fun s (o : Option (Option B)) => (s.1, o.join, s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.push .TB (fun s => s.2.1) (.goto fun _ => .revB))
        (.goto fun _ => .zip))
  | .zip =>
    .pop .TA (fun s (o : Option (Option A)) => (o.join, s.2))
      (.pop .TB (fun s (o : Option (Option B)) => (s.1, o.join, s.2.2))
        (.branch (fun s => s.1.isSome || s.2.1.isSome)
          (.push .P (fun s => (s.1, s.2.1)) (.goto fun _ => .zip))
          (.goto fun _ => .out)))
  | .out =>
    .pop .P (fun _ (o : Option (Option A × Option B)) =>
        ((o.getD (none, none)).1, (o.getD (none, none)).2, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .O (fun s => (s.1, s.2.1)) (.goto fun _ => .out))
        (.load (fun _ => (none, none, false)) .halt))

/-- The machine. -/
def zM (A B : Type) [Fintype A] [Fintype B] : FinTM2 where
  K := ZK
  k₀ := .I
  k₁ := .O
  Γ := ZΓ A B
  Λ := ZL
  main := .split
  σ := Zσ A B
  initialState := (none, none, false)
  Γk₀Fin := inferInstanceAs (Fintype (A ⊕ B))
  m := zProg

/-- The contents of the seven stacks. -/
def lst (l : List (A ⊕ B)) (sa : List (Option A)) (sb : List (Option B)) (ta : List (Option A))
    (tb : List (Option B)) (p o : List (Option A × Option B)) : ∀ k, List (ZΓ A B k)
  | .I => l
  | .SA => sa
  | .SB => sb
  | .TA => ta
  | .TB => tb
  | .P => p
  | .O => o

section stackLemmas

variable (l l' : List (A ⊕ B)) (sa sa' : List (Option A)) (sb sb' : List (Option B))
  (ta ta' : List (Option A)) (tb tb' : List (Option B)) (p p' o o' : List (Option A × Option B))

theorem lst_I : lst l sa sb ta tb p o .I = l := rfl
theorem lst_SA : lst l sa sb ta tb p o .SA = sa := rfl
theorem lst_SB : lst l sa sb ta tb p o .SB = sb := rfl
theorem lst_TA : lst l sa sb ta tb p o .TA = ta := rfl
theorem lst_TB : lst l sa sb ta tb p o .TB = tb := rfl
theorem lst_P : lst l sa sb ta tb p o .P = p := rfl
theorem lst_O : lst l sa sb ta tb p o .O = o := rfl

theorem lst_set_I :
    Function.update (lst l sa sb ta tb p o) .I l' = lst l' sa sb ta tb p o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_SA :
    Function.update (lst l sa sb ta tb p o) .SA sa' = lst l sa' sb ta tb p o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_SB :
    Function.update (lst l sa sb ta tb p o) .SB sb' = lst l sa sb' ta tb p o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_TA :
    Function.update (lst l sa sb ta tb p o) .TA ta' = lst l sa sb ta' tb p o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_TB :
    Function.update (lst l sa sb ta tb p o) .TB tb' = lst l sa sb ta tb' p o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_P :
    Function.update (lst l sa sb ta tb p o) .P p' = lst l sa sb ta tb p' o := by
  funext k; cases k <;> simp [lst]

theorem lst_set_O :
    Function.update (lst l sa sb ta tb p o) .O o' = lst l sa sb ta tb p o' := by
  funext k; cases k <;> simp [lst]

theorem lst_start :
    lst l [] [] [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (ZΓ A B k)) .I l := by
  funext k; cases k <;> simp [lst]

theorem lst_end :
    lst ([] : List (A ⊕ B)) [] [] [] [] [] o =
      Function.update (fun _ => [] : ∀ k, List (ZΓ A B k)) .O o := by
  funext k; cases k <;> simp [lst]

end stackLemmas

/-- Configurations of the machine. -/
abbrev ZCfg (A B : Type) : Type := TM2.Cfg (ZΓ A B) ZL (Zσ A B)

/-- The step function on optional configurations. -/
abbrev zStep : Option (ZCfg A B) → Option (ZCfg A B) := flip bind (TM2.step zProg)

/-- Two runs, one after the other. -/
theorem chain {a b c : Option (ZCfg A B)} {m n : ℕ} (h1 : zStep^[n] a = b)
    (h2 : zStep^[m] b = c) : zStep^[m + n] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

section steps

variable (s : Zσ A B) (l : List (A ⊕ B)) (sa : List (Option A)) (sb : List (Option B))
  (ta : List (Option A)) (tb : List (Option B)) (p o : List (Option A × Option B))

theorem split_inl (a : A) :
    TM2.step zProg (⟨some .split, s, lst (Sum.inl a :: l) sa sb ta tb p o⟩ : ZCfg A B) =
      some ⟨some .split, (some a, none, false), lst l (some a :: sa) sb ta tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_I]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inl,
    Sum.getRight?_inl, Option.isSome_some, Bool.cond_true]
  rw [lst_set_I, lst_SA, lst_set_SA]

theorem split_inr (b : B) :
    TM2.step zProg (⟨some .split, s, lst (Sum.inr b :: l) sa sb ta tb p o⟩ : ZCfg A B) =
      some ⟨some .split, (none, some b, false), lst l sa (some b :: sb) ta tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_I]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inr,
    Sum.getRight?_inr, Option.isSome_some, Option.isSome_none, Bool.cond_true, Bool.cond_false]
  rw [lst_set_I, lst_SB, lst_set_SB]

theorem split_nil :
    TM2.step zProg (⟨some .split, s, lst [] sa sb ta tb p o⟩ : ZCfg A B) =
      some ⟨some .revA, (none, none, false), lst [] sa sb ta tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_I]
  simp only [List.head?_nil, List.tail_nil, Option.bind_none, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_I]

theorem revA_cons (a : A) :
    TM2.step zProg (⟨some .revA, s, lst l (some a :: sa) sb ta tb p o⟩ : ZCfg A B) =
      some ⟨some .revA, (some a, s.2), lst l sa sb (some a :: ta) tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_SA]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_SA, lst_TA, lst_set_TA]

theorem revA_nil :
    TM2.step zProg (⟨some .revA, s, lst l [] sb ta tb p o⟩ : ZCfg A B) =
      some ⟨some .revB, (none, s.2), lst l [] sb ta tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_SA]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_SA]

theorem revB_cons (b : B) :
    TM2.step zProg (⟨some .revB, s, lst l sa (some b :: sb) ta tb p o⟩ : ZCfg A B) =
      some ⟨some .revB, (s.1, some b, s.2.2), lst l sa sb ta (some b :: tb) p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_SB]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_SB, lst_TB, lst_set_TB]

theorem revB_nil :
    TM2.step zProg (⟨some .revB, s, lst l sa [] ta tb p o⟩ : ZCfg A B) =
      some ⟨some .zip, (s.1, none, s.2.2), lst l sa [] ta tb p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_SB]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_SB]

theorem zip_step (x : List A) (y : List B) (h : x ≠ [] ∨ y ≠ []) :
    TM2.step zProg (⟨some .zip, s, lst l sa sb (x.map some) (y.map some) p o⟩ : ZCfg A B) =
      some ⟨some .zip, (x.head?, y.head?, s.2.2),
        lst l sa sb (x.tail.map some) (y.tail.map some) ((x.head?, y.head?) :: p) o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_TA, lst_set_TA, lst_TB, lst_set_TB]
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;>
    simp [lst_P, lst_set_P] at h ⊢

theorem zip_nil :
    TM2.step zProg (⟨some .zip, s, lst l sa sb [] [] p o⟩ : ZCfg A B) =
      some ⟨some .out, (none, none, s.2.2), lst l sa sb [] [] p o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_TA, lst_set_TA, lst_TB, lst_set_TB]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none, Bool.or_self,
    Bool.cond_false]

theorem out_cons (q : Option A × Option B) :
    TM2.step zProg (⟨some .out, s, lst l sa sb ta tb (q :: p) o⟩ : ZCfg A B) =
      some ⟨some .out, (q.1, q.2, true), lst l sa sb ta tb p (q :: o)⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_P]
  simp only [List.head?_cons, List.tail_cons, Option.getD_some, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_P, lst_O, lst_set_O]

theorem out_nil :
    TM2.step zProg (⟨some .out, s, lst l sa sb ta tb [] o⟩ : ZCfg A B) =
      some ⟨none, (none, none, false), lst l sa sb ta tb [] o⟩ := by
  simp only [TM2.step, zProg, TM2.stepAux]
  rw [lst_P]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_set_P]

end steps

theorem splitLoop :
    ∀ (l : List (A ⊕ B)) (sa : List (Option A)) (sb : List (Option B)) (s : Zσ A B),
      zStep^[l.length + 1] (some (⟨some .split, s, lst l sa sb [] [] [] []⟩ : ZCfg A B)) =
        some ⟨some .revA, (none, none, false),
          lst [] ((l.filterMap Sum.getLeft?).reverse.map some ++ sa)
            ((l.filterMap Sum.getRight?).reverse.map some ++ sb) [] [] [] []⟩ := by
  intro l
  induction l with
  | nil => intro sa sb s; exact split_nil s sa sb [] [] [] []
  | cons x l ih =>
    intro sa sb s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : zStep (some (⟨some .split, s, lst (Sum.inl a :: l) sa sb [] [] [] []⟩ :
          ZCfg A B)) =
          some ⟨some .split, (some a, none, false), lst l (some a :: sa) sb [] [] [] []⟩ :=
        split_inl s l sa sb [] [] [] [] a
      rw [e, ih]
      simp [List.filterMap_cons]
    | inr b =>
      have e : zStep (some (⟨some .split, s, lst (Sum.inr b :: l) sa sb [] [] [] []⟩ :
          ZCfg A B)) =
          some ⟨some .split, (none, some b, false), lst l sa (some b :: sb) [] [] [] []⟩ :=
        split_inr s l sa sb [] [] [] [] b
      rw [e, ih]
      simp [List.filterMap_cons]

theorem revALoop (sb : List (Option B)) :
    ∀ (x : List A) (ta : List (Option A)) (s : Zσ A B),
      zStep^[x.length + 1]
          (some (⟨some .revA, s, lst [] (x.map some) sb ta [] [] []⟩ : ZCfg A B)) =
        some ⟨some .revB, (none, s.2), lst [] [] sb (x.reverse.map some ++ ta) [] [] []⟩ := by
  intro x
  induction x with
  | nil => intro ta s; exact revA_nil s [] sb ta [] [] []
  | cons a x ih =>
    intro ta s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zStep (some (⟨some .revA, s, lst [] ((a :: x).map some) sb ta [] [] []⟩ :
        ZCfg A B)) =
        some ⟨some .revA, (some a, s.2), lst [] (x.map some) sb (some a :: ta) [] [] []⟩ :=
      revA_cons s [] (x.map some) sb ta [] [] [] a
    rw [e, ih]
    simp

theorem revBLoop (ta : List (Option A)) :
    ∀ (y : List B) (tb : List (Option B)) (s : Zσ A B),
      zStep^[y.length + 1]
          (some (⟨some .revB, s, lst [] [] (y.map some) ta tb [] []⟩ : ZCfg A B)) =
        some ⟨some .zip, (s.1, none, s.2.2),
          lst [] [] [] ta (y.reverse.map some ++ tb) [] []⟩ := by
  intro y
  induction y with
  | nil => intro tb s; exact revB_nil s [] [] ta tb [] []
  | cons b y ih =>
    intro tb s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zStep (some (⟨some .revB, s, lst [] [] ((b :: y).map some) ta tb [] []⟩ :
        ZCfg A B)) =
        some ⟨some .revB, (s.1, some b, s.2.2),
          lst [] [] (y.map some) ta (some b :: tb) [] []⟩ :=
      revB_cons s [] [] (y.map some) ta tb [] [] b
    rw [e, ih]
    simp

theorem zip_head (x : List A) (y : List B) (h : x ≠ [] ∨ y ≠ []) :
    List.zipWithAll Prod.mk x y =
      (x.head?, y.head?) :: List.zipWithAll Prod.mk x.tail y.tail := by
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp at h ⊢

theorem zip_length :
    ∀ (x : List A) (y : List B),
      (List.zipWithAll Prod.mk x y).length = max x.length y.length := by
  intro x
  induction x with
  | nil => intro y; simp
  | cons a x ih =>
    intro y
    cases y with
    | nil => simp
    | cons b y => simp [ih]

theorem zipLoop :
    ∀ (n : ℕ) (x : List A) (y : List B) (p : List (Option A × Option B)) (s : Zσ A B),
      max x.length y.length = n →
      zStep^[n + 1]
          (some (⟨some .zip, s, lst [] [] [] (x.map some) (y.map some) p []⟩ : ZCfg A B)) =
        some ⟨some .out, (none, none, s.2.2),
          lst [] [] [] [] [] ((List.zipWithAll Prod.mk x y).reverse ++ p) []⟩ := by
  intro n
  induction n with
  | zero =>
    intro x y p s h
    have hx : x = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : y = [] := List.length_eq_zero_iff.mp (by omega)
    subst hx hy
    exact zip_nil s [] [] [] p []
  | succ n ih =>
    intro x y p s h
    rw [Function.iterate_succ_apply]
    have hne : x ≠ [] ∨ y ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rw [hc.1, hc.2] at h
      simp at h
    have e : zStep (some (⟨some .zip, s, lst [] [] [] (x.map some) (y.map some) p []⟩ :
        ZCfg A B)) =
        some ⟨some .zip, (x.head?, y.head?, s.2.2),
          lst [] [] [] (x.tail.map some) (y.tail.map some) ((x.head?, y.head?) :: p) []⟩ :=
      zip_step s [] [] [] p [] x y hne
    rw [e, ih x.tail y.tail _ _ (by simp only [List.length_tail]; omega), zip_head x y hne,
      List.reverse_cons, List.append_assoc]
    rfl

theorem outLoop :
    ∀ (p o : List (Option A × Option B)) (s : Zσ A B),
      zStep^[p.length + 1] (some (⟨some .out, s, lst [] [] [] [] [] p o⟩ : ZCfg A B)) =
        some ⟨none, (none, none, false), lst [] [] [] [] [] [] (p.reverse ++ o)⟩ := by
  intro p
  induction p with
  | nil => intro o s; exact out_nil s [] [] [] [] [] o
  | cons q p ih =>
    intro o s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zStep (some (⟨some .out, s, lst [] [] [] [] [] (q :: p) o⟩ : ZCfg A B)) =
        some ⟨some .out, (q.1, q.2, true), lst [] [] [] [] [] p (q :: o)⟩ :=
      out_cons s [] [] [] [] [] p o q
    rw [e, ih]
    simp

theorem zip_run [Fintype A] [Fintype B] (p : List A × List B) :
    ∃ n, n ≤ 4 * (Gen.gpair (p.1, p.2)).length + 5 ∧
      zStep^[n] (some (initList (zM A B) (Gen.gpair (p.1, p.2)))) =
        some (haltList (zM A B) (List.zipWithAll Prod.mk p.1 p.2)) := by
  have hs := splitLoop (Gen.gpair (p.1, p.2)) [] [] ((none, none, false) : Zσ A B)
  rw [Gen.gpair_left, Gen.gpair_right, List.append_nil, List.append_nil] at hs
  have hA := revALoop (p.2.reverse.map some) p.1.reverse [] ((none, none, false) : Zσ A B)
  rw [List.reverse_reverse, List.append_nil] at hA
  have hB := revBLoop (p.1.map some) p.2.reverse [] ((none, none, false) : Zσ A B)
  rw [List.reverse_reverse, List.append_nil] at hB
  have hZ := zipLoop (max p.1.length p.2.length) p.1 p.2 [] ((none, none, false) : Zσ A B) rfl
  rw [List.append_nil] at hZ
  have hO := outLoop (List.zipWithAll Prod.mk p.1 p.2).reverse []
    ((none, none, false) : Zσ A B)
  rw [List.reverse_reverse, List.append_nil] at hO
  refine ⟨((List.zipWithAll Prod.mk p.1 p.2).reverse.length + 1) +
    ((max p.1.length p.2.length + 1) + ((p.2.reverse.length + 1) + ((p.1.reverse.length + 1) +
      ((Gen.gpair (p.1, p.2)).length + 1)))), ?_, ?_⟩
  · rw [Gen.gpair_length, List.length_reverse, List.length_reverse, List.length_reverse,
      zip_length]
    omega
  · refine (congrArg (fun c => zStep^[_] (some c)) (initList_eq (zM A B) _)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq (zM A B) (List.zipWithAll Prod.mk p.1 p.2))).symm)
    show zStep^[_]
      (some (⟨some .split, (none, none, false),
        Function.update (fun _ => []) ZK.I (Gen.gpair (p.1, p.2))⟩ : ZCfg A B)) =
      some (⟨none, (none, none, false),
        Function.update (fun _ => []) ZK.O (List.zipWithAll Prod.mk p.1 p.2)⟩ : ZCfg A B)
    rw [← lst_start, ← lst_end]
    exact chain (chain (chain (chain hs hA) hB) hZ) hO

end Zip

open Zip in
/-- The padded zip of the two strings of a pair is computable in at most `4 * n + 5` steps. -/
theorem zip_polyTime {A B : Type} [Fintype A] [Fintype B] :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : List A × List B => PEqualNP.Library.Machines.Gen.gpair (p.1, p.2))
      (fun l : List (Option A × Option B) => l)
      (fun p : List A × List B => List.zipWithAll Prod.mk p.1 p.2)) :=
  ⟨{
    tm := zM A B
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 5
    outputsFun := fun p =>
      { steps := Classical.choose (zip_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun x => zStep^[Classical.choose (zip_run p)]
            (some (initList (zM A B) x))) (hm _ (Gen.gpair (p.1, p.2)))).trans
            ((Classical.choose_spec (zip_run p)).2.trans
              (congrArg (fun x => some (haltList (zM A B) x))
                (hm _ (List.zipWithAll Prod.mk p.1 p.2)).symm))
        steps_le_m := by
          have h := (Classical.choose_spec (zip_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.MetaComplexity.Helpers.Machines
