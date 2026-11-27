import PEqualNP.MetaComplexity.Helpers.MachinePrintMirror
import PEqualNP.MetaComplexity.Helpers.MachinePrintFlat
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Reading the input into tokens

Helper module (proofs only, no statement may use it).

The input is a tuple of unary numbers (only its head `n` is used) and a list of tuples of
unary numbers, each written with `encodeList`. A finite-state transducer (`tok1`) turns it into
tokens: `H` for each unit of `n`, then the separator `HE`; per tuple `TS`, then per entry a
start, its units and an end, each marked with the role of the entry (owner, first entry of the
list, later entry), then the separator `TE`; at the very end `LE`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds

inductive Role : Type
  | t | v | x
  deriving DecidableEq

instance : Fintype Role := Fintype.ofList [.t, .v, .x] (fun x => by cases x <;> simp)

def Role.next : Role → Role
  | .t => .v
  | .v => .x
  | .x => .x

inductive Tok : Type
  | H | HE | TS | ES (r : Role) | O (r : Role) | EE (r : Role) | TE | LE | M
  deriving DecidableEq

instance : Fintype Tok := Fintype.ofList
  [.H, .HE, .TS, .ES .t, .ES .v, .ES .x, .O .t, .O .v, .O .x, .EE .t, .EE .v, .EE .x, .TE, .LE, .M]
  (fun x => by
    cases x with
    | ES r => cases r <;> simp
    | O r => cases r <;> simp
    | EE r => cases r <;> simp
    | _ => simp)

/-- The separators of the segments. -/
def Tok.isSep : Tok → Bool
  | .HE => true
  | .TE => true
  | _ => false

/-- The tokens of one entry. -/
def tokE (r : Role) (a : ℕ) : List Tok := Tok.ES r :: (List.replicate a (Tok.O r) ++ [Tok.EE r])

/-- The tokens of the entries of a tuple, from role `r` on. -/
def elemsTok : Role → List ℕ → List Tok
  | _, [] => []
  | r, a :: l => tokE r a ++ elemsTok r.next l

/-- The segment of one tuple. -/
def segT (l : List ℕ) : List Tok := Tok.TS :: elemsTok .t l

/-! ## The reading transducer -/

inductive RQ : Type
  | a0 | a1 | a2 | a3 | b | c (r : Role) | d (r : Role) | z
  deriving DecidableEq

instance : Fintype RQ := Fintype.ofList
  [.a0, .a1, .a2, .a3, .b, .c .t, .c .v, .c .x, .d .t, .d .v, .d .x, .z]
  (fun x => by
    cases x with
    | c r => cases r <;> simp
    | d r => cases r <;> simp
    | _ => simp)

def δtok : RQ → Bool → RQ × Option Tok
  | .a0, true => (.a1, none)
  | .a0, false => (.b, some .HE)
  | .a1, true => (.a1, some .H)
  | .a1, false => (.a2, none)
  | .a2, true => (.a3, none)
  | .a2, false => (.b, some .HE)
  | .a3, true => (.a3, none)
  | .a3, false => (.a2, none)
  | .b, true => (.c .t, some .TS)
  | .b, false => (.z, some .LE)
  | .c r, true => (.d r, some (.ES r))
  | .c _, false => (.b, some .TE)
  | .d r, true => (.d r, some (.O r))
  | .d r, false => (.c r.next, some (.EE r))
  | .z, _ => (.z, none)

def tok1 (w : List Bool) : List Tok := fstRun δtok (fun _ => none) .a0 w

abbrev unaryE (a : ℕ) : List Bool := List.replicate a true ++ [false]

theorem run_rep (q : RQ) (o : Option Tok) (hq : ∀ x, δtok q true = (q, x) → True)
    (k : ℕ) (rest : List Bool) (h : δtok q true = (q, o)) :
    fstRun δtok (fun _ => none) q (List.replicate k true ++ rest) =
      (List.replicate k o).flatMap Option.toList ++ fstRun δtok (fun _ => none) q rest := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, fstRun, h, List.flatMap_cons,
      List.append_assoc]
    rw [ih]

theorem flatMap_rep_none (k : ℕ) : (List.replicate k (none : Option Tok)).flatMap Option.toList = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem flatMap_rep_some (k : ℕ) (t : Tok) :
    (List.replicate k (some t)).flatMap Option.toList = List.replicate k t := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The rest of the first tuple, after its first entry. -/
theorem run_a2 (l : List ℕ) (rest : List Bool) :
    fstRun δtok (fun _ => none) .a2 (encodeList unaryE l ++ rest) =
      Tok.HE :: fstRun δtok (fun _ => none) .b rest := by
  induction l with
  | nil => simp [encodeList, fstRun, δtok]
  | cons a l ih =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append, fstRun,
      δtok, Option.toList_none, List.nil_append]
    rw [run_rep .a3 none (fun _ _ => trivial) a _ rfl, flatMap_rep_none, List.nil_append]
    simp only [List.cons_append, List.nil_append, fstRun, δtok, Option.toList_none]
    have := ih
    simp only [encodeList, List.append_assoc, List.singleton_append] at this
    exact this

theorem run_head (l : List ℕ) (rest : List Bool) :
    fstRun δtok (fun _ => none) .a0 (encodeList unaryE l ++ rest) =
      List.replicate (l.headD 0) Tok.H ++ Tok.HE :: fstRun δtok (fun _ => none) .b rest := by
  cases l with
  | nil => simp [encodeList, fstRun, δtok]
  | cons a l =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append, fstRun,
      δtok, Option.toList_none, List.nil_append, List.headD_cons]
    rw [run_rep .a1 (some .H) (fun _ _ => trivial) a _ rfl, flatMap_rep_some]
    simp only [List.cons_append, List.nil_append, fstRun, δtok, Option.toList_none]
    have := run_a2 l rest
    simp only [encodeList, List.append_assoc, List.singleton_append] at this
    rw [this]

theorem run_elems (r : Role) (l : List ℕ) (rest : List Bool) :
    fstRun δtok (fun _ => none) (.c r) (encodeList unaryE l ++ rest) =
      elemsTok r l ++ Tok.TE :: fstRun δtok (fun _ => none) .b rest := by
  induction l generalizing r with
  | nil => simp [encodeList, fstRun, δtok, elemsTok]
  | cons a l ih =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append, fstRun,
      δtok, Option.toList_some, List.singleton_append, elemsTok, tokE]
    rw [run_rep (.d r) (some (.O r)) (fun _ _ => trivial) a _ rfl, flatMap_rep_some]
    simp only [List.cons_append, List.nil_append, fstRun, δtok, Option.toList_some,
      List.singleton_append, List.append_assoc]
    have := ih r.next
    simp only [encodeList, List.append_assoc, List.singleton_append] at this
    rw [this]

theorem run_tuples (ls : List (List ℕ)) :
    fstRun δtok (fun _ => none) .b (encodeList (encodeList unaryE) ls) =
      ls.flatMap (fun l => segT l ++ [Tok.TE]) ++ [Tok.LE] := by
  induction ls with
  | nil => simp [encodeList, fstRun, δtok]
  | cons l ls ih =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append, fstRun,
      δtok, Option.toList_some, List.singleton_append, List.nil_append]
    have := run_elems .t l (ls.flatMap (fun l => true :: encodeList unaryE l) ++ [false])
    simp only [encodeList, List.append_assoc, List.singleton_append] at this
    rw [this]
    have ih' := ih
    simp only [encodeList] at ih'
    rw [ih']
    simp [segT]

/-- The tokens of the input. -/
theorem tok1_eq (p : List ℕ × List (List ℕ)) :
    tok1 (encodeList unaryE p.1 ++ encodeList (encodeList unaryE) p.2) =
      joinS ((List.replicate (p.1.headD 0) Tok.H, Tok.HE) :: p.2.map (fun l => (segT l, Tok.TE)))
        [Tok.LE] := by
  unfold tok1
  rw [run_head, run_tuples]
  simp only [joinS, List.flatMap_cons, List.flatMap_map, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem cpt_tok1 : ComputableInPolyTime (fun w : List Bool => w) (fun l : List Tok => l) tok1 :=
  fst_polyTime _ _ _ δtok (fun _ => none) .a0 (fun _ => rfl)

end PEqualNP.MetaComplexity.Helpers.MachinePrint
