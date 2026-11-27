import PEqualNP.MetaComplexity.Helpers.MachinePrintTok
import PEqualNP.MetaComplexity.Helpers.MachinePrintRel

/-!
# Writing the relative gates from the mirrored tokens

Helper module (proofs only, no statement may use it).

After two segment mirrors every tuple segment `s` reads `s.reverse, M, s, M, s.reverse, M, s`
and then its separator. A list-writing transducer (`δF`) reads the four copies:

1. `s.reverse`: count the entries (up to three);
2. `s`: with one entry or none, nothing; with two, the AND of the owner and the entry; with
   more, the OR chain over the list;
3. `s.reverse`: with three entries or more, the AND of the owner (read last here) and the
   previous gate;
4. `s`: unless this is the leading block, the joining OR: one unit per entry of the tuple for
   the distance, then distance 1.

The header copies the unary `n` from its first copy. The result is the code of the input of D02
for `relGates`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds

inductive Ph : Type
  | hd | sg | tu | fn
  deriving DecidableEq

instance : Fintype Ph := Fintype.ofList [.hd, .sg, .tu, .fn] (fun x => by cases x <;> simp)

inductive Cp : Type
  | c1 | c2 | c3 | c4
  deriving DecidableEq

instance : Fintype Cp := Fintype.ofList [.c1, .c2, .c3, .c4] (fun x => by cases x <;> simp)

def Cp.next : Cp → Cp
  | .c1 => .c2
  | .c2 => .c3
  | .c3 => .c4
  | .c4 => .c4

inductive Kc : Type
  | k0 | k1 | k2 | k3
  deriving DecidableEq

instance : Fintype Kc := Fintype.ofList [.k0, .k1, .k2, .k3] (fun x => by cases x <;> simp)

def Kc.inc : Kc → Kc
  | .k0 => .k1
  | .k1 => .k2
  | .k2 => .k3
  | .k3 => .k3

def Kc.ge2 : Kc → Bool
  | .k2 => true
  | .k3 => true
  | _ => false

def kOf : ℕ → Kc
  | 0 => .k0
  | 1 => .k1
  | 2 => .k2
  | _ => .k3

abbrev FS : Type := Ph × Bool × Cp × Kc × Bool

def Tok.isES : Tok → Bool
  | .ES _ => true
  | _ => false

/-- Copy 2: the new flag and the output. -/
def e2 : Kc → Bool → Tok → Bool × List Bool
  | .k2, xf, .ES .t => (xf, [true, false, false])
  | .k2, xf, .O .t => (xf, [true])
  | .k2, xf, .EE .t => (xf, [false])
  | .k2, xf, .ES .v => (xf, [false])
  | .k2, xf, .O .v => (xf, [true])
  | .k2, xf, .EE .v => (xf, [false])
  | .k3, xf, .ES .v => (xf, [true, true, false])
  | .k3, xf, .O .v => (xf, [true])
  | .k3, xf, .EE .v => (xf, [false])
  | .k3, xf, .ES .x => (false, if xf then [false] else [true, true, true, true, false, false])
  | .k3, xf, .O .x => (xf, [true])
  | .k3, xf, .EE .x => (xf, [false])
  | _, xf, _ => (xf, [])

/-- Copy 3. -/
def e3 : Kc → Tok → List Bool
  | .k3, .EE .t => [true, false, false]
  | .k3, .O .t => [true]
  | .k3, .ES .t => [false, true, true, false]
  | _, _ => []

/-- Copy 4. -/
def e4 : Bool → Tok → List Bool
  | true, .TS => [true, true, true]
  | true, .ES _ => [true]
  | _, _ => []

def δtu (lead : Bool) (cp : Cp) (k : Kc) (xf : Bool) (tok : Tok) : FS × List Bool :=
  match tok with
  | .M => ((.tu, lead, cp.next, k, xf), [])
  | .TE => ((.sg, lead && !k.ge2, .c1, .k0, true),
      if k.ge2 && !lead then [false, true, true, false] else [])
  | _ =>
    match cp with
    | .c1 => ((.tu, lead, .c1, if tok.isES then k.inc else k, xf), [])
    | .c2 => ((.tu, lead, .c2, k, (e2 k xf tok).1), (e2 k xf tok).2)
    | .c3 => ((.tu, lead, .c3, k, xf), e3 k tok)
    | .c4 => ((.tu, lead, .c4, k, xf), e4 (k.ge2 && !lead) tok)

def δF : FS → Tok → FS × List Bool
  | (.hd, lead, cp, k, xf), tok =>
    match tok with
    | .H => ((.hd, lead, cp, k, xf), if cp = .c1 then [true] else [])
    | .M => ((.hd, lead, cp.next, k, xf), [])
    | .HE => ((.sg, true, .c1, .k0, true), [false])
    | _ => ((.hd, lead, cp, k, xf), [])
  | (.sg, lead, _, _, _), tok =>
    match tok with
    | .LE => ((.fn, lead, .c1, .k0, true), [false])
    | _ => δtu lead .c1 .k0 true tok
  | (.tu, lead, cp, k, xf), tok => δtu lead cp k xf tok
  | (.fn, lead, cp, k, xf), _ => ((.fn, lead, cp, k, xf), [])

/-- The output from state `q` over a token list. -/
def out (q : FS) (L : List Tok) : List Bool := lrun δF (fun _ => []) q L

/-- The state after a token list. -/
def nxt (q : FS) (L : List Tok) : FS := L.foldl (fun q x => (δF q x).1) q

theorem out_nil (q : FS) : out q [] = [] := rfl

theorem out_cons (q : FS) (x : Tok) (L : List Tok) :
    out q (x :: L) = (δF q x).2 ++ out (δF q x).1 L := rfl

theorem nxt_cons (q : FS) (x : Tok) (L : List Tok) : nxt q (x :: L) = nxt (δF q x).1 L := rfl

theorem out_append (q : FS) (a b : List Tok) : out q (a ++ b) = out q a ++ out (nxt q a) b := by
  induction a generalizing q with
  | nil => rfl
  | cons x a ih => simp [out_cons, nxt_cons, ih]

theorem nxt_append (q : FS) (a b : List Tok) : nxt q (a ++ b) = nxt (nxt q a) b := by
  simp [nxt, List.foldl_append]

/-- A run that changes nothing and writes nothing. -/
theorem idle (q : FS) (L : List Tok) (h : ∀ x ∈ L, δF q x = (q, [])) :
    out q L = [] ∧ nxt q L = q := by
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons x L ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rw [out_cons, nxt_cons, hx]
    exact ⟨by simp [ih'.1], ih'.2⟩

theorem rep_one (q : FS) (x : Tok) (b : Bool) (h : δF q x = (q, [b])) (a : ℕ) :
    out q (List.replicate a x) = List.replicate a b ∧ nxt q (List.replicate a x) = q := by
  induction a with
  | zero => exact ⟨rfl, rfl⟩
  | succ a ih =>
    rw [List.replicate_succ, out_cons, nxt_cons, h, ih.1, ih.2]
    exact ⟨by simp [List.replicate_succ], rfl⟩

theorem rep_none (q : FS) (x : Tok) (h : δF q x = (q, [])) (a : ℕ) :
    out q (List.replicate a x) = [] ∧ nxt q (List.replicate a x) = q :=
  idle q _ (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact h)

/-! ## Facts on the token lists -/

/-- No token of an entry list is `M`, `TE`, `LE`, `TS`, `H` or `HE`. -/
def plainTok : Tok → Prop
  | .ES _ => True
  | .O _ => True
  | .EE _ => True
  | _ => False

theorem tokE_plain (r : Role) (a : ℕ) : ∀ x ∈ tokE r a, plainTok x := by
  intro x hx
  simp only [tokE, List.mem_cons, List.mem_append, List.mem_replicate, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | ⟨_, rfl⟩ | rfl <;> trivial

theorem elemsTok_plain : ∀ (r : Role) (l : List ℕ), ∀ x ∈ elemsTok r l, plainTok x
  | _, [] => by simp [elemsTok]
  | r, a :: l => by
    intro x hx
    simp only [elemsTok, List.mem_append] at hx
    rcases hx with h | h
    · exact tokE_plain r a x h
    · exact elemsTok_plain r.next l x h

/-- The role of a plain token is not the owner's. -/
def notT : Tok → Prop
  | .ES r => r ≠ .t
  | .O r => r ≠ .t
  | .EE r => r ≠ .t
  | _ => False

theorem elemsTok_notT : ∀ (r : Role) (l : List ℕ), r ≠ .t → ∀ x ∈ elemsTok r l, notT x
  | _, [], _ => by simp [elemsTok]
  | r, a :: l, hr => by
    intro x hx
    simp only [elemsTok, List.mem_append] at hx
    rcases hx with h | h
    · simp only [tokE, List.mem_cons, List.mem_append, List.mem_replicate,
        List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with rfl | ⟨_, rfl⟩ | rfl <;> exact hr
    · exact elemsTok_notT r.next l (by cases r <;> simp [Role.next]) x h

def kadd (k : Kc) : ℕ → Kc
  | 0 => k
  | n + 1 => kadd k.inc n

theorem kadd_k0 : ∀ n, kadd .k0 n = kOf n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
    simp only [kadd, Kc.inc, kOf]
    have : ∀ m, kadd .k3 m = .k3 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => simp [kadd, Kc.inc, ih]
    exact this n

theorem kadd_add (k : Kc) (a b : ℕ) : kadd k (a + b) = kadd (kadd k a) b := by
  induction a generalizing k with
  | zero => simp [kadd]
  | succ a ih => rw [Nat.add_right_comm]; simp [kadd, ih]

/-! ## Copy 1 -/

theorem copy1 (lead xf : Bool) : ∀ (L : List Tok) (k : Kc), (∀ x ∈ L, plainTok x ∨ x = .TS) →
    out (.tu, lead, .c1, k, xf) L = [] ∧
      nxt (.tu, lead, .c1, k, xf) L = (.tu, lead, .c1, kadd k (L.countP Tok.isES), xf) := by
  intro L
  induction L with
  | nil => intro k _; exact ⟨rfl, rfl⟩
  | cons x L ih =>
    intro k h
    have hx := h x (by simp)
    have ih' := fun k => ih k (fun y hy => h y (by simp [hy]))
    rw [out_cons, nxt_cons]
    rcases hx with hx | rfl
    · cases x with
      | ES r =>
        simp only [δF, δtu, Tok.isES, if_true]
        rw [(ih' k.inc).1, (ih' k.inc).2]
        simp [List.countP_cons, Tok.isES, kadd]
      | O r =>
        simp only [δF, δtu, Tok.isES, Bool.false_eq_true, if_false]
        rw [(ih' k).1, (ih' k).2]
        simp [List.countP_cons, Tok.isES]
      | EE r =>
        simp only [δF, δtu, Tok.isES, Bool.false_eq_true, if_false]
        rw [(ih' k).1, (ih' k).2]
        simp [List.countP_cons, Tok.isES]
      | _ => exact absurd hx (by simp [plainTok])
    · simp only [δF, δtu, Tok.isES, Bool.false_eq_true, if_false]
      rw [(ih' k).1, (ih' k).2]
      simp [List.countP_cons, Tok.isES]

theorem count_tokE (r : Role) (a : ℕ) : (tokE r a).countP Tok.isES = 1 := by
  simp [tokE, List.countP_cons, Tok.isES, List.countP_append, List.countP_replicate]

theorem count_elemsTok : ∀ (r : Role) (l : List ℕ), (elemsTok r l).countP Tok.isES = l.length
  | _, [] => rfl
  | r, a :: l => by
    simp [elemsTok, List.countP_append, count_tokE, count_elemsTok r.next l, Nat.add_comm]

theorem segT_tok (l : List ℕ) : ∀ x ∈ segT l, plainTok x ∨ x = .TS := by
  intro x hx
  simp only [segT, List.mem_cons] at hx
  rcases hx with rfl | h
  · exact Or.inr rfl
  · exact Or.inl (elemsTok_plain _ _ x h)

theorem copy1_seg (lead : Bool) (l : List ℕ) :
    out (.tu, lead, .c1, .k0, true) (segT l).reverse = [] ∧
      nxt (.tu, lead, .c1, .k0, true) (segT l).reverse = (.tu, lead, .c1, kOf l.length, true) := by
  have h := copy1 lead true (segT l).reverse .k0
    (fun x hx => segT_tok l x (List.mem_reverse.mp hx))
  rw [List.countP_reverse] at h
  have hc : (segT l).countP Tok.isES = l.length := by
    simp [segT, List.countP_cons, Tok.isES, count_elemsTok]
  rw [hc, kadd_k0] at h
  exact h

end PEqualNP.MetaComplexity.Helpers.MachinePrint
