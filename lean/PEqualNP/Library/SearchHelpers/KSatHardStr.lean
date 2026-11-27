import PEqualNP.Library.SearchHelpers.KSatHardSplit
import PEqualNP.Library.SearchHelpers.SatVerifier
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

/-!
# Helpers: the splitting of clauses as a function on encodings

Helper module (proofs only, no statement may use it).

It defines a total function `g` on bit strings from small named total functions and proves
`g (encodeCNF φ) = encodeCNF (split φ)` (`g_enc`), with `split` of `KSatHardSplit.lean`, and
`g x = [false]` when `x` encodes no formula (`g_not`). No machine appears here.

The string is read in items (`headI`, `dropI` of the verifier of SAT): an item is a literal or
the end-of-clause pair. The round `i` looks at the item number `i`, the first item of
`dropI^[i] x`, and writes the clauses of that item (`outI`); the rounds past the last item
write nothing. The fresh variable `2 ^ (i + 1)` has the digits `false^(i + 1), true`, so its
literal is written from the unary counter `un i` with `spread`; the old variable `v` becomes
`2 * v + 1`, one digit pair `[true, true]` put after the polarity pair.
-/

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
  PEqualNP.Library.SearchHelpers.Tab.StepW

/-! ### Literals -/

theorem bits_two_pow (a : ℕ) : (2 ^ a).bits = List.replicate a false ++ [true] := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, Nat.mul_comm, Nat.bit0_bits _ (pow_ne_zero _ two_ne_zero), ih]
    rfl

theorem spread_un (a : ℕ) :
    spread (un a) = (List.replicate a false).flatMap fun d => [true, d] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [un_succ, List.replicate_succ, List.flatMap_cons, ← ih]
    rfl

/-- The literal of the fresh variable of the item whose number is `|i|`, with polarity `pol`. -/
def litY (pol : Bool) (i : List Bool) : List Bool :=
  true :: pol :: (spread (true :: i) ++ [true, true, false, true])

theorem litY_un (pol : Bool) (m : ℕ) : litY pol (un m) = encodeLiteral (Y m, pol) := by
  rw [litY, ← un_succ, spread_un]
  simp only [encodeLiteral, Y, bits_two_pow, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.append_assoc]

/-- A literal item with its variable `v` renamed to `2 * v + 1`. -/
def litX (it : List Bool) : List Bool :=
  tk [true, true] it ++ true :: true :: it.tail.tail

theorem litX_lit (l : Literal) : litX (encodeLiteral l) = encodeLiteral (X l.1, l.2) := by
  have e : X l.1 = Nat.bit true l.1 := by simp [X, Nat.bit_val]
  have h1 : encodeLiteral (X l.1, l.2) = true :: l.2 :: true :: true :: vcode l.1 := by
    rw [encodeLiteral_eq]
    show true :: l.2 :: vcode (X l.1) = _
    rw [e, vcode_bit true _ (fun _ => rfl)]
  rw [h1, litX, tk_eq, encodeLiteral_eq]
  rfl

/-! ### One round -/

/-- The clauses of the first item of `r`, the number of the item being `|i|`. -/
def outI (i r : List Bool) : List Bool :=
  sel r [] (sel (bflag (isEnd r))
    (litY false i ++ (litX (headI r) ++ (litY true (true :: i) ++ [false, false])))
    (litY false i ++ ([false, false] ++ (litY true (true :: i) ++ [false, false]))))

theorem outI_nil (i : List Bool) : outI i [] = [] := by simp [outI, sel]

theorem outI_lit (m : ℕ) (l : Literal) (rest : List Bool) :
    outI (un m) (encodeLiteral l ++ rest) =
      encodeClause [(Y m, false), (X l.1, l.2), (Y (m + 1), true)] := by
  have hne : encodeLiteral l ++ rest ≠ [] := by simp [encodeLiteral_eq]
  unfold outI
  rw [← un_succ, litY_un, litY_un, isEnd_lit, headI_lit, litX_lit]
  simp [sel, bflag, encodeClause, hne]

theorem outI_end (m : ℕ) (rest : List Bool) :
    outI (un m) (false :: false :: rest) =
      encodeCNF [[(Y m, false)], [(Y (m + 1), true)]] := by
  unfold outI
  rw [← un_succ, litY_un, litY_un]
  simp [sel, bflag, isEnd, encodeCNF, encodeClause]

/-! ### The walk along the items -/

/-- `n` rounds from the item number `m` on the remaining string `r`. -/
def walk : ℕ → ℕ → List Bool → List Bool
  | 0, _, _ => []
  | n + 1, m, r => outI (un m) r ++ walk n (m + 1) (dropI r)

theorem walk_nil (n : ℕ) : ∀ m : ℕ, walk n m [] = [] := by
  induction n with
  | zero => intro m; rfl
  | succ n ih => intro m; simp [walk, outI_nil, dropI, ih]

theorem walk_range (n : ℕ) : ∀ (m : ℕ) (r : List Bool),
    (List.range n).flatMap (fun i => outI (un (m + i)) (dropI^[i] r)) = walk n m r := by
  induction n with
  | zero => intro m r; rfl
  | succ n ih =>
    intro m r
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, walk, ← ih]
    congr 1
    refine List.flatMap_congr ?_
    intro i _
    rw [show m + (i + 1) = m + 1 + i by omega, Function.iterate_succ_apply]

theorem enc_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
  simp [encodeCNF]

theorem enc_append (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF]

theorem walk_clause (c : Clause) : ∀ (k m : ℕ) (rest : List Bool),
    walk (k + (c.length + 1)) m (encodeClause c ++ rest) =
      encodeCNF (chain m c) ++ walk k (m + c.length + 1) rest := by
  induction c with
  | nil =>
    intro k m rest
    have e : encodeClause [] ++ rest = false :: false :: rest := by simp [encodeClause]
    rw [e]
    show outI (un m) (false :: false :: rest) ++ walk k (m + 1) rest = _
    rw [outI_end]
    rfl
  | cons l c ih =>
    intro k m rest
    have e : encodeClause (l :: c) ++ rest = encodeLiteral l ++ (encodeClause c ++ rest) := by
      simp [encodeClause]
    rw [e]
    show outI (un m) (encodeLiteral l ++ (encodeClause c ++ rest)) ++
      walk (k + (c.length + 1)) (m + 1) (dropI (encodeLiteral l ++ (encodeClause c ++ rest))) = _
    rw [outI_lit, dropI_lit, ih, chain, enc_cons, List.append_assoc,
      show m + 1 + c.length + 1 = m + (l :: c).length + 1 by
        simp only [List.length_cons]; omega]

theorem walk_cnf (φ : CNF) : ∀ k m : ℕ,
    walk (k + nIt φ) m (encodeCNF φ) = encodeCNF (splitFrom m φ) := by
  induction φ with
  | nil => intro k m; exact walk_nil _ _
  | cons c φ ih =>
    intro k m
    rw [nIt, ← Nat.add_assoc, enc_cons, walk_clause, ih, splitFrom, enc_append]

/-! ### The whole function -/

/-- The clauses of all items of `x`. -/
def G (x : List Bool) : List Bool :=
  (List.range x.length).flatMap fun i => outI (un i) (dropI^[i] x)

theorem G_enc (φ : CNF) : G (encodeCNF φ) = encodeCNF (splitFrom 0 φ) := by
  have h := walk_range (encodeCNF φ).length 0 (encodeCNF φ)
  simp only [Nat.zero_add] at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (nIt_le φ)
  rw [G, h, hk, Nat.add_comm, walk_cnf]

/-- The reduction: on the encoding of `φ` the encoding of `split φ`, on any other string the
string `[false]`, which encodes no formula. -/
def g (x : List Bool) : List Bool :=
  sel (bflag (wfB x)) [false] (encodeClause [(Y 0, true)] ++ G x)

theorem g_enc (φ : CNF) : g (encodeCNF φ) = encodeCNF (split φ) := by
  have h : wfB (encodeCNF φ) = true := (wfB_iff _).2 ⟨φ, rfl⟩
  rw [g, h, G_enc, split, enc_cons]
  simp [sel, bflag]

theorem g_not (x : List Bool) (h : wfB x = false) : g x = [false] := by
  rw [g, h]
  simp [sel, bflag]

theorem not_enc_false (φ : CNF) : encodeCNF φ ≠ [false] := by
  intro h
  have h1 : wfB [false] = true := (wfB_iff _).2 ⟨φ, h⟩
  exact absurd h1 (by decide)

end PEqualNP.Library.SearchHelpers.KSat.Hard
