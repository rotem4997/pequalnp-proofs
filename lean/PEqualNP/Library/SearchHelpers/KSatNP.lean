import PEqualNP.Library.SearchHelpers.SatVerifierCPT
import PEqualNP.Library.L017
import PEqualNP.Library.L022
import PEqualNP.Library.L026
import PEqualNP.Library.L029

/-!
# 3-SAT is in NP

Helper module (proofs only, no statement may use it).

3-SAT reduces to SAT in polynomial time: a string that passes the width test is sent to itself,
every other string to the encoding of the formula with one empty clause, which is unsatisfiable.
The width test reads the string in pairs of bits and rejects when more than three end-of-literal
pairs occur since the last end-of-clause pair. On the encoding of a formula it passes exactly
when every clause has at most three literals. It is a finite-state transducer, so it runs in
polynomial time. Membership in NP then follows from SAT being in NP and from the closure of NP
under polynomial-time reductions.
-/

namespace PEqualNP.Library.SearchHelpers.KSat

namespace Mem

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### The width test as a function on strings -/

/-- The width test, with `n` literals already closed in the current clause. -/
def wt : ℕ → List Bool → Bool
  | _, [] => true
  | _, [_] => false
  | n, true :: _ :: r => wt n r
  | _, false :: false :: r => wt 0 r
  | n, false :: true :: r => decide (n < 3) && wt (n + 1) r

theorem wt_digits (n : ℕ) (ds r : List Bool) :
    wt n ((ds.flatMap fun d => [true, d]) ++ r) = wt n r := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [wt, ih]

theorem wt_literal (n : ℕ) (l : Literal) (r : List Bool) :
    wt n (encodeLiteral l ++ r) = (decide (n < 3) && wt (n + 1) r) := by
  have h : encodeLiteral l ++ r =
      true :: l.2 :: ((l.1.bits.flatMap fun d => [true, d]) ++ false :: true :: r) := by
    simp [encodeLiteral]
  rw [h, wt, wt_digits, wt]

theorem wt_clause (r : List Bool) : ∀ (c : Clause) (n : ℕ), n ≤ 3 →
    wt n (encodeClause c ++ r) = (decide (n + c.length ≤ 3) && wt 0 r)
  | [], n, hn => by
    have h : encodeClause [] ++ r = false :: false :: r := by simp [encodeClause]
    rw [h, wt]
    simp [hn]
  | l :: c, n, hn => by
    have h : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [h, wt_literal]
    by_cases h3 : n < 3
    · rw [wt_clause r c (n + 1) (by omega)]
      have e : (n + 1 + c.length ≤ 3) ↔ (n + (l :: c).length ≤ 3) := by
        simp only [List.length_cons]; omega
      simp [h3, e]
    · have e : ¬ (n + (c.length + 1) ≤ 3) := by omega
      simp [h3, e]

theorem wt_cnf : ∀ φ : CNF, wt 0 (encodeCNF φ) = true ↔ IsKCNF 3 φ
  | [] => by simp [encodeCNF, wt, IsKCNF]
  | c :: φ => by
    have h : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
    rw [h, wt_clause _ c 0 (by omega)]
    simp [wt_cnf φ, IsKCNF]

/-! ### The width test as a transducer -/

/-- Position inside a pair: at a pair boundary, after `true`, after `false`. -/
inductive Ph : Type
  | b | t | f
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{.b, .t, .f}, fun q => by cases q <;> simp⟩

/-- Transition of the width test. The state is the number of literals closed in the current
clause and the position inside a pair, or `none` after a rejection. Nothing is written. -/
def wD : Option (Fin 4 × Ph) → Bool → Option (Fin 4 × Ph) × Option Bool
  | none, _ => (none, none)
  | some (n, .b), true => (some (n, .t), none)
  | some (n, .b), false => (some (n, .f), none)
  | some (n, .t), _ => (some (n, .b), none)
  | some (_, .f), false => (some (⟨0, by omega⟩, .b), none)
  | some (n, .f), true =>
    (if h : n.val < 3 then some (⟨n.val + 1, by omega⟩, .b) else none, none)

/-- The symbol written at the end: `true` when the string is accepted. -/
def wF : Option (Fin 4 × Ph) → Option Bool
  | some (_, .b) => some true
  | _ => none

theorem wD_none (l : List Bool) : fstRun wD wF none l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, wD, ih]

theorem wD_run : ∀ (x : List Bool) (n : ℕ) (h : n < 4),
    fstRun wD wF (some (⟨n, h⟩, Ph.b)) x = bflag (wt n x)
  | [], n, h => by simp [fstRun, wF, wt, bflag]
  | [a], n, h => by cases a <;> simp [fstRun, wD, wF, wt, bflag]
  | true :: d :: r, n, h => by simp [fstRun, wD, wt, wD_run r n h]
  | false :: false :: r, n, h => by
    simp only [fstRun, wD, wt, Option.toList_none, List.nil_append]
    exact wD_run r 0 (by omega)
  | false :: true :: r, n, h => by
    by_cases h3 : n < 3
    · simp [fstRun, wD, wt, h3, wD_run r (n + 1) (by omega)]
    · simp [fstRun, wD, wt, h3, wD_none, bflag]

theorem cpt_wtF : CPT (fun x => bflag (wt 0 x)) :=
  fst_polyTime _ _ _ wD wF (some (⟨0, by omega⟩, Ph.b))
    (fun x => (wD_run x 0 (by omega)).symm)

/-! ### The reduction -/

/-- The reduction: a string that passes the width test is kept, every other string is sent to
the encoding of the formula with one empty clause. -/
def red (x : List Bool) : List Bool := sel (bflag (wt 0 x)) [false, false] x

theorem cpt_red : CPT red :=
  cpt_sel cpt_wtF (cpt_const [false, false]) cpt_id

theorem red_pass {x : List Bool} (h : wt 0 x = true) : red x = x := by
  simp [red, sel, bflag, h]

theorem red_fail {x : List Bool} (h : wt 0 x = false) : red x = [false, false] := by
  simp [red, sel, bflag, h]

theorem empty_clause_not_SAT : ([false, false] : List Bool) ∉ SAT := by
  rintro ⟨φ, hφ, hs⟩
  have e : encodeCNF φ = encodeCNF [[]] := by
    rw [hφ]; simp [encodeCNF, encodeClause]
  have := PEqualNP.Library.L026 e
  subst this
  exact PEqualNP.Library.L022 [[]] (by simp) hs

theorem red_correct (x : List Bool) : x ∈ KSAT 3 ↔ red x ∈ SAT := by
  constructor
  · rintro ⟨φ, hk, rfl, hs⟩
    rw [red_pass ((wt_cnf φ).mpr hk)]
    exact ⟨φ, rfl, hs⟩
  · intro h
    cases hw : wt 0 x with
    | false =>
      rw [red_fail hw] at h
      exact absurd h empty_clause_not_SAT
    | true =>
      rw [red_pass hw] at h
      obtain ⟨φ, rfl, hs⟩ := h
      exact ⟨φ, (wt_cnf φ).mp hw, rfl, hs⟩

end Mem

/-- 3-SAT is in NP. -/
theorem ksat3_in_NP : PEqualNP.Search.KSAT 3 ∈ PEqualNP.Library.NP :=
  PEqualNP.Library.L017 _ _ ⟨Mem.red, Mem.cpt_red, Mem.red_correct⟩ PEqualNP.Library.L029

end PEqualNP.Library.SearchHelpers.KSat
