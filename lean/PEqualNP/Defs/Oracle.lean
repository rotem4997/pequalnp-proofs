import PEqualNP.Defs.Base

/-!
# Oracle machines, P^A and NP^A

Needed to state the relativization barrier (Baker, Gill and Solovay, SIAM J. Comput. 4(4),
1975) and the algebrization barrier on this project's machines. The pinned Mathlib has no
oracle machines: the statements of `Turing.TM2` are fixed and none of them consults an oracle.

* An oracle machine is a `Turing.FinTM2` together with a query stack `kq`, a map `queryBit`
  reading each symbol of that stack as a bit, and three labels `ask`, `yes`, `no`.
* Relative to an oracle `A : Language Bool`, a step at label `ask` does not run the statement
  of `ask`: it empties the query stack and goes to label `yes` if the query string is in `A`,
  to `no` otherwise. The query string is the query stack read from the bottom (the first symbol
  pushed) to the top. A query costs one step, as in the usual oracle Turing machine. Every
  other step is Mathlib's `Turing.TM2.step`.
* Running time, input and output conventions are those of `Defs/Base.lean`: Mathlib's
  `StateTransition.EvalsToInTime` from `Turing.initList` to `Turing.haltList`, alphabets matched
  by equivalences, the answer written as `Computability.encodeBool`.
* `OracleP A` and `OracleNP A` are `P` and `NP` of `Defs/Base.lean` with every machine replaced
  by an oracle machine relative to `A`. For NP the verifier is the oracle machine; the witness
  bound is unchanged.
-/

namespace PEqualNP.Library

/-- An oracle machine: a machine, its query stack, how a query symbol reads as a bit, and the
labels of the query statement and of its two answers. -/
structure OracleTM2 where
  /-- The underlying machine. -/
  tm : Turing.FinTM2
  /-- The query stack. -/
  kq : tm.K
  /-- The bit each symbol of the query stack stands for. -/
  queryBit : tm.Γ kq → Bool
  /-- The label at which the machine asks the oracle. -/
  ask : tm.Λ
  /-- The label the machine goes to when the answer is yes. -/
  yes : tm.Λ
  /-- The label the machine goes to when the answer is no. -/
  no : tm.Λ

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `A`. At label `ask` it empties the
query stack and goes to `yes` if the query string (the query stack read bottom to top) is in
`A`, to `no` otherwise; the internal state is unchanged. Elsewhere it is the machine's step. -/
noncomputable def OracleTM2.step (M : OracleTM2) (A : Language Bool)
    (c : Turing.TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : Option (Turing.TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) :=
  if c.l = some M.ask then
    some
      { l := some (if (c.stk M.kq).reverse.map M.queryBit ∈ A then M.yes else M.no)
        var := c.var
        stk := Function.update c.stk M.kq [] }
  else Turing.TM2.step M.tm.m c

/-- Relative to `A`, the set `S` is decided within time `t`: some oracle machine, with input
alphabet matched to `αΓ` and output alphabet matched to `Bool`, started on the encoding of `a`
halts within `t (length of the encoding of a)` steps with the answer `[f a]`, where `f a` is
true exactly on the members of `S`. -/
def OracleDecidableInTime {α αΓ : Type} (A : Language Bool) (ea : α → List αΓ) (S : Set α)
    (t : ℕ → ℕ) : Prop :=
  ∃ (f : α → Bool) (M : OracleTM2) (ein : M.tm.Γ M.tm.k₀ ≃ αΓ) (eout : M.tm.Γ M.tm.k₁ ≃ Bool),
    (∀ a, a ∈ S ↔ f a = true) ∧
      ∀ a, Nonempty (StateTransition.EvalsToInTime (M.step A) (Turing.initList M.tm ((ea a).map ein.symm))
        (some (Turing.haltList M.tm ((Computability.encodeBool (f a)).map eout.symm))) (t (ea a).length))

/-- Relative to `A`, the set `S` is decided in polynomial time. -/
def OracleDecidableInPolyTime {α αΓ : Type} (A : Language Bool) (ea : α → List αΓ)
    (S : Set α) : Prop :=
  ∃ p : Polynomial ℕ, OracleDecidableInTime A ea S (fun n : ℕ => p.eval n)

/-- P^A: the languages decided in polynomial time by an oracle machine relative to `A`. -/
def OracleP (A : Language Bool) : Set (Language Bool) :=
  {L | OracleDecidableInPolyTime A (fun x : List Bool => x) L}

/-- NP^A, by verifiers: a set `R` of pairs decided in polynomial time relative to `A`, and a
polynomial `p`, such that `x` is in `L` exactly when some witness `w` of length at most
`p (length of x)` has `(x, w)` in `R`. -/
def OracleNP (A : Language Bool) : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
    OracleDecidableInPolyTime A encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R}

end PEqualNP.Library
