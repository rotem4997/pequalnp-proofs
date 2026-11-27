import Mathlib
import PEqualNP.Defs

/-!
# Parity needs large bounded-depth circuits: the plan (L-lib-034)

STATUS: statements only. Every `def ... : Prop` below is a CONJECTURE until a module proves
`theorem ... : <Name>` and the checker accepts the lemma that rests on it. The theorem is
known (Hastad 1986, by the switching lemma); this is its formalization on our circuit model.

Everything here is SEMANTIC: a gate is its Boolean function, a DNF of width `w` is a function
all of whose true points have a certificate of size at most `w`, and a restriction turns a
function on the variables `V` into a function on the subtype of its stars. So the plan never
handles syntax, and the two interfaces it consumes are:

* `SwitchingSem`: the switching lemma in counting form, for a function with small
  1-certificates (to be derived from `Switching.Core`, where it is proved for ordered DNFs
  and the canonical decision tree);
* `BridgeStmt`: a circuit of our model deciding parity gives a levelled family of gate
  functions (to be proved in `Switching.Bridge`).

The chain: `SwitchingSem` gives `Round` (one restriction lowers the depth by one), `Round`
gives `Iterate` (with `base` and `isPar_restr`, proved in `Switching/Basic.lean`), and
`BridgeStmt`, `Iterate` and `FinalArith` give the recorded statement `Stmt034`.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Plan

open PEqualNP.CircuitLowerBounds

/-- A Boolean function of the variables `V`. -/
abbrev BF (V : Type) := (V → Bool) → Bool

/-- Every true point of `f` has a certificate of at most `w` variables: `f` is a DNF of
width at most `w` (one term per certificate). -/
def Cert1 {V : Type} (w : ℕ) (f : BF V) : Prop :=
  ∀ x, f x = true → ∃ S : Finset V, S.card ≤ w ∧ ∀ y : V → Bool, (∀ i ∈ S, y i = x i) → f y = true

/-- Every false point of `f` has a certificate of at most `w` variables: `f` is a CNF of
width at most `w`. -/
def Cert0 {V : Type} (w : ℕ) (f : BF V) : Prop :=
  ∀ x, f x = false → ∃ S : Finset V, S.card ≤ w ∧ ∀ y : V → Bool, (∀ i ∈ S, y i = x i) → f y = false

/-- Both: what a function with a decision tree of depth at most `w` satisfies, and what a
literal, a constant, a term or a clause of width at most `w` satisfies (`w ≥ 1`). -/
def Low {V : Type} (w : ℕ) (f : BF V) : Prop := Cert1 w f ∧ Cert0 w f

/-- The number of true coordinates modulo two. -/
def cnt {V : Type} [Fintype V] (x : V → Bool) : ZMod 2 := ∑ v, if x v = true then 1 else 0

/-- The parity of a point. -/
def par {V : Type} [Fintype V] (x : V → Bool) : Bool := decide (cnt x = 1)

/-- `f` is parity or its negation, on all the variables of `V`. -/
def IsPar {V : Type} [Fintype V] (f : BF V) : Prop := ∃ b : Bool, ∀ x, f x = xor b (par x)

/-- A restriction: `none` is a star. -/
abbrev Restr (V : Type) := V → Option Bool

/-- The stars of a restriction, as a type of variables. -/
abbrev Stars {V : Type} (ρ : Restr V) := {v : V // ρ v = none}

/-- Complete an assignment of the stars by the fixed values. -/
def fill {V : Type} (ρ : Restr V) (y : Stars ρ → Bool) : V → Bool :=
  fun v => if h : ρ v = none then y ⟨v, h⟩ else (ρ v).getD false

/-- The restricted function, on the stars. -/
def restr {V : Type} (ρ : Restr V) (f : BF V) : BF (Stars ρ) := fun y => f (fill ρ y)

/-- A levelled family of gate functions of depth at most `k` over bottom functions with
certificates of size `w`. Every gate has a level between `2` and `k` and is the OR or the AND
of a set of inputs, each a gate of smaller level or a `Low w` function (a literal, a constant,
or after a round a function of small decision tree depth). Fan-in is not bounded and gates
with equal functions are one gate. -/
def IsCirc {V : Type} (w k : ℕ) (G : Finset (BF V)) (lev : BF V → ℕ) : Prop :=
  ∀ g ∈ G, 2 ≤ lev g ∧ lev g ≤ k ∧ ∃ I : Set (BF V),
    (∀ h ∈ I, (h ∈ G ∧ lev h < lev g) ∨ Low w h) ∧
    ((∀ x, g x = true ↔ ∃ h ∈ I, h x = true) ∨ (∀ x, g x = true ↔ ∀ h ∈ I, h x = true))

/-! ## The two interfaces -/

open scoped Classical in
/-- The switching lemma, counting form, semantic. For `f` with 1-certificates of size `w`,
among the restrictions with exactly `l` stars, those under which `f` fails to have both kinds
of certificates of size `t` number at most a `(8 w l / (N - l))^t` fraction. From the encoding
bound `bad ≤ |R(l - t)| (4w)^t` and `|R(l - t)| (N - l)^t ≤ |R(l)| (2l)^t`. -/
def SwitchingSem : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (w t l : ℕ) (f : BF V), Cert1 w f →
    (Finset.univ.filter fun ρ : Restr V =>
        Fintype.card (Stars ρ) = l ∧ ¬ Low t (restr ρ f)).card * (Fintype.card V - l) ^ t ≤
      (Finset.univ.filter fun ρ : Restr V => Fintype.card (Stars ρ) = l).card * (8 * w * l) ^ t

/-- The bridge. A circuit of AND, OR and NOT gates of depth at most `d` (NOT gates counted)
deciding parity on `n` bits gives a levelled family over literals and constants (`Low 1`), of
depth at most `d + 1` (level of a gate: one more than its grade), with at most `2 (n + s) + 2`
gate functions (the bound of `Switching.Bridge.layered`), containing the output function
unless that is a literal or a constant. -/
def BridgeStmt : Prop :=
  ∀ (d n : ℕ) (C : Circuit),
    (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    C.depth n ≤ d → C.Decides ({x : List Bool | x.count true % 2 = 1} : Language Bool) n →
    ∃ (G : Finset (BF (Fin n))) (lev : BF (Fin n) → ℕ) (f : BF (Fin n)),
      G.card ≤ 2 * (n + C.size) + 2 ∧ IsCirc 1 (d + 1) G lev ∧ (f ∈ G ∨ Low 1 f) ∧ IsPar f

/-! ## The chain -/

/-- One round. A levelled family of depth `k ≥ 3` with fewer than `2^t` gates over `Low w`
functions, `w ≤ t`: for any number `l` of stars with `16 w l ≤ N - l` some restriction with
`l` stars turns every level-2 gate into a `Low t` function, so the restricted family has depth
`k - 1` over `Low t` functions and no more gates. (Union bound over the level-2 gates, each a
`Cert1 w` or `Cert0 w` function, with `SwitchingSem`.) -/
def Round : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (w t k l : ℕ) (G : Finset (BF V)) (lev : BF V → ℕ),
    1 ≤ t → w ≤ t → 3 ≤ k → IsCirc w k G lev → G.card < 2 ^ t → l ≤ Fintype.card V →
    16 * w * l ≤ Fintype.card V - l →
    ∃ (ρ : Restr V) (G' : Finset (BF (Stars ρ))) (lev' : BF (Stars ρ) → ℕ),
      Fintype.card (Stars ρ) = l ∧ G'.card ≤ G.card ∧ IsCirc t (k - 1) G' lev' ∧
      ∀ f : BF V, (f ∈ G ∨ Low w f) → (restr ρ f ∈ G' ∨ Low t (restr ρ f))

/-- The iteration. A levelled family of depth `K ≥ 3` over literals with fewer than `2^t`
gates whose output is parity or its negation: after one round keeping a seventeenth of the
variables and `K - 3` rounds each keeping one in `16 t + 1`, at most `t` variables are left. -/
def Iterate : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (K t : ℕ) (G : Finset (BF V)) (lev : BF V → ℕ)
    (f : BF V), 3 ≤ K → 1 ≤ t → IsCirc 1 K G lev → G.card < 2 ^ t → (f ∈ G ∨ Low 1 f) → IsPar f →
    Fintype.card V / (17 * (16 * t + 1) ^ (K - 3)) ≤ t

/-- The arithmetic. With `t = log2 (2 (n + s) + 2) + 1` the conclusion of `Iterate` at
`K = d + 1` gives the recorded inequality, for one constant and all large `n` (for large `n`
a circuit with fewer than `n` gates is excluded outright, so the `n` inside the logarithm is
absorbed). -/
def FinalArith : Prop :=
  ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : ℕ,
    n / (17 * (16 * (Nat.log 2 (2 * (n + s) + 2) + 1) + 1) ^ (d - 2)) ≤
      Nat.log 2 (2 * (n + s) + 2) + 1 →
    n ≤ (c * Nat.log 2 s) ^ (d - 1)

/-- The recorded statement of L-lib-034. -/
def Stmt034 : Prop :=
  ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → C.depth n ≤ d → C.Decides ({x : List Bool | x.count true % 2 = 1} : Language Bool) n → n ≤ (c * Nat.log 2 C.size) ^ (d - 1)

/-- `SwitchingSem` gives `Round`. -/
def RoundOfSwitching : Prop := SwitchingSem → Round

/-- `Round` gives `Iterate` (with the base case and parity under restriction). -/
def IterateOfRound : Prop := Round → Iterate

/-- The assembly of the recorded statement. -/
def Assembly : Prop := BridgeStmt → Iterate → FinalArith → Stmt034

end PEqualNP.CircuitLowerBounds.Switching.Plan
