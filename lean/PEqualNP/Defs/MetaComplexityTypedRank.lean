import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Typed rank of a Boolean function

Let `f` be a Boolean function on `n` inputs. A pair is an input `x` with `f x = true` together
with an input `y` with `f y = false`. A typing gives every pair a position at which the two
inputs differ. A literal is a position `i` with a bit `b`; the pair `(x, y)` has the literal
`(i, b)` when its position is `i` and `x i = b` (so `y i` is the other bit). For each literal
take the 0/1 matrix of the pairs having it. The typed rank of `f` is the least, over all
typings, of the sum over the `2 * n` literals of the ranks of these matrices over the rationals.

It is a restricted form of span program size: there the matrices of the literals may have any
entries and overlapping supports; here they are 0/1 with disjoint supports.

* `IsTyping n f τ`: `τ` is a typing of `f`.
* `typedMatrix n f τ i b`: the matrix of the pairs having the literal `(i, b)`.
* `HasTypedRank n f s`: some typing has rank sum at most `s`.

Nothing here speaks of formulas; the module imports only Mathlib.
-/

namespace PEqualNP.MetaComplexity

/-- `τ` is a typing of `f`: for every input `x` with `f x = true` and every input `y` with
`f y = false`, the number `τ x y` is a position `i` below `n` at which `x` and `y` differ. The
values of `τ` at other arguments are not constrained and are never used. The values are
natural numbers, not elements of `Fin n`, so that a typing exists when `n = 0` (then `f` is
constant and there is no pair to type). -/
def IsTyping (n : ℕ) (f : (Fin n → Bool) → Bool)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) : Prop :=
  ∀ x y : Fin n → Bool, f x = true → f y = false →
    ∃ i : Fin n, τ x y = (i : ℕ) ∧ x i ≠ y i

/-- The matrix of the literal `(i, b)` under `τ`: rows and columns are all inputs; the entry at
`(x, y)` is `1` when `f x = true`, `f y = false`, `τ x y = i` and `x i = b`, and `0` otherwise.
Rows of inputs where `f` is false and columns of inputs where `f` is true are zero, so the rank
is that of the matrix restricted to the pairs. -/
def typedMatrix (n : ℕ) (f : (Fin n → Bool) → Bool)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (i : Fin n) (b : Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun x y => if f x = true ∧ f y = false ∧ τ x y = (i : ℕ) ∧ x i = b then 1 else 0

/-- `f` has typed rank at most `s`: there is a typing of `f` for which the ranks, over the
rationals, of the `2 * n` literal matrices sum to at most `s`. -/
def HasTypedRank (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ τ : (Fin n → Bool) → (Fin n → Bool) → ℕ, IsTyping n f τ ∧
    (∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank) ≤ s

end PEqualNP.MetaComplexity
