import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Definitions of the proof complexity program: matching moments

Families of values in the two-element field on partial matchings of pigeons to holes. They
are the dual objects of degree-bounded polynomial calculus on the functional pigeonhole
system: a consistent family is a linear functional that kills every static consequence.
The ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- A partial matching of `m` pigeons to `N` holes: a finite set of pairs in which two
different pairs share neither their pigeon nor their hole. -/
def IsPartialMatching {m N : ℕ} (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

/-- The family `z` is consistent up to size `k`: for every partial matching `T` with fewer
than `k` pairs and every pigeon `i` not in `T`, the value at `T` is the sum, over the holes
`j` not used by `T`, of the values at `T` with the pair `(i, j)` added. Only the values of `z`
on partial matchings of at most `k` pairs matter. -/
def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

/-- The extension property at level `k`: every family consistent up to size `k` agrees, on
partial matchings of at most `k` pairs, with a family consistent up to size `k + 1`. -/
def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

end PEqualNP.ProofComplexity
