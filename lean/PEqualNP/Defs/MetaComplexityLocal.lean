import Mathlib.Data.Nat.Log
import PEqualNP.Defs.MetaComplexity

/-!
# Local maps, for the meta-complexity program

One definition: a map on `n`-bit inputs every output position of which is fixed by few input
positions. It is the only notion of a local reduction the program's statements use; it speaks
of no machine. The ruling behind it is in `MetaComplexity/README.md`.
-/

namespace PEqualNP.MetaComplexity

/-- The map `w` on inputs of length `n` is `q`-local: for every output position `j` and every
input `x` there are at most `q` input positions such that every input agreeing with `x` on them
has the same symbol at position `j` of its output (the same bit, or in both cases no bit, so
the output length may vary with the input). This is "certificate complexity at most `q`" of
every output position. It is implied by: position `j` of the output is computed in `q` steps
with random access to the input. A statement that assumes only this is therefore stronger than
one about reductions computable in local time `q`. -/
def QueryLocal (n q : ℕ) (w : (Fin n → Bool) → List Bool) : Prop :=
  ∀ (j : ℕ) (x : Fin n → Bool), ∃ S : Finset (Fin n), S.card ≤ q ∧
    ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → (w y)[j]? = (w x)[j]?

end PEqualNP.MetaComplexity
