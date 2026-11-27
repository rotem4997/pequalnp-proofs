import PEqualNP.Defs.ProofComplexityPC
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Bitwise

/-!
# Draft definitions for the chain from Res(⊕) to polynomial calculus on bit pigeonhole

Draft, not part of the definitions root. These are the extra notions needed to state the
links of the proof chain of arXiv:2609.23015 (unrefereed) on our own definitions:

* `IsRowLinear m l k f`: the polynomial `f` in the bit variables is row-linear of degree at
  most `k`.
* `bitDecoder m l`: the substitution that reads bit variables as sums of one-hot variables.
* `BlockVar`, `blockProduct`, `blockSystem`: a base system extended by a family of blocks
  with fresh coefficient variables.
-/

namespace PEqualNP.ProofComplexity

open MvPolynomial

/-- `IsRowLinear m l k f`: every monomial of `f` has total degree at most `k` and uses at most
one bit variable of each pigeon `i`, with exponent one (the exponents of the row of `i` sum to
at most one). The zero polynomial and the constants are row-linear for every `k`. This is the
same condition as membership in the helper submodule `Helpers.rowLinear m l k`, whose carrier
is the set of polynomials with support inside the same set of exponent vectors. -/
def IsRowLinear (m l k : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)) : Prop :=
  ∀ u ∈ f.support, (u.sum fun _ e => e) ≤ k ∧ ∀ i : Fin m, ∑ t : Fin l, u (i, t) ≤ 1

/-- The bit decoder. A hole `j : Fin (2 ^ l)` is read as the string of `l` bits of the number
`j`. The decoder is the algebra map that sends the bit variable `(i, t)` to the sum of the
one-hot variables `(i, j)` over the holes `j` whose bit `t` is set. At a one-hot point (pigeon
`i` in exactly one hole) this sum is bit `t` of the hole of pigeon `i`. -/
noncomputable def bitDecoder (m l : ℕ) :
    MvPolynomial (Fin m × Fin l) (ZMod 2) →ₐ[ZMod 2]
      MvPolynomial (Fin m × Fin (2 ^ l)) (ZMod 2) :=
  aeval fun v : Fin m × Fin l =>
    ∑ j : Fin (2 ^ l), if j.val.testBit v.2.val = true then X (v.1, j) else 0

/-- The variables of a base system on `V` extended by `M` blocks of accuracy `h`, each with
`W` inputs: an old variable `Sum.inl v`, or the coefficient variable `Sum.inr (j, u, i)` of
block `j : Fin M`, factor `u : Fin h` and input `i : Fin W`. Different blocks have different
coefficient variables. All blocks have the same number `W` of inputs; a block with fewer
inputs is padded with zero inputs, which changes nothing (see `blockSystem`). -/
abbrev BlockVar (V : Type) (h M W : ℕ) : Type := V ⊕ (Fin M × Fin h × Fin W)

/-- The product of block `j`: over the `h` factors `u`, the product of
`1 + ∑ i, r (j, u, i) * g j i`, where `r` are the coefficient variables of the block and
`g j i` are its inputs, polynomials in the old variables (over `ZMod 2` the sign of the sum
does not matter). With `h = 0`, or with all inputs zero, the product is `1`. -/
noncomputable def blockProduct {V : Type} (h M W : ℕ)
    (g : Fin M → Fin W → MvPolynomial V (ZMod 2)) (j : Fin M) :
    MvPolynomial (BlockVar V h M W) (ZMod 2) :=
  ∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) * rename Sum.inl (g j i))

/-- The base system `F` on the old variables `V` extended by the `M` blocks with inputs `g`
and accuracy `h`. It consists of

* every polynomial of `F`, read in the old variables;
* the Boolean axiom `X r * X r + X r` for every coefficient variable `r`;
* for every block `j` and input `i`, the companion `g j i * blockProduct h M W g j`.

The block product itself is not an axiom. At a Boolean point the companions say: if some
input of block `j` is `1` then the product of block `j` is `0`. A zero input contributes the
zero polynomial as a companion and coefficient variables that occur in no other axiom except
their own Boolean axioms. The inputs are arbitrary polynomials here; statements add the
hypothesis that they are affine (`totalDegree ≤ 1`). -/
def blockSystem {V : Type} (F : Set (MvPolynomial V (ZMod 2))) (h M W : ℕ)
    (g : Fin M → Fin W → MvPolynomial V (ZMod 2)) :
    Set (MvPolynomial (BlockVar V h M W) (ZMod 2)) :=
  {p | (∃ q ∈ F, p = rename Sum.inl q) ∨
    (∃ r : Fin M × Fin h × Fin W, p = X (Sum.inr r) * X (Sum.inr r) + X (Sum.inr r)) ∨
    ∃ (j : Fin M) (i : Fin W), p = rename Sum.inl (g j i) * blockProduct h M W g j}

end PEqualNP.ProofComplexity
