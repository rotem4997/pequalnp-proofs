import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Riffle rank, in the case of two blocks

Riffle rank is a complexity measure for tensors introduced by B. Rossman (Riffle Rank, LAGOS
2025, Procedia Computer Science 273, Definition 3.1). Over a field `F`, a function
`f : [n]^(2k) → F` in the variables `(a₁, b₁, ..., a_k, b_k)` is riffle-basic if it is a product
`B(b₁, ..., b_k) * ∏ i, A_i(b₁, ..., b_(i-1), a_i)` of arbitrary `F`-valued factors, and the
riffle rank of `f` is the least number of riffle-basic functions with sum `f`.

This module states the case `k = 2` only, the one of Question C.1 of that paper: in the
variables `(a, b, c, d) = (a₁, b₁, a₂, b₂)` a riffle-basic function is
`A(a) * C(b, c) * D(b, d)`, with `A = A₁`, `C = A₂` and `D = B`.

The index set `[n]` is any type `X`; `Fin n` is the set of the source. The coefficients are any
type with the operations used, so a statement can be made over every field at once.

* `IsRiffleBasic f`: `f a b c d = A a * C b c * D b d` for some `A`, `C`, `D`.
* `RiffleRankLe r f`: `f` is a sum of `r` riffle-basic functions (so its riffle rank is at
  most `r`; summands may be zero, so the property is monotone in `r` over a ring).
* `pairId X F`: the function `[a = b] * [c = d]`, the tensor square of the identity matrix
  (`I_n ⊗ I_n` in the source, with `X = Fin n`).
-/

namespace PEqualNP.RiffleRank

/-- `f` is riffle-basic (two blocks): `f a b c d = A a * C b c * D b d` for some functions
`A` of `a`, `C` of `(b, c)` and `D` of `(b, d)`. -/
def IsRiffleBasic {X F : Type} [Mul F] (f : X → X → X → X → F) : Prop :=
  ∃ (A : X → F) (C D : X → X → F), ∀ a b c d : X, f a b c d = A a * C b c * D b d

/-- `f` is a sum of `r` riffle-basic functions: its riffle rank is at most `r`. -/
def RiffleRankLe {X F : Type} [Mul F] [AddCommMonoid F] (r : ℕ) (f : X → X → X → X → F) : Prop :=
  ∃ g : Fin r → X → X → X → X → F, (∀ i, IsRiffleBasic (g i)) ∧
    ∀ a b c d : X, f a b c d = ∑ i, g i a b c d

/-- The function `[a = b] * [c = d]`: one when `a = b` and `c = d`, zero otherwise. -/
def pairId (X F : Type) [DecidableEq X] [Zero F] [One F] : X → X → X → X → F :=
  fun a b c d => if a = b ∧ c = d then 1 else 0

end PEqualNP.RiffleRank
