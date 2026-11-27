import PEqualNP.Defs.ProofComplexityLin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Definitions of the proof complexity program: lifting by the inner-product gadget

A CNF formula `F` on variables `V` is lifted by replacing each variable by the inner product
`y₀ y₁ + y₂ y₃` (mod 2) of a block of four fresh bits `(v, 0), …, (v, 3)`. The lifted formula is
not fixed here as one clause set: `IsIPLiftOf F G` says only what every encoding of the lift
satisfies, that an assignment falsifying a clause of `G` falsifies, through the gadget, a clause
of `F`. The two measures at the end read a Res(⊕) line as it is written, equation by equation:
the blocks cut by equations that stay inside one block, and the number of (equation, block)
incidences of the equations that touch two or more blocks. The ruling is in
`ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- The gadget: the inner product of two pairs of bits, `y₀ y₁ + y₂ y₃` modulo 2. -/
def ipGadget (y : Fin 4 → Bool) : Bool := xor (y 0 && y 1) (y 2 && y 3)

/-- The assignment of the variables of `F` induced by an assignment of the lifted bits: the
value of `v` is the gadget applied to the block of `v`. -/
def liftAssign {V : Type} (a : V × Fin 4 → Bool) : V → Bool :=
  fun v => ipGadget (fun j => a (v, j))

/-- `G`, a clause set on the lifted bits, is (an encoding of) the lift of `F` by the gadget:
every assignment that falsifies a clause of `G` induces an assignment that falsifies a clause
of `F`. -/
def IsIPLiftOf {V : Type} (F : Set (Clause V)) (G : Set (Clause (V × Fin 4))) : Prop :=
  ∀ D ∈ G, ∃ C ∈ F, ∀ a : V × Fin 4 → Bool, ¬ ClauseSat a D → ¬ ClauseSat (liftAssign a) C

/-- The blocks an equation touches. -/
def eqBlocks {V : Type} [DecidableEq V] (q : LinEq (V × Fin 4)) : Finset V :=
  q.1.image Prod.fst

/-- The blocks cut by the block-local equations of a line: the blocks `v` such that some
equation of the line touches the block `v` and no other block. -/
def lineLocalBlocks {V : Type} [DecidableEq V] (L : LinClause (V × Fin 4)) : Finset V :=
  (L.filter (fun q => (eqBlocks q).card = 1)).biUnion eqBlocks

/-- The cross-block incidence of a line: the sum, over its equations that touch two or more
blocks, of the number of blocks touched. -/
def lineCrossInc {V : Type} [DecidableEq V] (L : LinClause (V × Fin 4)) : ℕ :=
  (L.filter (fun q => 2 ≤ (eqBlocks q).card)).sum (fun q => (eqBlocks q).card)

end PEqualNP.ProofComplexity
