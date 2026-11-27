import PEqualNP.ProofComplexity.Helpers.LiftRankWidth
import PEqualNP.ProofComplexity.Helpers.LiftRankSmall

/-!
# Plan for L-pcx-072 (quadratic size at constant F2 degree)

Nothing here is a recorded lemma: everything below is conjecture until the checker accepts it.
This file fixes the definitions and the interface statements for the quadratic size bound on
the lifted systems of `Helpers.LiftRankPlan`, and proves the induction and the final assembly
from those statements.

The argument (a reading of the printed proof, rebuilt for our rules). Fix a lifted system on an
`(s, δ)` boundary expander. A frozen system also fixes the gadget values of a set `K₀` of blocks
to `β`. A generalised derivation (`GDeriv`) for it has three rules: a semantic axiom (any line
covered by one equation of the frozen system), a semantic resolution step (`SemRes`), and a
semantic weakening. One round:

1. (`StmtPath`) Walk from the empty line toward the axioms, always to a premise that has no
   cover of at most `s / 3` equations. The walk ends at a medium line `z` whose rank satisfies
   `δ * s < 3 * (linRank z + |K₀|)` (closure argument of L-pcx-065 with `K₀` added to the
   closure set). Consecutive lines `A, B` of the walk satisfy `Step A B`: the falsifiers of `A`
   (all of them, or those on one side of a linear equation) falsify `B`.
2. (`StmtStep`, `StmtChain`) The space `impSpace L` of affine equations implied by the negation
   of `L` changes by at most one vector along a `Step`, starts at `⊥` on the empty line, and has
   dimension at least `linRank z` at the end. So one nonzero affine equation `f = a` is implied
   by at least `linRank z` distinct entries of the walk.
3. (`StmtGoodStep`) Pick a bit `(j, u)` of `f`. Choose the frozen value `b` of block `j` so that
   the frozen system stays locally consistent (`Good`).
4. (`StmtSubst`) Fix the other three bits of block `j` so that its gadget value is `b` whatever
   bit `u` is (1-stifling), and substitute for bit `u` the affine form that makes `f = a` false.
   Lines whose image is unfalsifiable are deleted (this kills every entry implying `f = a`);
   the rest is a generalised refutation of the frozen system with one more block, shorter by at
   least the number of killed entries.
5. (`quad_bound`, proved here) With `r` lines killed in a round where `3 * (r + |K₀|) ≤ δ * s`,
   induction gives `T * (T + 1) ≤ 2 * length` for `T = δ * s / 3`.
6. (`assembly_of`, proved here) With `δ = 2`, `s = n₁ / s₀` from L-pcx-043 and `n = 4 * n₁`:
   `n ^ 2 ≤ 576 * s₀ ^ 2 * length`.

Changes from the paper plan, with reasons:

1. The class of the induction is semantic: `GDeriv` takes any line covered by one equation as
   an axiom and uses semantic resolution (`SemRes`). Reason: after substitution the axioms are
   no longer clauses of a lifted system, and an image resolvent is only a superset of the
   resolvent of the images. Both would cost extra lines; with the semantic rules the image of a
   derivation is a derivation line for line.
2. The graph never changes. Frozen blocks keep their columns; their gadget values are the
   constants `β` (`fval`). The loss per round is absorbed by adding `K₀` to the closure set in
   the rank bound (`|K₀|` in `StmtPath`).
3. The measure is local consistency, `Good s K₀ β`: every set of at most `s` equations has a
   solution agreeing with `β` on `K₀`. It is what makes the empty line uncoverable. It is kept
   for all rounds with `2 * (|K₀| + 1) ≤ δ * s`, by the closure of `K₀`: the largest set `A` of
   at most `s` equations whose unique neighbours lie in `K₀ ∪ {j}` contains every such set
   (unions stay small by expansion), a solution of `A` from `Good` fixes the value `b`, and
   peeling extends it to any `U`. This is the expander form of "some value of a variable keeps
   the width"; the plain consistency notion would halve `s` at each round.
4. The walk goes to a premise only through `Step`, which is semantic. At a resolution step with
   one side of the pivot empty on the falsifiers of the conclusion, the conclusion is a
   weakening of the other premise, and the walk goes there. This is needed: with `SemRes` the
   premise on an empty side is unconstrained, and the span relation fails for it.
5. The chain lemma is applied to AFFINE spaces (`impSpace`, pairs of a form and a right side),
   not to the spans of forms. Reason: the paper needs one equation `f = a` with the SAME right
   side `a` implied by many lines. With spans of forms the right sides can differ: the
   resolvent `R = {x + y = 0, y = 0}` of `C = {x = 0}` and `D = {x = 1, x + y = 0, y = 0}` has
   `x = 0` on all its falsifiers while `C` has `x = 1` on all of its, although `x` is in both
   spans. On affine spaces the step relation holds (the vector added is `(f, 1)` or `(f, 0)`).
6. Edge cases. Lines on the walk are falsifiable (an unfalsifiable line is covered by no
   equation), so `impSpace` never jumps to the whole space on the walk. The walk is a `Sublist`
   of the refutation, so its entries are distinct entries of the list even when a line repeats.
   Weakening can drop the dimension of `impSpace` by any amount; the chain lemma needs only that
   growth toward the end is one vector per step and that the start is `⊥`
   (checked on `0, <a>, <a, b>, 0, <c>, <c, d>`: `c` lies in the last two).
-/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily PEqualNP.ProofComplexity.LiftRank

/-! ### Definitions -/

/-- The gadget values of a frozen system: the blocks of `K₀` have the constant values `β`. -/
def fval {N : ℕ} (K₀ : Finset (Fin N)) (β : Fin N → Bool) (a : Fin N × Fin 4 → Bool) :
    Fin N → Bool :=
  fun j => if j ∈ K₀ then β j else gval a j

/-- The set `U` of equations covers the line `L` in the frozen system: every assignment that
falsifies `L` violates an equation of `U`, read on the frozen gadget values. -/
def FCovers {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (U : Finset (Fin m)) (L : LinClause (Fin N × Fin 4)) : Prop :=
  ∀ a : Fin N × Fin 4 → Bool, ¬ LinClauseSat a L → ∃ i ∈ U, ¬ LinEqSat (fval K₀ β a) (G i, c i)

/-- Semantic resolution on the form `f`: every falsifier of `R` falsifies `C` when `f = 1`
and `D` when `f = 0`. A syntactic resolvent (with `(f, false) ∈ C`, `(f, true) ∈ D`) is one. -/
def SemRes {V : Type} (C D R : LinClause V) : Prop :=
  ∃ f : Finset V, ∀ a : V → Bool, ¬ LinClauseSat a R →
    (LinEqSat a (f, true) → ¬ LinClauseSat a C) ∧ (¬ LinEqSat a (f, true) → ¬ LinClauseSat a D)

/-- A generalised derivation for the frozen system, NEWEST LINE FIRST: each line is covered
by one equation (a semantic axiom), a semantic resolvent of two later lines, or a weakening of
a later line. -/
inductive GDeriv {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) : List (LinClause (Fin N × Fin 4)) → Prop
  | nil : GDeriv G c K₀ β []
  | ax {π : List (LinClause (Fin N × Fin 4))} {L : LinClause (Fin N × Fin 4)} :
      GDeriv G c K₀ β π → (∃ i : Fin m, FCovers G c K₀ β {i} L) → GDeriv G c K₀ β (L :: π)
  | res {π : List (LinClause (Fin N × Fin 4))} {C D R : LinClause (Fin N × Fin 4)} :
      GDeriv G c K₀ β π → C ∈ π → D ∈ π → SemRes C D R → GDeriv G c K₀ β (R :: π)
  | weak {π : List (LinClause (Fin N × Fin 4))} {C D : LinClause (Fin N × Fin 4)} :
      GDeriv G c K₀ β π → C ∈ π →
        (∀ a : Fin N × Fin 4 → Bool, LinClauseSat a C → LinClauseSat a D) →
        GDeriv G c K₀ β (D :: π)

/-- A generalised refutation: a generalised derivation containing the empty line. -/
def GRef {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (π : List (LinClause (Fin N × Fin 4))) : Prop :=
  GDeriv G c K₀ β π ∧ (∅ : LinClause (Fin N × Fin 4)) ∈ π

/-- Local consistency of the frozen system: every set of at most `s` equations has a solution
that agrees with `β` on the frozen blocks. -/
def Good {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (s : ℕ) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) : Prop :=
  ∀ U : Finset (Fin m), U.card ≤ s →
    ∃ x : Fin N → Bool, (∀ j ∈ K₀, x j = β j) ∧ ∀ i ∈ U, LinEqSat x (G i, c i)

/-- Some assignment falsifies the line. -/
def Falsifiable {V : Type} (L : LinClause V) : Prop := ∃ a : V → Bool, ¬ LinClauseSat a L

/-- Every assignment falsifying `L` satisfies the equation `q`. -/
def Imp {V : Type} (L : LinClause V) (q : LinEq V) : Prop :=
  ∀ a : V → Bool, ¬ LinClauseSat a L → LinEqSat a q

/-- The affine equations implied by the negation of `L`: pairs `(g, b)` with `g · x = b` at
every falsifier `x` of `L`. It is `⊤` when `L` is unfalsifiable. -/
def impSpace {V : Type} [Fintype V] [DecidableEq V] (L : LinClause V) :
    Submodule (ZMod 2) ((V → ZMod 2) × ZMod 2) where
  carrier := {p | ∀ a : V → Bool, ¬ LinClauseSat a L → p.1 ⬝ᵥ vec a = p.2}
  add_mem' := by
    intro p q hp hq a ha
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [Prod.fst_add, Prod.snd_add, add_dotProduct, hp a ha, hq a ha]
  zero_mem' := by
    intro a _
    simp
  smul_mem' := by
    intro r p hp a ha
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, hp a ha]

theorem mem_impSpace {V : Type} [Fintype V] [DecidableEq V] (L : LinClause V)
    (p : (V → ZMod 2) × ZMod 2) :
    p ∈ impSpace L ↔ ∀ a : V → Bool, ¬ LinClauseSat a L → p.1 ⬝ᵥ vec a = p.2 := Iff.rfl

/-- One step of the walk, from the line `R` to the line `P`: every falsifier of `R` falsifies
`P`, or every falsifier of `R` with `f = b` falsifies `P` and there is one. -/
def Step {V : Type} (R P : LinClause V) : Prop :=
  (∀ a : V → Bool, ¬ LinClauseSat a R → ¬ LinClauseSat a P) ∨
    ∃ (f : Finset V) (b : Bool), (∃ a : V → Bool, ¬ LinClauseSat a R ∧ LinEqSat a (f, b)) ∧
      ∀ a : V → Bool, ¬ LinClauseSat a R → LinEqSat a (f, b) → ¬ LinClauseSat a P

/-! ### Interface statements, one per proof leg -/

/-- Leg A1, the subspace chain lemma (pure linear algebra). Along a list starting at `⊥` in
which each space lies in the previous one plus one vector, a nonzero vector of the last space
lies in at least `k` entries, for every `1 ≤ k ≤ dim` of the last space. Proof: intersect with
the last space `W`; the relation is kept; let `j` be the last index where the dimension of the
intersection is at most `k - 1`; it is exactly `k - 1`, every later entry contains `W`, and
induction on the prefix gives the rest. -/
def StmtChain : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (α : Type) (E : α → Submodule (ZMod 2) M) (l : List α) (x z : α) (k : ℕ),
    l.head? = some x → E x = ⊥ → l.getLast? = some z →
    l.IsChain (fun A B => ∃ y : M, E B ≤ E A ⊔ Submodule.span (ZMod 2) {y}) →
    1 ≤ k → k ≤ Module.finrank (ZMod 2) (E z) →
    ∃ v ∈ E z, v ≠ 0 ∧ ∃ l' : List α, l'.Sublist l ∧ k ≤ l'.length ∧ ∀ A ∈ l', v ∈ E A

/-- Leg A2, the step relation. First case: `impSpace P ≤ impSpace R`. Second case, with `F` the
falsifiers of `R` with `f = b` (nonempty): `impSpace P ≤ impSpace R ⊔ span {(ind f, toZ b)}`.
For `(g, e)` implied on `F`: if `g ∈ formSpan R ⊔ span {ind f}` write `g = h + λ ind f`
(`h` is constant on the falsifiers of `R`); otherwise `exists_perp_of_notMem` gives `w` killing
`formSpan R` and `ind f` with `g · w ≠ 0`, and `x`, `x + w` in `F` (`fals_add`) contradict. -/
def StmtStep : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (R P : LinClause V), Step R P →
    ∃ y : (V → ZMod 2) × ZMod 2, impSpace P ≤ impSpace R ⊔ Submodule.span (ZMod 2) {y}

/-- Leg B, the walk. Port of `medium_or_small`, `covers_ustar`, `medium_rank` and
`not_covers_empty` of `Helpers.LiftRankWidth` to `FCovers`. By induction on `GDeriv`: every
entry `L` with no cover of at most `s / 3` equations starts a walk (a `Sublist`, `Step` at
each link) ending at a medium line. A semantic axiom is small (`3 ≤ s`); a weakening goes to its
premise; at `SemRes C D L` on `f`, go to a side whose falsifiers are nonempty and whose
premise is not small, else `L` is medium (the covers of the two sides have total size at most
`2 s / 3`). The empty line is not small by `Good`. At the medium end `z`, `ustar (K ∪ K₀) U`
covers `z` (`closure` gives `K`, the frozen values are constants), so
`δ * s < 3 * δ * |ustar| ≤ 3 * (|K| + |K₀|)`. A non-small line is falsifiable. -/
def StmtPath : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N)) (β : Fin N → Bool)
    (s δ : ℕ), IsBdryExpander G s δ → 3 ≤ s → 1 ≤ δ → Good G c s K₀ β →
    ∀ π : List (LinClause (Fin N × Fin 4)), GRef G c K₀ β π →
      ∃ path : List (LinClause (Fin N × Fin 4)), path.Sublist π ∧ path.head? = some ∅ ∧
        path.IsChain Step ∧ ∃ z, path.getLast? = some z ∧ Falsifiable z ∧
          δ * s < 3 * (linRank z + K₀.card)

/-- Leg C, substitution and pruning. Let `σ` fix the bits `(j, u')`, `u' ≠ u`, to constants
that force gadget value `b` on block `j` (`ip2_stifled`), and set bit `(j, u)` to the affine
form (in the bits outside block `j`) that makes `f = a` false. It acts on equations
syntactically (`LinEqSat y (σ q) ↔ LinEqSat (σ y) q`), and `fval K₀ β (σ y) =
fval (insert j K₀) (update β j b) y`. `π'` is the image of the entries whose image is
falsifiable. Semantic axioms go to semantic axioms; a weakening of a deleted line is deleted; a
semantic resolvent of a deleted line is a weakening of the image of the other premise (or is
deleted); otherwise it is a semantic resolvent of the images on the substituted form (sides
swapped if the constant flips). Every entry implying `f = a` has an unfalsifiable image. -/
def StmtSubst : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N)) (β : Fin N → Bool)
    (j : Fin N) (u : Fin 4) (f : Finset (Fin N × Fin 4)) (a b : Bool), (j, u) ∈ f →
    (j ∈ K₀ → b = β j) → ∀ π : List (LinClause (Fin N × Fin 4)), GDeriv G c K₀ β π →
      ∃ π' : List (LinClause (Fin N × Fin 4)),
        GDeriv G c (insert j K₀) (Function.update β j b) π' ∧ (∅ ∈ π → ∅ ∈ π') ∧
        ∀ l' : List (LinClause (Fin N × Fin 4)), l'.Sublist π → (∀ L ∈ l', Imp L (f, a)) →
          π'.length + l'.length ≤ π.length

/-- Leg D, keeping local consistency. If `j ∉ K₀`, let `K' = insert j K₀` and `A` a largest set
of at most `s` equations with `uniqueNbrs G A ⊆ K'`. Any such `T` has `δ * |T| ≤ |K'|`, so
`|T ∪ A| ≤ s` and `T ∪ A` is such a set: `T ⊆ A`. `Good` solves `A` (agreeing with `β`); its
value at `j` is `b`; `peel` relative to `K'` extends it to any `U`. If `j ∈ K₀`, `b = β j`. -/
def StmtGoodStep : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (j : Fin N), IsBdryExpander G s δ → 1 ≤ δ →
    2 * (K₀.card + 1) ≤ δ * s → Good G c s K₀ β →
    ∃ b : Bool, (j ∈ K₀ → b = β j) ∧ Good G c s (insert j K₀) (Function.update β j b)

/-- The recorded statement of L-pcx-072, verbatim. -/
def Stmt072 : Prop :=
  ∃ w d c : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)), (∀ C ∈ F, C.card ≤ w) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) d ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → n ^ 2 ≤ c * π.length

/-- The assembly (proved below as `assembly_of`). -/
def StmtAssemblyQuad : Prop :=
  StmtChain → StmtStep → StmtPath → StmtSubst → StmtGoodStep → Stmt072

end PEqualNP.ProofComplexity.LiftQuad
