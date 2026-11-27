import PEqualNP.Defs.ProofComplexityLift
import PEqualNP.ProofComplexity.Helpers.SizeWidth1
import PEqualNP.ProofComplexity.Helpers.Lin

/-!
# Plan for L-pcx-073 (a size against cross-incidence bound for Res(⊕) on a lifted formula)

Nothing here is a recorded lemma. This file fixes the definitions and the interface statements
so that the parts of the proof can be written independently, and proves the final assembly
(`assembly`, the recorded statement of L-pcx-073 word for word) from those statements.

The method has no probability and no affine substitution. The gadget `ipGadget` has ten zeros
and six ones, listed as `zeroPt` and `onePt`. A choice `c : V → Fin 10 × Fin 6` picks one zero
and one one for every block. An assignment `x : V → Bool` of the base variables is embedded
block by block (`emb c x`): the block of `v` gets the chosen one if `x v` is true and the
chosen zero otherwise, so the gadget values of `emb c x` are `x` (`liftAssign_emb`). The
restricted set of a line `L` is `S c L`, the set of `x` whose embedding falsifies `L`.

The parts:

* `StmtBlock` (proved here by `decide`, `stmtBlock`): for an equation on one block with
  nonempty support, at most 48 of the 60 pairs (zero, one) do not both satisfy it.
* `StmtKill`: for a block `v` cut by a block-local equation of `L` there is a set of at most
  48 pairs such that every choice whose pair at `v` is outside it empties `S c L`.
* `StmtCount`: pure counting over the choices. Given a list of pairs (set of blocks, a set of
  at most 48 pairs for each block of it), each with at least `w` blocks, of length `s` with
  `s * 4 ^ w < 5 ^ w`, some choice leaves, for every entry, the set of pairs at some block.
* `StmtJunta`: for every choice and every line, `S c L` depends only on the blocks touched by
  the equations of `L`, and there are at most
  `(lineLocalBlocks L).card + lineCrossInc L` of them.
* `StmtSem`: for every choice, the restricted sets of the lines of a Res(⊕) derivation from
  a lift of `F` form a semantic derivation from `F` (`SemDer`).
* `StmtL2`: a semantic refutation of `F` all of whose sets depend on at most `k` variables
  gives a resolution refutation of `F` (no weakening rule) of width at most `3 * k`.

`StmtBlock` is used by the proof of `StmtKill` only; the assembly takes the other five.
-/

namespace PEqualNP.ProofComplexity.LiftClass

open PEqualNP.ProofComplexity

/-- The ten zeros of the gadget. -/
def zeroPt : Fin 10 → Fin 4 → Bool :=
  ![![false, false, false, false], ![true, false, false, false], ![false, true, false, false],
    ![false, false, true, false], ![true, false, true, false], ![false, true, true, false],
    ![false, false, false, true], ![true, false, false, true], ![false, true, false, true],
    ![true, true, true, true]]

/-- The six ones of the gadget. -/
def onePt : Fin 6 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, true, true, false], ![true, true, false, true],
    ![false, false, true, true], ![true, false, true, true], ![false, true, true, true]]

theorem ipGadget_zeroPt : ∀ i : Fin 10, ipGadget (zeroPt i) = false := by decide

theorem ipGadget_onePt : ∀ j : Fin 6, ipGadget (onePt j) = true := by decide

/-- The embedding of a base assignment `x` under the choice `c`: the block of `v` gets the
chosen one of the gadget if `x v` is true, the chosen zero otherwise. -/
def emb {V : Type} (c : V → Fin 10 × Fin 6) (x : V → Bool) : V × Fin 4 → Bool :=
  fun u => if x u.1 = true then onePt (c u.1).2 u.2 else zeroPt (c u.1).1 u.2

theorem liftAssign_emb {V : Type} (c : V → Fin 10 × Fin 6) (x : V → Bool) :
    liftAssign (emb c x) = x := by
  funext v
  show ipGadget (fun j => if x v = true then onePt (c v).2 j else zeroPt (c v).1 j) = x v
  cases hx : x v
  · simpa using ipGadget_zeroPt (c v).1
  · simpa using ipGadget_onePt (c v).2

/-- The restricted set of the line `L` under the choice `c`: the base assignments whose
embedding falsifies `L`. -/
def S {V : Type} (c : V → Fin 10 × Fin 6) (L : LinClause (V × Fin 4)) : Set (V → Bool) :=
  {x | ¬ LinClauseSat (emb c x) L}

/-- The set `A` of assignments depends only on the variables in `U`. -/
def DependsOn {V : Type} (A : Set (V → Bool)) (U : Finset V) : Prop :=
  ∀ x y : V → Bool, (∀ v ∈ U, x v = y v) → (x ∈ A ↔ y ∈ A)

/-- The blocks touched by the equations of a line. -/
def lineBlocks {V : Type} [DecidableEq V] (L : LinClause (V × Fin 4)) : Finset V :=
  L.biUnion eqBlocks

/-- A semantic derivation from `F`, NEWEST SET FIRST: every set of assignments in the list is
inside the falsifying cube of a clause of `F`, or inside the union of two sets after it in the
list (the two may be the same set, which is weakening). -/
inductive SemDer {V : Type} (F : Set (Clause V)) : List (Set (V → Bool)) → Prop
  | nil : SemDer F []
  | ax {σ : List (Set (V → Bool))} {A : Set (V → Bool)} {C : Clause V} :
      SemDer F σ → C ∈ F → (∀ x ∈ A, ¬ ClauseSat x C) → SemDer F (A :: σ)
  | inf {σ : List (Set (V → Bool))} {A A₁ A₂ : Set (V → Bool)} :
      SemDer F σ → A₁ ∈ σ → A₂ ∈ σ → A ⊆ A₁ ∪ A₂ → SemDer F (A :: σ)

instance {V : Type} (a : V → Bool) (q : LinEq V) : Decidable (LinEqSat a q) := by
  unfold LinEqSat; infer_instance

/-- The per-equation counting fact: for an equation on one block with nonempty support, at
most 48 of the 60 pairs (zero, one) do not both satisfy it. -/
def StmtBlock : Prop :=
  ∀ (f : Finset (Fin 4)) (b : Bool), f.Nonempty →
    (Finset.univ.filter (fun ij : Fin 10 × Fin 6 =>
      ¬ (LinEqSat (zeroPt ij.1) (f, b) ∧ LinEqSat (onePt ij.2) (f, b)))).card ≤ 48

/-- A block cut by a block-local equation of `L` kills `L` under all but at most 48 of the 60
pairs at that block. -/
def StmtKill : Prop :=
  ∀ (V : Type) [DecidableEq V] (L : LinClause (V × Fin 4)) (v : V), v ∈ lineLocalBlocks L →
    ∃ B : Finset (Fin 10 × Fin 6), B.card ≤ 48 ∧
      ∀ c : V → Fin 10 × Fin 6, c v ∉ B → S c L = ∅

/-- Counting over the choices: each entry of the list is a set of at least `w` blocks with a
set of at most 48 pairs at each of them; if the list is short, some choice leaves, for every
entry, the set of pairs at some block of the entry. -/
def StmtCount : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (ls : List (Finset V × (V → Finset (Fin 10 × Fin 6)))) (w : ℕ),
    (∀ e ∈ ls, w ≤ e.1.card ∧ ∀ v ∈ e.1, (e.2 v).card ≤ 48) →
    ls.length * 4 ^ w < 5 ^ w →
    ∃ c : V → Fin 10 × Fin 6, ∀ e ∈ ls, ∃ v ∈ e.1, c v ∉ e.2 v

/-- The restricted set of a line depends only on the blocks its equations touch, and these are
at most the local blocks plus the cross incidence. -/
def StmtJunta : Prop :=
  ∀ (V : Type) [DecidableEq V] (c : V → Fin 10 × Fin 6) (L : LinClause (V × Fin 4)),
    DependsOn (S c L) (lineBlocks L) ∧
      (lineBlocks L).card ≤ (lineLocalBlocks L).card + lineCrossInc L

/-- The restricted sets of the lines of a Res(⊕) derivation from a lift of `F` form a semantic
derivation from `F`. -/
def StmtSem : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (G : Set (Clause (V × Fin 4)))
    (π : List (LinClause (V × Fin 4))) (c : V → Fin 10 × Fin 6),
    IsIPLiftOf F G → IsLinDerivation ((fun C => linOfClause C) '' G) π →
    SemDer F (π.map (S c))

/-- From sets depending on few variables to width: a semantic refutation of `F` all of whose
sets depend on at most `k` variables gives a resolution refutation of width at most `3 * k`. -/
def StmtL2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (σ : List (Set (V → Bool))) (k : ℕ),
    SemDer F σ → (Set.univ : Set (V → Bool)) ∈ σ →
    (∀ A ∈ σ, ∃ U : Finset V, U.card ≤ k ∧ DependsOn A U) →
    ∃ ρ : List (Clause V), IsRefutation F ρ ∧ ∀ C ∈ ρ, C.card ≤ 3 * k

set_option maxRecDepth 100000 in
theorem stmtBlock : StmtBlock := by
  unfold StmtBlock
  decide

theorem S_empty_line {V : Type} (c : V → Fin 10 × Fin 6) :
    S c (∅ : LinClause (V × Fin 4)) = Set.univ := by
  ext x
  simp [S, LinClauseSat]

/-- The recorded statement of L-pcx-073, from the parts. -/
theorem assembly (hKill : StmtKill) (hCount : StmtCount) (hJunta : StmtJunta) (hSem : StmtSem)
    (hL2 : StmtL2) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (G : Set (PEqualNP.ProofComplexity.Clause (V × Fin 4))) (π : List (PEqualNP.ProofComplexity.LinClause (V × Fin 4))) (w I₀ : ℕ), 1 ≤ w → PEqualNP.ProofComplexity.IsIPLiftOf F G → PEqualNP.ProofComplexity.IsLinRefutation G π → (∀ L ∈ π, (PEqualNP.ProofComplexity.lineLocalBlocks L).card < w → PEqualNP.ProofComplexity.lineCrossInc L ≤ I₀) → (π.filter (fun L => w ≤ (PEqualNP.ProofComplexity.lineLocalBlocks L).card)).length * 4 ^ w < 5 ^ w → ∃ ρ : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F ρ ∧ ∀ C ∈ ρ, C.card ≤ 3 * (w - 1 + I₀) := by
  intro V _ _ F G π w I₀ hw hLift hRef hCross hSize
  classical
  -- the kill sets, one for each line and each of its local blocks
  let B : LinClause (V × Fin 4) → V → Finset (Fin 10 × Fin 6) := fun L v =>
    if h : v ∈ lineLocalBlocks L then (hKill V L v h).choose else ∅
  have hB : ∀ (L : LinClause (V × Fin 4)) (v : V), v ∈ lineLocalBlocks L →
      (B L v).card ≤ 48 ∧ ∀ c : V → Fin 10 × Fin 6, c v ∉ B L v → S c L = ∅ := by
    intro L v h
    have := (hKill V L v h).choose_spec
    simpa only [B, h, ↓reduceDIte] using this
  -- a choice that kills every line with at least `w` local blocks
  obtain ⟨c, hc⟩ := hCount V
    ((π.filter (fun L => w ≤ (lineLocalBlocks L).card)).map
      (fun L => (lineLocalBlocks L, B L))) w
    (by
      intro e he
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 he
      have hLw : w ≤ (lineLocalBlocks L).card := by simpa using (List.mem_filter.1 hL).2
      exact ⟨hLw, fun v hv => (hB L v hv).1⟩)
    (by simpa using hSize)
  have hdead : ∀ L ∈ π, w ≤ (lineLocalBlocks L).card → S c L = ∅ := by
    intro L hL hLw
    obtain ⟨v, hv, hcv⟩ := hc (lineLocalBlocks L, B L)
      (List.mem_map.2 ⟨L, List.mem_filter.2 ⟨hL, by simpa using hLw⟩, rfl⟩)
    exact (hB L v hv).2 c hcv
  -- the semantic refutation and its width
  refine hL2 V F (π.map (S c)) (w - 1 + I₀) (hSem V F G π c hLift hRef.1)
    (List.mem_map.2 ⟨∅, hRef.2, S_empty_line c⟩) ?_
  intro A hA
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hA
  by_cases hLw : w ≤ (lineLocalBlocks L).card
  · refine ⟨∅, by simp, ?_⟩
    rw [hdead L hL hLw]
    intro x y _
    simp
  · have h1 : (lineLocalBlocks L).card < w := Nat.lt_of_not_le hLw
    have h2 := hCross L hL h1
    have h3 := (hJunta V c L).2
    exact ⟨lineBlocks L, by omega, (hJunta V c L).1⟩

end PEqualNP.ProofComplexity.LiftClass
