import PEqualNP.MetaComplexity.Helpers.LocModel
import PEqualNP.MetaComplexity.Helpers.LocGraph

/-!
# Monotone local-class bound (`L-meta-115`): the plan, reduced to named pieces

Plan module of the last-gate line. Every piece below is a closed `Prop` (NOT proved here); the
assemblies `fan_of_pieces`, `step_of_pieces`, `main_of_pieces` and `loc_of_pieces` are proved.
Target: `RowStmt`, the statement of `L-meta-115`.

Paper: `routes/lifting/lgp/g97-local-class.md` (Theorem LOC) and the proof sheet
`routes/lifting/lgp/FO1-monotone-direct.md` (sections 0 to 7, holes H1 to H9 of section 9), with
`gadv32-class.md` (free steps), `gadv33-fanout2.md` (FO2), `gadv31-direct.md` (case table),
`gadv27-FC.md` and `gadv44-local-class.md`.

Two tiers. Tier 1 (`P...` and `ToolLeast`): the pieces the assembly consumes. Tier 2 (`Tool...`):
tools with a fixed statement, so that builders of different tier 1 pieces share one interface.

Conventions. Model layer `LocModel.lean`, graph layer `LocGraph.lean`. The arity `n` is fixed;
a restriction deletes edges. `Phi1 G A = |A| + |E| + tau`, and the bound is `Phi1 ≤ size + 1`.
The class is closed under every subgraph `G' ≤ G`, so the induction hypothesis `IH` speaks of all
subgraphs with fewer edges (and of the same graph with fewer free inputs). A run is symmetric
(`Run.symm`), so each cell is stated once, at one end, and used at both ends.
-/

namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open SimpleGraph

/-! ## The frame of the induction -/

/-- The bound for circuits with no NOT gate. -/
abbrev Bound {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  BoundOf (HasMonoSize n) G A

/-- The induction hypothesis at `(G, A)`: the bound at every subgraph with fewer edges (any free
inputs), and at the same graph with fewer free inputs. -/
def IH {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)), G' ≤ G → AFree G' A' →
    (G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) → Bound G' A'

/-- A counterexample under the induction hypothesis: a least circuit with no NOT gate for
`F G A`, at least two gates below `Phi1`. Every cell derives `False` or a shape from it. -/
structure Cex {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) :
    Prop where
  inv : AFree G A
  ih : IH G A
  least : MLeast n (F G A) gs o
  small : gs.length + 2 ≤ Phi1 G A

/-- A counterexample at a run, with no free input. -/
structure Ctx {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) : Prop where
  cex : Cex G A gs o
  run : Run G a' a s t b b'
  hA : A = ∅

theorem Ctx.symm {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    {a' a s t b b' : Fin n} (h : Ctx G A gs o a' a s t b b') : Ctx G A gs o b' b t s a a' :=
  ⟨h.cex, h.run.symm, h.hA⟩

/-- Fan-out one at the four inner vertices of the run: the readers are `qa, qs, qt, qb`. -/
structure Fan {n : ℕ} (gs : List Gate) (a s t b : Fin n) (qa qs qt qb : ℕ) : Prop where
  fa : RdSet gs a = {qa}
  fs : RdSet gs s = {qs}
  ft : RdSet gs t = {qt}
  fb : RdSet gs b = {qb}

theorem Fan.symm {n : ℕ} {gs : List Gate} {a s t b : Fin n} {qa qs qt qb : ℕ}
    (h : Fan gs a s t b qa qs qt qb) : Fan gs b t s a qb qt qs qa :=
  ⟨h.fb, h.ft, h.fs, h.fa⟩

/-! ## Tier 2: circuit tools (any graph) -/

/-- TOOL. A function that is not constant and has a NOT-free circuit has a least clean NOT-free
one. Copy of `Parity3.clean_of` and `Readers.exists_least` with the fact that the simplifier
`elim` emits AND from AND and OR from OR only (`simpAnd`, `simpOr` of `Elim.lean`), so a NOT-free
list stays NOT-free. Paper: FO1 D4 (reduction step). Closes: H9 (reduced circuit exists). -/
def ToolLeast : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), (∃ x y : Fin n → Bool, f x ≠ f y) →
    HasMonoSize n f s → ∃ (gs : List Gate) (o : ℕ), MLeast n f gs o ∧ gs.length ≤ s

/-- TOOL. A clean NOT-free list is a NOT-free circuit (as `Readers.has_of_clean`). -/
def ToolOfClean : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ), MClean m gs →
    HasMonoSize m (fun x => vl gs x o) gs.length

/-- TOOL (the cleaning lemma, repaired). Remove a set `S` of aliases and orphans on a set `P` of
input points: a clean list shorter by `|S|`, and a wire map `r` fixing the inputs, such that
every wire that is not an orphan keeps its value on `P`. NOT-freeness is kept. Basis-neutral.
Proof: `r` sends an input to itself, an alias to `r` of its target, a kept gate `p` to
`m + p - #{q ∈ S, q < p}`; the new list is the kept gates with inputs mapped by `r`; induction on
the wire. Material: `SLLive.dropC`, `SLLive.run_drop`, `SLCompile.fold_spec`.
Paper: FO1 D6. Closes: H1. The paper's wording (a gate all of whose readers are dead is dead) is
false when the gate is the target of a copy; the orphan clause of `Removable` repairs it. -/
def ToolRemoval : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ), CleanL m gs → Removable m gs o P S tgt →
    ∃ (gs' : List Gate) (r : ℕ → ℕ), CleanL m gs' ∧ (NotFree gs → NotFree gs') ∧
      gs'.length + S.card ≤ gs.length ∧ (∀ j, j < m → r j = j) ∧
      ∀ j, j < m + gs.length → (∀ p ∈ S, tgt p = none → j ≠ m + p) →
        r j < m + gs'.length ∧ ∀ x ∈ P, vl gs' x (r j) = vl gs x j

/-- TOOL. Fix one input of a clean NOT-free list: if the restricted function is not constant it
has a NOT-free circuit of no larger size, at the same arity. Copy of `Readers.save` at the empty
set, with NOT-freeness of `elim` and of `relabel`. Paper: FO1 D6. -/
def ToolRestrict : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (i : Fin m) (b : Bool), MClean m gs →
    (∃ x y : Fin m → Bool,
      vl gs (Function.update x i b) o ≠ vl gs (Function.update y i b) o) →
    HasMonoSize m (fun x => vl gs (Function.update x i b) o) gs.length

/-- TOOL (fact M). Every wire of a clean NOT-free list is monotone. Paper: FO1 D5. Closes: H2. -/
def ToolMono : Prop :=
  ∀ (m : ℕ) (gs : List Gate), MClean m gs → ∀ x y : Fin m → Bool,
    (∀ i, x i = true → y i = true) → ∀ j, vl gs x j = true → vl gs y j = true

/-- TOOL (fact M0). Every gate of a clean NOT-free list is false at the zero point.
Paper: FO1 D5. Closes: H2. -/
def ToolZero : Prop :=
  ∀ (m : ℕ) (gs : List Gate), MClean m gs → ∀ j, m ≤ j → vl gs (fun _ : Fin m => false) j = false

/-- TOOL. In a least NOT-free circuit of a function that is not constant no gate computes the
function of an earlier wire, inputs included. From `ToolRemoval` on all points. Paper: FO1 D4. -/
def ToolNoAlias : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) → ∀ p, p < gs.length → ∀ j, j < m + p →
      ¬ ∀ x : Fin m → Bool, vl gs x (m + p) = vl gs x j

/-- TOOL. In a least NOT-free circuit of a function that is not constant the output is a wire of
the circuit and every gate other than the output is read. From `ToolRemoval`. Paper: FO1 D4. -/
def ToolLive : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) →
      o < m + gs.length ∧ ∀ p, p < gs.length → o ≠ m + p → (RdSet gs (m + p)).Nonempty

/-- TOOL (Lemma U). If input `t` has the single reader `q`, a gate true at the point `e_t` is
`q` or some reader of `q` is true at `e_t`. Proof: strong induction on the gate; an operand of a
gate true at `e_t` is true at `e_t`, and it is not an input other than `t`.
Paper: FO1 section 5, Lemma U. Closes: H5. -/
def ToolU : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (t : Fin m) (q : ℕ), MClean m gs → RdSet gs t = {q} →
    ∀ p, p < gs.length → vl gs (pt {t}) (m + p) = true →
      p = q ∨ ∃ r ∈ RdSet gs (m + q), vl gs (pt {t}) (m + r) = true

/-- TOOL (fact P and the shortcut). Two points agree on every wire below `K` outside a set `D` of
wires when they agree on the inputs outside `D` and every gate below `K` outside `D` reads
nothing in `D` or is known to agree. Basis-neutral.
Paper: FO1 section 5, fact P; shortcut of B1. Closes: H4, H6. -/
def ToolProp : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (x x' : Fin m → Bool) (D : Set ℕ) (K : ℕ), CleanL m gs →
    (∀ i : Fin m, (i : ℕ) ∉ D → x i = x' i) →
    (∀ p g, gs[p]? = some g → m + p < K → m + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ vl gs x (m + p) = vl gs x' (m + p)) →
    ∀ j, j < K → j ∉ D → vl gs x j = vl gs x' j

/-- TOOL (first half of Lemma 2). Gate `p` is below a wire `W` that is below the output, on `P`,
and input `z` is false on `P`: replacing gate `p` by `AND(z, z)` gives a clean NOT-free list
whose output, joined by OR with `W`, is the old output on `P`; earlier wires are unchanged.
Paper: FO1 section 4, Lemma 2. Closes: H7. -/
def ToolLower : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (z : Fin m) (p W : ℕ),
    MClean m gs → p < gs.length → W < m + p → (∀ x ∈ P, x z = false) →
    (∀ x ∈ P, vl gs x (m + p) = true → vl gs x W = true) →
    (∀ x ∈ P, vl gs x W = true → vl gs x o = true) →
    MClean m (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) ∧
      (∀ x ∈ P, vl gs x o =
        (vl (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) x o || vl gs x W)) ∧
      ∀ (x : Fin m → Bool) (j : ℕ), j < m + p →
        vl (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) x j = vl gs x j

/-- TOOL (second half of Lemma 2). Appending one OR gate. Paper: FO1 section 4, Lemma 2. -/
def ToolSnoc : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (j k : ℕ), MClean m gs → j < m + gs.length → k < m + gs.length →
    MClean m (gs ++ [⟨GateOp.or, [j, k]⟩]) ∧ ∀ x : Fin m → Bool,
      vl (gs ++ [⟨GateOp.or, [j, k]⟩]) x (m + gs.length) = (vl gs x j || vl gs x k) ∧
      ∀ i, i < m + gs.length → vl (gs ++ [⟨GateOp.or, [j, k]⟩]) x i = vl gs x i

/-- TOOL (Lemma 1(a)). Input `s` has the single reader `q = OR(s, w)`, and `t` is a neighbour of
`s`: `w` is false wherever `x_t` is true and `F` is false. Basis-neutral. Without `AFree` it is
false (one edge `st`, `A = {s}`, output the input `s`).
Paper: FO1 section 4, Lemma 1(a). -/
def ToolLemma1a : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (s t : Fin n) (q w : ℕ), AFree G A → CleanL n gs → Computes n gs o (F G A) →
    RdSet gs s = {q} →
    OrRd gs q s w → G.Adj s t → ∀ z : Fin n → Bool, z t = true → F G A z = false →
      vl gs z w = false

/-! ## Tier 2: residual functions and drops (any graph) -/

/-- TOOL. `x_v := 0` deletes the edges at `v`. Paper: FO1 E0. Closes: H3 (part). -/
def ToolRes0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (x : Fin n → Bool),
    v ∉ A → F G A (Function.update x v false) = F (delV G {v}) A x

/-- TOOL. `x_v := 1` frees the neighbours of `v` and deletes the edges at `v` and at them.
Paper: FO1 E1. Closes: H3 (part). -/
def ToolRes1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (N : Finset (Fin n))
    (x : Fin n → Bool), v ∉ A → (∀ w, G.Adj v w ↔ w ∈ N) →
    F G A (Function.update x v true) = F (delV G (insert v N)) (A ∪ N) x

/-- TOOL. A free input set to `0` leaves the set. Paper: gadv32 section 1, S1. -/
def ToolResA : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n) (x : Fin n → Bool),
    AFree G A → a ∈ A → F G A (Function.update x a false) = F G (A.erase a) x

/-- TOOL. The pair `x_t := 1, x_s := 0` with `N(t) = {s, b}`, `b ≠ s`. The identity is false at
`b = s` (witness: one edge). Paper: FO1 E2. Closes: H3 (part). -/
def ToolResPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (s t b : Fin n) (x : Fin n → Bool),
    s ≠ t → b ≠ s → s ∉ A → t ∉ A → b ∉ A → (∀ w, G.Adj t w ↔ w = s ∨ w = b) →
    F G A (Function.update (Function.update x t true) s false) =
      F (delV G {s, t, b}) (insert b A) x

/-- TOOL. Drop at `x_v := 0`, `v` with at most two neighbours: at most 3. Paper: FO1 E0. -/
def ToolDrop0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v u1 u2 : Fin n), G.Adj v u1 →
    (∀ w, G.Adj v w → w = u1 ∨ w = u2) →
    Phi1 G A ≤ Phi1 (delV G {v}) A + 3 ∧ (delV G {v}).edgeSet.ncard < G.edgeSet.ncard

/-- TOOL. Drop at `x_v := 1`, `v` with neighbours `u1, u2` of at most one further neighbour
each: at most 4. Paper: FO1 E1; gadv44 item 5 (the degree of the outer neighbours). -/
def ToolDrop1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v u1 u2 c1 c2 : Fin n),
    (∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) → (∀ w, G.Adj u1 w → w = v ∨ w = c1) →
    (∀ w, G.Adj u2 w → w = v ∨ w = c2) → u1 ∉ A → u2 ∉ A →
    Phi1 G A ≤ Phi1 (delV G (insert v {u1, u2})) (A ∪ {u1, u2}) + 4 ∧
      (delV G (insert v {u1, u2})).edgeSet.ncard < G.edgeSet.ncard

/-- TOOL. Drop at the pair: at most 5. Paper: FO1 E2. -/
def ToolDropPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a s t b c : Fin n),
    [s, t, b].Nodup → (∀ w, G.Adj s w → w = a ∨ w = t) → (∀ w, G.Adj t w ↔ w = s ∨ w = b) →
    (∀ w, G.Adj b w → w = t ∨ w = c) → b ∉ A →
    Phi1 G A ≤ Phi1 (delV G {s, t, b}) (insert b A) + 5 ∧
      (delV G {s, t, b}).edgeSet.ncard < G.edgeSet.ncard

/-! ## Tier 2: rigidity (no vertex pays), from the induction hypothesis -/

/-- TOOL (rigidity at `x_v := 0`). No clean NOT-free list three gates shorter computes `F` on
`{x_v = 0}`. From `ToolRestrict`, `ToolRes0`, `ToolDrop0` and the induction hypothesis.
Paper: FO1 section 2, R. Closes: H3. -/
def ToolPay0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (v u1 u2 : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o → G.Adj v u1 →
    (∀ w, G.Adj v w → w = u1 ∨ w = u2) → (A.Nonempty ∨ ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v) →
    MClean n gs' → gs'.length + 3 ≤ gs.length →
    (∀ x : Fin n → Bool, x v = false → vl gs' x o' = F G A x) → False

/-- TOOL (rigidity at `x_v := 1`, `v` deep). No clean NOT-free list four gates shorter computes
`F` on `{x_v = 1}`. Paper: FO1 section 2, R. Closes: H3. -/
def ToolPay1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (v : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o → Deep G v →
    MClean n gs' → gs'.length + 4 ≤ gs.length →
    (∀ x : Fin n → Bool, x v = true → vl gs' x o' = F G A x) → False

/-- TOOL (rigidity at the pair). No clean NOT-free list five gates shorter computes `F` on
`{x_t = 1, x_s = 0}`. Paper: FO1 section 2, R, and section 6 step 5. Closes: H3. -/
def ToolPayPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o →
    Run G a' a s t b b' → MClean n gs' → gs'.length + 5 ≤ gs.length →
    (∀ x : Fin n → Bool, x t = true → x s = false → vl gs' x o' = F G A x) → False

/-- TOOL (consequences of Lemma 1(a), and L). With OR readers `qs = OR(s, ws)`, `qt = OR(t, wt)`:
the two readers are distinct gates and `ws` is false at `e_a`, `e_t`, `e_b`.
Paper: FO1 section 5, CONSEQUENCES. Uses fact M (H2). -/
def ToolCons : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    qs ≠ qt ∧ vl gs (pt {a}) ws = false ∧ vl gs (pt {t}) ws = false ∧
      vl gs (pt {b}) ws = false

/-! ## Tier 1: graph pieces -/

/-- PIECE. The class is closed under subgraphs. Paper: g97 section 1; gadv44 item 2. -/
def PClosure : Prop :=
  ∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), InL G → G' ≤ G → InL G'

/-- PIECE (structure lemma). A graph of the class with an edge, with no leaf at a vertex of at
most two neighbours and no two leaves at one vertex, has a run of six.
Paper: g97 section 3; gadv44 item 3 and item 5. Closes: H9 (structure lemma), H8. -/
def PStructure : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), InL G → (∃ i j, G.Adj i j) →
    (¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q) →
    (¬ ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p) →
    ∃ a' a s t b b', Run G a' a s t b b'

/-! ## Tier 1: base and free steps -/

/-- PIECE (base). No edge: `|A|` inputs the function depends on need `|A| - 1` gates. From
`HasMonoSize.has` and `PermInputs.dep_lower_set`. Paper: gadv32 section 3. Closes: H9 (base). -/
def PBase : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ i j, ¬ G.Adj i j) → Bound G A

/-- PIECE (free step S1). A free input, set to `0`, costs a gate.
Paper: gadv32 section 1, S1 (with its scope repair: the graph has an edge). Closes: H9. -/
def PS1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), AFree G A → IH G A →
    A.Nonempty → (∃ i j, G.Adj i j) → Bound G A

/-- PIECE (free steps S3, S4). A leaf `l` at a vertex `p` with at most one further neighbour:
two gates at a value chosen by the circuit; the one-edge graph by the count of inputs.
As `ForestBound.claimQ`, first case, in NOT-free form.
Paper: gadv32 section 1, S3 (at degree 2 only) and S4. Closes: H9. -/
def PLeafLow : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n), AFree G A →
    IH G A → A = ∅ → G.Adj l p → (∀ w, G.Adj l w → w = p) →
    (∀ w, G.Adj p w → w = l ∨ w = q) → Bound G A

/-- PIECE (free step S2, twin leaves). Two leaves at one vertex: one gate at `x_l := 0`, the
cover number is kept. As `ForestBound.claimQ`, second case (`cov_swap`), in NOT-free form.
Paper: gadv32 section 1, S2. Closes: H9. -/
def PTwin : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p l' : Fin n), AFree G A →
    IH G A → A = ∅ → G.Adj l p → (∀ w, G.Adj l w → w = p) → G.Adj p l' → l' ≠ l →
    (∀ w, G.Adj l' w → w = p) → Bound G A

/-! ## Tier 1: fan-out at a deep vertex (Lemma FO2), per input -/

/-- PIECE (FO2, fan-out 0 and fan-out at least 3). A deep input has one or two readers: with
none the circuit ignores it; three readers are three aliases at `x_v := 0` (`ToolPay0`).
Paper: FO1 section 3; gadv33 section 1. -/
def PFanLow : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) (v : Fin n),
    Cex G A gs o → Deep G v → 1 ≤ (RdSet gs v).card ∧ (RdSet gs v).card ≤ 2

/-- PIECE (FO2, fan-out 2: the death table). A deep input does not have exactly two readers:
AND + AND and AND + OR pay at `0` (`ToolPay0`), OR + OR pays at `1` (`ToolPay1`).
Paper: FO1 section 3, DEATH TABLE; gadv33 section 1. -/
def PFanTwo : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) (v : Fin n),
    Cex G A gs o → Deep G v → (RdSet gs v).card ≠ 2

/-! ## Tier 1: the case table at a run (each cell once; the mirror by `Run.symm`) -/

/-- PIECE (cell A: A0 to A3). The reader of `x_s` is an OR gate.
Paper: FO1 section 5, CELL A; gadv31 section 1. Uses H2 (fact M), H3. -/
def PCellA : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → ∃ w, OrRd gs qs s w

/-- PIECE (cells "not the output" and B3). The reader `e_t` of `x_t` has one or two readers.
Paper: FO1 section 5, CONSEQUENCES (last line) and B3. -/
def PReadFew : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    1 ≤ (RdSet gs (n + qt)).card ∧ (RdSet gs (n + qt)).card ≤ 2

/-- PIECE (cells B1 with an AND reader: none, B1-AND, with the shortcut). `e_t` does not have a
single reader that is an AND gate.
Paper: FO1 section 5, B1, B1-AND, SHORTCUT; gadv31 section 2. Closes: H4. -/
def PReadOneAnd : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt r : ℕ) (g : Gate), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    RdSet gs (n + qt) = {r} → gs[r]? = some g → g.op = GateOp.and → False

/-- PIECE (cell B1-OR, with the shortcut). `e_t` does not have a single reader that is an OR
gate. Paper: FO1 section 5, B1-OR; gadv31 section 2. Closes: H4. -/
def PReadOneOr : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt r : ℕ) (g : Gate), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    RdSet gs (n + qt) = {r} → gs[r]? = some g → g.op = GateOp.or → False

/-- `e_t` does not have exactly one reader (assembled from the two cells below). -/
def PReadOne : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qt)).card ≠ 1

/-- PIECE (cell B2-OR). If `e_t` has exactly two readers, both are false at `e_t`.
Paper: FO1 section 5, B2-OR and B2-AND. -/
def PReadTwo : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qt)).card = 2 → ∀ q ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + q) = false

/-- PIECE (last cell). With two quiet readers at each of `e_s`, `e_t`, some gate reads both.
Paper: FO1 section 5, LAST CELL; gadv31 section 3. Closes: H5 (through `ToolU`), H6. -/
def PLast : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qs)).card = 2 → (∀ q ∈ RdSet gs (n + qs), vl gs (pt {s}) (n + q) = false) →
    (RdSet gs (n + qt)).card = 2 → (∀ q ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + q) = false) →
    ∃ q, q ∈ RdSet gs (n + qs) ∧ q ∈ RdSet gs (n + qt)

/-- PIECE (Theorem FC). The last cell is impossible: on `{x_t = 1, x_s = 0}` five gates go.
The proof is the planner's rewriting of FO1 section 6 (three cases on the readers of `G_as`:
alias, lowering with one OR added, orphan), since step 2 there needs the shape of the cleaned
circuit. Paper: FO1 section 6; gadv27. Closes: H7. -/
def PFC : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt q : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qs)).card = 2 → (∀ r ∈ RdSet gs (n + qs), vl gs (pt {s}) (n + r) = false) →
    (RdSet gs (n + qt)).card = 2 → (∀ r ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + r) = false) →
    q ∈ RdSet gs (n + qs) → q ∈ RdSet gs (n + qt) → False

/-! ## The assemblies (proved) -/

/-- The step at a run: the statement the cells assemble to. -/
def PStep : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a' a s t b b' : Fin n),
    AFree G A → IH G A → A = ∅ → Run G a' a s t b b' → Bound G A

/-- FO2 from its two pieces: a deep input of a counterexample has exactly one reader. -/
theorem fan_of_pieces (hLow : PFanLow) (hTwo : PFanTwo) {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} {gs : List Gate} {o : ℕ} (v : Fin n) (hc : Cex G A gs o)
    (hd : Deep G v) : ∃ q, RdSet gs v = {q} := by
  have h1 := hLow n G A gs o v hc hd
  have h2 := hTwo n G A gs o v hc hd
  exact Finset.card_eq_one.1 (by omega)

/-- B1 from its two cells: the single reader is an AND or an OR gate. -/
theorem readOne_of_pieces (hAnd : PReadOneAnd) (hOr : PReadOneOr) : PReadOne := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hcard
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hcard
  have hrm : r ∈ RdSet gs (n + qt) := by rw [hr]; exact Finset.mem_singleton_self r
  obtain ⟨g, hg, _⟩ := mem_rdSet.1 hrm
  have hcl := hctx.cex.least.1 r g hg
  have hnf := hctx.cex.least.2.1 g (List.mem_of_getElem? hg)
  rcases hcl with ⟨h1, _⟩ | ⟨h1 | h1, _⟩
  · exact hnf h1
  · exact hAnd n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg h1
  · exact hOr n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg h1

/-- The step from the cells. -/
theorem step_of_pieces (hLeast : ToolLeast) (hLow : PFanLow) (hTwo : PFanTwo) (hA : PCellA)
    (hFew : PReadFew) (hAnd : PReadOneAnd) (hOr : PReadOneOr) (hTwoR : PReadTwo) (hLast : PLast)
    (hFC : PFC) : PStep := by
  have hOne : PReadOne := readOne_of_pieces hAnd hOr
  intro n G A a' a s t b b' hinv hih hA0 hrun s0 hC
  by_contra hlt
  have hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y :=
    F_nc G A (Or.inr ⟨s, t, (hrun.hs t).2 (Or.inr rfl)⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G A) s0 hnc hC
  have hc : Cex G A gs o := ⟨hinv, hih, hL, by omega⟩
  have hctx : Ctx G A gs o a' a s t b b' := ⟨hc, hrun, hA0⟩
  obtain ⟨qa, hqa⟩ := fan_of_pieces hLow hTwo a hc hrun.deep_a
  obtain ⟨qs, hqs⟩ := fan_of_pieces hLow hTwo s hc hrun.deep_s
  obtain ⟨qt, hqt⟩ := fan_of_pieces hLow hTwo t hc hrun.deep_t
  obtain ⟨qb, hqb⟩ := fan_of_pieces hLow hTwo b hc hrun.deep_b
  have hfan : Fan gs a s t b qa qs qt qb := ⟨hqa, hqs, hqt, hqb⟩
  obtain ⟨ws, hws⟩ := hA n G A gs o a' a s t b b' qa qs qt qb hctx hfan
  obtain ⟨wt, hwt⟩ := hA n G A gs o b' b t s a a' qb qt qs qa hctx.symm hfan.symm
  have ht1 := hFew n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have ht2 := hOne n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hs1 := hFew n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws
  have hs2 := hOne n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws
  have hct : (RdSet gs (n + qt)).card = 2 := by omega
  have hcs : (RdSet gs (n + qs)).card = 2 := by omega
  have hqt2 := hTwoR n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hct
  have hqs2 := hTwoR n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws hcs
  obtain ⟨q, hq1, hq2⟩ :=
    hLast n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hcs hqs2 hct hqt2
  exact hFC n G A gs o a' a s t b b' qa qs qt qb ws wt q hctx hfan hws hwt hcs hqs2 hct hqt2
    hq1 hq2

/-- The bound on the whole class, by induction on the number of edges, then on `|A|`. -/
theorem main_of_pieces (hCl : PClosure) (hSt : PStructure) (hB : PBase) (hS1 : PS1)
    (hLL : PLeafLow) (hTw : PTwin) (hStep : PStep) :
    ∀ (n e c : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), G.edgeSet.ncard = e →
      A.card = c → InL G → AFree G A → Bound G A := by
  intro n e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro G A he hc hL hinv
  have hih : IH G A := by
    intro G' A' hle hinv' hlt
    rcases hlt with hlt | ⟨hG, hlt⟩
    · exact ihe _ (by rw [← he]; exact hlt) _ G' A' rfl rfl (hCl n G G' hL hle) hinv'
    · rw [hG]
      rw [hG] at hinv'
      exact ihc _ (by rw [← hc]; exact hlt) G A' he rfl hL hinv'
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · exact hB n G A (fun i j h => hE ⟨i, j, h⟩)
  by_cases hA : A.Nonempty
  · exact hS1 n G A hinv hih hA hE
  have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
  by_cases h1 : ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q
  · obtain ⟨l, p, q, h, h', h''⟩ := h1
    exact hLL n G A l p q hinv hih hA0 h h' h''
  by_cases h2 : ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p
  · obtain ⟨l, p, l', h, h', h'', h3, h4⟩ := h2
    exact hTw n G A l p l' hinv hih hA0 h h' h'' h3 h4
  obtain ⟨a', a, s, t, b, b', hrun⟩ := hSt n G hL hE h1 h2
  exact hStep n G A a' a s t b b' hinv hih hA0 hrun

/-- The statement of `L-meta-115`. -/
def RowStmt : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 7 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ G.edgeFinset.card + T.card ≤ D.size + 1

theorem ncard_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    (G.neighborSet u).ncard = G.degree u := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

/-- The row from the bound on the class. -/
theorem row_of_main
    (h : ∀ (n e c : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), G.edgeSet.ncard = e →
      A.card = c → InL G → AFree G A → Bound G A) : RowStmt := by
  intro n G _ hg hd D hF hN hfun
  have hL : InL G := ⟨hg, fun u v huv hu hv p =>
    hd u v huv (by rwa [ncard_nbr] at hu) (by rwa [ncard_nbr] at hv) p⟩
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  have hM : HasMonoSize n (F G ∅) D.size :=
    ⟨D, hF, hN, le_refl _, fun x => by rw [← hf, ← hfun]; rfl⟩
  have hb := h n _ _ G ∅ rfl rfl hL (fun _ _ _ => by simp) D.size hM
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  refine ⟨T, hT, ?_⟩
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  unfold Phi1 at hb
  rw [Finset.card_empty] at hb
  omega

/-- THE ASSEMBLY. The row from the sixteen pieces. -/
theorem loc_of_pieces (hCl : PClosure) (hSt : PStructure) (hB : PBase) (hS1 : PS1)
    (hLL : PLeafLow) (hTw : PTwin) (hLeast : ToolLeast) (hLow : PFanLow) (hTwo : PFanTwo)
    (hA : PCellA) (hFew : PReadFew) (hAnd : PReadOneAnd) (hOr : PReadOneOr) (hTwoR : PReadTwo)
    (hLast : PLast) (hFC : PFC) : RowStmt :=
  row_of_main (main_of_pieces hCl hSt hB hS1 hLL hTw
    (step_of_pieces hLeast hLow hTwo hA hFew hAnd hOr hTwoR hLast hFC))

end PEqualNP.MetaComplexity.Loc
