import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.CoverPromise
import PEqualNP.MetaComplexity.Helpers.OwnerLinkDefs

/-!
# Pieces of the assembly of L-meta-444 (the reduction of the complement of SAT to the last-gate problem)

Part 1 of the assembly. For every row the assembly imports that is not yet checked,
`Stmt<id>` is its recorded statement, verbatim, so that the theorems of the assembly take it as a
readable hypothesis and a checked row later discharges it by `exact L<id>`. Then the map of record
(E, N, n, the renaming, the owner lists, `R`, `r`) and the placement objects (e, off, num, H, T_H,
the subdivision S and the forward cover F), each defined so that the rows apply by unfolding. Then
bridge B5 (retyping the output of a polynomial-time map along equal codes).
-/

namespace PEqualNP.MetaComplexity.Reduction

open PEqualNP.Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise
open PEqualNP.MetaComplexity.Helpers.OwnerLink (OWN REN)

/-! ## Recorded statements of the rows not yet checked -/

/-- L-meta-285 (conjecture, unowned): Every cycle of the 2k-fold subdivision of a graph, numbered on Fin, has length at least 6k + 3. Recorded statement, verbatim. -/
def Stmt285 : Prop := ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m)), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → S.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L

/-- L-meta-286 (conjecture, unowned): The 2k-fold subdivision of a graph on Fin has exactly 2k + 1 times as many edges as the graph. Recorded statement, verbatim. -/
def Stmt286 : Prop := ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard

/-- L-meta-290 (conjecture, unowned): Cover shift: if every vertex cover of H has at least c vertices, every cover of its 2k-fold subdivision has at least c + k times the edge count. Recorded statement, verbatim. -/
def Stmt290 : Prop := ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card

/-- L-meta-307 (conjecture, unowned): Placing a graph on Fin N along a numbering injective on its edges keeps every lower bound on cover size. Recorded statement, verbatim. -/
def Stmt307 : Prop := ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card)

/-- L-meta-352 (conjecture, unowned): A map correct on CNF codes and sending non-codes to YES meets the hypothesis of the last-gate hardness row. Recorded statement, verbatim. -/
def Stmt352 : Prop := ∀ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, Function.Injective PEqualNP.Search.encodeCNF → (∀ φ : PEqualNP.Search.CNF, (¬ PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpYes (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2) ∧ (PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpNo (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2)) → (∀ x : List Bool, x ∉ Set.range PEqualNP.Search.encodeCNF → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) → ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2)

/-- L-meta-376 (conjecture, unowned): Given the lower bound and the cover upper bound, an edge-function circuit of size |E| + |T| - 1 is minimal iff the cover T is minimum. Recorded statement, verbatim. -/
def Stmt376 : Prop := (∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1) → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∃ i j : Fin n, G.Adj i j) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → ∃ s : ℕ, s + 1 = G.edgeSet.ncard + S.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size + 1 = G.edgeSet.ncard + T.card → (PEqualNP.MetaComplexity.IsMinimalCircuit n C ↔ ∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card)

/-- L-meta-388 (conjecture, unowned): Given the lower and upper bounds, a cover one above the minimum yields a NO instance of the last-gate problem. Recorded statement, verbatim. -/
def Stmt388 : Prop := (∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1) → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∃ i j : Fin n, G.Adj i j) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → ∃ s : ℕ, s + 1 = G.edgeSet.ncard + S.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card + 1) → (∃ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) ∧ S.card < T.card) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size + 1 = G.edgeSet.ncard + T.card → PEqualNP.MetaComplexity.LgpNo n C

/-- L-meta-473 (conjecture, unowned): Numbering a graph onto Fin N injectively on its edge vertices sends a cover made of edge vertices to a cover of the same size. Recorded statement, verbatim. -/
def Stmt473 : Prop := ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card

/-- L-meta-474 (conjecture, unowned): Every vertex of the cover cvcCover phi has a neighbour in the graph cvcGraph phi. Recorded statement, verbatim. -/
def Stmt474 : Prop := ∀ φ : PEqualNP.Search.CNF, ∀ u ∈ PEqualNP.MetaComplexity.CoverPromise.cvcCover φ, ∃ v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v

/-- L-meta-475 (conjecture, unowned): The graph cvcGraph phi has an edge for every CNF formula phi. Recorded statement, verbatim. -/
def Stmt475 : Prop := ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v

/-- L-meta-478 (conjecture, unowned): Placing cvcGraph phi on numbers puts every vertex lying on an edge below 3(|encodeCNF phi| + 1). Recorded statement, verbatim. -/
def Stmt478 : Prop := ∀ (φ : PEqualNP.Search.CNF) (E : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v → num u < (3 * (E + 1))

/-- L-meta-479 (conjecture, unowned): The placement of cvcGraph phi on numbers is injective on the vertices lying on edges. Recorded statement, verbatim. -/
def Stmt479 : Prop := ∀ (φ : PEqualNP.Search.CNF) (E : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ u v w z : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v → (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj w z → num u = num w → u = w

/-- L-meta-489 (conjecture, unowned): The index of the earliest occurrence of a variable in the clause item list of phi is below |encodeCNF phi| and injective. Recorded statement, verbatim. -/
def Stmt489 : Prop := ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < (PEqualNP.Search.encodeCNF φ).length) ∧ ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z'

/-- L-meta-492: In the 2k-fold subdivision of a graph on Fin, two distinct vertices with at least three neighbours are joined by no walk shorter than 2k + 1. Recorded statement, verbatim. -/
def Stmt492 : Prop := ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard → ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length

/-- L-meta-499 (conjecture, unowned): The owner lists in rounds of the slot-subdivided placed graph of a renamed CNF are polynomial time to write from E, k and the code. Recorded statement, verbatim. -/
def Stmt499 : Prop := PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × {φ : PEqualNP.Search.CNF // ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum} => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ PEqualNP.Search.encodeCNF p.2.1) (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) (fun p : List ℕ × {φ : PEqualNP.Search.CNF // ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum} => (fun (E k : ℕ) (ψ : PEqualNP.Search.CNF) => (fun (off : ℕ → ℕ) => (fun (pos : ℕ → ℕ → ℕ) (X : ℕ → ℕ → ℕ → ℕ) => (fun (inner : ℕ → ℕ → Bool → List (List ℕ)) (lit : ℕ → ℕ → PEqualNP.Search.Literal) (w : ℕ → ℕ) (f : ℕ → ℕ) => (List.range ψ.length).flatMap (fun i : ℕ => (List.range (w i + 1)).flatMap (fun j : ℕ => (if j < w i then inner (2 * (lit i j).1 + (if (lit i j).2 then 1 else 0)) (pos i j) (lit i j).2 else inner (2 * E + 1) (pos i j) true) ++ ((List.range (w i + 1)).filter (fun l : ℕ => decide (j < l))).flatMap (fun l : ℕ => inner (pos i j) (pos i l) (decide (j ≠ f i))) ++ (if j < w i ∧ (lit i j).1 = off i + j then inner (2 * (lit i j).1) (2 * (lit i j).1 + 1) false else []) ++ (if j ≠ f i then [pos i j :: ((if j < w i ∧ (lit i j).2 = false then [X (2 * (lit i j).1) (pos i j) (2 * k)] else []) ++ (if f i < j then [X (pos i (f i)) (pos i j) (2 * k)] else []) ++ ((List.range (w i + 1)).filter (fun l : ℕ => decide (j < l))).map (fun l : ℕ => X (pos i j) (pos i l) 1))] else []) ++ (if j < w i ∧ (lit i j).1 = off i + j then [(2 * (lit i j).1 + 1) :: X (2 * (lit i j).1) (2 * (lit i j).1 + 1) (2 * k) :: (List.range ψ.length).flatMap (fun i' : ℕ => ((List.range (w i')).filter (fun j' : ℕ => decide ((lit i' j').1 = (lit i j).1 ∧ (lit i' j').2 = true))).map (fun j' : ℕ => X (2 * (lit i j).1 + 1) (pos i' j') 1))] else []))) ++ inner (2 * E) (2 * E + 1) false ++ inner (2 * E) (3 * E + 2) false ++ [(2 * E + 1) :: X (2 * E) (2 * E + 1) (2 * k) :: (List.range ψ.length).map (fun i : ℕ => X (2 * E + 1) (pos i (w i)) 1)] ++ [[3 * E + 2, X (2 * E) (3 * E + 2) (2 * k)]]) (fun (u v : ℕ) (inT : Bool) => ((List.range (2 * k)).filter (fun s : ℕ => decide ((s + 1) % 2 = 0 ↔ inT = true))).map (fun s : ℕ => [X u v (s + 1), if s = 0 then u else X u v s, if s + 1 = 2 * k then v else X u v (s + 2)])) (fun (i j : ℕ) => (ψ.getD i []).getD j (0, false)) (fun (i : ℕ) => (ψ.getD i []).length) (fun (i : ℕ) => (ψ.getD i []).findIdx (fun l : PEqualNP.Search.Literal => l.2))) (fun (i j : ℕ) => 2 * (E + 1) + off i + j) (fun (u v t : ℕ) => 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + t - 1)) (fun (i : ℕ) => ((ψ.take i).map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum)) (p.1.getD 0 0) (p.1.getD 1 0) p.2.1)

/-- L-meta-500 (conjecture, unowned): Renaming each variable of a CNF to the item index of its earliest occurrence in the code is polynomial time. Recorded statement, verbatim. -/
def Stmt500 : Prop := PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2))))

/-- L-meta-501 (conjecture, unowned): After renaming to earliest-occurrence item indices, a CNF keeps its clause widths and every variable is below its item count. Recorded statement, verbatim. -/
def Stmt501 : Prop := ∀ φ : PEqualNP.Search.CNF, ((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map List.length = φ.map List.length ∧ ∀ c ∈ (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ, ∀ l ∈ c, l.1 < (((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum

/-- L-meta-507: Any fixed list of polynomials with natural coefficients is computable in polynomial time on tuples of unary numbers. Recorded statement, verbatim. -/
def Stmt507 : Prop := ∀ (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)), PEqualNP.Library.ComputableInPolyTime (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (fun t : List ℕ => P.map (fun q : MvPolynomial (Fin s) ℕ => MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q))

/-- L-meta-508 (conjecture, unowned): The block cover circuit of a list of owner lists, with its number of inputs, is polynomial time to write as a circuit code. Recorded statement, verbatim. -/
def Stmt508 : Prop := PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × List (List ℕ) => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) p.2) PEqualNP.MetaComplexity.encodeLgp (fun p : List ℕ × List (List ℕ) => (p.1.headD 0, PEqualNP.MetaComplexity.coverCircuitB (p.1.headD 0) (p.2.map (fun l : List ℕ => (l.headD 0, l.tail)))))

/-! ## The map of record -/

/-! REN (L-meta-500's function) and OWN (the function inside L-meta-499) are the shared definitions
`OwnerLink.REN`, `OwnerLink.OWN` of `Helpers/OwnerLinkDefs.lean` (the import map's terms verbatim). -/

/-- The subdivision parameter of record. -/
def kRec : ℕ := 4

/-- E: the length of the code of the formula. -/
def Eof (φ : CNF) : ℕ := (encodeCNF φ).length

/-- N = 3(E + 1): the number of placed vertices. -/
def Nof (E : ℕ) : ℕ := 3 * (E + 1)

/-- n = 3(E + 1) + 18k(E + 1)^2: the number of inputs of the output circuit. -/
def nOf (E k : ℕ) : ℕ := 3 * (E + 1) + 18 * k * (E + 1) ^ 2

/-- The map on formulas at parameter k: n inputs, the cover circuit of the owner lists. -/
def Rk (k : ℕ) (φ : CNF) : ℕ × Circuit :=
  (nOf (Eof φ) k, coverCircuitB (nOf (Eof φ) k)
    ((OWN (Eof φ) k (REN φ)).map (fun l : List ℕ => (l.headD 0, l.tail))))

/-- The map of record on formulas. -/
def R : CNF → ℕ × Circuit := Rk kRec

/-- The map of record on strings: codes to `R φ`, non-codes to the empty circuit on no inputs. -/
noncomputable def r (x : List Bool) : ℕ × Circuit := by
  classical
  exact if h : ∃ φ : CNF, encodeCNF φ = x then R h.choose else (0, Circuit.mk [] 0)

/-! ## The placement objects -/

/-- e: the item index of the earliest occurrence of a variable. -/
def eOf (φ : CNF) : ℕ → ℕ := fun z =>
  (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))

/-- off: the item index of the first position of each clause. -/
def offOf (φ : CNF) : ℕ → ℕ := fun i => ((φ.take i).map (fun c => c.length + 1)).sum

/-- num: the placement of record of the vertices of `cvcGraph φ` on numbers. -/
def numOf (E : ℕ) (φ : CNF) : Vertex → ℕ
  | Sum.inl (z, b) => if z = fresh φ then 2 * E + (if b then 1 else 0)
      else 2 * eOf φ z + (if b then 1 else 0)
  | Sum.inr (i, j) => if i < φ.length then 2 * (E + 1) + offOf φ i + j else 3 * E + 2

/-- H: the placed graph on Fin (3(E + 1)). -/
def HOf (E : ℕ) (φ : CNF) : SimpleGraph (Fin (3 * (E + 1))) :=
  SimpleGraph.fromRel (fun a b : Fin (3 * (E + 1)) =>
    ∃ u v, (cvcGraph φ).Adj u v ∧ numOf E φ u = a.val ∧ numOf E φ v = b.val)

/-- T_H: the image of `cvcCover φ` on Fin (3(E + 1)). -/
noncomputable def THOf (E : ℕ) (φ : CNF) : Finset (Fin (3 * (E + 1))) := by
  classical
  exact Finset.univ.filter (fun a => ∃ u ∈ cvcCover φ, numOf E φ u = a.val)

/-- S: the 2k-fold subdivision in the slot numbering of set (i) (the inline graph of L-meta-285). -/
def subdivOf (m k : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin (m + 2 * k * m * m)) :=
  SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val)))

/-- F: the forward cover of a cover T of H (the set of L-meta-288). -/
noncomputable def fwdOf (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) :
    Finset (Fin (m + 2 * k * m * m)) := by
  classical
  exact Finset.univ.filter (fun j => (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k),
    u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T))

theorem mem_THOf (E : ℕ) (φ : CNF) (a : Fin (3 * (E + 1))) :
    a ∈ THOf E φ ↔ ∃ u ∈ cvcCover φ, numOf E φ u = a.val := by
  classical
  unfold THOf; simp

theorem mem_fwdOf (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m))
    (j : Fin (m + 2 * k * m * m)) :
    j ∈ fwdOf m k H T ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k),
      u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T) := by
  classical
  unfold fwdOf
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem numOf_lit (E : ℕ) (φ : CNF) : ∀ z ∈ vars φ, ∀ b : Bool,
    numOf E φ (Sum.inl (z, b)) = 2 * eOf φ z + (if b then 1 else 0) := by
  intro z hz b
  have : z ≠ fresh φ := fun h => fresh_not_mem φ (h ▸ hz)
  simp [numOf, this]

theorem numOf_fresh (E : ℕ) (φ : CNF) : ∀ b : Bool,
    numOf E φ (Sum.inl (fresh φ, b)) = 2 * E + (if b then 1 else 0) := by
  intro b; simp [numOf]

theorem numOf_pos (E : ℕ) (φ : CNF) : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
    numOf E φ (Sum.inr (i, j)) = 2 * (E + 1) + offOf φ i + j := by
  intro i j hi _; simp [numOf, hi]

theorem numOf_end (E : ℕ) (φ : CNF) : numOf E φ (Sum.inr (φ.length, 0)) = 3 * E + 2 := by
  simp [numOf]

/-! ## Bridge B5 (retype) -/

/-- B5: a polynomial-time map may be replaced by any map with the same output codes. Stated as in
the import map. -/
theorem retype : ∀ (α β β' : Type) (ea : α → List Bool) (eb : β → List Bool) (eb' : β' → List Bool) (f : α → β) (f' : α → β'), PEqualNP.Library.ComputableInPolyTime ea eb f → (∀ a : α, eb (f a) = eb' (f' a)) → PEqualNP.Library.ComputableInPolyTime ea eb' f' := by
  rintro α β β' ea eb eb' f f' ⟨c⟩ h
  exact ⟨{ c with outputsFun := fun a => by rw [← h a]; exact c.outputsFun a }⟩

end PEqualNP.MetaComplexity.Reduction
