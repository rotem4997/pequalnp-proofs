import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import PEqualNP.MetaComplexity.Helpers.LgpSanity
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The cover circuit for a graph on `Fin n`: upper bound and exact size

The statements of `L-meta-154` (size + 1 at most edges + cover) and `L-meta-221` (size + 1
equal to edges + cover, after appending gates that read no wire), derived from the explicit
list circuit `coverCircuit`. The import closure of this file reaches neither `OrChain` nor
`Parity3`, so these bounds can be used next to the lower bounds built over `Parity3`.
-/

namespace PEqualNP.MetaComplexity.CoverCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.LgpSanity

/-- The ordered pairs `i < j` of adjacent vertices. -/
def graph_pairs (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)

/-- The edge list of a graph on `Fin n`: each edge once, as `(i, j)` with `i < j`. -/
noncomputable def graph_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (ℕ × ℕ) :=
  (graph_pairs n G).toList.map (fun p => (p.1.val, p.2.val))

/-- The cover list of a vertex set. -/
noncomputable def graph_cover {n : ℕ} (T : Finset (Fin n)) : List ℕ := T.toList.map Fin.val

theorem graph_pairs_card (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (graph_pairs n G).card = G.edgeFinset.card := by
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · intro p hp
    simp only [graph_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2
  · intro p hp q hq h
    simp only [graph_pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have a := hp.1
      have b := hq.1
      rw [h1, h2] at a
      exact lt_asymm a b
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases lt_trichotomy a b with h | h | h
      · refine ⟨(a, b), ?_, rfl⟩
        simp only [graph_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, he⟩
      · exact absurd h (G.ne_of_adj he)
      · refine ⟨(b, a), ?_, Sym2.eq_swap⟩
        simp only [graph_pairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, G.adj_symm he⟩

theorem graph_edges_length (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (graph_edges n G).length = G.edgeFinset.card := by
  rw [graph_edges, List.length_map, Finset.length_toList, graph_pairs_card]

theorem graph_cover_length {n : ℕ} (T : Finset (Fin n)) : (graph_cover T).length = T.card := by
  rw [graph_cover, List.length_map, Finset.length_toList]

theorem graph_mem_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : ℕ × ℕ) :
    e ∈ graph_edges n G ↔ ∃ p : Fin n × Fin n, (p.1 < p.2 ∧ G.Adj p.1 p.2) ∧
      (p.1.val, p.2.val) = e := by
  simp only [graph_edges, List.mem_map, Finset.mem_toList, graph_pairs, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem graph_hG (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    G.Adj i j ↔ ((i.val, j.val) ∈ graph_edges n G ∨ (j.val, i.val) ∈ graph_edges n G) := by
  simp only [graph_mem_edges]
  constructor
  · intro h
    rcases lt_trichotomy i j with hl | hl | hl
    · exact Or.inl ⟨(i, j), ⟨hl, h⟩, rfl⟩
    · exact absurd hl (G.ne_of_adj h)
    · exact Or.inr ⟨(j, i), ⟨hl, G.adj_symm h⟩, rfl⟩
  · rintro (⟨p, ⟨_, hp⟩, he⟩ | ⟨p, ⟨_, hp⟩, he⟩)
    · simp only [Prod.mk.injEq] at he
      have h1 : p.1 = i := Fin.ext he.1
      have h2 : p.2 = j := Fin.ext he.2
      rw [← h1, ← h2]; exact hp
    · simp only [Prod.mk.injEq] at he
      have h1 : p.1 = j := Fin.ext he.1
      have h2 : p.2 = i := Fin.ext he.2
      rw [← h1, ← h2]; exact G.adj_symm hp

theorem graph_hE (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ e ∈ graph_edges n G, e.1 < n ∧ e.2 < n := by
  intro e he
  obtain ⟨p, _, rfl⟩ := (graph_mem_edges n G e).mp he
  exact ⟨p.1.isLt, p.2.isLt⟩

theorem graph_hT (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    ∀ e ∈ graph_edges n G, e.1 ∈ graph_cover T ∨ e.2 ∈ graph_cover T := by
  intro e he
  obtain ⟨p, ⟨_, hp⟩, rfl⟩ := (graph_mem_edges n G e).mp he
  simp only [graph_cover, List.mem_map, Finset.mem_toList]
  rcases hT p.1 p.2 hp with h | h
  · exact Or.inl ⟨p.1, h, rfl⟩
  · exact Or.inr ⟨p.2, h, rfl⟩

theorem graph_edges_ne_nil (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : ∃ i j : Fin n, G.Adj i j) : graph_edges n G ≠ [] := by
  obtain ⟨i, j, h⟩ := he
  intro h0
  rcases (graph_hG n G i j).mp h with h' | h' <;> rw [h0] at h' <;> exact List.not_mem_nil h'

/-- The upper bound of `L-meta-154`, from the explicit list circuit. -/
theorem graph_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ D.size + 1 ≤ G.edgeFinset.card + T.card := by
  intro n G _ T he hT
  obtain ⟨hF, hN⟩ := fanInTwo_notFree n (graph_edges n G) (graph_cover T)
  refine ⟨coverCircuit n (graph_edges n G) (graph_cover T), hF, hN,
    circuitFun_eq_graph n _ _ G (graph_hG n G) (graph_hE n G) (graph_hT n G T hT), ?_⟩
  have := size_le n (graph_edges n G) (graph_cover T) (graph_edges_ne_nil n G he)
  rw [graph_edges_length, graph_cover_length] at this
  exact this

/-- Appending `j` gates that read no wire. -/
def graph_pad : ℕ → Circuit → Circuit
  | 0, C => C
  | j + 1, C => appendDead (graph_pad j C)

theorem graph_pad_fun (n : ℕ) (C : Circuit) : ∀ j : ℕ,
    circuitFun n (graph_pad j C) = circuitFun n C
  | 0 => rfl
  | j + 1 => by rw [graph_pad, fun_appendDead, graph_pad_fun n C j]

theorem graph_pad_fanIn (C : Circuit) (hC : FanInTwo C) : ∀ j : ℕ,
    FanInTwo (graph_pad j C)
  | 0 => hC
  | j + 1 => fanInTwo_appendDead _ (graph_pad_fanIn C hC j)

theorem graph_pad_size (C : Circuit) : ∀ j : ℕ, (graph_pad j C).size = C.size + j
  | 0 => rfl
  | j + 1 => by
    have h := graph_pad_size C j
    simp only [Circuit.size] at h ⊢
    simp only [graph_pad, appendDead, List.length_append, List.length_cons,
      List.length_nil, h]
    omega

theorem graph_pad_noNot (C : Circuit) (hC : ∀ g ∈ C.gates, g.op ≠ GateOp.not) : ∀ j : ℕ,
    ∀ g ∈ (graph_pad j C).gates, g.op ≠ GateOp.not
  | 0 => hC
  | j + 1 => by
    intro g hg
    simp only [graph_pad, appendDead, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact graph_pad_noNot C hC j g hg
    · simp

/-- The exact size of `L-meta-221`: the circuit of `graph_upper` padded with gates that read
no wire. -/
theorem graph_exact : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ D.size + 1 = G.edgeFinset.card + T.card := by
  intro n G _ T he hT
  obtain ⟨D, hF, hN, hfun, hsz⟩ := graph_upper n G T he hT
  refine ⟨graph_pad (G.edgeFinset.card + T.card - (D.size + 1)) D,
    graph_pad_fanIn D hF _, graph_pad_noNot D hN _, ?_, ?_⟩
  · rw [graph_pad_fun, hfun]
  · rw [graph_pad_size]
    omega

end PEqualNP.MetaComplexity.CoverCircuit
