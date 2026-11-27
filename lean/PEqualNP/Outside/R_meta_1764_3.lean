import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1764_3
  (peel : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ (C : Circuit), Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
    ∀ E ⊆ G.edgeFinset, ∀ d : Nat, ∃ H ⊆ E, E.card ≤ d*(C.size+1) + H.card ∧ ∀ v : Fin n, (H.filter fun e => v ∈ e).card = 0 ∨ d < (H.filter fun e => v ∈ e).card)
  (core : ∃ d c : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
    (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
    ∀ C : Circuit, Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
    ∀ H ⊆ {e ∈ G.edgeFinset | ¬∃ u v : Fin n, e = s(u,v) ∧ ∃ j : Fin C.gates.length,
          PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
          ∀ p q : Fin n, PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput p q) = true →
            G.Adj p q}, (∀ v : Fin n, (H.filter fun e => v ∈ e).card = 0 ∨ d < (H.filter fun e => v ∈ e).card) → H.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨d,c,bound⟩ := core
  refine ⟨d+c, ?_⟩
  intro n G dec deg girth C mono computes
  classical
  let E := {e ∈ G.edgeFinset | ¬∃ u v : Fin n, e = s(u,v) ∧ ∃ j : Fin C.gates.length,
          PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
          ∀ p q : Fin n, PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput p q) = true →
            G.Adj p q}
  change E.card ≤ (d+c)*(C.size+1)
  obtain ⟨H, hsub, price, density⟩ := peel n G C mono computes E (Finset.filter_subset _ _) d
  have hc := bound n G deg girth C mono computes H hsub density
  rw [Nat.add_mul]
  exact price.trans (Nat.add_le_add_left hc _)
