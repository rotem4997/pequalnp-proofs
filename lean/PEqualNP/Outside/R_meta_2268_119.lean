import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Remove the isolated positive literals before comparing the circuit to a star cover.
-- Only pure edge circuits strictly smaller than that cover enter the residual.
theorem PEqualNP.Outside.R_meta_2268_119 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) → ∀ s, HasCircuitSize n (graphFun G A) s →
      ∃ k, k + A.card ≤ s ∧ HasCircuitSize n (graphFun G ∅) k) →
    (∀ (n : ℕ) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (s : ℕ),
      HasCircuitSize n f s → HasCircuitSize n (fun x => decide (∃ a ∈ A, x a = true) || f x) (s + A.card)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.Colorable 2 → (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) → ∃ u v, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧ ∃ t : ℕ,
        t + 8 ≤ 2 * (n - A.card) - 1 ∧ HasCircuitSize n (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.Colorable 2 → (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) → ∀ s, HasCircuitSize n (graphFun G ∅) s →
      s < 2 * (n - A.card) - 1 → ∃ u v, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧ ∃ t : ℕ,
        t + 8 ≤ s ∧ HasCircuitSize n (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro strip append benchmark residual n G A f bipartite cubic girth isolates edge spec s size
  classical
  have eq : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change f x = true ↔ (_ || _) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  subst f
  obtain ⟨k, small, pure⟩ := strip n G A isolates edge s size
  have pair : ∃ u v, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧ ∃ t : ℕ,
      t + 8 ≤ k ∧ HasCircuitSize n
        (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) t := by
    by_cases cheap : k < 2 * (n - A.card) - 1
    · exact residual n G A bipartite cubic girth isolates edge k pure cheap
    · obtain ⟨u,v,hu,hv,ne,far,t,budget,model⟩ :=
        benchmark n G A bipartite cubic girth isolates edge
      exact ⟨u,v,hu,hv,ne,far,t,by omega,model⟩
  obtain ⟨u,v,hu,hv,ne,far,t,budget,model⟩ := pair
  refine ⟨u,v,hu,hv,ne,far,t + A.card,by omega,?_⟩
  have fixed (x : Fin n → Bool) (a : Fin n) (ha : a ∈ A) :
      Function.update (Function.update x u false) v false a = x a := by
    have ua : a ≠ u := fun h => hu (h ▸ ha)
    have va : a ≠ v := fun h => hv (h ▸ ha)
    simp [Function.update_of_ne, ua, va]
  have same (x : Fin n → Bool) :
      (∃ a ∈ A, (Function.update (Function.update x u false) v false) a = true) ↔
      (∃ a ∈ A, x a = true) := by
    constructor <;> rintro ⟨a,ha,lit⟩
    · exact ⟨a,ha,(fixed x a ha) ▸ lit⟩
    · exact ⟨a,ha,(fixed x a ha).symm ▸ lit⟩
  convert append n A _ t model using 1
  funext x
  change (decide (∃ a ∈ A, (Function.update (Function.update x u false) v false) a = true) || _) =
    (decide (∃ a ∈ A, x a = true) || (decide (∃ a ∈ (∅ : Finset (Fin n)), (Function.update (Function.update x u false) v false) a = true) || _))
  simp only [same, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
