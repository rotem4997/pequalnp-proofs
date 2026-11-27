import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4461_271
    (first : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)),
      G.Colorable 2 → (∀ v ∉ I, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ p q, G.Adj p q → p ∉ I) → (∃ p q, G.Adj p q) →
      ∀ s, HasCircuitSize n (graphFun G ∅) s → s < 2 * (n-I.card)-1 →
      ∃ u ∉ I, ∃ t, t+4 ≤ s ∧
        HasCircuitSize n (fun x => graphFun G ∅ (Function.update x u false)) t)
    (second : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)),
      G.Colorable 2 → (∀ v ∉ I, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ p q, G.Adj p q → p ∉ I) → (∃ p q, G.Adj p q) →
      let F := fun u (x : Fin n → Bool) => graphFun G ∅ (Function.update x u false)
      ∀ u ∉ I, ∀ t, HasCircuitSize n (F u) t →
        (∀ v ∉ I, ∀ b, HasCircuitSize n (F v) b → t ≤ b) →
        t+4 < 2 * (n-I.card)-1 →
        ∃ v ∉ I, v ≠ u ∧ ¬G.Adj u v ∧ ∃ b, b+4 ≤ t ∧
          HasCircuitSize n (fun x => F u (Function.update x v false)) b) :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15) := by
  classical
  intro n G inst I color cubic girth isolated edge s model small
  let F := fun u (x : Fin n → Bool) => graphFun G ∅ (Function.update x u false)
  let P := fun t => ∃ u ∉ I, HasCircuitSize n (F u) t
  obtain ⟨a,ha,b,saved,hb⟩ := first n G I color cubic girth isolated edge s model small
  have pb : P b := ⟨a,ha,hb⟩
  have existsP : ∃ t, P t := ⟨b,pb⟩
  let t := Nat.find existsP
  obtain ⟨u,hu,ht⟩ := (Nat.find_spec existsP : P t)
  have least (v : Fin n) (hv : v ∉ I) (k : ℕ) (hk : HasCircuitSize n (F v) k) :
      t ≤ k := Nat.find_min' existsP (show P k from ⟨v,hv,hk⟩)
  have saving : t + 4 ≤ s := (Nat.add_le_add_right (least a ha b hb) 4).trans saved
  obtain ⟨v,hv,vu,apart,c,drop,hc⟩ :=
    second n G I color cubic girth isolated edge u hu t ht least (lt_of_le_of_lt saving small)
  refine ⟨u,v,hu,hv,Ne.symm vu,apart,c,by omega,?_⟩
  have eqF : (fun x => F u (Function.update x v false)) =
      (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) := by
    funext x
    exact congrArg (graphFun G ∅) (Function.update_comm vu false false x)
  rw [eqF] at hc
  exact hc
