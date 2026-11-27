import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2640_801
  (locate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    ¬ G.Colorable 2 → (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
    ∃ (u v : Fin n) (D : Circuit) (a b : ℕ → ℕ), G.Adj u v ∧ FanInTwo D ∧ D.size ≤ C.size ∧
      circuitFun n D = circuitFun n C ∧ ∀ i < 7, a i < D.size ∧ b i < n + a i ∧
      (∀ j < i, a i < a j) ∧ ((∀ x : Fin n → Bool,
        let w := D.wires (List.ofFn (Function.update (Function.update x u false) v false))
        w.getD (n+a i) false = w.getD (b i) false) ∨
        (D.output ≠ n+a i ∧ (∀ j < i, b j ≠ n+a i) ∧
          ∀ (j : ℕ) (g : Gate), a i < j → D.gates[j]? = some g → n+a i ∈ g.inputs → ∃ s < i, a s = j)))
  (realize : ∀ (n k : ℕ) (D : Circuit) (X : Set (Fin n → Bool)) (a b : ℕ → ℕ),
    let same := fun (E : Circuit) (i : ℕ) => ∀ x ∈ X,
      let w := E.wires (List.ofFn x)
      w.getD (n+a i) false = w.getD (b i) false
    (∀ i < k, a i < D.size ∧ b i < n + a i ∧ (∀ j < i, a i < a j) ∧ (same D i ∨
      (D.output ≠ n+a i ∧ (∀ j < i, b j ≠ n+a i) ∧
       ∀ (j : ℕ) (g : Gate), a i < j → D.gates[j]? = some g → n+a i ∈ g.inputs → ∃ s < i, a s = j))) →
    ∃ S : ℕ → Circuit, S 0 = D ∧ ∀ i < k, a i < (S i).size ∧
      S (i+1) = eraseGate n (S i) (a i) (b i) ∧ (same (S i) i ∨
        ((S i).output ≠ n+a i ∧ ∀ g ∈ (S i).gates.drop (a i+1), n+a i ∉ g.inputs))) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  classical
  intro n G A C notColor degree girth isolates edge minimal computes
  have G7 : 7 ≤ G.egirth := (SimpleGraph.le_egirth (G := G)).2 (fun v w hw => by exact_mod_cast girth v w hw)
  have spec : circuitFun n C = NestedCover.graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using computes x
  obtain ⟨u,v,D,a,b,adj,fan,size,funEq,static⟩ := locate n G A C notColor degree G7 isolates edge minimal spec
  let clamp := fun (x : Fin n → Bool) => Function.update (Function.update x u false) v false
  specialize realize n 7 D (Set.range clamp) a b
  obtain ⟨S,h0,moves⟩ := realize (by
    intro i hi
    obtain ⟨ha,hb,hd,h⟩ := static i hi
    refine ⟨ha,hb,hd,h.imp ?_ id⟩
    intro eq x hx
    obtain ⟨z,rfl⟩ := hx
    exact eq z)
  refine ⟨u,v,adj,S,h0 ▸ fan,h0 ▸ size,h0 ▸ funEq,?_⟩
  intro i hi
  obtain ⟨hs, step, h⟩ := moves i hi
  refine ⟨a i,b i,hs,Or.inl (static i hi).2.1,step,h.imp ?_ id⟩
  intro eq x
  exact eq (clamp x) ⟨x,rfl⟩
