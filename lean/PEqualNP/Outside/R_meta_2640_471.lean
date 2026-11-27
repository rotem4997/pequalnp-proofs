import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2640_471
    (cycle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), ¬ G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth → (∀ u v, G.Adj u v → u ∉ A) →
      ∃ m : ℕ, 7 ≤ m ∧ Odd m ∧ ∃ f g : Fin m ↪ Fin n,
        (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) ∧
        (∀ i j, G.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val))
    (erase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (D : Circuit)
      (m : ℕ) (f g : Fin m ↪ Fin n), Odd m →
      (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
      (∀ i j, G.Adj (f i) (f j) ↔ (i.val+1)%m = j.val ∨ (j.val+1)%m = i.val) →
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) → 7 ≤ G.egirth →
      IsMinimalCircuit n D → circuitFun n D = NestedCover.graphFun G A →
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧
        ∃ C : ℕ → Circuit, FanInTwo (C 0) ∧ (C 0).size ≤ D.size ∧
        circuitFun n (C 0) = circuitFun n D ∧
        ∀ i' : ℕ, i' < 7 → ∃ a b : ℕ, a < (C i').size ∧
        (b < n + a ∨ n + (C i').size ≤ b) ∧ C (i' + 1) = eraseGate n (C i') a b ∧
        ((∀ x : Fin n → Bool,
          let w := (C i').wires (List.ofFn (Function.update (Function.update x (f i) false) (f j) false))
          w.getD (n + a) false = w.getD b false) ∨
          ((C i').output ≠ n + a ∧ ∀ g ∈ (C i').gates.drop (a + 1), n + a ∉ g.inputs))) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  classical
  intro n G A D notColor degree girth isolates _ minimal computes
  have G7 : 7 ≤ G.egirth := (SimpleGraph.le_egirth (G := G)).2 (fun v w hw => by exact_mod_cast girth v w hw)
  obtain ⟨m, hm, odd, f, g, spokes, edges⟩ := cycle n G A notColor degree G7 isolates
  have spec : circuitFun n D = NestedCover.graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using computes x
  have deg (v : Fin n) : (G.neighborSet v).ncard = if v ∈ A then 0 else 3 := by
    by_cases hv : v ∈ A
    · have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun u hu => (isolates v u hu) hv)
      simp [hv, empty]
    · simpa [hv] using degree v hv
  obtain ⟨i, j, edge, path⟩ := erase n G A D m f g odd spokes edges deg G7 minimal spec
  exact ⟨f i, f j, edge, path⟩
