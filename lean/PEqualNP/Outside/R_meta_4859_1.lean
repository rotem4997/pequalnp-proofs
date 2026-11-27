import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4859_1
    (findAliases : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (D : Circuit) (m : ℕ) (f g : Fin m ↪ Fin n), Odd m →
      (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
      (∀ i j, G.Adj (f i) (f j) ↔ (i.val+1)%m = j.val ∨ (j.val+1)%m = i.val) →
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) → 7 ≤ G.egirth →
      IsMinimalCircuit n D → circuitFun n D = NestedCover.graphFun G A →
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧
        ∃ C : Circuit, FanInTwo C ∧ C.size ≤ D.size ∧ circuitFun n C = circuitFun n D ∧
          ∃ K : Finset ℕ, 7 ≤ K.card ∧ ∀ a ∈ K, a < C.size ∧
            ((∃ b : ℕ, ((b < n+a ∧ (b < n ∨ b-n ∉ K)) ∨ n+C.size ≤ b) ∧
              ∀ x : Fin n → Bool,
                let w := C.wires (List.ofFn (Function.update (Function.update x (f i) false) (f j) false))
                w.getD (n+a) false = w.getD b false) ∨
             (C.output ≠ n+a ∧ readsIn C (Finset.range C.size \ K) (n+a) = 0)))
    (schedule : ∀ (n : ℕ) (u v : Fin n) (C : Circuit) (K : Finset ℕ),
      (∀ a ∈ K, a < C.size) →
      (∀ a ∈ K,
        (∃ b : ℕ, ((b < n+a ∧ (b < n ∨ b-n ∉ K)) ∨ n+C.size ≤ b) ∧
          ∀ x : Fin n → Bool,
            let w := C.wires (List.ofFn (Function.update (Function.update x u false) v false))
            w.getD (n+a) false = w.getD b false) ∨
        (C.output ≠ n+a ∧ readsIn C (Finset.range C.size \ K) (n+a) = 0)) →
      ∃ path : ℕ → Circuit, path 0 = C ∧
        ∀ k < K.card, ∃ a b : ℕ, a < (path k).size ∧
          (b < n+a ∨ n+(path k).size ≤ b) ∧
          path (k+1) = eraseGate n (path k) a b ∧
          ((∀ x : Fin n → Bool,
            let w := (path k).wires (List.ofFn (Function.update (Function.update x u false) v false))
            w.getD (n+a) false = w.getD b false) ∨
           ((path k).output ≠ n+a ∧ ∀ g ∈ (path k).gates.drop (a+1), n+a ∉ g.inputs)))
    :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),   Odd x6 →     (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →       (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →         (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →           (7 : ℕ∞) ≤ x2.egirth →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →                 ∃ (x16 : Fin x6) (x17 : Fin x6),                   x2.Adj (x7 x16) (x7 x17) ∧                     ∃ (x18 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x18 (0 : ℕ)) ∧                         (x18 (0 : ℕ)).size ≤ x5.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x18 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧                             ∀ x19 < (7 : ℕ),                               ∃ (x21 : ℕ) (x22 : ℕ),                                 x21 < (x18 x19).size ∧                                   (x22 < x1 + x21 ∨ x1 + (x18 x19).size ≤ x22) ∧                                     x18 (x19 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x18 x19) x21 x22 ∧                                       ((∀ (x23 : Fin x1 → Bool),                                           have x24 : List Bool := (x18 x19).wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));                                           x24.getD (x1 + x21) Bool.false = x24.getD x22 Bool.false) ∨                                         (x18 x19).output ≠ x1 + x21 ∧ ∀ x23 ∈ List.drop (x21 + (1 : ℕ)) (x18 x19).gates, x1 + x21 ∉ x23.inputs) := by
  intro n G inst A D m f g odd spokes edges degree girth minimal computes
  obtain ⟨i,j,adj,C,fan,bound,fn,K,count,cert⟩ :=
    findAliases n G A D m f g odd spokes edges degree girth minimal computes
  obtain ⟨path,start,steps⟩ := schedule n (f i) (f j) C K
    (fun a ha => (cert a ha).1) (fun a ha => (cert a ha).2)
  refine ⟨i,j,adj,path,start.symm ▸ fan,start.symm ▸ bound,start.symm ▸ fn,?_⟩
  intro k hk
  obtain ⟨a,b,inbounds,redirect,next,equal⟩ := steps k (Nat.lt_of_lt_of_le hk count)
  exact ⟨a,b,inbounds,redirect,next,equal⟩
