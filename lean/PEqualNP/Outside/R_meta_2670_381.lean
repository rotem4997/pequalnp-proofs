import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Separate the minimum-circuit normal form and output range from the local repair.
theorem PEqualNP.Outside.R_meta_2670_381
    (shape : ∀ (n : ℕ) (C : Circuit), IsMinimalMonoCircuit n C →
      (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
      IsAO2 n C ∧ ∀ g ∈ C.gates, g.inputs.Nodup)
    (output : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      circuitFun n C = graphFun G ∅ → (∃ u v, G.Adj u v) →
      n ≤ C.output ∧ C.output < n + C.size)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let target := graphFun G ∅
      let owner := fun (D : Circuit) j => ∃ u v, G.Adj u v ∧ Owns n D j u v
      let cost := fun (D : Circuit) =>
        {j : ℕ | j < D.size ∧ (gateAt D j).op = .and ∧ ¬ owner D j}.ncard
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = target →
      IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      n ≤ C.output → C.output < n+C.size →
      ∀ j < C.size, (gateAt C j).op = .and → ¬ owner C j →
      (∀ i < j, (gateAt C i).op = .and → owner C i) →
      ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
      circuitFun n (eraseGate n C j (n + C.size)) (pairInput u v) = false →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = target ∧ D.size ≤ C.size ∧
        cost D < cost C) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => {x7 : ℕ | x7 < x6.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → ¬PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9}.ncard;       ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → ¬PEqualNP.EdgeOwnership.Owns x1 x7 x10 x13 x14) → (∀ x14 < x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x14 x17 x18) → ∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x7 x10 (x1 + x7.gates.length)) (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.false → ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x20 ∧ PEqualNP.MetaComplexity.circuitFun x1 x20 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x20.size ≤ x7.size ∧ x6 x20 < x6 x7 := by

  intro n G d noTriangle noFour
  dsimp only
  intro C least computes j hj hand unowned prior u v adj live erased
  have range := output n G C computes ⟨u,v,adj⟩
  have expand (x : Fin n → Bool) : graphFun G ∅ x =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
       decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) := rfl
  have h0 : graphFun G ∅ (fun _ => false) = false := by
    rw [expand]
    simp
  have h1 : graphFun G ∅ (fun _ => true) = true := by
    rw [expand]
    simp [show ∃ a b, G.Adj a b from ⟨u,v,adj⟩]
  have normal := shape n C least ⟨fun _ => true,fun _ => false,by
    rw [computes,h0,h1]
    decide⟩
  have noOwner : ¬ (∃ a b, G.Adj a b ∧ Owns n C j a b) := by
    rintro ⟨a,b,h,o⟩
    exact unowned a b h o
  obtain ⟨D,mono,eq,budget,decrease⟩ :=
    repair n G C noTriangle noFour least computes normal.1 normal.2 range.1 range.2 j hj
      hand noOwner prior u v adj live erased
  refine ⟨D,mono,eq,budget,?_⟩
  dsimp only at decrease ⊢
  simp only [not_exists,not_and] at decrease
  exact decrease
