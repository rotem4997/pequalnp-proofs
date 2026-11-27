import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.NotPremium

theorem PEqualNP.Outside.R_meta_2434_317
    (bypass :
      ∀ (n : ℕ) (C : Circuit) (j p : ℕ), Monotone2 C → j < C.size →
        (gateAt C j).op = GateOp.or → p ∈ (gateAt C j).inputs → p < n + j →
        let D := eraseGate n C j p
        Monotone2 D ∧ D.size < C.size ∧ circuitFun n D ≤ circuitFun n C)
    (price : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      let ok (C : Circuit) := Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅
      let hits (C : Circuit) := G.edgeFinset.filter (fun e => circuitFun n C (fun v => decide (v ∈ e)) = true)
      let bad (C : Circuit) (j : ℕ) := (gateAt C j).op = GateOp.and ∧
        ∃ u v, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      ∀ C : Circuit, ok C → (∀ D, ok D → D.size < C.size → (hits D).card < (hits C).card) →
        (∀ j < C.size, (gateAt C j).op = GateOp.or →
          ∀ p ∈ (gateAt C j).inputs, p < n + j → (hits (eraseGate n C j p)).card < (hits C).card) →
        (∃ j, bad C j) → ∃ j, bad C j ∧ ∃ D : Circuit, ok D ∧ D.size < C.size ∧
          hits D = hits ⟨replaceByConst C.gates j false, C.output⟩ ∧
          (hits C).card ≤ (hits D).card + c * (C.size - D.size)) :
    ∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →         have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x7 x8 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ x8 = Bool.true;         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x8 fun (x10 : Fin x2) => Decidable.decide (x10 ∈ x9)) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x11 : Fin x2) (x12 : Fin x2), ¬x3.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x9 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true;         ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → x7 x10 → (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 → x7 x13 → x13.size < x10.size → (x8 x13).card < (x8 x10).card) → (∃ (x14 : ℕ), x9 x10 x14) → ∃ (x15 : ℕ), x9 x10 x15 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ x7 x16 ∧ x16.size < x10.size ∧ x8 x16 = x8 { gates := PEqualNP.NotPremium.replaceByConst x10.gates x15 Bool.false, output := x10.output : PEqualNP.CircuitLowerBounds.Circuit } ∧ (x8 x10).card ≤ (x8 x16).card + x1 * (x10.size - x16.size) := by
  obtain ⟨c, hPrice⟩ := price
  refine ⟨c, ?_⟩
  intro n G _ hDegree hCycle
  dsimp only
  intro C hMono hSafe hMinimal hBad
  have hOK : Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅ :=
    ⟨hMono, fun x => Bool.le_iff_imp.mpr (hSafe x)⟩
  have hMinimal' (D : Circuit) (hD : Monotone2 D ∧ circuitFun n D ≤ graphFun G ∅)
      (hSize : D.size < C.size) :=
    hMinimal D hD.1 (fun x => Bool.le_iff_imp.mp (hD.2 x)) hSize
  have hStrict (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.or)
      (p : ℕ) (hp : p ∈ (gateAt C j).inputs) (hp' : p < n + j) := by
    have h := bypass n C j p hMono hj hop hp hp'
    exact hMinimal' _ ⟨h.1, le_trans h.2.2 hOK.2⟩ h.2.1
  obtain ⟨j, hj, D, hD, hSize, hHits, hLoss⟩ :=
    hPrice n G hDegree hCycle C hOK hMinimal' hStrict hBad
  exact ⟨j, hj, D, hD.1, fun x => Bool.le_iff_imp.mp (hD.2 x), hSize, hHits, hLoss⟩
