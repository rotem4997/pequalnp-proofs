import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotPremium PEqualNP.CarriedProduct

-- Any lost edge used the disabled gate in its original live computation.
-- A gate with no more live edges than freed gates already pays the required charge.
theorem PEqualNP.Outside.R_meta_4281_1
    (trace : ∀ (n : ℕ) (C : Circuit) (j : ℕ), Monotone2 C → j < C.size →
      ∀ x : Fin n → Bool, circuitFun n C x = true →
      circuitFun n (⟨replaceByConst C.gates j false, C.output⟩ : Circuit) x = false →
      IsLive n C x (n+j))
    (largeLoad : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → 5 ≤ G.egirth →
      let input := fun (e : Sym2 (Fin n)) (v : Fin n) => decide (v ∈ e)
      let hits := fun C : Circuit => G.edgeFinset.filter fun e => circuitFun n C (input e) = true
      let admissible := fun C : Circuit => Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅
      let dirty := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = .and ∧
        ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      ∀ C : Circuit, admissible C →
      (∀ D : Circuit, admissible D → D.size < C.size → (hits D).card < (hits C).card) →
      let after := fun j => (⟨replaceByConst C.gates j false, C.output⟩ : Circuit)
      let freed := fun j => C.size -
        (((Finset.range C.size).erase j).filter fun i =>
          ∃ e ∈ G.edgeFinset, IsLive n (after j) (input e) (n+i)).card
      (∃ j, dirty C j) →
      (∀ j, dirty C j →
        freed j < ((hits C).filter fun e => IsLive n C (input e) (n+j)).card) →
      ∃ j, dirty C j ∧ (hits C \ hits (after j)).card ≤ c * freed j) :
    ∃ (x1 : ℕ),
      ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →
      (5 : ℕ∞) ≤ x3.egirth →
      have x7 : Sym2 (Fin x2) → Fin x2 → Bool := fun (x7 : Sym2 (Fin x2)) (x8 : Fin x2) => Decidable.decide (x8 ∈ x7);
      have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | PEqualNP.MetaComplexity.circuitFun x2 x8 (x7 x9) = Bool.true};
      have x9 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.circuitFun x2 x9 ≤ PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅;
      have x10 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x12 : Fin x2) (x13 : Fin x2), ¬x3.Adj x12 x13 ∧ PEqualNP.EdgeOwnership.gateVal x2 x10 x11 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true;
      ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
      x9 x11 →
      (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x9 x13 → x13.size < x11.size → (x8 x13).card < (x8 x11).card) →
      have x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x14 : ℕ) => { gates := PEqualNP.NotPremium.replaceByConst x11.gates x14 Bool.false, output := x11.output : PEqualNP.CircuitLowerBounds.Circuit };
      (∀ x15 < x11.size, x8 (x14 x15) ⊂ x8 x11) → (∃ (x16 : ℕ), x10 x11 x16) → ∃ (x17 : ℕ), x10 x11 x17 ∧ (x8 x11 \ x8 (x14 x17)).card ≤ x1 * (x11.size - {x18 ∈ (Finset.range x11.size).erase x17 | ∃ x19 ∈ x3.edgeFinset, PEqualNP.CarriedProduct.IsLive x2 (x14 x17) (x7 x19) (x2 + x18)}.card) := by
  classical
  obtain ⟨c, charge⟩ := largeLoad
  refine ⟨c + 1, ?_⟩
  intro n G inst degree girth
  dsimp only
  intro C admissible minimal _pivotal hasDirty
  let input (e : Sym2 (Fin n)) (v : Fin n) := decide (v ∈ e)
  let hits (D : Circuit) := G.edgeFinset.filter fun e => circuitFun n D (input e) = true
  let dirty (j : ℕ) := (gateAt C j).op = .and ∧
    ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
  let after (j : ℕ) : Circuit := ⟨replaceByConst C.gates j false, C.output⟩
  let freed (j : ℕ) := C.size -
    (((Finset.range C.size).erase j).filter fun i =>
      ∃ e ∈ G.edgeFinset, IsLive n (after j) (input e) (n+i)).card
  let liveEdges (j : ℕ) := (hits C).filter fun e => IsLive n C (input e) (n+j)
  by_cases small : ∃ j, dirty j ∧ (liveEdges j).card ≤ freed j
  · obtain ⟨j, bad, load⟩ := small
    have bound : j < C.size := by
      by_contra! out
      have op := bad.1
      change (C.gates.getD j ⟨.or, []⟩).op = .and at op
      rw [List.getD_eq_default _ _ out] at op
      contradiction
    have lostLive : hits C \ hits (after j) ⊆ liveEdges j := by
      intro e he
      obtain ⟨old, lost⟩ := Finset.mem_sdiff.mp he
      obtain ⟨edge, hit⟩ := Finset.mem_filter.mp old
      have gone : circuitFun n (after j) (input e) = false := by
        exact Bool.eq_false_iff.mpr (fun still => lost (Finset.mem_filter.mpr ⟨edge, still⟩))
      exact Finset.mem_filter.mpr ⟨old, trace n C j admissible.1 bound (input e) hit gone⟩
    refine ⟨j, bad, ?_⟩
    change (hits C \ hits (after j)).card ≤ (c+1) * freed j
    have count := (Finset.card_le_card lostLive).trans load
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · obtain ⟨j, bad, paid⟩ := charge n G degree girth C admissible minimal hasDirty
      (fun j bad => Nat.lt_of_not_ge fun load => small ⟨j, bad, load⟩)
    refine ⟨j, bad, ?_⟩
    change (hits C \ hits (after j)).card ≤ (c+1) * freed j
    exact paid.trans (Nat.mul_le_mul_right _ (by omega))
