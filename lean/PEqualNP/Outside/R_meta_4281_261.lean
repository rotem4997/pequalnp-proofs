import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CarriedProduct PEqualNP.EdgeOwnership PEqualNP.NotPremium

theorem PEqualNP.Outside.R_meta_4281_261
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
      (∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size) →
      PEqualNP.TopForm.IsAO2 n C)
    (price : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → 5 ≤ G.egirth →
      let bits := fun (e : Sym2 (Fin n)) (v : Fin n) => decide (v ∈ e)
      let hits := fun C : Circuit => G.edgeFinset.filter fun e => circuitFun n C (bits e) = true
      let admissible := fun C : Circuit => Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅
      let dirty := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = GateOp.and ∧
        ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      ∀ C : Circuit, admissible C → PEqualNP.TopForm.IsAO2 n C →
        (∀ D : Circuit, admissible D → D.size < C.size → (hits D).card < (hits C).card) →
        let mute := fun j : ℕ => (⟨replaceByConst C.gates j false, C.output⟩ : Circuit)
        (∀ j < C.size, hits (mute j) ⊂ hits C) → (∃ j, dirty C j) →
        ∃ j, dirty C j ∧ (hits C \ hits (mute j)).card ≤ k *
          (C.size - (((Finset.range C.size).erase j).filter fun i =>
            ∃ e ∈ G.edgeFinset, IsLive n (mute j) (bits e) (n + i)).card)) :
  ∃ (x1 : ℕ),
   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →
       (5 : ℕ∞) ≤ x3.egirth →
         have x7 : Sym2 (Fin x2) → Fin x2 → Bool :=
           fun (x7 : Sym2 (Fin x2)) (x8 : Fin x2) => Decidable.decide (x8 ∈ x7);
         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) :=
           fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) =>
             {x9 ∈ x3.edgeFinset | PEqualNP.MetaComplexity.circuitFun x2 x8 (x7 x9) = Bool.true};
         have x9 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
           fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x9 ∧
             PEqualNP.MetaComplexity.circuitFun x2 x9 ≤ PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅;
         have x10 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop :=
           fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) =>
             (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
               ∃ (x12 : Fin x2) (x13 : Fin x2), ¬x3.Adj x12 x13 ∧
                 PEqualNP.EdgeOwnership.gateVal x2 x10 x11
                   (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true;
         ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
           x9 x11 →
             (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x9 x13 → x13.size < x11.size → (x8 x13).card < (x8 x11).card) →
               have x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit :=
                 fun (x14 : ℕ) =>
                   { gates := PEqualNP.NotPremium.replaceByConst x11.gates x14 Bool.false,
                     output := x11.output : PEqualNP.CircuitLowerBounds.Circuit };
               (∀ x15 < x11.size, x8 (x14 x15) ⊂ x8 x11) → (∃ (x16 : ℕ), x10 x11 x16) →
                 ∃ (x17 : ℕ), x10 x11 x17 ∧ (x8 x11 \ x8 (x14 x17)).card ≤ x1 *
                   (x11.size - {x18 ∈ (Finset.range x11.size).erase x17 |
                     ∃ x19 ∈ x3.edgeFinset,
                       PEqualNP.CarriedProduct.IsLive x2 (x14 x17) (x7 x19) (x2 + x18)}.card) := by
  obtain ⟨k, price⟩ := price
  refine ⟨k, ?_⟩
  intro n G inst hdegree hgirth
  dsimp only
  intro C hsafe hrecord hpiv hbad
  let bits (e : Sym2 (Fin n)) (v : Fin n) := decide (v ∈ e)
  let hits (D : Circuit) := G.edgeFinset.filter fun e => circuitFun n D (bits e) = true
  obtain ⟨j, hop, hnonedge⟩ := hbad
  have hj : j < C.size := by
    by_contra! h
    change (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and at hop
    rw [List.getD_eq_default _ _ h] at hop
    contradiction
  have hpos : (hits C).Nonempty := by
    exact Finset.card_pos.mp ((Nat.zero_le _).trans_lt (Finset.card_lt_card (hpiv j hj)))
  obtain ⟨e, he⟩ := hpos
  have hon : circuitFun n C (bits e) = true := (Finset.mem_filter.mp he).2
  have hoff : circuitFun n C (fun _ => false) = false := by
    have h := hsafe.2 (fun _ => false)
    have hzero : graphFun G ∅ (fun _ => false) = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), false = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ false = true ∧ false = true)) = false
      simp
    rw [hzero] at h
    exact Bool.eq_false_of_le_false h
  have hnonconstant : ∃ x y, circuitFun n C x ≠ circuitFun n C y :=
    ⟨bits e, fun _ => false, by simp [hon, hoff]⟩
  have hleast : ∀ D : Circuit, Monotone2 D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size := by
    intro D hmono heq
    by_contra! hlt
    have hs : circuitFun n D ≤ graphFun G ∅ := by rw [heq]; exact hsafe.2
    have h := hrecord D ⟨hmono, hs⟩ hlt
    simp [heq] at h
  have hshape := normalize n C hsafe.1 hnonconstant hleast
  exact price n G hdegree hgirth C hsafe hshape hrecord hpiv ⟨j, hop, hnonedge⟩
