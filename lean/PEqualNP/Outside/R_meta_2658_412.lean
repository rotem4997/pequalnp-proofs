import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.NotPremium

-- An AND gate is needed on a pair when forcing its wire low loses that edge.
-- Repair the gates needed on at most one pair first. The other hypothesis
-- concerns circuits in which every unsound AND gate is needed on two distinct pairs.
theorem PEqualNP.Outside.R_meta_2658_412
    (repairFew : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ),
      Monotone2 C → circuitFun n C = graphFun G ∅ → j ∈ junk G C →
      (∃ a b, G.Adj a b ∧ ∀ u v, G.Adj u v →
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput u v) = false →
        pairInput u v = pairInput a b) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card)
    (repairMany : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ → (junk G C).Nonempty →
      (∀ j ∈ junk G C, ∃ a b u v, G.Adj a b ∧ G.Adj u v ∧ pairInput a b ≠ pairInput u v ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput a b) = false ∧
        circuitFun n {C with gates := replaceByConst C.gates j false} (pairInput u v) = false) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G C edge noCycle mono computes
  have hit (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    unfold graphFun
    simp
  have computesGraph : circuitFun n C = graphFun G ∅ := by
    funext x
    exact Bool.eq_iff_iff.mpr ((computes x).trans (hit x).symm)
  have fourFree : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have ha := (Finset.mem_filter.mp hc).2
    have hb := (Finset.mem_filter.mp hd).2
    by_contra hcd
    exact noCycle a c b d (G.ne_of_adj ha.1) hab (G.ne_of_adj hb.1)
      (G.ne_of_adj ha.2).symm hcd (G.ne_of_adj hb.2) ha.1 ha.2.symm hb.2 hb.1.symm
  have normalize : ∀ (k : ℕ) (D : Circuit), Monotone2 D →
      circuitFun n D = graphFun G ∅ → (junk G D).card = k →
      ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size ≤ D.size ∧ junk G E = ∅ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hM hD count
      by_cases nonempty : (junk G D).Nonempty
      · let loses := fun (j : ℕ) (a b : Fin n) => G.Adj a b ∧
          circuitFun n {D with gates := replaceByConst D.gates j false} (pairInput a b) = false
        have progress : ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧
            E.size ≤ D.size ∧ (junk G E).card < (junk G D).card := by
          by_cases few : ∃ j ∈ junk G D, ∃ a b, G.Adj a b ∧
              ∀ u v, loses j u v → pairInput u v = pairInput a b
          · obtain ⟨j, hj, a, b, hab, unique⟩ := few
            exact repairFew n G D j hM hD hj ⟨a, b, hab, fun u v huv hu => unique u v ⟨huv, hu⟩⟩
          · apply repairMany n G D fourFree hM hD nonempty
            intro j hj
            have someLoss : ∃ a b, loses j a b := by
              by_contra none
              obtain ⟨a, b, hab⟩ := edge
              exact few ⟨j, hj, a, b, hab, fun u v huv => (none ⟨u, v, huv⟩).elim⟩
            obtain ⟨a, b, ab⟩ := someLoss
            have another : ∃ u v, loses j u v ∧ pairInput u v ≠ pairInput a b := by
              by_contra none
              apply few
              refine ⟨j, hj, a, b, ab.1, fun u v uv => ?_⟩
              by_contra unequal
              exact none ⟨u, v, uv, unequal⟩
            obtain ⟨u, v, uv, unequal⟩ := another
            exact ⟨a, b, u, v, ab.1, uv.1, Ne.symm unequal, ab.2, uv.2⟩
        obtain ⟨E, eM, eD, sizeE, less⟩ := progress
        rw [count] at less
        obtain ⟨F, fM, fD, sizeF, clean⟩ := ih _ less E eM eD rfl
        exact ⟨F, fM, fD, sizeF.trans sizeE, clean⟩
      · exact ⟨D, hM, hD, le_rfl, Finset.not_nonempty_iff_eq_empty.mp nonempty⟩
  obtain ⟨E, eM, eD, sizeE, clean⟩ := normalize _ C mono computesGraph rfl
  refine ⟨E, eM, fun x => ?_, sizeE, ?_⟩
  · change circuitFun n E x = true ↔ _
    rw [eD]
    exact hit x
  · intro j g actual isAnd x value
    apply (hit x).mp
    by_contra notHit
    have hfalse : graphFun G ∅ x = false := Bool.eq_false_iff.mpr notHit
    have existsGate := (List.getElem?_eq_some_iff.mp actual).1
    have op : (gateAt E j).op = GateOp.and := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, actual]
      exact isAnd
    have mem : j ∈ junk G E := by
      change j ∈ (Finset.range E.gates.length).filter (fun i => IsDirtyAnd n G E i)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr existsGate, op, existsGate, x, value, hfalse⟩
    rw [clean] at mem
    exact Finset.notMem_empty j mem
