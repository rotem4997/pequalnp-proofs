import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.NotPremium PEqualNP.CarriedProduct

-- Keep the union of the live computations on the edge inputs after a gate is set to false.
-- Removing every other gate must preserve the surviving edges and can only narrow the output.
-- A record circuit loses an edge when any one of its gates is set to false.
-- The graph estimate counts the lost edges against the gates outside the live computations.
theorem PEqualNP.Outside.R_meta_2434_1
    (prune : ∀ (n : ℕ) (C : Circuit) (j : ℕ) (X : Finset (Fin n → Bool)),
      Monotone2 C → j < C.size →
      let P : Circuit := ⟨replaceByConst C.gates j false, C.output⟩
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D ≤ circuitFun n C ∧
        (∀ x ∈ X, circuitFun n D x = circuitFun n P x) ∧
        D.size ≤ (((Finset.range C.size).erase j).filter fun i =>
          ∃ x ∈ X, IsLive n P x (n+i)).card)
    (charge : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → 5 ≤ G.egirth →
      let bits := fun (e : Sym2 (Fin n)) (v : Fin n) => decide (v ∈ e)
      let hits := fun C : Circuit => G.edgeFinset.filter fun e => circuitFun n C (bits e) = true
      let admissible := fun C : Circuit => Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅
      let bad := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = GateOp.and ∧
        ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      ∀ C : Circuit, admissible C →
      (∀ B : Circuit, admissible B → B.size < C.size → (hits B).card < (hits C).card) →
      let P := fun j : ℕ => (⟨replaceByConst C.gates j false, C.output⟩ : Circuit)
      (∀ j < C.size, hits (P j) ⊂ hits C) → (∃ j, bad C j) → ∃ j, bad C j ∧
        (hits C \ hits (P j)).card ≤ k * (C.size - (((Finset.range C.size).erase j).filter fun i =>
          ∃ e ∈ G.edgeFinset, IsLive n (P j) (bits e) (n+i)).card)) :
∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →         have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x7 x8 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ x8 = Bool.true;         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x8 fun (x10 : Fin x2) => Decidable.decide (x10 ∈ x9)) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x11 : Fin x2) (x12 : Fin x2), ¬x3.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x9 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true;         ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → x7 x10 → (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 → x7 x13 → x13.size < x10.size → (x8 x13).card < (x8 x10).card) → (∃ (x14 : ℕ), x9 x10 x14) → ∃ (x15 : ℕ), x9 x10 x15 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ x7 x16 ∧ x16.size < x10.size ∧ x8 x16 = x8 { gates := PEqualNP.NotPremium.replaceByConst x10.gates x15 Bool.false, output := x10.output : PEqualNP.CircuitLowerBounds.Circuit } ∧ (x8 x10).card ≤ (x8 x16).card + x1 * (x10.size - x16.size) := by
  classical
  obtain ⟨k, charge⟩ := charge
  refine ⟨k, ?_⟩
  intro n G inst hdeg hgirth
  dsimp only
  intro C hC hsafe hrecord hbad
  let bits (e : Sym2 (Fin n)) (v : Fin n) := decide (v ∈ e)
  let hits (B : Circuit) := G.edgeFinset.filter fun e => circuitFun n B (bits e) = true
  have safe_iff (B : Circuit) : circuitFun n B ≤ graphFun G ∅ ↔
      ∀ x, circuitFun n B x = true → graphFun G ∅ x = true := by
    exact ⟨fun h x => Bool.le_iff_imp.mp (h x), fun h x => Bool.le_iff_imp.mpr (h x)⟩
  have hg : 5 ≤ G.egirth := SimpleGraph.le_egirth.mpr fun v p hp => by exact_mod_cast hgirth v p hp
  let P (j : ℕ) : Circuit := ⟨replaceByConst C.gates j false, C.output⟩
  let X := G.edgeFinset.image bits
  let kept (j : ℕ) := ((Finset.range C.size).erase j).filter fun i =>
    ∃ e ∈ G.edgeFinset, IsLive n (P j) (bits e) (n+i)
  have compress (j : ℕ) (hj : j < C.size) : ∃ D : Circuit, Monotone2 D ∧
      circuitFun n D ≤ circuitFun n C ∧ D.size < C.size ∧ hits D = hits (P j) ∧ D.size ≤ (kept j).card := by
    obtain ⟨D, hm, hle, hagree, hsize⟩ := prune n C j X hC hj
    have hbound : D.size ≤ (kept j).card := by
      convert hsize using 2
      ext i
      simp [kept, X, P]
    have hsub : (kept j).card ≤ ((Finset.range C.size).erase j).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range] at hsub
    refine ⟨D, hm, hle, by omega, ?_, hbound⟩
    apply Finset.filter_congr
    intro e he
    rw [hagree (bits e) (Finset.mem_image_of_mem bits he)]
  have pivotal (j : ℕ) (hj : j < C.size) : hits (P j) ⊂ hits C := by
    obtain ⟨D, hm, hle, hlt, heq, _⟩ := compress j hj
    rw [← heq, Finset.ssubset_iff_subset_ne]
    constructor
    · intro e he
      obtain ⟨hedge, hon⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hedge, Bool.le_iff_imp.mp (hle (bits e)) hon⟩
    · have hltCard : (hits D).card < (hits C).card :=
        hrecord D hm ((safe_iff D).mp (hle.trans ((safe_iff C).mpr hsafe))) hlt
      exact fun h => hltCard.ne (congrArg Finset.card h)
  obtain ⟨j, hj, hprice⟩ := charge n G hdeg hg C ⟨hC, (safe_iff C).mpr hsafe⟩
    (fun B hb => hrecord B hb.1 ((safe_iff B).mp hb.2)) pivotal hbad
  have hjlt : j < C.size := by
    by_contra! h
    have hop := hj.1
    change (C.gates.getD j ⟨.or, []⟩).op = .and at hop
    rw [List.getD_eq_default _ _ h] at hop
    contradiction
  obtain ⟨D, hm, hle, hlt, heq, hbound⟩ := compress j hjlt
  refine ⟨j, hj, D, hm, (safe_iff D).mp (hle.trans ((safe_iff C).mpr hsafe)), hlt, heq, ?_⟩
  change (hits C).card ≤ (hits D).card + k * (C.size - D.size)
  change (hits C \ hits (P j)).card ≤ k * (C.size - (kept j).card) at hprice
  rw [Finset.card_sdiff_of_subset (pivotal j hjlt).subset] at hprice
  rw [heq]
  have hsaved := Nat.mul_le_mul_left k (Nat.sub_le_sub_left hbound C.size)
  omega
