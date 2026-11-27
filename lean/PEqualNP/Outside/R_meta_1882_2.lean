import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Charge a local singleton operand to its gate and input position.
-- Count both inputs reached through OR and truth values on singleton assignments.
-- Two potential centres must have two common neighbours, by counting their intersection.
-- For the remaining edges, use the two possible kinds of activation at a top AND.
-- The four-cycle construction follows R_meta_1735_7.

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1882_2
    (trace : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.Ustar x2 x4, (∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x12 : Fin (2 : ℕ)), ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x9 ∈ PEqualNP.TopForm.side x4 x11 x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x12 ≠ x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true)
    (mixedBound : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        (∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone n C i j) →
        ∀ W : Finset (Sym2 (Fin n)), W ⊆ Ustar G C →
        let S (raw : Bool) (w : ℕ) : Finset (Fin n) :=
          if raw then orIn n C w else
            ((List.finRange n).filter (fun v => (C.wires (List.ofFn (pairInput v v))).getD w false)).toFinset
        let localEdge (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧
        ∃ raw : Bool, ∃ h < C.gates.length, ∃ b : Fin 2,
          (S raw (n + h)).card + 2 ≤
            2 * (((S raw (n + h)).toList.filter (fun w => decide (G.Adj u w))).toFinset).card ∧
          S raw (opnd C h b) = [v].toFinset
        let witness (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) h ∧
          gateVal n C h (pairInput u v) = true
        (∀ e ∈ W, ¬ localEdge e ∧ witness e) → W.card ≤ k * (C.size + 1))
    (twoJunkBound : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        (∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone n C i j) →
        ∀ W : Finset (Sym2 (Fin n)), W ⊆ Ustar G C →
        let S (raw : Bool) (w : ℕ) : Finset (Fin n) :=
          if raw then orIn n C w else
            ((List.finRange n).filter (fun v => (C.wires (List.ofFn (pairInput v v))).getD w false)).toFinset
        let localEdge (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧
        ∃ raw : Bool, ∃ h < C.gates.length, ∃ b : Fin 2,
          (S raw (n + h)).card + 2 ≤
            2 * (((S raw (n + h)).toList.filter (fun w => decide (G.Adj u w))).toFinset).card ∧
          S raw (opnd C h b) = [v].toFinset
        let witness (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ h ∈ junk G C, ∃ j ∈ junk G C,
        h ≠ j ∧ OrReaches n C (opnd C a 0) h ∧ OrReaches n C (opnd C a 1) j ∧
          gateVal n C h (pairInput u v) = true ∧ gateVal n C j (pairInput u v) = true
        (∀ e ∈ W, ¬ localEdge e ∧ witness e) → W.card ≤ k * (C.size + 1))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨km, hkm⟩ := mixedBound
  obtain ⟨kd, hkd⟩ := twoJunkBound
  refine ⟨4 + km + kd, ?_⟩
  intro n G _ hg _ C hLeast hTop _ hNest
  let S (raw : Bool) (w : ℕ) : Finset (Fin n) :=
    if raw then orIn n C w else
      ((List.finRange n).filter (fun v => (C.wires (List.ofFn (pairInput v v))).getD w false)).toFinset
  let P (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧
        ∃ raw : Bool, ∃ h < C.gates.length, ∃ b : Fin 2,
          (S raw (n + h)).card + 2 ≤
            2 * (((S raw (n + h)).toList.filter (fun w => decide (G.Adj u w))).toFinset).card ∧
          S raw (opnd C h b) = [v].toFinset
  let M (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) h ∧
          gateVal n C h (pairInput u v) = true
  let B (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ h ∈ junk G C, ∃ j ∈ junk G C,
        h ≠ j ∧ OrReaches n C (opnd C a 0) h ∧ OrReaches n C (opnd C a 1) j ∧
          gateVal n C h (pairInput u v) = true ∧ gateVal n C j (pairInput u v) = true
  have charge (W : Finset (Sym2 (Fin n))) (hW : ∀ e ∈ W, P e) : W.card ≤ 4 * C.size := by
    have h4 : NoFourCycle G := by
      intro a b hab
      by_contra hc
      rw [not_le] at hc
      obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
      rw [Finset.mem_filter] at hw1 hw2
      obtain ⟨-, ha1, hb1⟩ := hw1
      obtain ⟨-, ha2, hb2⟩ := hw2
      have e1 := G.ne_of_adj ha1
      have e2 := G.ne_of_adj hb1
      have e3 := G.ne_of_adj ha2
      have e4 := G.ne_of_adj hb2
      have hcyc : (SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons hb1.symm
          (SimpleGraph.Walk.cons hb2 (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))).IsCycle := by
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        refine ⟨?_, ?_⟩
        · simp [SimpleGraph.Walk.cons_isPath_iff, e4, hne, Ne.symm e1, Ne.symm e2,
            Ne.symm e3, Ne.symm hab]
        · simp [e1, e3, hab, hne, Ne.symm e1, Ne.symm e2]
      have h5 := hg a _ hcyc
      simp at h5
    classical
    have hW' (e : ↥W) := hW e.val e.property
    choose u v he raw h hh b hs hv using hW'
    let code (e : ↥W) : Bool × Fin C.gates.length × Fin 2 := (raw e, ⟨h e, hh e⟩, b e)
    have hinj : Function.Injective code := by
      intro e e' codeEq
      have hmode : raw e = raw e' := congrArg Prod.fst codeEq
      have hgate : h e = h e' := congrArg (fun p => p.2.1.val) codeEq
      have hslot : b e = b e' := congrArg (fun p => p.2.2) codeEq
      have hleaf : v e = v e' := by
        have hEq := (hv e).symm.trans (by simpa only [hmode, hgate, hslot] using hv e')
        simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.singleton_inj] using hEq
      have hcent : u e = u e' := by
        by_contra hneq
        let V := S (raw e) (n + h e)
        let L := V.filter (G.Adj (u e))
        let R := V.filter (G.Adj (u e'))
        have filterEq (a : Fin n) :
            (V.toList.filter (fun w => decide (G.Adj a w))).toFinset = V.filter (G.Adj a) := by
          ext w
          simp
        have hLeft : V.card + 2 ≤ 2 * L.card := by
          have ht : V.card + 2 ≤ 2 * (V.toList.filter (fun w => decide (G.Adj (u e) w))).toFinset.card :=
            hs e
          rw [filterEq] at ht
          exact ht
        have hRight : V.card + 2 ≤ 2 * R.card := by
          have ht := hs e'
          rw [← hmode, ← hgate] at ht
          change V.card + 2 ≤ 2 * (V.toList.filter (fun w => decide (G.Adj (u e') w))).toFinset.card at ht
          rw [filterEq] at ht
          exact ht
        have hUnion : L ∪ R ⊆ V :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hInter : L ∩ R ⊆ Finset.univ.filter (fun w => G.Adj (u e) w ∧ G.Adj (u e') w) := by
          intro w hw
          obtain ⟨hl, hr⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hr).2⟩
        have hUnionCard := Finset.card_le_card hUnion
        have hInterCard := (Finset.card_le_card hInter).trans (h4 (u e) (u e') hneq)
        have hCards := Finset.card_union_add_card_inter L R
        omega
      apply Subtype.ext
      exact (he e).trans (by rw [hcent, hleaf, ← he e'])
    have hc := Fintype.card_le_of_injective code hinj
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
    change W.card ≤ 4 * C.gates.length
    omega
  classical
  let U := Ustar G C
  let W0 := U.filter P
  let Wm := U.filter (fun e => ¬ P e ∧ M e)
  let Wd := U.filter (fun e => ¬ P e ∧ ¬ M e)
  have h0 : W0.card ≤ 4 * C.size :=
    charge W0 (fun _ he => (Finset.mem_filter.mp he).2)
  have hm : Wm.card ≤ km * (C.size + 1) :=
    hkm n G hg C hLeast hTop hNest Wm (Finset.filter_subset _ _)
      (fun _ he => (Finset.mem_filter.mp he).2)
  have hd : Wd.card ≤ kd * (C.size + 1) := by
    apply hkd n G hg C hLeast hTop hNest Wd (Finset.filter_subset _ _)
    intro e he
    obtain ⟨heU, heP, heM⟩ := Finset.mem_filter.mp he
    have hCases : M e ∨ B e := trace n G C hLeast hTop e heU
    exact ⟨heP, hCases.resolve_left heM⟩
  have hParts : U ⊆ W0 ∪ (Wm ∪ Wd) := by
    intro e he
    by_cases hp : P e
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hp⟩)
    · apply Finset.mem_union_right
      by_cases hmix : M e
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hp, hmix⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hp, hmix⟩)
  change U.card ≤ (4 + km + kd) * (C.size + 1)
  calc
    U.card ≤ (W0 ∪ (Wm ∪ Wd)).card := Finset.card_le_card hParts
    _ ≤ W0.card + (Wm.card + Wd.card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤ 4 * (C.size + 1) + (km * (C.size + 1) + kd * (C.size + 1)) :=
      Nat.add_le_add (h0.trans (Nat.mul_le_mul_left 4 (Nat.le_succ _))) (Nat.add_le_add hm hd)
    _ = (4 + km + kd) * (C.size + 1) := by simp only [Nat.add_mul, Nat.add_assoc]
