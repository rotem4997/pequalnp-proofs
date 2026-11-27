import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Ring.Finset
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 50000 in

theorem PEqualNP.Outside.R_meta_2258_887
    (large :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ D : Circuit, IsLeastAO G D → TopForm G D →
      let U := Ustar G D
      let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
      D.size ≤ 21 → 3 ≤ (junk G D).card → 4 ≤ U.card → B < 2 * U.card →
      (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card + B ≤ 6 + U.card) →
      False)
    (matching :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ D : Circuit, IsLeastAO G D → TopForm G D →
      let U := Ustar G D
      let V := centreless G D
      let T := (tops G D \ V).card
      let B := 2 * V.card + (junk G D).card + (orN G D \ lam G D).card
      D.size ≤ 21 → 3 ≤ (junk G D).card → U ∈
        ([{s(0,9),s(1,4),s(3,6)}, {s(1,4),s(2,5),s(6,7)},
          {s(1,4),s(2,5),s(3,7)}, {s(1,4),s(2,5),s(3,6)}] : List (Finset (Sym2 (Fin 11)))) →
      4 ≤ T → T + B ≤ 9 → (V.Nonempty ∨ (orN G D \ lam G D).Nonempty) →
      False)
    (singleBridge :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ D : Circuit, IsLeastAO G D → TopForm G D →
      let U := Ustar G D
      D.size ≤ 21 → U.card = 3 → (tops G D).card = 5 →
      centreless G D = ∅ → (junk G D).card = 3 → (orN G D \ lam G D).card = 1 →
      (∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ K.card = 5) →
      False)
    : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  let exampleGraph : SimpleGraph (Fin 11) := edgeGraph 11
    [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
     (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

  let edges : Finset (Sym2 (Fin 11)) :=
    {s(0,9),s(0,10),s(1,4),s(1,8),s(2,5),s(2,10),s(3,6),s(3,7),
     s(4,8),s(4,10),s(5,8),s(5,9),s(6,7),s(6,10),s(7,9),s(8,9)}

  let unhit (K : Finset (Fin 11)) : Finset (Sym2 (Fin 11)) :=
    edges.filter (fun e => ∀ v ∈ K, v ∉ e)

  let matchingMasks : List (Finset (Sym2 (Fin 11))) :=
    [{s(0,9),s(1,4),s(3,6)}, {s(1,4),s(2,5),s(6,7)},
     {s(1,4),s(2,5),s(3,7)}, {s(1,4),s(2,5),s(3,6)}]

  have edges_eq : exampleGraph.edgeFinset = edges := by dsimp only [exampleGraph, edges]; decide +kernel +revert

  have graph_small_covers : ∀ K : Finset (Fin 11),
      7 ≤ K.card + (unhit K).card ∧
      ((unhit K).card ≤ 3 → 4 ≤ K.card) ∧
      ((unhit K).card ≤ 3 → K.card = 4 → unhit K ∈ matchingMasks ∧ (unhit K).card = 3) := by
    let count (a : Bool) : ℕ := if a then 1 else 0
    let miss (a b : Bool) : ℕ := count (!(a || b))
    let masks : List (Finset (Fin 11)) :=
      [{5,7,8,10}, {3,8,9,10}, {6,8,9,10}, {7,8,9,10}]
    have casesChecked :
        ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool),
        let k := count b0 + count b1 + count b2 + count b3 + count b4 +
            count b5 + count b6 + count b7 + count b8 + count b9 +
            count b10
        let z := miss b0 b9 + miss b0 b10 + miss b1 b4 + miss b1 b8 +
            miss b2 b5 + miss b2 b10 + miss b3 b6 + miss b3 b7 +
            miss b4 b8 + miss b4 b10 + miss b5 b8 + miss b5 b9 +
            miss b6 b7 + miss b6 b10 + miss b7 b9 + miss b8 b9
        7 ≤ k + z ∧ (z ≤ 3 → 4 ≤ k) ∧
        (z ≤ 3 → k = 4 → ∃ X ∈ masks, ∀ i : Fin 11,
          (![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10] : Fin 11 → Bool) i = decide (i ∈ X)) := by
      dsimp only [count, miss, masks]
      decide +kernel +revert
    have masksChecked : ∀ X ∈ masks, unhit X ∈ matchingMasks ∧ (unhit X).card = 3 := by
      dsimp only [masks, unhit, edges, matchingMasks]
      decide +kernel +revert
    intro K
    let b (i : Fin 11) : Bool := decide (i ∈ K)
    have hCard : K.card = count (b 0) + count (b 1) + count (b 2) + count (b 3) + count (b 4) +
        count (b 5) + count (b 6) + count (b 7) + count (b 8) + count (b 9) +
        count (b 10) := by
      have heq : ∑ i : Fin 11, (if i ∈ K then (1 : ℕ) else 0) = K.card := by simp
      rw [← heq]
      simp only [Fin.sum_univ_succ]
      simp [count, b, Nat.add_assoc]
    have hEnds (a b : Fin 11) : (∀ v ∈ K, v ∉ s(a,b)) ↔ a ∉ K ∧ b ∉ K := by
      constructor
      · intro h
        exact ⟨fun ha => h a ha (Sym2.mem_iff.mpr (Or.inl rfl)),
          fun hb => h b hb (Sym2.mem_iff.mpr (Or.inr rfl))⟩
      · rintro ⟨ha, hb⟩ v hv hs
        rcases Sym2.mem_iff.mp hs with rfl | rfl
        · exact ha hv
        · exact hb hv
    have hMissing : (unhit K).card = miss (b 0) (b 9) + miss (b 0) (b 10) + miss (b 1) (b 4) + miss (b 1) (b 8) +
        miss (b 2) (b 5) + miss (b 2) (b 10) + miss (b 3) (b 6) + miss (b 3) (b 7) +
        miss (b 4) (b 8) + miss (b 4) (b 10) + miss (b 5) (b 8) + miss (b 5) (b 9) +
        miss (b 6) (b 7) + miss (b 6) (b 10) + miss (b 7) (b 9) + miss (b 8) (b 9) := by
      unfold unhit
      rw [Finset.card_filter]
      dsimp only [edges]
      simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, hEnds]
      simp [count, miss, b, Nat.add_assoc]
    have validation := casesChecked (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10)
    dsimp only at validation
    rw [← hCard, ← hMissing] at validation
    refine ⟨validation.1, validation.2.1, ?_⟩
    intro hSmall hFour
    obtain ⟨X, hX, hTest⟩ := validation.2.2 hSmall hFour
    have hSame : K = X := by
      ext v
      have hBit : (![b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] : Fin 11 → Bool) v = b v := by
        fin_cases v <;> rfl
      have hv := hTest v
      rw [hBit] at hv
      simpa [b] using hv
    rw [hSame]
    exact masksChecked X hX

  have unhit_subset (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
      (hK : (exampleGraph.deleteEdges (↑U : Set (Sym2 (Fin 11)))).IsVertexCover ↑K) :
      unhit K ⊆ U := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hCross := Finset.mem_filter.mp he
      have hadj : exampleGraph.Adj a b := by
        rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset, edges_eq]

        exact hCross.1
      by_contra hs
      have hh : (exampleGraph.deleteEdges ↑U).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hs⟩
      rcases hK hh with ha | hb
      · exact hCross.2 a ha (by simp)
      · exact hCross.2 b hb (by simp)


  let canonical : DecidableRel exampleGraph.Adj := inferInstance

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    delta gateAt
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj


  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj


  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    delta GateOp.eval
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩


  let _ : DecidableEq GateOp := gateOpDecEq
  have orStep_unfold (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      orStep n cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := rfl
  have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [orStep_unfold]
      omega

  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        simp only [orStep_unfold, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp only [orStep_unfold, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp only [orStep_unfold, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3
            exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp only [orStep_unfold, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega

  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    delta OrReaches orSets gateAt
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩


  have junk_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
      (hArity : ∀ g ∈ D.gates, g.inputs.length = 2)
      (a : ℕ) (ha : a ∈ tops G D) (b : Fin 2) (j : ℕ) (hj : j ∈ junk G D)
      (hReach : OrReaches n D (opnd D a b) j) :
      a ∈ centreless G D ∨ (orN G D \ lam G D).Nonempty := by
    let _ : DecidableEq GateOp := gateOpDecEq
    have hJunk : IsDirtyAnd n G D j := (Finset.mem_filter.mp hj).2
    obtain ⟨hAnd, hJ, x, hx, hNot⟩ := hJunk
    have hEmpty : orIn n D (n + j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      delta orIn at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with h | ⟨k, _, hk, hOr, _⟩
      · have hi' := i.isLt
        omega
      · rcases (orReaches_iff n D j k).mp hk with ⟨_, h | ⟨hOr', _⟩⟩
        · rw [h, hAnd] at hOr
          cases hOr
        · rw [hAnd] at hOr'
          cases hOr'
    have direct : ∀ w, OrReaches n D w j →
        w = n + j ∨ ∃ q < D.gates.length, (gateAt D q).op = GateOp.or ∧
          n + j ∈ (gateAt D q).inputs ∧ j < q := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        have hn := hw.1
        obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        rcases (orReaches_iff n D k j).mp hw with ⟨hk, h | ⟨hop, i, hi, hlt, hr⟩⟩
        · left
          rw [h]
        · rcases ih i hlt hr with he | he
          · right
            exact ⟨k, hk, hop, he ▸ hi, by omega⟩
          · exact Or.inr he
    rcases direct _ hReach with hDirect | ⟨q, hq, hOr, hInput, hLt⟩
    · left
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      have hb : side (n := n) D a b = ∅ := by
        delta side
        exact hDirect.symm ▸ hEmpty
      fin_cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · right
      have hNotBelow : ¬ BelowF G D q := by
        intro hBelow
        have hVal : gateVal n D q x = true := by
          apply (val_or (n := n) (C := D) (x := List.ofFn x) (by simp) hq hOr).mpr
          exact ⟨n + j, hInput, by omega, hx⟩
        have hf := hBelow x hVal
        exact Bool.noConfusion (hNot.symm.trans hf)
      have hN : q ∈ orN G D := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq, hOr, hNotBelow⟩
      refine ⟨q, Finset.mem_sdiff.mpr ⟨hN, ?_⟩⟩
      intro hLam
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hLam
      have hLength := hArity (gateAt D q) (gateAt_mem hq)
      obtain ⟨p, r, hp⟩ : ∃ p r : ℕ, (gateAt D q).inputs = [p, r] := by
        cases hin : (gateAt D q).inputs with
        | nil => simp [hin] at hLength
        | cons p ts =>
          cases ts with
          | nil => simp [hin] at hLength
          | cons r rs =>
            have eqNil : rs = [] := by simpa [hin] using hLength
            exact ⟨p, r, by simp [eqNil]⟩
      rw [hp] at hInput
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hInput
      rcases hInput with h | h
      · have hEq : opnd D q 0 = n + j := by
          delta opnd
          simpa [hp] using h.symm
        rw [hEq, hEmpty] at h0
        exact Finset.not_nonempty_empty h0
      · have hEq : opnd D q 1 = n + j := by
          delta opnd
          simpa [hp] using h.symm
        rw [hEq, hEmpty] at h1
        exact Finset.not_nonempty_empty h1


  intro G decG D hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hJunk
  by_contra hShort
  have hSize : D.size ≤ 21 := by omega
  subst G
  have hDec : decG = canonical := Subsingleton.elim _ _
  subst decG
  classical
  let U := Ustar exampleGraph D
  let V := centreless exampleGraph D
  let T := tops exampleGraph D
  let J := junk exampleGraph D
  let R := orN exampleGraph D \ lam exampleGraph D
  let B := 2 * V.card + J.card + R.card
  change 15 + (T \ V).card + 2 * V.card + J.card + R.card ≤ D.size + U.card at hCount
  change 3 ≤ J.card at hJunk
  have hBudget : (T \ V).card + B ≤ 6 + U.card := by
    dsimp only [B]
    omega
  let H := exampleGraph.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let Q (t : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover ↑K ∧ K.card = t
  have hExists : ∃ t, Q t := by
    refine ⟨_, Finset.univ, ?_, rfl⟩
    intro a b _
    exact Or.inl (Finset.mem_univ a)
  obtain ⟨K, hK, hCard⟩ := Nat.find_spec hExists
  have hKMin : IsMinCover H K := by
    refine ⟨hK, fun X hX => ?_⟩
    rw [hCard]
    exact Nat.find_min' hExists ⟨X, hX, rfl⟩
  have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
  have hMissing : unhit K ⊆ U := unhit_subset U K hK
  have hMissingCard : (unhit K).card ≤ U.card := Finset.card_le_card hMissing
  obtain ⟨hFull, hFour, hMatch⟩ := graph_small_covers K
  have hDeletion : 7 ≤ K.card + U.card := by omega
  have hDouble : B < 2 * U.card := by
    dsimp only [B] at hBudget ⊢
    omega
  have hUNonempty : U.Nonempty := Finset.card_pos.mp (by
    dsimp only [B] at hBudget
    omega)
  have hConnect : V.Nonempty ∨ R.Nonempty := by
    obtain ⟨e, he⟩ := hUNonempty
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, ha, b, j, hj, _, hReach, _⟩ := hOff u v he
      exact (junk_trace exampleGraph D hLeast.1.2.2 a ha b j hj hReach).imp (fun hm => ⟨a,hm⟩) id
  have hExtra : 1 ≤ 2 * V.card + R.card := by
    rcases hConnect with hV | hR
    · have hP := Finset.card_pos.mpr hV
      omega
    · have hP := Finset.card_pos.mpr hR
      omega
  have hB : 4 ≤ B := by dsimp only [B]; omega
  by_cases hLarge : 4 ≤ U.card
  · apply large D hLeast hTop hSize hJunk hLarge hDouble
    intro X hX
    change X.card + B ≤ 6 + U.card
    have hXT : X.card ≤ (T \ V).card := hCoverBound X hX
    omega
  have hU3 : U.card = 3 := by omega
  have hK4 : 4 ≤ K.card := hFour (by omega)
  have hK5 : K.card ≤ 5 := by omega
  by_cases hKIs4 : K.card = 4
  · obtain ⟨hMask, hMaskCard⟩ := hMatch (by omega) hKIs4
    have hMaskEq : unhit K = U := Finset.eq_of_subset_of_card_le hMissing (by omega)
    rw [hMaskEq] at hMask
    have hT4 : 4 ≤ (T \ V).card := by omega
    have hT9 : (T \ V).card + B ≤ 9 := by omega
    exact matching D hLeast hTop hSize hJunk hMask hT4 hT9 hConnect
  have hKIs5 : K.card = 5 := by omega
  have hT5 : (T \ V).card = 5 := by omega
  have hV0 : V.card = 0 := by
    dsimp only [B] at hBudget
    omega
  have hVEmpty : V = ∅ := Finset.card_eq_zero.mp hV0
  have hTCard : T.card = 5 := by simpa [hVEmpty] using hT5
  have hJ3 : J.card = 3 := by
    dsimp only [B] at hBudget
    omega
  have hR1 : R.card = 1 := by
    dsimp only [B] at hBudget
    omega
  exact singleBridge D hLeast hTop hSize hU3 hTCard hVEmpty hJ3 hR1 ⟨K, hKMin, hKIs5⟩



