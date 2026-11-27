import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4715_619
    (twoJunk : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
    (junk G C).card = 2 →
    let U := Ustar G C
    let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    (orN G C \ lam G C).Nonempty →
    ((centreless G C).Nonempty ∨ 2 ≤ (orN G C \ lam G C).card) →
    4 ≤ B → U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
    (∀ X : Finset (Fin 11), (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ X ∨ v ∈ X) → B - U.card < X.card) →
    ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
      G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card)
    (manyJunk : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
    3 ≤ (junk G C).card →
    let U := Ustar G C
    let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    (orN G C \ lam G C).Nonempty →
    ((centreless G C).Nonempty ∨ 2 ≤ (orN G C \ lam G C).card) →
    5 ≤ B → U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
    (∀ X : Finset (Fin 11), (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ X ∨ v ∈ X) → B - U.card < X.card) →
    ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
      G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card)
    : (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card) := by
  have geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    IsLeastAO G C → TopForm G C →
    let U := Ustar G C
    let H := G.deleteEdges (↑U)
    (centreless G C = ∅ → (orN G C \ lam G C).card ≤ 1 → (∃ u v : Fin n, s(u,v) ∈ U) →
    (orN G C \ lam G C).card = 1 ∧ ∃ q : Fin n, ∀ u v : Fin n, s(u,v) ∈ U → ∃ w : Fin n, (w=u ∨ w=v) ∧ H.Adj q w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset (Fin n), (S.card ≤ 1 ∨ ∃ c, ∀ z ∈ S, H.Adj z c) ∧
        (∀ i j : Fin n, s(i,j) ∈ U → i ∈ S ∨ j ∈ S) ∧ ∀ z ∈ S, x z = false) ∧
    ((orN G C \ lam G C = ∅) →
      (∀ u v : Fin n, s(u,v) ∈ U → ∃ a ∈ centreless G C, gateVal n C a (pairInput u v) = true) ∧
      (∀ a ∈ centreless G C, ∀ x : Fin n → Bool, graphFun G ∅ x = false →
        ∃ S : Finset (Fin n), (S.card ≤ 1 ∨ ∃ z : Fin n, ∀ y ∈ S, H.Adj y z) ∧
          (∀ y ∈ S, x y = false) ∧
          (∀ u v : Fin n, gateVal n C a (pairInput u v) = true → u ∈ S ∨ v ∈ S))) := by

    let stepWire (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have wires_eq_foldl (C : Circuit) (x : List Bool) :
        C.wires x = C.gates.foldl stepWire x := rfl

    have foldl_length (gs : List Gate) (w : List Bool) :
        (gs.foldl stepWire w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp (config := {congrConsts := false})
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp (config := {congrConsts := false}) [stepWire]
        omega

    have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp (config := {congrConsts := false}) only [List.foldl_cons]
        have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
        rw [ih (stepWire w g) hlt]
        simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

    have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
        (gs.foldl stepWire w).getD (w.length + j) false =
          (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
      induction gs generalizing w j with
      | nil => simp (config := {congrConsts := false}) at hj
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
          rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
          simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
          have h2 : (stepWire w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
            simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
          have key := ih (stepWire w g) j hj'
          have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
          rw [e]
          exact key

    let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
    have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      dsimp only [gateAt]
      simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

    have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
      rw [gateAt_eq hj]; exact List.getElem_mem hj

    have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
        val C x u = x.getD u false := by
      simp (config := {congrConsts := false}) only [val]; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

    have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
        (hu : n + C.gates.length ≤ u) : val C x u = false := by
      simp (config := {congrConsts := false}) only [val]; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

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
      dsimp only [GateOp.eval]
      simp (config := {congrConsts := false}) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      constructor
      · rintro ⟨i, hi, h⟩
        by_cases hlt : i < n + r
        · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
        · rw [ite_eq_right hlt] at h; cases h
      · rintro ⟨i, hi, hlt, h⟩
        exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

    have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
        (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
        val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
      rw [val_gate hx hr, hop]
      dsimp only [GateOp.eval]
      simp (config := {congrConsts := false}) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have h' := h i hi
        by_cases hlt : i < n + r
        · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
        · rw [ite_eq_right hlt] at h'; cases h'
      · intro h i hi
        rw [ite_eq_left (h i hi).1]; exact (h i hi).2
    have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
        val C (List.ofFn x) u.val = x u := by
      rw [val_input (n := n) (by simp (config := {congrConsts := false})) u.isLt]
      simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]

    have gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
        PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

    let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
      ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
        w' ∈ (gateAt C k).inputs ∧ w' < n + k

    have orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
        val C x w = true := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact hv
      | head hstep _ ih =>
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

    have or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
        ∀ w : ℕ, val C x w = true →
          ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
            (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hv
        by_cases hw : w < n
        · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
        · by_cases hlen : n + C.gates.length ≤ w
          · rw [val_ge hx hlen] at hv; cases hv
          · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
            have hk : k < C.gates.length := by omega
            by_cases hop : (gateAt C k).op = GateOp.or
            · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
              obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
              exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
            · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

    have pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
      dsimp only [pairInput]
      simp (config := {congrConsts := false})

    have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
      dsimp only [pairInput]
      simp (config := {congrConsts := false})

    have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
      dsimp only [pairInput]
      simp (config := {congrConsts := false})

    have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
        graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
      dsimp only [graphFun]
      simp (config := {congrConsts := false}) only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq, pairInput_true]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (G.irrefl hab).elim
        · exact hab
        · exact hab.symm
        · exact (G.irrefl hab).elim
      · intro h
        exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
    have operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
        (hv : val C (List.ofFn (pairInput u v)) p = true) :
        (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
        (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
          Relation.ReflTransGen (OrStep n C) p (n + h) ∧
          val C (List.ofFn (pairInput u v)) (n + h) = true) := by
      obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
        (by simp (config := {congrConsts := false})) p hv
      rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
      · left
        refine ⟨⟨w', hlt⟩, ?_, hr⟩
        have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
        rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
        exact (pairInput_true u v _).mp h1.symm
      · right
        exact ⟨h, hh, hop, hr, hv'⟩

    have reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
        (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
        val C (List.ofFn x) p = true :=
      orStep_up (n := n) (by simp (config := {congrConsts := false})) hr (by rw [val_ofFn]; exact ht)
    have edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
        (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
        (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
        (u v : Fin n) (huv : F (pairInput u v) = true) :
        ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
          Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
          val C (List.ofFn (pairInput u v)) (n + a) = true := by
      rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
        ⟨t, _, hr⟩ | h
      · exfalso
        have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
        rw [hout] at h1
        exact G.irrefl (hF t t h1)
      · exact h

    have below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
        (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
        (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
        (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
      rw [← hout]
      exact orStep_up (n := n) (by simp (config := {congrConsts := false})) hr hv
    have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp (config := {congrConsts := false})
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        dsimp only [coneStep]
        simp (config := {congrConsts := false})
        omega

    have cones_char (n : ℕ) (gs : List Gate) :
        ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp (config := {congrConsts := false})
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
          rw [cones_len]; simp (config := {congrConsts := false})
        have key : ∀ k, k < gs.length →
            (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
              (gs.foldl (coneStep n) []).getD k [] := by
          intro k hk
          dsimp only [coneStep]
          simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨by simp (config := {congrConsts := false}); omega, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨h, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)] at h3
            exact h3
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
          have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
            dsimp only [coneStep]
            simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp (config := {congrConsts := false}) [hlen]
          rw [e2, e1]
          simp (config := {congrConsts := false}) only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
          constructor
          · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
            refine ⟨by simp (config := {congrConsts := false}), w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            rw [key (w - n) (by omega)] at h3
            exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
            dsimp only [coneStep]
            simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp (config := {congrConsts := false}); omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; simp (config := {congrConsts := false}) at h0
          · rintro ⟨h0, _⟩
            simp (config := {congrConsts := false}) at h0
            omega

    have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
        InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
          (i = k ∨ InCone n C i k) := by
      have h := cones_char n C.gates i j
      dsimp only [InCone, cones, gateAt]
      rw [h]
      constructor
      · rintro ⟨h0, w, hw, h1, h2, h3⟩
        refine ⟨h0, w - n, by omega, ?_, h3⟩
        have : n + (w - n) = w := by omega
        rw [this]
        exact hw
      · rintro ⟨h0, k, hk, hw, h3⟩
        refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
        have : n + k - n = k := by omega
        rw [this]
        exact h3

    have orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_rfl
      | head hstep _ ih =>
        obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
        omega

    have orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') :
        ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro k h' h1 h2; left; omega
      | @head a c hstep hrest ih =>
        intro k h' h1 h2
        obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
        have hk : k0 = k := by omega
        subst hk
        have hle := orStep_le hrest
        obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
        subst hk1
        right
        rw [inCone_iff]
        exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

    have operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
        (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
        (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
      have hle := orStep_le hr
      obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
      rw [inCone_iff]
      exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
    have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp (config := {congrConsts := false})
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        dsimp only [orStep]
        simp (config := {congrConsts := false})
        omega

    have orSets_char (n : ℕ) (gs : List Gate) :
        ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
          j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
            ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
              i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp (config := {congrConsts := false})
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (orStep n) []).length = gs.length := by
          rw [orSets_len]; simp (config := {congrConsts := false})
        have key : ∀ k, k < gs.length →
            (orStep n (gs.foldl (orStep n) []) g).getD k [] =
              (gs.foldl (orStep n) []).getD k [] := by
          intro k hk
          dsimp only [orStep]
          simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, h3⟩
            refine ⟨by simp (config := {congrConsts := false}); omega, ?_⟩
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
            simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
          rw [e1]
          by_cases hop : g.op = GateOp.or
          · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
                gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                  (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
              dsimp only [orStep]
              simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by omega)]
              simp (config := {congrConsts := false}) [hlen, hop]
            rw [e2]
            simp (config := {congrConsts := false}) only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
            constructor
            · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
              · exact ⟨by simp (config := {congrConsts := false}), Or.inl h3⟩
              · refine ⟨by simp (config := {congrConsts := false}), Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
                rw [key (w - n) (by omega)]
                exact h3
            · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
              · exact Or.inl h3
              · rw [key (w - n) (by omega)] at h3
                exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
          · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
              dsimp only [orStep]
              simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by omega)]
              simp (config := {congrConsts := false}) [hlen, hop]
            rw [e2]
            simp (config := {congrConsts := false}) only [List.mem_singleton]
            constructor
            · intro h3
              exact ⟨by simp (config := {congrConsts := false}), Or.inl h3⟩
            · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
              · exact h3
              · exact (hop hop2).elim
        · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
            dsimp only [orStep]
            simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp (config := {congrConsts := false}); omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; simp (config := {congrConsts := false}) at h0
          · rintro ⟨h0, _⟩
            simp (config := {congrConsts := false}) at h0
            omega

    have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
        OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
          ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
      have h := orSets_char n C.gates g k
      dsimp only [OrReaches, orSets, gateAt]
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

    have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w2) :
        ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro g h1 hg
        subst h1
        exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
      | @head a c hstep hrest ih =>
        intro g h1 hg
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

    have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
        ∀ w, OrReaches n C w g →
          Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro h
        have hnw : n ≤ w := h.1
        obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
        rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
        · exact ⟨Relation.ReflTransGen.refl, hk⟩
        · obtain ⟨hr2, hg⟩ := ih i hlt hr
          exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

    have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
        (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
        Relation.ReflTransGen (OrStep n C) p u.val := by
      dsimp only [PEqualNP.TopForm.orIn] at hu
      simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with h | ⟨k, hk, hr, hop, hin⟩
      · rw [h]
      · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

    have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
        (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
        u ∈ PEqualNP.TopForm.orIn n C p := by
      dsimp only [PEqualNP.TopForm.orIn]
      simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
      · exact Or.inl h
      · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
        exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

    intro n G _ C least top _ _
    letI : DecidableEq GateOp := gateOpDecEq

    have topData {a : ℕ} (ha : a ∈ tops G C) :
        a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
      obtain ⟨hr, ho, hb⟩ := Finset.mem_filter.mp ha
      exact ⟨Finset.mem_range.mp hr, ho, hb⟩
    have junkData {a : ℕ} (ha : a ∈ junk G C) :
        a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
          ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
      rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
      exact ⟨hal, hop, hd⟩
    have binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
        ∃ p q, (gateAt C a).inputs = [p, q] :=
      List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
    have opndDef (a : ℕ) (b : Fin 2) :
        opnd C a b = (gateAt C a).inputs.getD b.val 0 := rfl
    have opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
        opnd C a b ∈ (gateAt C a).inputs := by
      obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
      fin_cases b <;> simp (config := {congrConsts := false}) [opndDef, hpq]
    have opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
        opnd C a b < n + a :=
      hAO.2.1 a ha _ (opndMem hAO ha b)
    have andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
        (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
        gateVal n C a x = true ↔
          val C (List.ofFn x) (opnd C a 0) = true ∧
          val C (List.ofFn x) (opnd C a 1) = true := by
      rw [gateVal_eq_val, val_and (n := n) (by simp (config := {congrConsts := false})) ha hop]
      constructor
      · intro h
        exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
      · intro h i hi
        refine ⟨hAO.2.1 a ha i hi, ?_⟩
        obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
        rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
        · simpa (config := {congrConsts := false}) [opndDef, hpq] using h.1
        · have e : i = q := List.mem_singleton.mp hq
          subst i
          simpa (config := {congrConsts := false}) [opndDef, hpq] using h.2
    have andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
        (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
        gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
      rw [andValBoth hAO ha hop]
      constructor
      · intro h b
        fin_cases b
        · exact h.1
        · exact h.2
      · intro h
        exact ⟨h 0, h 1⟩
    have operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
        {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
        InCone n C h a :=
      operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
        (orReaches_reach h _ hr).1
    have operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
        (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
        {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
        (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
      have hlen := (orReaches_reach h _ hr).2
      have hnb : ¬ BelowF G C h :=
        fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
      have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
        by_contra hne
        apply hnb
        intro x hx
        by_contra hf
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
    have inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
        (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
      obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
      rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
      · exact ⟨0, by simp (config := {congrConsts := false}) [opndDef, hpq]⟩
      · have e : z = q := List.mem_singleton.mp hq
        exact ⟨1, by simpa (config := {congrConsts := false}) [opndDef, hpq] using e⟩
    have sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
        (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
        val C (List.ofFn x) (opnd C a b) = true :=
      reach_var_val x _ t (mem_orIn_reach t ht) hx

    have andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
        (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
        {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
        (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
      (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

    have topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
        {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
        G.Adj u v := by
      obtain ⟨hl, ho, hb⟩ := topData ha
      exact (graphFun_pair G u v).mp
        (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

    have acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
        ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
      have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
        congrFun hL.2.1 x
      obtain ⟨a, hl, ho, hr, hv⟩ :=
        edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
          hout u v ((graphFun_pair G u v).mpr hadj)
      have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
      have hb : BelowF G C a := fun x hx =>
        below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl, hand, hb⟩, hv⟩

    have operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
        (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
        {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
        (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
          ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
            gateVal n C j (pairInput u v) = true := by
      rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
      · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
      · have hr' := reach_orReaches hr j rfl hj
        exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
          ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

    have andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
        orIn n C (n + j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      dsimp only [orIn] at hv
      simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases hv with he | ⟨k, _, hr, ho, _⟩
      · have := v.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
        · subst k
          rw [hj] at ho
          cases ho
        · rw [hj] at hof
          cases hof

    have lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
        w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
          Relation.ReflTransGen (OrStep n C) w (n + m) := by
      rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
      · exact .inl eq.symm
      · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
        exact .inr ⟨m, hm, ho, hi, hb, hz⟩

    have lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
        (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
        (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
        m ∈ orN G C \ lam G C := by
      obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
      have hNotBelow : ¬ BelowF G C m := by
        intro h
        have hvm : gateVal n C m x = true := (val_or (n := n) (by simp (config := {congrConsts := false})) hm ho).mpr
          ⟨n + j, hi, hb, hjx⟩
        exact Bool.noConfusion (hx.symm.trans (h x hvm))
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, ho, hNotBelow⟩
      · intro hl
        obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
        obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
        have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
          fin_cases b
          · exact h0
          · exact h1
        rw [← be, andRawEmpty hjop] at hnonempty
        exact Finset.not_nonempty_empty hnonempty

    have residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
        (he : s(u,v) ∈ Ustar G C) :
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
          gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
      obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
      have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
      obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
      obtain ⟨hl, ho, _⟩ := topData ha
      have h := (andValOperands hL.1 hl ho _).mp hv
      rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
      · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
        · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
          apply (miss ?_).elim
          dsimp only [starEdges]
          refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
            ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
          rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
      · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩

    have opposite (b c : Fin 2) : c = b ∨ c = 1 - b := by
      revert b c
      decide

    have topSides (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
        (b : Fin 2) : (side (n := n) C a b).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hc : a ∈ centreless G C := by
        apply Finset.mem_filter.mpr
        refine ⟨ha, ?_⟩
        fin_cases b
        · exact Or.inl he
        · exact Or.inr he
      rw [empty] at hc
      exact Finset.notMem_empty _ hc

    have orData {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
        m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
      obtain ⟨hr, ho, hb⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1
      exact ⟨Finset.mem_range.mp hr, ho, hb⟩

    have emptyInputOutside (ao : IsAO2 n C) {j m : ℕ}
        (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
        (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
        (hin : n + j ∈ (gateAt C m).inputs) :
        m ∈ orN G C \ lam G C := by
      have hbad : ¬ BelowF G C m := by
        intro hb
        apply dirty
        intro x hx
        exact hb x ((val_or (n := n) (by simp (config := {congrConsts := false})) hm hop).mpr
          ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hop, hbad⟩
      · intro hl
        obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
        obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
        have hne : (orIn n C (opnd C m b)).Nonempty := by
          fin_cases b
          · exact h0
          · exact h1
        rw [← hb, empty] at hne
        exact Finset.not_nonempty_empty hne

    have residualPath (ao : IsAO2 n C) (empty : centreless G C = ∅)
        {a j : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hj : j ∈ junk G C)
        (path : OrReaches n C (opnd C a b) j) :
        ∃ m ∈ orN G C \ lam G C, n + j ∈ (gateAt C m).inputs ∧
          Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) := by
      rcases lastOrBefore (orReaches_reach j _ path).1 with he | ⟨m, hm, hop, hin, hlt, hp⟩
      · have hne := topSides empty ha b
        change (orIn n C (opnd C a b)).Nonempty at hne
        rw [he, andRawEmpty (junkData hj).2.1] at hne
        exact (Finset.not_nonempty_empty hne).elim
      · exact ⟨m, lastOrOutside ao hj hm hop hin hlt, hin, hp⟩

    have mixingRaw (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
        (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
        (ha : a ∈ tops G C) (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
        (orIn n C (n + m)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hz
      rcases lastOrBefore path with he | ⟨k, hk, hop, hin, hlt, _⟩
      · have hne := topSides empty ha b
        change (orIn n C (opnd C a b)).Nonempty at hne
        rw [he, hz] at hne
        exact Finset.not_nonempty_empty hne
      · have hk' := emptyInputOutside ao (orData hm).2.2 hz hk hop hin
        rw [only, Finset.mem_singleton] at hk'
        omega

    have singleJunkInput (ao : IsAO2 n C) {m j k : ℕ}
        (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
        (hj : j ∈ junk G C) (hk : k ∈ junk G C)
        (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
        j = k := by
      by_contra hjk
      obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
      have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
        intro w hw
        simp (config := {congrConsts := false}) only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
        omega
      obtain ⟨t, ht⟩ := hne
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
      · have := t.isLt
        omega
      · obtain ⟨l, _, he, _, hin, _⟩ := hs
        have hl : l = m := by omega
        subst l
        have ht' := reach_mem_orIn t hrest
        rcases hinputs w hin with rfl | rfl
        · rw [andRawEmpty (junkData hj).2.1] at ht'
          exact Finset.notMem_empty _ ht'
        · rw [andRawEmpty (junkData hk).2.1] at ht'
          exact Finset.notMem_empty _ ht'

    have cleanAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
        {t w : Fin n} (ht : t ∈ side C a b) (hw : w ∈ side C a (1 - b)) :
        (G.deleteEdges ↑(Ustar G C)).Adj t w := by
      have cross {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
          (G.deleteEdges ↑(Ustar G C)).Adj u v := by
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨topAdj ao ha hu hv, ?_⟩
        intro he
        apply (Finset.mem_sdiff.mp (show s(u, v) ∈ Ustar G C from he)).2
        exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
      fin_cases b
      · exact cross ht hw
      · exact (cross hw ht).symm

    have firingTop (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
        (ha : a ∈ tops G C)
        (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
        (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
        (hmx : gateVal n C m x = true) (hwx : x w = true) :
        graphFun G ∅ x = true := by
      obtain ⟨haLen, haOp, haBelow⟩ := topData ha
      apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
      intro c
      rcases opposite b c with rfl | rfl
      · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) path hmx
      · exact sideVal hw hwx

    have oppositeEndpoint (least : IsLeastAO G C) (top : TopForm G C)
        (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2} {u v : Fin n}
        (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
        (ha : a ∈ tops G C) (hv : gateVal n C a (pairInput u v) = true)
        (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
        ∃ w ∈ side C a (1 - b), w = u ∨ w = v := by
      obtain ⟨al, aop, ab⟩ := topData ha
      have hv' := (andValOperands least.1 al aop _).mp hv (1 - b)
      rcases operandSupport least.1 top al aop hv' with h | ⟨j, hj, hr, _⟩
      · exact h
      · obtain ⟨k, hk, _, hp⟩ := residualPath least.1 empty ha hj hr
        rw [only, Finset.mem_singleton] at hk
        subst k
        exfalso
        apply (orData hm).2.2
        intro x hx
        apply ab x ((andValOperands least.1 al aop x).mpr ?_)
        intro c
        rcases opposite b c with rfl | rfl
        · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) path hx
        · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) hp hx

    have rawCoverShape (ao : IsAO2 n C) {m w : ℕ}
        (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
        (hw : w < n + m) :
        (orIn n C w).card ≤ 1 ∨
          ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
      by_cases hcard : (orIn n C w).card ≤ 1
      · exact Or.inl hcard
      have hne : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, hu⟩ := hne
      by_cases hi : w < n
      · exfalso
        apply hcard
        apply Finset.card_le_one.mpr
        intro t ht v hv
        have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
          rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
          · exact he.symm
          · obtain ⟨k, _, he, _, _, _⟩ := hs
            omega
        exact Fin.ext ((eq t ht).trans (eq v hv).symm)
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkm : k < m := by omega
      have hkl := hkm.trans (orData hm).1
      have hko : (gateAt C k).op = GateOp.or := by
        rcases ao.1 _ (gateAt_mem hkl) with h | h
        · rw [andRawEmpty h] at hu
          exact (Finset.notMem_empty _ hu).elim
        · exact h
      have hbelow : ¬ BelowF G C k := by
        intro hb
        have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
        exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
      have hkN : k ∈ orN G C := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hko, hbelow⟩
      have hkL : k ∈ lam G C := by
        by_contra hn
        have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
        rw [only, Finset.mem_singleton] at hk
        omega
      obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
      exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
        (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

    have falseJunkCover (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
        (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
        (x : Fin n → Bool) :
        ∀ j < m, j ∈ junk G C →
          (∀ u v : Fin n, s(u, v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) →
          gateVal n C j x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
            (∀ u v : Fin n, s(u, v) ∈ Ustar G C → u ∈ S ∨ v ∈ S) ∧
            ∀ t ∈ S, x t = false := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjm hj fires hx
        obtain ⟨jl, jo, _⟩ := junkData hj
        have hfalse : ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
          by_contra hn
          have hv := (andValOperands ao jl jo x).mpr
            (fun b => by
              cases hval : val C (List.ofFn x) (opnd C j b) with
              | true => rfl
              | false => exact (hn ⟨b, hval⟩).elim)
          exact Bool.false_ne_true (hx.symm.trans hv)
        obtain ⟨b, hb⟩ := hfalse
        have firesOp (u v : Fin n) (he : s(u, v) ∈ Ustar G C) :
            val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
          (andValOperands ao jl jo _).mp (fires u v he) b
        have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
            opnd C j b = n + k := by
          rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
          · exact h
          · have hr' := lastOrOutside ao hk rl ro ri rb
            rw [only, Finset.mem_singleton] at hr'
            have hle := orStep_le rp
            have hlt := opndBound ao jl b
            omega
        by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
        · obtain ⟨k, hk, he⟩ := hd
          have hbnd := opndBound ao jl b
          have hkj : k < j := by omega
          apply ih k hkj (hkj.trans hjm) hk
          · intro u v hu
            have hv := firesOp u v hu
            rw [he] at hv
            exact hv
          · rw [he] at hb
            exact hb
        · refine ⟨orIn n C (opnd C j b), rawCoverShape ao only hm (by
            have := opndBound ao jl b
            omega), ?_, ?_⟩
          · intro u v he
            rcases operandSupport ao top jl jo (firesOp u v he) with ⟨t, ht, rfl | rfl⟩ | ⟨k, hk, hr, _⟩
            · exact Or.inl ht
            · exact Or.inr ht
            · exact (hd ⟨k, hk, direct k hk hr⟩).elim
          · intro t ht
            apply Bool.eq_false_iff.mpr
            intro ht'
            exact Bool.false_ne_true (hb.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) ht'))

    have finish (least : IsLeastAO G C) (top : TopForm G C)
        (empty : centreless G C = ∅)
        (outsideAtMostOne : (orN G C \ lam G C).card ≤ 1)
        (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
        (orN G C \ lam G C).card = 1 ∧
        ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
          ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
            ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
              ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
                ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
                (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
                ∀ y ∈ S, x y = false := by
      obtain ⟨u, v, he⟩ := nonempty
      obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace least top he
      obtain ⟨m, hm, hin, path⟩ := residualPath least.1 empty ha hj hr
      have hpos := Finset.card_pos.mpr ⟨m, hm⟩
      have only : orN G C \ lam G C = {m} := by
        ext k
        rw [Finset.mem_singleton]
        exact ⟨fun hk => Finset.card_le_one.mp (by omega) k hk m hm, fun h => h.symm ▸ hm⟩
      obtain ⟨t, ht⟩ := mixingRaw least.1 empty only hm ha path
      refine ⟨by omega, t, ?_⟩
      have hml := (orData hm).1
      have hmo := (orData hm).2.1
      have hlt := least.1.2.1 m hml _ hin
      have uniform (p q : Fin n) (hpq : s(p, q) ∈ Ustar G C) :
          gateVal n C j (pairInput p q) = true := by
        obtain ⟨a', ha', b', k, hk, _, hr', hv⟩ := residualTrace least top hpq
        obtain ⟨l, hl, hkin, _⟩ := residualPath least.1 empty ha' hk hr'
        rw [only, Finset.mem_singleton] at hl
        subst l
        have heq := singleJunkInput least.1 hm ⟨t, ht⟩ hj hk hin hkin
        rwa [heq]
      intro p q hpq
      obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace least top hpq
      obtain ⟨l, hl, _, hp⟩ := residualPath least.1 empty ha' hk hr'
      rw [only, Finset.mem_singleton] at hl
      subst l
      obtain ⟨w, hw, hend⟩ := oppositeEndpoint least top empty only hm ha' hav hp
      have ht' : t ∈ side C a' b' :=
        reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
      refine ⟨w, hend, cleanAdj least.1 ha' b' ht' hw, ?_⟩
      intro x hx hf
      have hjx : gateVal n C j x = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have hmx : gateVal n C m x = true :=
          (val_or (n := n) (by simp (config := {congrConsts := false})) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
        exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
      exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx
    have directJunk (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
        {j w : ℕ} (hj : j ∈ junk G C) (hr : OrReaches n C w j) : w = n + j := by
      rcases lastOrBefore (orReaches_reach j _ hr).1 with eq | ⟨m, hm, ho, hi, hb, _⟩
      · exact eq
      · have bad := lastOrOutside ao hj hm ho hi hb
        rw [none] at bad
        exact (Finset.notMem_empty _ bad).elim

    have admissibleRaw (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
        {w : ℕ} (hw : w < n + C.gates.length) :
        (orIn n C w).card ≤ 1 ∨
          ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
      by_cases hcard : (orIn n C w).card ≤ 1
      · exact Or.inl hcard
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C w).card)
      by_cases hi : w < n
      · exfalso
        apply hcard
        apply Finset.card_le_one.mpr
        intro t ht v hv
        have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
          rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
          · exact he.symm
          · obtain ⟨k, _, he, _, _, _⟩ := hs
            omega
        exact Fin.ext ((eq t ht).trans (eq v hv).symm)
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkl : k < C.gates.length := by omega
      have hko : (gateAt C k).op = GateOp.or := by
        rcases ao.1 _ (gateAt_mem hkl) with h | h
        · rw [andRawEmpty h] at hu
          exact (Finset.notMem_empty _ hu).elim
        · exact h
      have hbelow : ¬ BelowF G C k := by
        intro hb
        have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
        exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
      have hkN : k ∈ orN G C := by
        dsimp only [orN, gatesWhere]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hko, hbelow⟩
      have hkL : k ∈ lam G C := by
        by_contra hn
        have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
        rw [none] at hk
        exact Finset.notMem_empty _ hk
      obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
      exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
        (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

    have falseClause (ao : IsAO2 n C) (top : TopForm G C)
        (none : orN G C \ lam G C = ∅) (x : Fin n → Bool) :
        ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → gateVal n C a x = false →
          ∃ S : Finset (Fin n),
            (S.card ≤ 1 ∨ ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ y ∈ S, x y = false) ∧
            (∀ u v : Fin n, gateVal n C a (pairInput u v) = true → u ∈ S ∨ v ∈ S) := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        intro ha op hfalse
        have hex : ∃ b : Fin 2, val C (List.ofFn x) (opnd C a b) = false := by
          by_contra h
          have both : ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
            intro b
            cases he : val C (List.ofFn x) (opnd C a b) with
            | false => exact (h ⟨b, he⟩).elim
            | true => rfl
          exact Bool.false_ne_true (hfalse.symm.trans ((andValOperands ao ha op x).mpr both))
        obtain ⟨b, hb⟩ := hex
        have hwire := opndBound ao ha b
        have fires (u v : Fin n) (hv : gateVal n C a (pairInput u v) = true) :
            val C (List.ofFn (pairInput u v)) (opnd C a b) = true :=
          (andValOperands ao ha op _).mp hv b
        by_cases hJ : ∃ j ∈ junk G C, opnd C a b = n + j
        · obtain ⟨j, hj, eq⟩ := hJ
          obtain ⟨hl, hop, _⟩ := junkData hj
          have hlt : j < a := by omega
          have hjfalse : gateVal n C j x = false := by
            rw [eq] at hb
            exact hb
          obtain ⟨S, shape, hS, applies⟩ := ih j hlt hl hop hjfalse
          refine ⟨S, shape, hS, ?_⟩
          intro u v huv
          have hv := fires u v huv
          rw [eq] at hv
          exact applies u v hv
        · refine ⟨orIn n C (opnd C a b), admissibleRaw ao none (by omega), ?_, ?_⟩
          · intro y hy
            apply Bool.eq_false_iff.mpr
            intro yy
            have hv := reach_var_val x _ y (mem_orIn_reach y hy) yy
            exact Bool.false_ne_true (hb.symm.trans hv)
          · intro u v hv
            rcases operandSupport ao top ha op (b := b) (fires u v hv) with
              ⟨y, hy, rfl | rfl⟩ | ⟨j, hj, hr, _⟩
            · exact Or.inl hy
            · exact Or.inr hy
            · exact (hJ ⟨j, hj, directJunk ao none hj hr⟩).elim
    refine ⟨finish least top, ?_⟩
    intro none
    constructor
    · intro u v huv
      obtain ⟨a, ha, b, j, hj, hv, hr, _⟩ := residualTrace least top huv
      have hside : side (n := n) C a b = ∅ := by
        change orIn n C (opnd C a b) = ∅
        rw [directJunk least.1 none hj hr, andRawEmpty (junkData hj).2.1]
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, hv⟩
      fin_cases b
      · exact Or.inl hside
      · exact Or.inr hside
    · intro a ha x hx
      have ht : a ∈ tops G C := (Finset.mem_filter.mp ha).1
      obtain ⟨hl, ho, hbelow⟩ := topData ht
      have hfalse : gateVal n C a x = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact Bool.false_ne_true (hx.symm.trans (hbelow _ htrue))
      exact falseClause least.1 top none x a hl ho hfalse

  have finite : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ U : Finset (Sym2 (Fin 11)), U ⊆ G.edgeFinset → 2 ≤ U.card →
    let H := G.deleteEdges (↑U)
    (∃ q : Fin 11, ∀ u v : Fin 11, s(u,v) ∈ U → ∃ w : Fin 11, (w=u ∨ w=v) ∧ H.Adj q w ∧
        ∀ x : Fin 11 → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset (Fin 11), (S.card ≤ 1 ∨ ∃ c, ∀ z ∈ S, H.Adj z c) ∧
        (∀ i j : Fin 11, s(i,j) ∈ U → i ∈ S ∨ j ∈ S) ∧ ∀ z ∈ S, x z = false) →
    U.card = 2 ∧ ∃ K X : Finset (Fin 11), IsMinCover H K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ 3-U.card := by
    let V := Fin 11
    let I := Fin 16

    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

    let ends : I → V × V := ![(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

    let edge (i : I) : Sym2 V := s((ends i).1, (ends i).2)

    let pair (i j : I) : Finset (Sym2 V) := {edge i, edge j}

    let drop (D : Finset (Sym2 V)) := G.deleteEdges ↑D

    let Premise (D : Finset (Sym2 V)) : Prop :=
      ∃ c : V, ∀ u v : V, s(u, v) ∈ D →
        ∃ w : V, (w = u ∨ w = v) ∧ (drop D).Adj c w ∧
          ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
            ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop D).Adj t z) ∧
              (∀ a b : V, s(a, b) ∈ D → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false

    have premise_mono {D F : Finset (Sym2 V)} (hsub : D ⊆ F) (h : Premise F) :
        Premise D := by
      have adj {u v : V} (h : (drop F).Adj u v) : (drop D).Adj u v := by
        obtain ⟨ha, hm⟩ := SimpleGraph.deleteEdges_adj.mp h
        exact SimpleGraph.deleteEdges_adj.mpr ⟨ha, fun hd => hm (hsub hd)⟩
      obtain ⟨c, hc⟩ := h
      refine ⟨c, fun u v hmem => ?_⟩
      obtain ⟨w, hw, ha, hx⟩ := hc u v (hsub hmem)
      refine ⟨w, hw, adj ha, fun x hwx hG => ?_⟩
      obtain ⟨S, hs, hcover, hfalse⟩ := hx x hwx hG
      refine ⟨S, ?_, fun a b hab => hcover a b (hsub hab), hfalse⟩
      rcases hs with hs | ⟨z, hz⟩
      · exact Or.inl hs
      · exact Or.inr ⟨z, fun t ht => adj (hz t ht)⟩

    let neighborMask : V → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

    let adjacent (u v : V) : Bool := (neighborMask u).testBit v.val

    have adj_iff (u v : V) : G.Adj u v ↔ adjacent u v = true := by
      revert u v
      decide

    let between (i : I) (u v : V) : Bool :=
      (u == (ends i).1 && v == (ends i).2) || (u == (ends i).2 && v == (ends i).1)

    have between_iff (i : I) (u v : V) : between i u v = true ↔ s(u, v) = edge i := by
      simp (config := {congrConsts := false}) only [edge, Sym2.eq_iff]
      simp (config := {congrConsts := false}) [between]

    have index_exists : ∀ u v : V, adjacent u v = true → ∃ i : I, between i u v = true := by
      decide

    have edge_index {a : Sym2 V} (h : a ∈ G.edgeFinset) : ∃ i : I, a = edge i := by
      revert h
      induction a using Sym2.ind with
      | _ u v =>
        intro h
        obtain ⟨i, hi⟩ := index_exists u v ((adj_iff u v).mp (show G.Adj u v from SimpleGraph.mem_edgeFinset.mp h))
        exact ⟨i, (between_iff i u v).mp hi⟩

    let near (i j : I) (u v : V) : Bool :=
      adjacent u v && !between i u v && !between j u v

    have near_iff (i j : I) (u v : V) : near i j u v = true ↔ (drop (pair i j)).Adj u v := by
      simp (config := {congrConsts := false}) [near, drop, pair, SimpleGraph.deleteEdges_adj, adj_iff, ← between_iff, and_assoc]

    let hit (k : I) (f : V → Bool) : Bool := f (ends k).1 || f (ends k).2

    let hits (i j : I) (f : V → Bool) : Bool := hit i f && hit j f

    have hits_of_cover {i j : I} {S : Finset V} {f : V → Bool}
        (hcover : ∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S)
        (hf : ∀ t ∈ S, f t = true) : hits i j f = true := by
      have one (k : I) (hk : edge k ∈ pair i j) : hit k f = true := by
        rcases hcover (ends k).1 (ends k).2 hk with h | h
        · simp (config := {congrConsts := false}) [hit, hf _ h]
        · simp (config := {congrConsts := false}) [hit, hf _ h]
      simp (config := {congrConsts := false}) [hits, one i (by simp (config := {congrConsts := false}) [pair]), one j (by simp (config := {congrConsts := false}) [pair])]

    let extraTable : List (List ℕ) := [
      [0, 0, 343598039040, 0, 206158430214, 0, 481204109312, 0, 343597383689],
      [0, 0, 0, 9942849290240, 0, 0, 0, 8799045812224],
      [0, 0, 0, 0, 5636096],
      [0, 0, 0, 0, 0, 9942849290240],
      [0, 0, 0, 0, 0, 0, 0, 0, 5245184, 0, 0, 0, 7342080],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11751030521856],
      [],
      [],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30065295360],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9895605043200, 0, 0, 0, 11751030521856, 9895605305344],
      [],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11751030521856],
      [],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8796260794368, 11751030521856],
      [],
      []
    ]
    let extra (i j : I) (w : V) : V :=
      let packed := (extraTable.getD i.val []).getD j.val 0
      let entry := (packed >>> (4 * w.val)) &&& 15
      if entry = 0 then w else Fin.ofNat 11 (entry - 1)

    let probe (i j : I) (w t : V) : Bool := t == w || t == extra i j w

    let vertexMask (u : V) : ℕ := 2 ^ u.val

    have vertex_bit (u v : V) : (vertexMask u).testBit v.val = (u == v) := by
      apply Bool.eq_iff_iff.mpr
      simp (config := {congrConsts := false}) [vertexMask, Nat.testBit_two_pow, Fin.ext_iff]
      exact ⟨Fin.ext, congrArg Fin.val⟩

    have conditional_bit (b : Bool) (m k : ℕ) :
        (if b then m else 0).testBit k = (b && m.testBit k) := by
      cases b <;> simp (config := {congrConsts := false})

    let removedAt (k : I) (u : V) : ℕ :=
      (if u == (ends k).1 then vertexMask (ends k).2 else 0) |||
      (if u == (ends k).2 then vertexMask (ends k).1 else 0)

    have removed_bit (k : I) (u v : V) : (removedAt k u).testBit v.val = between k u v := by
      simp (config := {congrConsts := false}) only [removedAt, Nat.testBit_or, conditional_bit, vertex_bit, between]
      have swap (a b : V) : (a == b) = (b == a) := by
        apply Bool.eq_iff_iff.mpr
        simpa (config := {congrConsts := false}) using (eq_comm : a = b ↔ b = a)
      rw [swap (ends k).2 v, swap (ends k).1 v]

    let neighbors (i j : I) (u : V) : ℕ :=
      neighborMask u &&& (2047 ^^^ (removedAt i u ||| removedAt j u))

    have neighbor_bit (i j : I) (u v : V) : (neighbors i j u).testBit v.val = near i j u v := by
      have hall : (2047 : ℕ).testBit v.val = true := by
        change (2^11 - 1 : ℕ).testBit v.val = true
        exact (Nat.testBit_two_pow_sub_one 11 v.val).trans (decide_eq_true v.isLt)
      simp (config := {congrConsts := false}) only [neighbors, near, adjacent]
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, removed_bit, removed_bit, hall]
      cases between i u v <;> cases between j u v <;> simp (config := {congrConsts := false})

    let reachMask (k : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
      (if f (ends k).1 then m (ends k).1 else 0) |||
      (if f (ends k).2 then m (ends k).2 else 0)

    let meetMask (i j : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
      reachMask i f m &&& reachMask j f m

    have meet_bit (i j : I) (f : V → Bool) (m : V → ℕ) (c : V) :
        (meetMask i j f m).testBit c.val = hits i j (fun t => f t && (m t).testBit c.val) := by
      simp (config := {congrConsts := false}) [meetMask, reachMask, conditional_bit, hits, hit]

    let failed (i j : I) (w : V) : Bool :=
      let available := fun t => !probe i j w t
      !adjacent w (extra i j w) &&
        (meetMask i j available vertexMask == 0) &&
        (meetMask i j available (neighbors i j) == 0)

    have probe_false {i j : I} {w : V} (h : adjacent w (extra i j w) = false) :
        graphFun G ∅ (probe i j w) = false := by
      dsimp only [graphFun]
      simp (config := {congrConsts := false}) only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_false_iff_not]
      rintro ⟨u, v, ha, hu, hv⟩
      have hu' : u = w ∨ u = extra i j w := by simpa (config := {congrConsts := false}) [probe] using hu
      have hv' : v = w ∨ v = extra i j w := by simpa (config := {congrConsts := false}) [probe] using hv
      have nh : ¬ G.Adj w (extra i j w) := by simp (config := {congrConsts := false}) [adj_iff, h]
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at ha
      · exact G.irrefl ha
      · exact nh ha
      · exact nh ha.symm
      · exact G.irrefl ha

    have failed_blocks {i j : I} {w : V} (h : failed i j w = true)
        (hw : ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
            ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop (pair i j)).Adj t z) ∧
              (∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false) :
        False := by
      simp (config := {congrConsts := false}) only [failed, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
      obtain ⟨⟨hind, hsingle⟩, hstandard⟩ := h
      let x := probe i j w
      obtain ⟨S, hs, hcover, hfalse⟩ := hw x (by simp (config := {congrConsts := false}) [x, probe]) (probe_false hind)
      have blocked (c : V) (m : V → ℕ) (hm : meetMask i j (fun t => !x t) m = 0)
          (hf : ∀ t ∈ S, (!x t && (m t).testBit c.val) = true) : False := by
        have hb := meet_bit i j (fun t => !x t) m c
        rw [hm, hits_of_cover hcover hf] at hb
        exact Bool.false_ne_true (by simpa (config := {congrConsts := false}) only [Nat.zero_testBit] using hb)
      rcases hs with hs | ⟨c, hc⟩
      · have hmem := hcover (ends i).1 (ends i).2 (by change edge i ∈ pair i j; simp (config := {congrConsts := false}) [pair])
        have hne : S.Nonempty := hmem.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
        obtain ⟨c, hc⟩ := hne
        refine blocked c vertexMask hsingle fun t ht => ?_
        simp (config := {congrConsts := false}) [vertex_bit, Finset.card_le_one.mp hs t ht c hc, hfalse c hc]
      · refine blocked c (neighbors i j) hstandard fun t ht => ?_
        simp (config := {congrConsts := false}) [neighbor_bit, (near_iff i j t c).mpr (hc t ht), hfalse t ht]

    let allowed (i j : I) : Bool :=
      (i == 1 && j == 10) || (i == 2 && j == 11) ||
      (i == 5 && j == 15) || (i == 9 && j == 11)

    have pair_certificate : ∀ i j : I, i < j →
        allowed i j = true ∨ meetMask i j (fun w => !failed i j w) (neighbors i j) = 0 := by
      decide

    have pair_allowed {i j : I} (hlt : i < j) (h : Premise (pair i j)) : allowed i j = true := by
      obtain ⟨c, hc⟩ := h
      have one (k : I) (hk : edge k ∈ pair i j) :
          hit k (fun w => !failed i j w && (neighbors i j w).testBit c.val) = true := by
        obtain ⟨w, hw, hcw, hx⟩ := hc (ends k).1 (ends k).2 hk
        have hfail : failed i j w = false := Bool.eq_false_iff.mpr fun hf => failed_blocks hf hx
        have hadj := (near_iff i j w c).mpr hcw.symm
        rcases hw with rfl | rfl <;> simp (config := {congrConsts := false}) [hit, neighbor_bit, hadj, hfail]
      rcases pair_certificate i j hlt with ha | hbad
      · exact ha
      · have hb := meet_bit i j (fun w => !failed i j w) (neighbors i j) c
        rw [hbad] at hb
        simp (config := {congrConsts := false}) [hits, one i (by simp (config := {congrConsts := false}) [pair]), one j (by simp (config := {congrConsts := false}) [pair])] at hb

    let allowedEither (i j : I) : Bool := allowed i j || allowed j i

    have subpair_allowed {D : Finset (Sym2 V)} (h : Premise D) {i j : I}
        (hi : edge i ∈ D) (hj : edge j ∈ D) (hij : i ≠ j) : allowedEither i j = true := by
      have hs (p q : I) (hp : edge p ∈ D) (hq : edge q ∈ D) : pair p q ⊆ D := by
        intro z hz
        simp (config := {congrConsts := false}) only [pair, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · simp (config := {congrConsts := false}) [allowedEither, pair_allowed hlt (premise_mono (hs i j hi hj) h)]
      · simp (config := {congrConsts := false}) [allowedEither, pair_allowed hgt (premise_mono (hs j i hj hi) h)]

    have no_triple : ∀ i j k : I, allowedEither i j = true → allowedEither i k = true →
        allowedEither j k = false := by
      decide

    have allowed_cases {i j : I} (h : allowed i j = true) :
        (i = 1 ∧ j = 10) ∨ (i = 2 ∧ j = 11) ∨ (i = 5 ∧ j = 15) ∨ (i = 9 ∧ j = 11) := by
      simpa (config := {congrConsts := false}) [allowed, or_assoc] using h

    have edge_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
        {a b : V} (hab : K.Adj a b) : 1 ≤ (T ∩ {a, b}).card := by
      apply Finset.card_pos.mpr
      rcases hT hab with ha | hb
      · exact ⟨a, Finset.mem_inter.mpr ⟨ha, by simp (config := {congrConsts := false})⟩⟩
      · exact ⟨b, Finset.mem_inter.mpr ⟨hb, by simp (config := {congrConsts := false})⟩⟩

    have triangle_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
        {a b c : V} (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c) :
        2 ≤ (T ∩ {a, b, c}).card := by
      have two (u v : V) (huv : u ≠ v) (hu : u ∈ T) (hv : v ∈ T)
          (hu' : u ∈ ({a, b, c} : Finset V)) (hv' : v ∈ ({a, b, c} : Finset V)) :
          2 ≤ (T ∩ {a, b, c}).card := by
        rw [← Finset.card_pair huv]
        apply Finset.card_le_card
        intro z hz
        simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu, hu'⟩
        · exact Finset.mem_inter.mpr ⟨hv, hv'⟩
      rcases hT hab with ha | hb
      · rcases hT hbc with hb | hc
        · exact two a b hab.ne ha hb (by simp (config := {congrConsts := false})) (by simp (config := {congrConsts := false}))
        · exact two a c hac.ne ha hc (by simp (config := {congrConsts := false})) (by simp (config := {congrConsts := false}))
      · rcases hT hac with ha | hc
        · exact two a b hab.ne ha hb (by simp (config := {congrConsts := false})) (by simp (config := {congrConsts := false}))
        · exact two b c hbc.ne hb hc (by simp (config := {congrConsts := false})) (by simp (config := {congrConsts := false}))

    have add_lower {T A B : Finset V} {a b : ℕ} (hd : Disjoint A B)
        (ha : a ≤ (T ∩ A).card) (hb : b ≤ (T ∩ B).card) :
        a + b ≤ (T ∩ (A ∪ B)).card := by
      rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]
      exact Nat.add_le_add ha hb

    let packingA : List (V × V) := [(0, 9), (1, 8), (2, 5), (3, 6), (3, 7), (6, 7), (4, 10)]

    let packingB : List (V × V) := [(0, 9), (1, 4), (1, 8), (4, 8), (2, 10), (3, 6), (3, 7), (6, 7)]

    have lowerA {i j : I}
        (hp : packingA.all (fun p => near i j p.1 p.2) = true)
        {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
      have adj (u v : V) (hm : (u, v) ∈ packingA) : (drop (pair i j)).Adj u v :=
        (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
      have h1 := edge_lower hT (adj 0 9 (by decide))
      have h2 := edge_lower hT (adj 1 8 (by decide))
      have h3 := edge_lower hT (adj 2 5 (by decide))
      have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
      have h5 := edge_lower hT (adj 4 10 (by decide))
      have h12 := add_lower (by decide) h1 h2
      have h123 := add_lower (by decide) h12 h3
      have h1234 := add_lower (by decide) h123 h4
      have h12345 := add_lower (by decide) h1234 h5
      exact h12345.trans (Finset.card_le_card Finset.inter_subset_left)

    have lowerB {i j : I}
        (hp : packingB.all (fun p => near i j p.1 p.2) = true)
        {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
      have adj (u v : V) (hm : (u, v) ∈ packingB) : (drop (pair i j)).Adj u v :=
        (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
      have h1 := edge_lower hT (adj 0 9 (by decide))
      have h2 := triangle_lower hT (adj 1 4 (by decide)) (adj 1 8 (by decide)) (adj 4 8 (by decide))
      have h3 := edge_lower hT (adj 2 10 (by decide))
      have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
      have h12 := add_lower (by decide) h1 h2
      have h123 := add_lower (by decide) h12 h3
      have h1234 := add_lower (by decide) h123 h4
      exact h1234.trans (Finset.card_le_card Finset.inter_subset_left)

    have witness {i j : I} (S : Finset V) (z : V) (hc : S.card = 6)
        (hS : ∀ u v : V, near i j u v = true → u ∈ S ∨ v ∈ S)
        (hG : ∀ u v : V, adjacent u v = true → u ∈ (S ∪ {z}) ∨ v ∈ (S ∪ {z}))
        (hl : ∀ T : Finset V, (drop (pair i j)).IsVertexCover ↑T → 6 ≤ T.card) :
        ∃ T E : Finset V, IsMinCover (drop (pair i j)) T ∧ G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 1 := by
      refine ⟨S, {z}, ⟨?_, ?_⟩, ?_, by simp (config := {congrConsts := false})⟩
      · intro u v h
        exact hS u v ((near_iff i j u v).mpr h)
      · intro T hT
        rw [hc]
        exact hl T hT
      · intro u v h
        exact hG u v ((adj_iff u v).mp h)

    have solve_pair {i j : I} (ha : allowed i j = true) :
        ∃ T E : Finset V, IsMinCover (drop (pair i j)) T ∧ G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 1 := by
      rcases allowed_cases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact witness {2, 3, 4, 6, 8, 9} 0 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
      · exact witness {0, 2, 4, 6, 7, 8} 5 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
      · exact witness {0, 4, 5, 6, 7, 8} 2 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
      · exact witness {0, 2, 4, 6, 7, 8} 5 (by decide) (by decide) (by decide) (fun _ => lowerB (by decide))

    have solve (D : Finset (Sym2 V)) (hsub : D ⊆ G.edgeFinset)
        (hlo : 2 ≤ D.card) (h : Premise D) :
        D.card = 2 ∧ ∃ T E : Finset V, IsMinCover (drop D) T ∧
          G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 3 - D.card := by
      have index (a : Sym2 V) (ha : a ∈ D) : ∃ i : I, a = edge i := edge_index (hsub ha)
      have hc : D.card = 2 := by
        by_contra hn
        obtain ⟨D', hD', hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ D.card by omega)
        have h' := premise_mono hD' h
        obtain ⟨a, b, c, hab, hac, hbc, hd⟩ := Finset.card_eq_three.mp hcard
        obtain ⟨i, rfl⟩ := index a (hD' (by simp (config := {congrConsts := false}) [hd]))
        obtain ⟨j, rfl⟩ := index b (hD' (by simp (config := {congrConsts := false}) [hd]))
        obtain ⟨k, rfl⟩ := index c (hD' (by simp (config := {congrConsts := false}) [hd]))
        have ij := subpair_allowed h' (i := i) (j := j) (by simp (config := {congrConsts := false}) [hd]) (by simp (config := {congrConsts := false}) [hd]) (fun e => hab (congrArg edge e))
        have ik := subpair_allowed h' (i := i) (j := k) (by simp (config := {congrConsts := false}) [hd]) (by simp (config := {congrConsts := false}) [hd]) (fun e => hac (congrArg edge e))
        have jk := subpair_allowed h' (i := j) (j := k) (by simp (config := {congrConsts := false}) [hd]) (by simp (config := {congrConsts := false}) [hd]) (fun e => hbc (congrArg edge e))
        rw [no_triple i j k ij ik] at jk
        cases jk
      refine ⟨hc, ?_⟩
      rw [hc]
      obtain ⟨a, b, hab, hd⟩ := Finset.card_eq_two.mp hc
      obtain ⟨i, rfl⟩ := index a (by simp (config := {congrConsts := false}) [hd])
      obtain ⟨j, rfl⟩ := index b (by simp (config := {congrConsts := false}) [hd])
      have hij : i ≠ j := fun e => hab (congrArg edge e)
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hd' : D = pair i j := hd
        rw [hd'] at h ⊢
        exact solve_pair (pair_allowed hlt h)
      · have hd' : D = pair j i := by
          rw [hd]
          simp (config := {congrConsts := false}) only [pair, Finset.pair_comm]
        rw [hd'] at h ⊢
        exact solve_pair (pair_allowed hgt h)
    intro _ D hsub hlo _ h
    exact solve D hsub hlo h

  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let blocks : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
  have noCharges (C : Circuit) (least : IsLeastAO G C) (top : TopForm G C)
      (two : 2 ≤ (junk G C).card) (none : orN G C \ lam G C = ∅) :
      2 * (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card := by
    have profile := (geometry 11 G C least top).2 none
    let Vertex := Fin 11
    let EIndex := Fin 16
    let Edge := Sym2 Vertex

    let adjacency (a b : Fin 11) : Bool :=
      ((#[1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85] : Array ℕ)[a.val]!).testBit b.val

    have adjacency_spec : ∀ a b : Fin 11, adjacency a b = true ↔ G.Adj a b := by decide

    let hits (ok : Fin 11 → Bool) : Sym2 (Fin 11) → Bool :=
      Sym2.lift ⟨fun u v => ok u || ok v, fun u v => Bool.or_comm (ok u) (ok v)⟩

    let covers (es : List (Sym2 (Fin 11))) (ok : Fin 11 → Bool) : Bool :=
      es.all (hits ok)

    let cleanNeighbor (es : List (Sym2 (Fin 11))) (a b : Fin 11) : Bool :=
      adjacency a b && !(decide (s(a, b) ∈ es))

    have cleanNeighbor_spec (es : List (Sym2 (Fin 11))) (a b : Fin 11) :
        cleanNeighbor es a b = true ↔ (G.deleteEdges ↑es.toFinset).Adj a b := by
      simp (config := {congrConsts := false}) [cleanNeighbor, adjacency_spec]

    let endpoints : EIndex → Vertex × Vertex :=
      ![(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

    let codedEdge (i : EIndex) : Edge := s((endpoints i).1, (endpoints i).2)

    have indexEdge : ∀ u v : Vertex, G.Adj u v → ∃ i : EIndex, codedEdge i = s(u, v) := by
      decide +kernel

    let negativeRow (k : Fin 24) (v : Vertex) : Bool :=
      (![15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
          k : ℕ).testBit v.val

    have negativeRow_ok : ∀ k : Fin 24, graphFun G ∅ (negativeRow k) = false := by
      decide +kernel

    let clausesAt (D : List Edge) (i j : EIndex) (k : Fin 24) : Bool :=
      let E := [codedEdge i, codedEdge j]
      (List.finRange 11).any (fun z => covers E (fun y => decide (y = z) && !(negativeRow k y))) ||
        (List.finRange 11).any (fun z => covers E (fun y => cleanNeighbor D y z && !(negativeRow k y)))

    let pairCheck (D : List EIndex) (i j : EIndex) : Bool :=
      (List.finRange 24).all (clausesAt (D.map codedEdge) i j)

    let allowedPairs : List (EIndex × EIndex) := [(1,10), (2,11), (5,15), (9,11)]

    have checkedPairs : ∀ i j : EIndex, i < j → pairCheck [i,j] i j = true → (i,j) ∈ allowedPairs := by
      decide +kernel

    have conflictingPairs :
        pairCheck [1,10,2,11] 1 10 = false ∧ pairCheck [1,10,5,15] 1 10 = false ∧
        pairCheck [1,10,9,11] 1 10 = false ∧ pairCheck [5,15,2,11] 5 15 = false ∧
        pairCheck [5,15,9,11] 5 15 = false := by
      decide +kernel

    have checkFromClauses (U : Finset Edge) (D : List EIndex) (i j : EIndex)
        (hD : ∀ d ∈ D, codedEdge d ∈ U)
        (hS : ∀ k : Fin 24, ∃ S : Finset Vertex,
          (S.card ≤ 1 ∨ ∃ z : Vertex, ∀ y ∈ S, (G.deleteEdges ↑U).Adj y z) ∧
          (∀ y ∈ S, negativeRow k y = false) ∧
          ((endpoints i).1 ∈ S ∨ (endpoints i).2 ∈ S) ∧
          ((endpoints j).1 ∈ S ∨ (endpoints j).2 ∈ S)) : pairCheck D i j = true := by
      apply List.all_eq_true.mpr
      intro k _
      obtain ⟨S, hs, hz, hi, hj⟩ := hS k
      have coverWith {p : Vertex → Bool} (hp : ∀ w ∈ S, p w = true) :
          covers [codedEdge i, codedEdge j] p = true := by
        have hhit {l : EIndex} (hl : (endpoints l).1 ∈ S ∨ (endpoints l).2 ∈ S) :
            hits p (codedEdge l) = true := by
          change (p (endpoints l).1 || p (endpoints l).2) = true
          exact Bool.or_eq_true_iff.mpr (hl.imp (hp _) (hp _))
        simp (config := {congrConsts := false}) [covers, hhit hi, hhit hj]
      change clausesAt (D.map codedEdge) i j k = true
      unfold clausesAt
      apply Bool.or_eq_true_iff.mpr
      rcases hs with hs | ⟨z, hns⟩
      · obtain ⟨z, hzS⟩ : S.Nonempty := by
          rcases hi with h | h
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
        left
        apply List.any_eq_true.mpr
        refine ⟨z, List.mem_finRange z, coverWith ?_⟩
        intro y hy
        simp (config := {congrConsts := false}) [Finset.card_le_one.mp hs y hy z hzS, hz z hzS]
      · right
        apply List.any_eq_true.mpr
        refine ⟨z, List.mem_finRange z, coverWith ?_⟩
        intro y hy
        have hclean : cleanNeighbor (D.map codedEdge) y z = true := by
          apply (cleanNeighbor_spec _ _ _).mpr
          obtain ⟨ha, hn⟩ := SimpleGraph.deleteEdges_adj.mp (hns y hy)
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨ha, ?_⟩
          intro h
          change s(y,z) ∈ (D.map codedEdge).toFinset at h
          obtain ⟨d, hd, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
          exact hn (eq ▸ hD d hd)
        simp (config := {congrConsts := false}) [hclean, hz y hy]
    classical
    let U := Ustar G C
    let Z := centreless G C
    let I : Finset EIndex := Finset.univ.filter (fun i => codedEdge i ∈ U)
    let A (a : ℕ) := I.filter (fun i =>
      gateVal 11 C a (pairInput (endpoints i).1 (endpoints i).2) = true)
    let occurs (i j : EIndex) := ∃ a ∈ Z, i ∈ A a ∧ j ∈ A a
    have memI (i : EIndex) : i ∈ I ↔ codedEdge i ∈ U := by simp (config := {congrConsts := false}) [I]
    have fires (a : ℕ) (i : EIndex) (hi : i ∈ A a) :
        gateVal 11 C a (pairInput (endpoints i).1 (endpoints i).2) = true :=
      (Finset.mem_filter.mp hi).2
    have edgeIn {i j : EIndex} (h : occurs i j) : codedEdge i ∈ U ∧ codedEdge j ∈ U := by
      obtain ⟨a, _, hi, hj⟩ := h
      exact ⟨(memI i).mp (Finset.mem_filter.mp hi).1, (memI j).mp (Finset.mem_filter.mp hj).1⟩
    have checker (D : List EIndex) (i j : EIndex)
        (hd : ∀ d ∈ D, codedEdge d ∈ U) (h : occurs i j) : pairCheck D i j = true := by
      apply checkFromClauses U D i j hd
      intro k
      obtain ⟨a, ha, hi, hj⟩ := h
      obtain ⟨S, hS, hr, hh⟩ := profile.2 a ha (negativeRow k) (negativeRow_ok k)
      exact ⟨S, hS, hr, hh _ _ (fires a i hi), hh _ _ (fires a j hj)⟩
    have allowed (i j : EIndex) (lt : i < j) (h : occurs i j) :
        (i = 1 ∧ j = 10) ∨ (i = 2 ∧ j = 11) ∨ (i = 5 ∧ j = 15) ∨ (i = 9 ∧ j = 11) := by
      have e := edgeIn h
      have check := checker [i,j] i j (by
        intro d hd
        simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact e.1
        · exact e.2) h
      simpa (config := {congrConsts := false}) [allowedPairs] using (checkedPairs i j lt check)
    have exclude (i j p q : EIndex) (h : occurs i j) (h' : occurs p q)
        (bad : pairCheck [i,j,p,q] i j = false) : False := by
      have e := edgeIn h
      have f := edgeIn h'
      have check := checker [i,j,p,q] i j (by
        intro d hd
        simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact e.1
        · exact e.2
        · exact f.1
        · exact f.2) h
      rw [bad] at check
      cases check
    obtain ⟨c, pairMeets⟩ : ∃ c : EIndex, ∀ i j : EIndex, i < j → occurs i j → i = c ∨ j = c := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := conflictingPairs
      by_cases hp : occurs 1 10
      · refine ⟨1, ?_⟩
        intro i j lt hoff
        rcases allowed i j lt hoff with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl rfl
        · exact (exclude 1 10 2 11 hp hoff h1).elim
        · exact (exclude 1 10 5 15 hp hoff h2).elim
        · exact (exclude 1 10 9 11 hp hoff h3).elim
      · by_cases hq : occurs 5 15
        · refine ⟨5, ?_⟩
          intro i j lt hoff
          rcases allowed i j lt hoff with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact (hp hoff).elim
          · exact (exclude 5 15 2 11 hq hoff h4).elim
          · exact Or.inl rfl
          · exact (exclude 5 15 9 11 hq hoff h5).elim
        · refine ⟨11, ?_⟩
          intro i j lt hoff
          rcases allowed i j lt hoff with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact (hp hoff).elim
          · exact Or.inr rfl
          · exact (hq hoff).elim
          · exact Or.inr rfl
    have maxOne (a : ℕ) (ha : a ∈ Z) : ((A a).erase c).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hin, hiA⟩ := Finset.mem_erase.mp hi
      obtain ⟨hjn, hjA⟩ := Finset.mem_erase.mp hj
      rcases lt_trichotomy i j with lt | eq | gt
      · exact ((pairMeets i j lt ⟨a,ha,hiA,hjA⟩).elim hin hjn).elim
      · exact eq
      · exact ((pairMeets j i gt ⟨a,ha,hjA,hiA⟩).elim hjn hin).elim
    have unionSub : I.erase c ⊆ Z.biUnion (fun a => (A a).erase c) := by
      intro i hi
      obtain ⟨hic, hiI⟩ := Finset.mem_erase.mp hi
      obtain ⟨a, ha, hv⟩ := profile.1 (endpoints i).1 (endpoints i).2 ((memI i).mp hiI)
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_erase.mpr ⟨hic, Finset.mem_filter.mpr ⟨hiI, hv⟩⟩⟩
    have unionCard : (Z.biUnion (fun a => (A a).erase c)).card ≤ Z.card := by
      calc
        _ ≤ ∑ a ∈ Z, ((A a).erase c).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ Z, 1 := Finset.sum_le_sum maxOne
        _ = Z.card := by simp (config := {congrConsts := false})
    have Icard : I.card ≤ Z.card + 1 := by
      have e := (Finset.card_le_card unionSub).trans unionCard
      by_cases hc : c ∈ I
      · have h := Finset.card_erase_add_one hc
        omega
      · rw [Finset.erase_eq_of_notMem hc] at e
        omega
    have img : U ⊆ I.image codedEdge := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        have huv := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
        obtain ⟨i, eq⟩ := indexEdge u v huv
        exact Finset.mem_image.mpr ⟨i, (memI i).mpr (eq.symm ▸ he), eq⟩
    have Ucard : U.card ≤ I.card := (Finset.card_le_card img).trans Finset.card_image_le
    change 2 * U.card ≤ 2 * Z.card + (junk G C).card
    omega

  have certify : ∀ b ∈ blocks, let vertices := Finset.univ.filter (fun v : Fin 11 => b.testBit v.val)
      ∀ S ∈ vertices.powerset, (∀ u ∈ vertices, ∀ v ∈ vertices, G.Adj u v → u ∈ S ∨ v ∈ S) →
        (b.bitIndices.length + 1) / 2 ≤ S.card := by
    intro b hb
    simp (config := {congrConsts := false}) only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have pack :
      ∀ (P : List Nat) (X : Finset (Fin 11)),
        List.Pairwise (fun a b => a &&& b = 0) P →
        (∀ b ∈ P,
          (b.bitIndices.length + 1) / 2 ≤ (X.filter fun v => b.testBit v.val).card) →
        (P.map fun b => (b.bitIndices.length + 1) / 2).sum ≤ X.card := by
    intro P
    induction P with
    | nil =>
        intro X _ _
        simp (config := {congrConsts := false})
    | cons b bs ih =>
        intro X hpair hweight
        rw [List.pairwise_cons] at hpair
        rcases hpair with ⟨hhead, htail⟩
        let A : Finset (Fin 11) := X.filter fun v => b.testBit v.val
        have hAsub : A ⊆ X := Finset.filter_subset _ _
        have hheadWeight : (b.bitIndices.length + 1) / 2 ≤ A.card := by
          exact hweight b (by simp (config := {congrConsts := false}))
        have hmaskDisjoint : ∀ c ∈ bs,
            Disjoint A (X.filter fun v => c.testBit v.val) := by
          intro c hc
          apply Finset.disjoint_left.mpr
          intro v hvA hvC
          have hb : b.testBit v.val = true := (Finset.mem_filter.mp hvA).2
          have hcbit : c.testBit v.val = true := (Finset.mem_filter.mp hvC).2
          have hbits : (b &&& c).testBit v.val = true := by
            simp (config := {congrConsts := false}) [Nat.testBit_and, hb, hcbit]
          rw [hhead c hc] at hbits
          simp (config := {congrConsts := false}) at hbits
        have hfilterEq (c : ℕ) (hc : c ∈ bs) :
            (X \ A).filter (fun v => c.testBit v.val) =
              X.filter (fun v => c.testBit v.val) := by
          ext v
          constructor
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr
              ⟨(Finset.mem_sdiff.mp hmem.1).1, hmem.2⟩
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            have hrem : v ∈ X \ A := by
              refine Finset.mem_sdiff.mpr ⟨hmem.1, ?_⟩
              intro hvA
              exact Finset.disjoint_left.mp (hmaskDisjoint c hc) hvA hv
            exact Finset.mem_filter.mpr ⟨hrem, hmem.2⟩
        have hweightTail : ∀ c ∈ bs,
            (c.bitIndices.length + 1) / 2 ≤
              ((X \ A).filter fun v => c.testBit v.val).card := by
          intro c hc
          have h := hweight c (by simp (config := {congrConsts := false}) [hc])
          rw [hfilterEq c hc]
          exact h
        have htailBound := ih (X \ A) htail hweightTail
        have hcard : (X \ A).card + A.card = X.card :=
          Finset.card_sdiff_add_card_eq_card hAsub
        simp (config := {congrConsts := false}) only [List.map_cons, List.sum_cons]
        omega

  dsimp only
  intro C hsize hleast htop hjunk
  let U := Ustar G C
  let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  change U.card ≤ B → B < 2 * U.card → B - U.card < 7 → _
  intro hlow hhigh hbudget
  classical
  have supplement : ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
      G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card := by
    by_cases cheap : ∃ X : Finset (Fin 11),
        (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ X ∨ v ∈ X) ∧ X.card ≤ B - U.card
    · obtain ⟨X, covers, size⟩ := cheap
      let H := G.deleteEdges (↑U)
      let Q (k : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = k
      have ex : ∃ k, Q k := ⟨_, Finset.univ, by simp (config := {congrConsts := false}) [H], rfl⟩
      obtain ⟨K, hk, card⟩ := Nat.find_spec ex
      have least : IsMinCover H K := ⟨hk, fun T ht => card.trans_le (Nat.find_min' ex ⟨T, ht, rfl⟩)⟩
      refine ⟨K, X, least, ?_, size⟩
      intro u v edge
      by_cases gone : s(u,v) ∈ U
      · exact (covers u v gone).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
      · exact (hk (SimpleGraph.deleteEdges_adj.mpr ⟨edge, gone⟩)).imp
          (Finset.mem_union_left X) (Finset.mem_union_left X)
    · have hj : 2 ≤ (junk G C).card := hjunk
      have outside : (orN G C \ lam G C).Nonempty := by
        by_contra hn
        have empty : orN G C \ lam G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        have hb : 2 * U.card ≤ B := by
          simpa (config := {congrConsts := false}) [U, B, empty] using noCharges C hleast htop hj empty
        omega
      by_cases restricted : centreless G C = ∅ ∧ (orN G C \ lam G C).card ≤ 1
      · have hU : U.Nonempty := Finset.card_pos.mp (by omega)
        have e : ∃ u v : Fin 11, s(u,v) ∈ U := by
          obtain ⟨a, ha⟩ := hU
          induction a using Sym2.inductionOn with
          | _ i j => exact ⟨i, j, ha⟩
        obtain ⟨outsideOne, sup⟩ := (geometry 11 G C hleast htop).1 restricted.1 restricted.2 e
        have three : 3 ≤ B := by
          simp (config := {congrConsts := false}) only [B]
          omega
        have uTwo : 2 ≤ U.card := by omega
        obtain ⟨_, K, X, m, c, hx⟩ := finite U Finset.sdiff_subset uTwo sup
        exact ⟨K, X, m, c, show X.card ≤ B - U.card by omega⟩
      · have shape : (centreless G C).Nonempty ∨ 2 ≤ (orN G C \ lam G C).card := by
          by_cases present : (centreless G C).Nonempty
          · exact Or.inl present
          · have hz : centreless G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp present
            have outsideMany : ¬ (orN G C \ lam G C).card ≤ 1 := fun h => restricted ⟨hz, h⟩
            exact Or.inr (by omega)
        have expensive : ∀ X : Finset (Fin 11), (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ X ∨ v ∈ X) → B - U.card < X.card :=
          fun X hX => Nat.lt_of_not_ge (fun le => cheap ⟨X, hX, le⟩)
        have big : 4 ≤ B := by
          simp (config := {congrConsts := false}) only [B]
          rcases shape with present | outsideMany
          · have hc := Finset.card_pos.mpr present
            omega
          · omega
        by_cases two : (junk G C).card = 2
        · exact twoJunk C hsize hleast htop two outside shape big hlow hhigh hbudget expensive
        · have many : 3 ≤ (junk G C).card := Nat.lt_of_le_of_ne hj (Ne.symm two)
          have five : 5 ≤ B := by
            simp (config := {congrConsts := false}) only [B]
            rcases shape with present | outsideMany
            · have hc := Finset.card_pos.mpr present
              omega
            · omega
          exact manyJunk C hsize hleast htop many outside shape five hlow hhigh hbudget expensive
  obtain ⟨K, X, least, hwhole, size⟩ := supplement
  refine ⟨K, least, ?_⟩
  intro P hp good
  have charge (b : Nat) (hb : b ∈ P) :
      (b.bitIndices.length + 1) / 2 ≤ (X.filter (fun v : Fin 11 => b.testBit v.val)).card := by
    obtain ⟨inblocks, avoids⟩ := good b hb
    let V := Finset.univ.filter (fun v : Fin 11 => b.testBit v.val)
    let S := X.filter (fun v : Fin 11 => b.testBit v.val)
    have sub : S ⊆ V := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ v,(Finset.mem_filter.mp hv).2⟩
    apply certify b inblocks S (Finset.mem_powerset.mpr sub)
    intro u hu v hv edge
    have au := (Finset.mem_filter.mp hu).2
    have av := (Finset.mem_filter.mp hv).2
    have du : u ∉ K := fun mem => Bool.noConfusion ((avoids u mem).symm.trans au)
    have dv : v ∉ K := fun mem => Bool.noConfusion ((avoids v mem).symm.trans av)
    exact (hwhole edge).imp
      (fun xu => Finset.mem_filter.mpr ⟨(Finset.mem_union.mp xu).resolve_left du, au⟩)
      (fun xv => Finset.mem_filter.mpr ⟨(Finset.mem_union.mp xv).resolve_left dv, av⟩)
  exact (pack P X hp charge).trans size
