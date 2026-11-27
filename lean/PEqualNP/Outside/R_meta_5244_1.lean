import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 30000000 in
theorem PEqualNP.Outside.R_meta_5244_1 :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (4 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7,
          x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
        (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
          x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
          ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
            ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
              ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
        ((Ustar x3 x7).filter (fun e =>
          ∃ u v : Fin x2, e = s(u, v) ∧ ∃ a ∈ tops x3 x7, ∃ b : Fin 2,
            ∃ j ∈ junk x3 x7, u ∈ side x7 a b ∧
              OrReaches x2 x7 (opnd x7 a (1 - b)) j ∧
              gateVal x2 x7 j (pairInput u v) = true)).card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (4 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7,
          x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
        (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
          x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
          ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
            ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
              ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
        ((Ustar x3 x7).filter (fun e =>
          ∃ u v : Fin x2, e = s(u, v) ∧ ∃ a ∈ tops x3 x7,
            ∃ j ∈ junk x3 x7, ∃ k ∈ junk x3 x7, j ≠ k ∧
              OrReaches x2 x7 (opnd x7 a 0) j ∧
              OrReaches x2 x7 (opnd x7 a 1) k ∧
              gateVal x2 x7 j (pairInput u v) = true ∧
              gateVal x2 x7 k (pairInput u v) = true)).card ≤ x1 * (x7.size + (1 : ℕ))) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro largeContact largePair
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

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    (dsimp only [gateAt]; simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj])

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · (dsimp only [GateOp.eval]; simp (config := {congrConsts := false}) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq])
      intro h1 i hi; exact h i hi (h1 i hi)
    · (dsimp only [GateOp.eval]; simp (config := {congrConsts := false}) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq])
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    (dsimp only [GateOp.eval]; simp (config := {congrConsts := false}) only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq])
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
    (dsimp only [GateOp.eval]; simp (config := {congrConsts := false}) only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq])
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
      (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
      A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra hcon
    simp (config := {congrConsts := false}) only [not_or, not_le] at hcon
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
    obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
    exact h4 a b c d hac hbd
      ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

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
    (dsimp only [pairInput]; simp (config := {congrConsts := false}))

  have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
    (dsimp only [pairInput]; simp (config := {congrConsts := false}))

  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    (dsimp only [pairInput]; simp (config := {congrConsts := false}))

  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    (dsimp only [graphFun]; simp (config := {congrConsts := false}) only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq, pairInput_true])
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

  have side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
      (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
      (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
      (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
      (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
      (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
    apply hF
    apply hbel
    rw [val_and (n := n) (by simp (config := {congrConsts := false})) ha hop, hin]
    intro i hi
    simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
    · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

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
      (dsimp only [coneStep]; simp (config := {congrConsts := false}))
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
        (dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
          (dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
          (dsimp only [coneStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
    delta InCone cones gateAt
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
      (dsimp only [orStep]; simp (config := {congrConsts := false}))
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
        (dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
            (dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
            (dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
          (dsimp only [orStep]; simp (config := {congrConsts := false}) only [List.getD_eq_getElem?_getD])
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
    (dsimp only [PEqualNP.TopForm.orIn] at hu; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu)
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    (dsimp only [PEqualNP.TopForm.orIn]; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and])
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

  have pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
    funext w
    dsimp only [pairInput]
    exact decide_eq_decide.mpr or_comm

  have caseA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (u v : Fin n)
      (a : ℕ) (hatop : a ∈ tops G C) (i : Fin 2) (h : ℕ) (hjunk : h ∈ junk G C) (t1 : Fin n)
      (ht1 : t1 = u ∨ t1 = v) (hside : t1 ∈ side (n := n) C a i)
      (hor : OrReaches n C (opnd C a ((1 : Fin 2) - i)) h)
      (hv : gateVal n C h (pairInput u v) = true) :
      ∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C, ∃ (x12 : Fin 2),
        ∃ x13 ∈ junk G C, x9 ∈ side C x11 x12 ∧
          OrReaches n C (opnd C x11 ((1 : Fin 2) - x12)) x13 ∧
          gateVal n C x13 (pairInput x9 x10) = true := by
    rcases ht1 with h1 | h1
    · rw [h1] at hside
      exact ⟨u, v, rfl, a, hatop, i, h, hjunk, hside, hor, hv⟩
    · rw [h1] at hside
      exact ⟨v, u, Sym2.eq_swap, a, hatop, i, h, hjunk, hside, hor, by
        rw [pairInput_comm]; exact hv⟩

  have off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
      (huv : s(u, v) ∈ Ustar G C) :
      (∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C, ∃ (x12 : Fin 2),
        ∃ x13 ∈ junk G C, x9 ∈ side C x11 x12 ∧
          OrReaches n C (opnd C x11 ((1 : Fin 2) - x12)) x13 ∧
          gateVal n C x13 (pairInput x9 x10) = true) ∨
      ∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C,
        ∃ x12 ∈ junk G C, ∃ x13 ∈ junk G C, x12 ≠ x13 ∧
          OrReaches n C (opnd C x11 (0 : Fin 2)) x12 ∧
          OrReaches n C (opnd C x11 (1 : Fin 2)) x13 ∧
          gateVal n C x12 (pairInput x9 x10) = true ∧
          gateVal n C x13 (pairInput x9 x10) = true := by
    obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
    (dsimp only [Ustar] at huv; simp (config := {congrConsts := false}) only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv)
    obtain ⟨hadj, hns⟩ := huv
    have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
      fun u v h => (graphFun_pair G u v).mp h
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
      fun x => congrFun hfun x
    obtain ⟨a, halen, hnor, hreach, hval⟩ :=
      edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
    have hop : (gateAt C a).op = GateOp.and := by
      rcases hAO _ (gateAt_mem halen) with h | h
      · exact h
      · exact (hnor h).elim
    have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
    have hatop : a ∈ tops G C := by
      (dsimp only [tops, gatesWhere]; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_range])
      exact ⟨halen, hop, hbel⟩
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
    have e0 : opnd C a 0 = p := by (dsimp only [opnd]; simp (config := {congrConsts := false}) [hin])
    have e1 : opnd C a 1 = q := by (dsimp only [opnd]; simp (config := {congrConsts := false}) [hin])
    have d0 : opnd C a ((1 : Fin 2) - 0) = q := by
      rw [show ((1 : Fin 2) - 0) = 1 from by decide]; exact e1
    have d1 : opnd C a ((1 : Fin 2) - 1) = p := by
      rw [show ((1 : Fin 2) - 1) = 0 from by decide]; exact e0
    have hpq := (val_and (n := n) (by simp (config := {congrConsts := false})) halen hop).mp hval
    have hpin : p ∈ (gateAt C a).inputs := by rw [hin]; simp (config := {congrConsts := false})
    have hqin : q ∈ (gateAt C a).inputs := by rw [hin]; simp (config := {congrConsts := false})
    have hp := hpq p hpin
    have hq := hpq q hqin
    have junk_of : ∀ (w : ℕ), w ∈ (gateAt C a).inputs → w < n + a →
        ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
        Relation.ReflTransGen (OrStep n C) w (n + h) →
        h ∈ junk G C ∧ OrReaches n C w h ∧ ¬ BelowF G C h := by
      intro w hwin hwlt h hh hhor hr
      have hhand : (gateAt C h).op = GateOp.and := by
        rcases hAO _ (gateAt_mem hh) with h3 | h3
        · exact h3
        · exact (hhor h3).elim
      have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
      have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
      have hdirty : IsDirtyAnd n G C h := by
        delta IsDirtyAnd IsDirty
        refine ⟨hhand, hh, ?_⟩
        by_contra hne
        apply hnb
        intro x hx
        by_contra hfx
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
      have hjunk : h ∈ junk G C := by
        delta junk gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
      exact ⟨hjunk, reach_orReaches hr h rfl hh, hnb⟩
    rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
    · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
      · exfalso
        apply hns
        have hadj12 : G.Adj t1 t2 :=
          side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
        have hne : t1 ≠ t2 := G.ne_of_adj hadj12
        have hs : s(u, v) = s(t1, t2) := by
          rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
          · exact (hne (h1.trans h2.symm)).elim
          · rw [h1, h2]
          · rw [h1, h2]; exact Sym2.eq_swap
          · exact (hne (h1.trans h2.symm)).elim
        rw [hs]
        (dsimp only [starEdges]; simp (config := {congrConsts := false}) only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product])
        refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
        · (dsimp only [side]; simp (config := {congrConsts := false}) only [e0])
          exact reach_mem_orIn t1 hr1
        · (dsimp only [side]; simp (config := {congrConsts := false}) only [e1])
          exact reach_mem_orIn t2 hr2
      · obtain ⟨hjunk, hor, _⟩ := junk_of q hqin hq.1 h hh hhor hr
        left
        refine caseA G C u v a hatop 0 h hjunk t1 ht1 ?_ ?_ hv
        · (dsimp only [side]; simp (config := {congrConsts := false}) only [e0])
          exact reach_mem_orIn t1 hr1
        · rw [d0]; exact hor
    · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨k, hk, hkor, hrk, hvk⟩
      · obtain ⟨hjunk, hor, _⟩ := junk_of p hpin hp.1 h hh hhor hr
        left
        refine caseA G C u v a hatop 1 h hjunk t2 ht2 ?_ ?_ hv
        · (dsimp only [side]; simp (config := {congrConsts := false}) only [e1])
          exact reach_mem_orIn t2 hr2
        · rw [d1]; exact hor
      · obtain ⟨hjunk, hor, hnb⟩ := junk_of p hpin hp.1 h hh hhor hr
        obtain ⟨hjunkk, hork, _⟩ := junk_of q hqin hq.1 k hk hkor hrk
        right
        refine ⟨u, v, rfl, a, hatop, h, hjunk, k, hjunkk, ?_, ?_, ?_, hv, hvk⟩
        · intro heq
          subst heq
          apply hnb
          intro x hx
          apply hbel x
          show val C (List.ofFn x) (n + a) = true
          rw [val_and (n := n) (by simp (config := {congrConsts := false})) halen hop, hin]
          intro i hi
          simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨hp.1, orStep_up (n := n) (by simp (config := {congrConsts := false})) hr hx⟩
          · exact ⟨hq.1, orStep_up (n := n) (by simp (config := {congrConsts := false})) hrk hx⟩
        · rw [e0]; exact hor
        · rw [e1]; exact hork

  have no4 {n : ℕ} (G : SimpleGraph (Fin n))
      (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
      (hac : a ≠ c) (hbd : b ≠ d) : False := by
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hcd
    have e4 := G.ne_of_adj hda
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp (config := {congrConsts := false}) [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
      · simp (config := {congrConsts := false}) [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    have h5 := hg a _ hcyc
    simp (config := {congrConsts := false}) at h5

  have fin2_cases : ∀ (i b : Fin 2), b = i ∨ b = 1 - i := by decide

  let rd (n : ℕ) (C : Circuit) : Finset (Fin n) :=
    Finset.univ.filter fun i => ∃ k < C.gates.length, (i : ℕ) ∈ (gateAt C k).inputs

  have rd_card (n : ℕ) (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
      (rd n C).card ≤ 2 * C.gates.length := by
    have hsub : (rd n C).image (fun i => i.val) ⊆
        (Finset.range C.gates.length ×ˢ Finset.range 2).image
          (fun p => (gateAt C p.1).inputs.getD p.2 0) := by
      intro w hw
      simp (config := {congrConsts := false}) only [rd, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨i, ⟨k, hk, hin⟩, rfl⟩ := hw
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
      rw [hab] at hin
      simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false] at hin
      refine Finset.mem_image.mpr ?_
      rcases hin with h | h
      · exact ⟨(k, 0), Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr (by norm_num)⟩, by
            show (gateAt C k).inputs.getD 0 0 = i.val
            rw [hab, h]; rfl⟩
      · exact ⟨(k, 1), Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr (by norm_num)⟩, by
            show (gateAt C k).inputs.getD 1 0 = i.val
            rw [hab, h]; rfl⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h1
    have h3 := Finset.card_image_le (s := Finset.range C.gates.length ×ˢ Finset.range 2)
      (f := fun p => (gateAt C p.1).inputs.getD p.2 0)
    rw [Finset.card_product, Finset.card_range, Finset.card_range] at h3
    omega

  have orIn_sub_rd {n : ℕ} {C : Circuit} {k w : ℕ} (hk : k < C.gates.length)
      (hw : w ∈ (gateAt C k).inputs) : PEqualNP.TopForm.orIn n C w ⊆ rd n C := by
    intro u hu
    (dsimp only [PEqualNP.TopForm.orIn] at hu; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hu)
    simp (config := {congrConsts := false}) only [rd, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hu with h | ⟨k2, hk2, _, _, hin⟩
    · exact ⟨k, hk, by rw [h]; exact hw⟩
    · exact ⟨k2, hk2, hin⟩

  have biclique_card {n : ℕ} (G : SimpleGraph (Fin n))
      (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (P Q : Finset (Fin n)) (hab : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b) :
      ((P ×ˢ Q).image (fun p => s(p.1, p.2))).card ≤ P.card + Q.card := by
    have h1 := Finset.card_image_le (s := P ×ˢ Q) (f := fun p => s(p.1, p.2))
    rw [Finset.card_product] at h1
    rcases biclique_star G h4 P Q hab with h | h
    · have h3 : P.card * Q.card ≤ 1 * Q.card := Nat.mul_le_mul_right _ h
      omega
    · have h3 : P.card * Q.card ≤ P.card * 1 := Nat.mul_le_mul_left _ h
      omega



  have operands {n : ℕ} {C : Circuit} (model : IsAO2 n C) {j : ℕ}
      (hj : j < C.gates.length) (w : ℕ) :
      w ∈ (gateAt C j).inputs ↔ ∃ b : Fin 2, opnd C j b = w := by
    obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp (model.2.2 _ (gateAt_mem hj))
    rw [hpq]
    constructor
    · simp (config := {congrConsts := false}) only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl)
      · exact ⟨0, by (dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq])⟩
      · exact ⟨1, by (dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq])⟩
    · rintro ⟨b, rfl⟩
      fin_cases b <;> (dsimp only [opnd]; simp (config := {congrConsts := false}) [hpq])

  have andValues {n : ℕ} {C : Circuit} (model : IsAO2 n C) {j : ℕ}
      (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
      gateVal n C j x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C j b) = true := by
    change val C (List.ofFn x) (n+j) = true ↔ _
    rw [val_and (n := n) (by simp (config := {congrConsts := false})) hj ha]
    constructor
    · intro hall b
      exact (hall _ ((operands model hj _).mpr ⟨b, rfl⟩)).2
    · intro hall w hw
      obtain ⟨b,e⟩ := (operands model hj w).mp hw
      exact ⟨model.2.1 j hj w hw, e ▸ hall b⟩

  have junkGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      {j : ℕ} (hj : j ∈ junk G C) :
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
    delta junk gatesWhere at hj
    have hm := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp hm.1, hm.2.1⟩

  have junkSupports {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) {j : ℕ} (hj : j ∈ junk G C) (b : Fin 2) :
      side (n := n) C j b ⊆ rd n C := by
    have hj' := (junkGate G hj).1
    exact orIn_sub_rd hj' ((operands model hj' _).mpr ⟨b, rfl⟩)

  have topsSafe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool)
      (hx : ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true) :
      graphFun G ∅ x = true := by
    (dsimp only [tops, gatesWhere] at ha; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_range] at ha)
    obtain ⟨hidx, hop, hbelow⟩ := ha
    exact hbelow x ((andValues model hidx hop x).mpr hx)

  have topContact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
      (u : Fin n) (hu : u ∈ side C a b) (hj : OrReaches n C (opnd C a (1-b)) j) :
      u ∈ wmax G C j ∩ rd n C := by
    rw [Finset.mem_inter]
    have ha' : a < C.gates.length := by
      have hb := ha
      (dsimp only [tops, gatesWhere] at hb; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_range] at hb)
      exact hb.1
    refine ⟨?_, orIn_sub_rd ha' ((operands model ha' _).mpr ⟨b,rfl⟩) hu⟩
    (dsimp only [wmax]; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and])
    intro x hx hxu
    apply topsSafe G model ha x
    intro i
    rcases fin2_cases b i with rfl | rfl
    · exact reach_var_val x _ u (mem_orIn_reach u hu) hxu
    · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) (orReaches_reach j _ hj).1 hx

  have topPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) {a j k : ℕ} (ha : a ∈ tops G C)
      (hj : OrReaches n C (opnd C a 0) j) (hk : OrReaches n C (opnd C a 1) k) :
      ∀ x : Fin n → Bool, gateVal n C j x = true → gateVal n C k x = true →
        graphFun G ∅ x = true := by
    intro x hx hy
    apply topsSafe G model ha x
    intro b
    fin_cases b
    · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) (orReaches_reach j _ hj).1 hx
    · exact orStep_up (n := n) (by simp (config := {congrConsts := false})) (orReaches_reach k _ hk).1 hy

  have clauseBound {n d : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n))
      (h4 : ∀ a b c e : Fin n, a ≠ c → b ≠ e →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e a))
      (S : Fin d → Finset (Fin n)) (hR : ∀ i, S i ⊆ R)
      (sound : ∀ u v, (∀ i, u ∈ S i ∨ v ∈ S i) → G.Adj u v)
      (E : Finset (Sym2 (Fin n)))
      (covers : ∀ e ∈ E, ∃ u v, e = s(u,v) ∧ ∀ i, u ∈ S i ∨ v ∈ S i) :
      E.card ≤ 2^d * (2 * R.card) := by
    let L (m : Finset (Fin d)) := R.filter fun u => ∀ i ∈ m, u ∈ S i
    let K (m : Finset (Fin d)) := R.filter fun v => ∀ i ∉ m, v ∈ S i
    let B (m : Finset (Fin d)) := (L m ×ˢ K m).image fun p => s(p.1,p.2)
    have hsub : E ⊆ (Finset.univ : Finset (Finset (Fin d))).biUnion B := by
      intro e he
      obtain ⟨u,v,rfl,h⟩ := covers e he
      have hu : u ∈ R := by
        by_contra hn
        exact G.irrefl (sound v v (fun i => Or.inl ((h i).resolve_left (fun H => hn (hR i H)))))
      have hv : v ∈ R := by
        by_contra hn
        exact G.irrefl (sound u u (fun i => Or.inl ((h i).resolve_right (fun H => hn (hR i H)))))
      let m := Finset.univ.filter fun i => u ∈ S i
      have hm (i : Fin d) : i ∈ m ↔ u ∈ S i := by simp (config := {congrConsts := false}) [m]
      apply Finset.mem_biUnion.mpr
      refine ⟨m, Finset.mem_univ _, Finset.mem_image.mpr ⟨(u,v), ?_, rfl⟩⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hu, fun i hi => (hm i).mp hi⟩,
        Finset.mem_filter.mpr ⟨hv, fun i hi => (h i).resolve_left (fun H => hi ((hm i).mpr H))⟩⟩
    have hB (m : Finset (Fin d)) : (B m).card ≤ 2 * R.card := by
      have hbc := biclique_card G h4 (L m) (K m) (by
        intro u hu v hv
        apply sound u v
        intro i
        by_cases hi : i ∈ m
        · exact Or.inl ((Finset.mem_filter.mp hu).2 i hi)
        · exact Or.inr ((Finset.mem_filter.mp hv).2 i hi))
      have hl := Finset.card_filter_le (s := R) (p := fun u => ∀ i ∈ m, u ∈ S i)
      have hk := Finset.card_filter_le (s := R) (p := fun v => ∀ i ∉ m, v ∈ S i)
      change (B m).card ≤ _ at hbc
      change (L m).card ≤ _ at hl
      change (K m).card ≤ _ at hk
      omega
    refine (Finset.card_le_card hsub).trans ?_
    simpa (config := {congrConsts := false}) only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] using
      (Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Finset (Fin d))) B _ (fun m _ => hB m))

  have pairWitness {n : ℕ} (u v : Fin n) (S : Finset (Fin n)) (h : u ∈ S ∨ v ∈ S) :
      ∃ w ∈ S, pairInput u v w = true := by
    rcases h with h | h
    · exact ⟨u,h,pairInput_left u v⟩
    · exact ⟨v,h,pairInput_right u v⟩

  let contacts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
      Finset (Sym2 (Fin n)) :=
    (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u,v) ∧
      u ∈ wmax G C j ∩ rd n C ∧ gateVal n C j (pairInput u v) = true
  have clauseBoundList {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n))
      (h4 : ∀ a b c e : Fin n, a ≠ c → b ≠ e →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e a))
      (L : List (Finset (Fin n))) (hR : ∀ S ∈ L, S ⊆ R)
      (sound : ∀ u v, (∀ S ∈ L, u ∈ S ∨ v ∈ S) → G.Adj u v)
      (E : Finset (Sym2 (Fin n)))
      (covers : ∀ e ∈ E, ∃ u v, e = s(u, v) ∧ ∀ S ∈ L, u ∈ S ∨ v ∈ S) :
      E.card ≤ 2 ^ L.length * (2 * R.card) := by
    let S : Fin L.length → Finset (Fin n) := fun i => L[i.val]'i.isLt
    refine clauseBound G R h4 S ?_ ?_ E ?_
    · intro i
      exact hR _ (List.getElem_mem i.isLt)
    · intro u v hu
      apply sound u v
      intro A hA
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact hu ⟨i, hi⟩
    · intro e he
      obtain ⟨u, v, rfl, hcov⟩ := covers e he
      exact ⟨u, v, rfl, fun i => hcov _ (List.getElem_mem i.isLt)⟩

  have sumBound {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n))
      (h4 : ∀ a b c e : Fin n, a ≠ c → b ≠ e →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e a))
      (D : ℕ) (Fs : List (List (Finset (Fin n))))
      (hlen : ∀ L ∈ Fs, L.length ≤ D)
      (hR : ∀ L ∈ Fs, ∀ S ∈ L, S ⊆ R)
      (hsound : ∀ L ∈ Fs, ∀ u v, (∀ S ∈ L, u ∈ S ∨ v ∈ S) → G.Adj u v)
      (E : Finset (Sym2 (Fin n)))
      (hcovers : ∀ e ∈ E, ∃ L ∈ Fs, ∃ u v, e = s(u, v) ∧ ∀ S ∈ L, u ∈ S ∨ v ∈ S) :
      E.card ≤ Fs.length * (2 ^ D * (2 * R.card)) := by
    classical
    induction Fs generalizing E with
    | nil =>
      have hE : E = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨L, hL, _⟩ := hcovers e he
        simp (config := {congrConsts := false}) at hL
      rw [hE]
      simp (config := {congrConsts := false})
    | cons L Fs ih =>
      let E1 := E.filter fun e => ∃ u v, e = s(u, v) ∧ ∀ S ∈ L, u ∈ S ∨ v ∈ S
      let E2 := E \ E1
      have h1 : E1.card ≤ 2 ^ D * (2 * R.card) := by
        have hb := clauseBoundList G R h4 L (hR L List.mem_cons_self)
          (hsound L List.mem_cons_self) E1 (fun e he => (Finset.mem_filter.mp he).2)
        have hpow : 2 ^ L.length ≤ 2 ^ D :=
          Nat.pow_le_pow_right (by omega) (hlen L List.mem_cons_self)
        have hmul := Nat.mul_le_mul_right (2 * R.card) hpow
        exact hb.trans hmul
      have h2 : E2.card ≤ Fs.length * (2 ^ D * (2 * R.card)) := by
        refine ih (fun L' hL' => hlen L' (List.mem_cons_of_mem _ hL'))
          (fun L' hL' => hR L' (List.mem_cons_of_mem _ hL'))
          (fun L' hL' => hsound L' (List.mem_cons_of_mem _ hL')) E2 ?_
        intro e he
        obtain ⟨heE, he1⟩ := Finset.mem_sdiff.mp he
        obtain ⟨L', hL', u, v, rfl, hcov⟩ := hcovers e heE
        rcases List.mem_cons.mp hL' with rfl | hL''
        · exact (he1 (Finset.mem_filter.mpr ⟨heE, u, v, rfl, hcov⟩)).elim
        · exact ⟨L', hL'', u, v, rfl, hcov⟩
      have hsub : E ⊆ E1 ∪ E2 := by
        intro e he
        by_cases hm : e ∈ E1
        · exact Finset.mem_union_left _ hm
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hm⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le E1 E2)
      simp (config := {congrConsts := false}) only [List.length_cons]
      rw [Nat.succ_mul]
      omega

  have operandStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C)
      {g : ℕ} (hg : g ∈ junk G C) (b : Fin 2) (u v : Fin n)
      (hv : val C (List.ofFn (pairInput u v)) (opnd C g b) = true) :
      (u ∈ side (n := n) C g b ∨ v ∈ side (n := n) C g b) ∨
      ∃ h ∈ junk G C, h < g ∧ OrReaches n C (opnd C g b) h ∧
        gateVal n C h (pairInput u v) = true := by
    obtain ⟨hg', hgand⟩ := junkGate G hg
    let w := opnd C g b
    have hw : w ∈ (gateAt C g).inputs := (operands model hg' _).mpr ⟨b, rfl⟩
    have hwlt : w < n + g := model.2.1 g hg' w hw
    rcases operand_trace (C := C) u v w hv with ⟨t, ht, hr⟩ | ⟨h, hh, hhor, hr, hval⟩
    · left
      rcases ht with rfl | rfl
      · exact Or.inl (reach_mem_orIn _ hr)
      · exact Or.inr (reach_mem_orIn _ hr)
    · right
      have ha : (gateAt C h).op = GateOp.and :=
        (model.1 _ (gateAt_mem hh)).resolve_right hhor
      have hle : n + h ≤ w := orStep_le hr
      have hc : InCone n C h g := operand_cone hg' hw hwlt hr
      have hnot : ¬ BelowF G C h := fun hb => top h hh g hg' ha hb hgand hc
      have hd : IsDirtyAnd n G C h := by
        delta IsDirtyAnd IsDirty
        refine ⟨ha, hh, ?_⟩
        by_contra hne
        apply hnot
        intro x hx
        by_contra hfx
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
      have hhj : h ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hd⟩
      exact ⟨h, hhj, by omega, reach_orReaches hr h rfl hh, hval⟩

  let Hits {n : ℕ} (x : Fin n → Bool) (L : List (Finset (Fin n))) : Prop :=
    ∀ S ∈ L, ∃ w ∈ S, x w = true

  let prodFs {n : ℕ} (A B : List (List (Finset (Fin n)))) : List (List (Finset (Fin n))) :=
    A.flatMap fun L0 => B.map fun L1 => L0 ++ L1

  have prodFs_len {n : ℕ} (A B : List (List (Finset (Fin n)))) :
      (prodFs A B).length = A.length * B.length := by
    induction A with
    | nil => simp (config := {congrConsts := false}) [prodFs]
    | cons a A ih =>
      simp (config := {congrConsts := false}) only [prodFs, List.flatMap_cons,
        List.length_append, List.length_map, List.length_cons]
      have : (A.flatMap fun L0 => B.map fun L1 => L0 ++ L1).length = A.length * B.length := ih
      rw [this, Nat.succ_mul]
      omega

  have prodFs_mem {n : ℕ} {A B : List (List (Finset (Fin n)))} {L : List (Finset (Fin n))} :
      L ∈ prodFs A B ↔ ∃ L0 ∈ A, ∃ L1 ∈ B, L = L0 ++ L1 := by
    simp (config := {congrConsts := false}) only [prodFs, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨L0, h0, L1, h1, rfl⟩; exact ⟨L0, h0, L1, h1, rfl⟩
    · rintro ⟨L0, h0, L1, h1, rfl⟩; exact ⟨L0, h0, L1, h1, rfl⟩

  have sort3 (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      ∃ j0 j1 j2 : ℕ, j0 < j1 ∧ j1 < j2 ∧ ({a, b, c} : Finset ℕ) = {j0, j1, j2} := by
    rcases lt_or_gt_of_ne hab with h1 | h1 <;>
    rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
    · exact ⟨a, b, c, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩
    · exact ⟨a, c, b, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩
    · exfalso; omega
    · exact ⟨c, a, b, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩
    · exact ⟨b, a, c, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩
    · exfalso; omega
    · exact ⟨b, c, a, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩
    · exact ⟨c, b, a, by omega, by omega, by ext x; simp (config := {congrConsts := false}); all_goals tauto⟩

  let IsRep {n : ℕ} (C : Circuit) (g N D : ℕ) (Fs : List (List (Finset (Fin n)))) : Prop :=
    Fs.length ≤ N ∧
    (∀ L ∈ Fs, L.length ≤ D) ∧
    (∀ L ∈ Fs, ∀ S ∈ L, S ⊆ rd n C) ∧
    (∀ L ∈ Fs, ∀ x : Fin n → Bool, Hits x L → gateVal n C g x = true) ∧
    (∀ u v : Fin n, gateVal n C g (pairInput u v) = true →
      ∃ L ∈ Fs, ∀ S ∈ L, u ∈ S ∨ v ∈ S)

  let IsOpRep {n : ℕ} (C : Circuit) (w N D : ℕ) (Ws : List (List (Finset (Fin n)))) : Prop :=
    Ws.length ≤ N ∧
    (∀ L ∈ Ws, L.length ≤ D) ∧
    (∀ L ∈ Ws, ∀ S ∈ L, S ⊆ rd n C) ∧
    (∀ L ∈ Ws, ∀ x : Fin n → Bool, Hits x L → val C (List.ofFn x) w = true) ∧
    (∀ u v : Fin n, val C (List.ofFn (pairInput u v)) w = true →
      ∃ L ∈ Ws, ∀ S ∈ L, u ∈ S ∨ v ∈ S)

  have gateRep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
      (model : IsAO2 n C) {g : ℕ} (hg : g ∈ junk G C)
      {N0 D0 N1 D1 : ℕ} {W0 W1 : List (List (Finset (Fin n)))}
      (h0 : IsOpRep C (opnd C g 0) N0 D0 W0)
      (h1 : IsOpRep C (opnd C g 1) N1 D1 W1) :
      IsRep C g (N0 * N1) (D0 + D1) (prodFs W0 W1) := by
    obtain ⟨hg', hgand⟩ := junkGate G hg
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [prodFs_len]; exact Nat.mul_le_mul h0.1 h1.1
    · intro L hL
      obtain ⟨L0, hL0, L1, hL1, rfl⟩ := prodFs_mem.mp hL
      rw [List.length_append]
      exact Nat.add_le_add (h0.2.1 L0 hL0) (h1.2.1 L1 hL1)
    · intro L hL S hS
      obtain ⟨L0, hL0, L1, hL1, rfl⟩ := prodFs_mem.mp hL
      rcases List.mem_append.mp hS with hS0 | hS1
      · exact h0.2.2.1 L0 hL0 S hS0
      · exact h1.2.2.1 L1 hL1 S hS1
    · intro L hL x hx
      obtain ⟨L0, hL0, L1, hL1, rfl⟩ := prodFs_mem.mp hL
      apply (andValues model hg' hgand x).mpr
      intro b
      fin_cases b
      · exact h0.2.2.2.1 L0 hL0 x (fun S hS => hx S (List.mem_append_left _ hS))
      · exact h1.2.2.2.1 L1 hL1 x (fun S hS => hx S (List.mem_append_right _ hS))
    · intro u v hv
      have hb := (andValues model hg' hgand (pairInput u v)).mp hv
      obtain ⟨L0, hL0, hc0⟩ := h0.2.2.2.2 u v (hb 0)
      obtain ⟨L1, hL1, hc1⟩ := h1.2.2.2.2 u v (hb 1)
      refine ⟨L0 ++ L1, prodFs_mem.mpr ⟨L0, hL0, L1, hL1, rfl⟩, fun S hS => ?_⟩
      rcases List.mem_append.mp hS with hS0 | hS1
      · exact hc0 S hS0
      · exact hc1 S hS1

  have contactBoundRep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (model : IsAO2 n C)
      (h4 : ∀ a b c e : Fin n, a ≠ c → b ≠ e →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e a))
      {g N D : ℕ} {Fs : List (List (Finset (Fin n)))}
      (hrep : IsRep C g N D Fs) :
      (contacts G C g).card ≤ N * (2 ^ (D + 1) * (4 * C.size)) := by
    let Fs' := Fs.map fun L => (wmax G C g ∩ rd n C) :: L
    have hs : (contacts G C g).card ≤ Fs'.length * (2 ^ (D + 1) * (2 * (rd n C).card)) := by
      refine sumBound G (rd n C) h4 (D + 1) Fs' ?_ ?_ ?_ (contacts G C g) ?_
      · intro L' hL'
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
        have := hrep.2.1 L hL
        simp (config := {congrConsts := false}); omega
      · intro L' hL' S hS
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
        rcases List.mem_cons.mp hS with rfl | hSL
        · exact Finset.inter_subset_right
        · exact hrep.2.2.1 L hL S hSL
      · intro L' hL' u v hcov
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
        have hhead := hcov _ List.mem_cons_self
        obtain ⟨z, hz, hzx⟩ := pairWitness u v (wmax G C g ∩ rd n C) hhead
        have hw : z ∈ wmax G C g := (Finset.mem_inter.mp hz).1
        (dsimp only [wmax] at hw; simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_univ, true_and] at hw)
        have hhits : Hits (pairInput u v) L := fun S hS =>
          pairWitness u v S (hcov S (List.mem_cons_of_mem _ hS))
        exact (graphFun_pair G u v).mp (hw _ (hrep.2.2.2.1 L hL _ hhits) hzx)
      · intro e he
        obtain ⟨u, v, heq, hu, hx⟩ := (Finset.mem_filter.mp he).2
        obtain ⟨L, hL, hcov⟩ := hrep.2.2.2.2 u v hx
        refine ⟨(wmax G C g ∩ rd n C) :: L, List.mem_map.mpr ⟨L, hL, rfl⟩, u, v, heq, ?_⟩
        intro S hS
        rcases List.mem_cons.mp hS with rfl | hSL
        · exact Or.inl hu
        · exact hcov S hSL
    have hfl : Fs'.length ≤ N := by simp (config := {congrConsts := false}) [Fs', hrep.1]
    have hrd := rd_card n C model.2.2
    have hsz : C.size = C.gates.length := rfl
    have hr2 : 2 * (rd n C).card ≤ 4 * C.size := by omega
    have hm1 : 2 ^ (D + 1) * (2 * (rd n C).card) ≤ 2 ^ (D + 1) * (4 * C.size) :=
      Nat.mul_le_mul_left _ hr2
    have hm2 : Fs'.length * (2 ^ (D + 1) * (2 * (rd n C).card)) ≤ N * (2 ^ (D + 1) * (4 * C.size)) :=
      Nat.mul_le_mul hfl hm1
    exact hs.trans hm2

  let pairEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (j k : ℕ) : Finset (Sym2 (Fin n)) :=
    (Ustar G C).filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C,
      OrReaches n C (opnd C a 0) j ∧ OrReaches n C (opnd C a 1) k ∧
      gateVal n C j (pairInput u v) = true ∧ gateVal n C k (pairInput u v) = true

  have pairBoundRep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (model : IsAO2 n C)
      (h4 : ∀ a b c e : Fin n, a ≠ c → b ≠ e →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c e ∧ G.Adj e a))
      {j k N1 D1 N2 D2 : ℕ} {Fs1 Fs2 : List (List (Finset (Fin n)))}
      (hrep1 : IsRep C j N1 D1 Fs1) (hrep2 : IsRep C k N2 D2 Fs2) :
      (pairEdges G C j k).card ≤ (N1 * N2) * (2 ^ (D1 + D2) * (4 * C.size)) := by
    classical
    by_cases he : (pairEdges G C j k).Nonempty
    · obtain ⟨e0, he0⟩ := he
      obtain ⟨_, _, _, a, ha, h0, h1, _, _⟩ := (Finset.mem_filter.mp he0).2
      have safe := topPair G model ha h0 h1
      let Fs := prodFs Fs1 Fs2
      have hs : (pairEdges G C j k).card ≤ Fs.length * (2 ^ (D1 + D2) * (2 * (rd n C).card)) := by
        refine sumBound G (rd n C) h4 (D1 + D2) Fs ?_ ?_ ?_ (pairEdges G C j k) ?_
        · intro L hL
          obtain ⟨L1, hL1, L2, hL2, rfl⟩ := prodFs_mem.mp hL
          rw [List.length_append]
          exact Nat.add_le_add (hrep1.2.1 L1 hL1) (hrep2.2.1 L2 hL2)
        · intro L hL S hS
          obtain ⟨L1, hL1, L2, hL2, rfl⟩ := prodFs_mem.mp hL
          rcases List.mem_append.mp hS with hS1 | hS2
          · exact hrep1.2.2.1 L1 hL1 S hS1
          · exact hrep2.2.2.1 L2 hL2 S hS2
        · intro L hL u v hcov
          obtain ⟨L1, hL1, L2, hL2, rfl⟩ := prodFs_mem.mp hL
          have hhits1 : Hits (pairInput u v) L1 := fun S hS =>
            pairWitness u v S (hcov S (List.mem_append_left _ hS))
          have hhits2 : Hits (pairInput u v) L2 := fun S hS =>
            pairWitness u v S (hcov S (List.mem_append_right _ hS))
          exact (graphFun_pair G u v).mp
            (safe _ (hrep1.2.2.2.1 L1 hL1 _ hhits1) (hrep2.2.2.2.1 L2 hL2 _ hhits2))
        · intro e he'
          obtain ⟨u, v, heq, _, _, _, _, hjv, hkv⟩ := (Finset.mem_filter.mp he').2
          obtain ⟨L1, hL1, hc1⟩ := hrep1.2.2.2.2 u v hjv
          obtain ⟨L2, hL2, hc2⟩ := hrep2.2.2.2.2 u v hkv
          refine ⟨L1 ++ L2, prodFs_mem.mpr ⟨L1, hL1, L2, hL2, rfl⟩, u, v, heq, fun S hS => ?_⟩
          rcases List.mem_append.mp hS with hS1 | hS2
          · exact hc1 S hS1
          · exact hc2 S hS2
      have hfl : Fs.length ≤ N1 * N2 := by
        rw [show Fs.length = Fs1.length * Fs2.length from prodFs_len Fs1 Fs2]
        exact Nat.mul_le_mul hrep1.1 hrep2.1
      have hrd := rd_card n C model.2.2
      have hsz : C.size = C.gates.length := rfl
      have hr2 : 2 * (rd n C).card ≤ 4 * C.size := by omega
      have hm1 : 2 ^ (D1 + D2) * (2 * (rd n C).card) ≤ 2 ^ (D1 + D2) * (4 * C.size) :=
        Nat.mul_le_mul_left _ hr2
      have hm2 : Fs.length * (2 ^ (D1 + D2) * (2 * (rd n C).card)) ≤
          (N1 * N2) * (2 ^ (D1 + D2) * (4 * C.size)) :=
        Nat.mul_le_mul hfl hm1
      exact hs.trans hm2
    · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty]
      exact Nat.zero_le _

  have threeJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (girth : ∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5 ≤ w.length)
      (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C)
      (hcount : (junk G C).card = 3) :
      (Ustar G C).card ≤ 5089824 * (C.size + 1) := by
    classical
    obtain ⟨a0, a1, a2, h01, h02, h12, hJ0⟩ := Finset.card_eq_three.mp hcount
    obtain ⟨j0, j1, j2, hj01, hj12, hsort⟩ := sort3 a0 a1 a2 h01 h02 h12
    have hJ : junk G C = {j0, j1, j2} := hJ0.trans hsort
    have hj0 : j0 ∈ junk G C := by simp (config := {congrConsts := false}) [hJ]
    have hj1 : j1 ∈ junk G C := by simp (config := {congrConsts := false}) [hJ]
    have hj2 : j2 ∈ junk G C := by simp (config := {congrConsts := false}) [hJ]
    have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :=
      fun a b c d hac hbd h => no4 G girth a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
    have sideOpRep : ∀ {g : ℕ} (hg : g ∈ junk G C) (b : Fin 2) (x : Fin n → Bool),
        Hits x [side (n := n) C g b] → val C (List.ofFn x) (opnd C g b) = true := by
      intro g _ b x hx
      obtain ⟨u, hu, hux⟩ := hx _ List.mem_cons_self
      exact reach_var_val x _ u (mem_orIn_reach u hu) hux
    have liftOpRep : ∀ {w h Nh Dh : ℕ} {Fsh : List (List (Finset (Fin n)))},
        OrReaches n C w h → IsRep C h Nh Dh Fsh →
        ∀ L ∈ Fsh, ∀ x : Fin n → Bool, Hits x L → val C (List.ofFn x) w = true := by
      intro w h _ _ Fsh hr hrep L hL x hx
      exact orStep_up (n := n) (by simp (config := {congrConsts := false}))
        (orReaches_reach h w hr).1 (hrep.2.2.2.1 L hL x hx)
    let W0 (b : Fin 2) : List (List (Finset (Fin n))) := [[side (n := n) C j0 b]]
    have hW0 (b : Fin 2) : IsOpRep C (opnd C j0 b) 1 1 (W0 b) := by
      refine ⟨by simp (config := {congrConsts := false}) [W0], ?_, ?_, ?_, ?_⟩
      · intro L hL
        simp (config := {congrConsts := false}) [W0] at hL; subst hL
        simp (config := {congrConsts := false})
      · intro L hL S hS
        simp (config := {congrConsts := false}) [W0] at hL; subst hL
        simp (config := {congrConsts := false}) at hS; subst hS
        exact junkSupports G least.1 hj0 b
      · intro L hL x hx
        simp (config := {congrConsts := false}) [W0] at hL; subst hL
        exact sideOpRep hj0 b x hx
      · intro u v hv
        rcases operandStep G least.1 top hj0 b u v hv with hside | ⟨h, hh, hlt, _, _⟩
        · exact ⟨[side (n := n) C j0 b], List.mem_cons_self, fun S hS => by
            simp (config := {congrConsts := false}) at hS; subst hS; exact hside⟩
        · rw [hJ] at hh
          simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hh
          omega
    let Fs0 := prodFs (W0 0) (W0 1)
    have hFs0 : IsRep C j0 1 2 Fs0 := gateRep G least.1 hj0 (hW0 0) (hW0 1)
    let W1 (b : Fin 2) : List (List (Finset (Fin n))) :=
      [side (n := n) C j1 b] :: (if OrReaches n C (opnd C j1 b) j0 then Fs0 else [])
    have hW1 (b : Fin 2) : IsOpRep C (opnd C j1 b) 2 2 (W1 b) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [W1]
        by_cases hr : OrReaches n C (opnd C j1 b) j0
        · rw [if_pos hr, List.length_cons]
          have := hFs0.1
          omega
        · rw [if_neg hr]
          simp (config := {congrConsts := false})
      · intro L hL
        dsimp only [W1] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · simp (config := {congrConsts := false})
        · split_ifs at hL'
          · exact hFs0.2.1 L hL'
          · simp (config := {congrConsts := false}) at hL'
      · intro L hL S hS
        dsimp only [W1] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · simp (config := {congrConsts := false}) at hS; subst hS
          exact junkSupports G least.1 hj1 b
        · split_ifs at hL'
          · exact hFs0.2.2.1 L hL' S hS
          · simp (config := {congrConsts := false}) at hL'
      · intro L hL x hx
        dsimp only [W1] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · exact sideOpRep hj1 b x hx
        · split_ifs at hL' with hr
          · exact liftOpRep hr hFs0 L hL' x hx
          · simp (config := {congrConsts := false}) at hL'
      · intro u v hv
        rcases operandStep G least.1 top hj1 b u v hv with hside | ⟨h, hh, hlt, hr, hval⟩
        · refine ⟨[side (n := n) C j1 b], List.mem_cons_self, fun S hS => ?_⟩
          simp (config := {congrConsts := false}) at hS; subst hS; exact hside
        · rw [hJ] at hh
          simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hh
          have hh0 : h = j0 := by omega
          subst hh0
          obtain ⟨L, hL, hcov⟩ := hFs0.2.2.2.2 u v hval
          refine ⟨L, List.mem_cons_of_mem _ ?_, hcov⟩
          rw [if_pos hr]
          exact hL
    let Fs1 := prodFs (W1 0) (W1 1)
    have hFs1 : IsRep C j1 4 4 Fs1 := gateRep G least.1 hj1 (hW1 0) (hW1 1)
    let W2 (b : Fin 2) : List (List (Finset (Fin n))) :=
      [side (n := n) C j2 b] ::
        ((if OrReaches n C (opnd C j2 b) j0 then Fs0 else []) ++
         (if OrReaches n C (opnd C j2 b) j1 then Fs1 else []))
    have hW2 (b : Fin 2) : IsOpRep C (opnd C j2 b) 6 4 (W2 b) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [W2]
        rw [List.length_cons, List.length_append]
        have hlen0 : (if OrReaches n C (opnd C j2 b) j0 then Fs0 else []).length ≤ 1 := by
          split_ifs
          · exact hFs0.1
          · simp (config := {congrConsts := false})
        have hlen1 : (if OrReaches n C (opnd C j2 b) j1 then Fs1 else []).length ≤ 4 := by
          split_ifs
          · exact hFs1.1
          · simp (config := {congrConsts := false})
        omega
      · intro L hL
        dsimp only [W2] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · simp (config := {congrConsts := false})
        · rcases List.mem_append.mp hL' with hL0 | hL1
          · split_ifs at hL0
            · exact (hFs0.2.1 L hL0).trans (by omega)
            · simp (config := {congrConsts := false}) at hL0
          · split_ifs at hL1
            · exact hFs1.2.1 L hL1
            · simp (config := {congrConsts := false}) at hL1
      · intro L hL S hS
        dsimp only [W2] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · simp (config := {congrConsts := false}) at hS; subst hS
          exact junkSupports G least.1 hj2 b
        · rcases List.mem_append.mp hL' with hL0 | hL1
          · split_ifs at hL0
            · exact hFs0.2.2.1 L hL0 S hS
            · simp (config := {congrConsts := false}) at hL0
          · split_ifs at hL1
            · exact hFs1.2.2.1 L hL1 S hS
            · simp (config := {congrConsts := false}) at hL1
      · intro L hL x hx
        dsimp only [W2] at hL
        rcases List.mem_cons.mp hL with rfl | hL'
        · exact sideOpRep hj2 b x hx
        · rcases List.mem_append.mp hL' with hL0 | hL1
          · split_ifs at hL0 with hr0
            · exact liftOpRep hr0 hFs0 L hL0 x hx
            · simp (config := {congrConsts := false}) at hL0
          · split_ifs at hL1 with hr1
            · exact liftOpRep hr1 hFs1 L hL1 x hx
            · simp (config := {congrConsts := false}) at hL1
      · intro u v hv
        rcases operandStep G least.1 top hj2 b u v hv with hside | ⟨h, hh, hlt, hr, hval⟩
        · refine ⟨[side (n := n) C j2 b], List.mem_cons_self, fun S hS => ?_⟩
          simp (config := {congrConsts := false}) at hS; subst hS; exact hside
        · rw [hJ] at hh
          simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl | rfl
          · obtain ⟨L, hL, hcov⟩ := hFs0.2.2.2.2 u v hval
            refine ⟨L, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), hcov⟩
            rw [if_pos hr]; exact hL
          · obtain ⟨L, hL, hcov⟩ := hFs1.2.2.2.2 u v hval
            refine ⟨L, List.mem_cons_of_mem _ (List.mem_append_right _ ?_), hcov⟩
            rw [if_pos hr]; exact hL
          · omega
    let Fs2 := prodFs (W2 0) (W2 1)
    have hFs2 : IsRep C j2 36 8 Fs2 := gateRep G least.1 hj2 (hW2 0) (hW2 1)
    have hc0 := contactBoundRep G C least.1 h4 hFs0
    have hc1 := contactBoundRep G C least.1 h4 hFs1
    have hc2 := contactBoundRep G C least.1 h4 hFs2
    have hp01 := pairBoundRep G C least.1 h4 hFs0 hFs1
    have hp10 := pairBoundRep G C least.1 h4 hFs1 hFs0
    have hp02 := pairBoundRep G C least.1 h4 hFs0 hFs2
    have hp20 := pairBoundRep G C least.1 h4 hFs2 hFs0
    have hp12 := pairBoundRep G C least.1 h4 hFs1 hFs2
    have hp21 := pairBoundRep G C least.1 h4 hFs2 hFs1
    let Cset := contacts G C j0 ∪ contacts G C j1 ∪ contacts G C j2
    let Pset :=
      (pairEdges G C j0 j1 ∪ pairEdges G C j1 j0) ∪
      (pairEdges G C j0 j2 ∪ pairEdges G C j2 j0) ∪
      (pairEdges G C j1 j2 ∪ pairEdges G C j2 j1)
    have hsub : Ustar G C ⊆ Cset ∪ Pset := by
      intro e he
      induction e using Sym2.ind with
      | _ p q =>
        rcases off_star G C least top p q he with
          ⟨u, v, heq, a, ha, b, g, hg, hu, hor, hval⟩ |
          ⟨u, v, heq, a, ha, g, hg, h, hh, hne, hr0, hr1, hvg, hvh⟩
        · have hcon := topContact G least.1 ha b u hu hor
          have hmem : s(p, q) ∈ contacts G C g :=
            Finset.mem_filter.mpr ⟨he, u, v, heq, hcon, hval⟩
          rw [hJ] at hg
          simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hg
          apply Finset.mem_union_left
          rcases hg with rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hmem)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
          · exact Finset.mem_union_right _ hmem
        · have hmem : s(p, q) ∈ pairEdges G C g h :=
            Finset.mem_filter.mpr ⟨he, u, v, heq, a, ha, hr0, hr1, hvg, hvh⟩
          rw [hJ] at hg hh
          simp (config := {congrConsts := false}) only [Finset.mem_insert, Finset.mem_singleton] at hg hh
          apply Finset.mem_union_right
          rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
          · exact (hne rfl).elim
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ hmem))
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
          · exact (hne rfl).elim
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hmem)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hmem))
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ hmem)
          · exact (hne rfl).elim
    have hU := Finset.card_le_card hsub
    have hcu := Finset.card_union_le Cset Pset
    have hcs1 := Finset.card_union_le (contacts G C j0 ∪ contacts G C j1) (contacts G C j2)
    have hcs2 := Finset.card_union_le (contacts G C j0) (contacts G C j1)
    have hps1 := Finset.card_union_le
      ((pairEdges G C j0 j1 ∪ pairEdges G C j1 j0) ∪ (pairEdges G C j0 j2 ∪ pairEdges G C j2 j0))
      (pairEdges G C j1 j2 ∪ pairEdges G C j2 j1)
    have hps2 := Finset.card_union_le
      (pairEdges G C j0 j1 ∪ pairEdges G C j1 j0) (pairEdges G C j0 j2 ∪ pairEdges G C j2 j0)
    have hps3 := Finset.card_union_le (pairEdges G C j0 j1) (pairEdges G C j1 j0)
    have hps4 := Finset.card_union_le (pairEdges G C j0 j2) (pairEdges G C j2 j0)
    have hps5 := Finset.card_union_le (pairEdges G C j1 j2) (pairEdges G C j2 j1)
    change Cset.card ≤ _ at hcs1
    change Pset.card ≤ _ at hps1
    norm_num at hc0 hc1 hc2 hp01 hp10 hp02 hp20 hp12 hp21
    omega

  obtain ⟨d, hd⟩ := largeContact
  obtain ⟨k, hk⟩ := largePair
  refine ⟨max (d + k) 5089824, ?_⟩
  intro n G _ hg hn C hL hT hcount hdom hnocov
  by_cases hlarge : 4 ≤ (PEqualNP.TopForm.junk G C).card
  · let A := (Ustar G C).filter (fun e =>
      ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
        ∃ j ∈ junk G C, u ∈ side C a b ∧
          OrReaches n C (opnd C a (1 - b)) j ∧
          gateVal n C j (pairInput u v) = true)
    let B := (Ustar G C).filter (fun e =>
      ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C,
        ∃ j ∈ junk G C, ∃ k ∈ junk G C, j ≠ k ∧
          OrReaches n C (opnd C a 0) j ∧
          OrReaches n C (opnd C a 1) k ∧
          gateVal n C j (pairInput u v) = true ∧
          gateVal n C k (pairInput u v) = true)
    have hA : A.card ≤ d * (C.size + 1) := hd n G hg hn C hL hT hlarge hdom hnocov
    have hB : B.card ≤ k * (C.size + 1) := hk n G hg hn C hL hT hlarge hdom hnocov
    have hsub : Ustar G C ⊆ A ∪ B := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rcases off_star G C hL hT u v he with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, h⟩)
    calc
      (Ustar G C).card ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le _ _
      _ ≤ d * (C.size + 1) + k * (C.size + 1) := Nat.add_le_add hA hB
      _ = (d + k) * (C.size + 1) := (Nat.add_mul d k _).symm
      _ ≤ max (d + k) 5089824 * (C.size + 1) := Nat.mul_le_mul_right _ (le_max_left _ _)
  · have hthree : (PEqualNP.TopForm.junk G C).card = 3 := by omega
    exact (threeJunk G C hg hL hT hthree).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
