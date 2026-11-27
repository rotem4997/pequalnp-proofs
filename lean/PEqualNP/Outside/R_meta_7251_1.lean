import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 65000 in
set_option maxHeartbeats 26000000 in
theorem PEqualNP.Outside.R_meta_7251_1 :
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit) (g m a : ℕ) (b : Fin 2) (e f : Sym2 (Fin 26)) (U : Finset (Sym2 (Fin 26))) (T : Finset ℕ),
      G = SimpleGraph.fromRel (fun p l : Fin 26 => p.val < 13 ∧ 13 ≤ l.val ∧
        (p.val + 26 - l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      ∀
        ⦃_ : U = Ustar G C⦄
        ⦃_ : T = tops G C⦄
        ⦃_ : IsLeastAO G C⦄
        ⦃_ : TopForm G C⦄
        ⦃_ : C.size ≤ 64⦄
        ⦃_ : centreless G C = ∅⦄
        ⦃_ : 2 ≤ (junk G C).card⦄
        ⦃_ : 3 ≤ (orN G C \ lam G C).card⦄
        ⦃_ : 5 ≤ U.card⦄
        ⦃_ : 2 ≤ (mixing G C).card⦄
        ⦃_ : T.card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + U.card⦄
        ⦃_ : 52 ≤ 4 * T.card + U.card⦄
        ⦃_ : ∀ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ T.card⦄
        ⦃_ : g ∈ junk G C⦄
        ⦃_ : m ∈ mixing G C⦄
        ⦃_ : a ∈ T⦄
        ⦃_ : OrReaches 26 C (opnd C a b) m⦄
        ⦃_ : OrReaches 26 C (26 + m) g⦄
        ⦃_ : gammaE G C g ∩ U ⊆ gammaE G C m⦄
        ⦃_ : e ≠ f⦄
        ⦃_ : ∀ z : Sym2 (Fin 26), z = e ∨ z = f → z ∈ U ∧ z ∈ gammaE G C g ∧ ∃ t ∈ T, ∃ d : Fin 2, z ∈ gammaE G C t ∧ OrReaches 26 C (opnd C t d) g⦄
        ⦃_ : ∃ v : Fin 26, v ∈ e ∧ v ∈ f⦄, False) →
    (∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit) (g m a : ℕ) (b : Fin 2) (e f : Sym2 (Fin 26)) (U : Finset (Sym2 (Fin 26))) (T : Finset ℕ),
      G = SimpleGraph.fromRel (fun p l : Fin 26 => p.val < 13 ∧ 13 ≤ l.val ∧
        (p.val + 26 - l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      ∀
        ⦃_ : U = Ustar G C⦄
        ⦃_ : T = tops G C⦄
        ⦃_ : IsLeastAO G C⦄
        ⦃_ : TopForm G C⦄
        ⦃_ : C.size ≤ 64⦄
        ⦃_ : centreless G C = ∅⦄
        ⦃_ : 2 ≤ (junk G C).card⦄
        ⦃_ : 3 ≤ (orN G C \ lam G C).card⦄
        ⦃_ : 5 ≤ U.card⦄
        ⦃_ : 2 ≤ (mixing G C).card⦄
        ⦃_ : T.card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + U.card⦄
        ⦃_ : 52 ≤ 4 * T.card + U.card⦄
        ⦃_ : ∀ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ T.card⦄
        ⦃_ : g ∈ junk G C⦄
        ⦃_ : m ∈ mixing G C⦄
        ⦃_ : a ∈ T⦄
        ⦃_ : OrReaches 26 C (opnd C a b) m⦄
        ⦃_ : OrReaches 26 C (26 + m) g⦄
        ⦃_ : gammaE G C g ∩ U ⊆ gammaE G C m⦄
        ⦃_ : e ≠ f⦄
        ⦃_ : ∀ z : Sym2 (Fin 26), z = e ∨ z = f → z ∈ U ∧ z ∈ gammaE G C g ∧ ∃ t ∈ T, ∃ d : Fin 2, z ∈ gammaE G C t ∧ OrReaches 26 C (opnd C t d) g⦄
        ⦃_ : ¬ ∃ v : Fin 26, v ∈ e ∧ v ∈ f⦄, False) →
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x10 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x11 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           PEqualNP.TopForm.centreless x1 x3 = ∅ → (2 : ℕ) ≤ x9.card → (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card → (3 : ℕ) ≤ x10.card → x8.card + x9.card + x11.card ≤ (13 : ℕ) + x10.card → (52 : ℕ) ≤ (4 : ℕ) * x8.card + x10.card → (∀ (x18 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x18 → x18.card ≤ x8.card) → False := by
  have gateAt_d : ∀ (C : Circuit) (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := by
    intros; exact rfl
  have pairInput_d : ∀ {n : ℕ} (u v : Fin n), pairInput u v = fun w => decide (w = u ∨ w = v) := by
    intros; exact rfl
  have graphFun_d : ∀ {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (x : Fin n → Bool), graphFun K A x =
        (decide (∃ a ∈ A, x a = true) || decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)) := by
    intros; exact rfl
  have coneStep_d : ∀ (n : ℕ) (cs : List (List ℕ)) (g : Gate), coneStep n cs g =
      cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := by
    intros; exact rfl
  have orStep_d : letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq; ∀ (n : ℕ) (cs : List (List ℕ)) (g : Gate), orStep n cs g =
      cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := by
    intros; exact rfl
  have opnd_d : ∀ (C : Circuit) (a : ℕ) (b : Fin 2), opnd C a b = (gateAt C a).inputs.getD b 0 := by
    intros; exact rfl
  have orIn_d : letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq; ∀ (n : ℕ) (C : Circuit) (w : ℕ), orIn n C w = Finset.univ.filter fun i : Fin n =>
      (i : ℕ) = w ∨ ∃ k < C.gates.length,
        OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs := by
    intros; exact rfl
  have gatesWhere_d : ∀ (C : Circuit) (P : ℕ → Prop) [DecidablePred P],
      gatesWhere C P = (Finset.range C.gates.length).filter P := by
    intros; exact rfl
  have tops_d : letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq; ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      tops G C = gatesWhere C fun j => (gateAt C j).op = GateOp.and ∧ BelowF G C j := by
    intros; exact rfl
  have orN_d : letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq; ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      orN G C = gatesWhere C fun j => (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j := by
    intros; exact rfl
  have evalOr_d : ∀ l : List Bool, GateOp.eval GateOp.or l = l.any id := by
    intros; exact rfl
  have evalAnd_d : ∀ l : List Bool, GateOp.eval GateOp.and l = l.all id := by
    intros; exact rfl
  have bitSeparation : ∀ (k : Fin 5), 2 ≤ k.val →
      ∀ f : Fin k.val → Fin (k.val-1) → Bool,
        ¬ (∀ i j, i ≠ j → ∃ t, f i t = true ∧ f j t = false) := by
    intro k
    fin_cases k <;> decide +kernel
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl
  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [stepWire]
      omega
  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp -congrConsts only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp -congrConsts [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp -congrConsts [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp -congrConsts [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp -congrConsts at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp -congrConsts [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp -congrConsts only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp -congrConsts [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp -congrConsts [stepWire]; omega)]
          simp -congrConsts [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa -congrConsts using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp -congrConsts [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp -congrConsts only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    simp -congrConsts [gateAt_d, List.getD_eq_getElem?_getD, hj]
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
  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp -congrConsts only [evalOr_d, evalAnd_d, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
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
    simp -congrConsts only [evalOr_d, evalAnd_d, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
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
    rw [val_input (n := n) (by simp -congrConsts) u.isLt]
    simp -congrConsts [List.getD_eq_getElem?_getD]
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
    simp -congrConsts [pairInput_d]
  have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
    simp -congrConsts [pairInput_d]
  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    simp -congrConsts [pairInput_d]
  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    simp -congrConsts only [graphFun_d, Finset.notMem_empty, false_and, exists_false, decide_false,
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
      (by simp -congrConsts) p hv
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
    orStep_up (n := n) (by simp -congrConsts) hr (by rw [val_ofFn]; exact ht)
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
    exact orStep_up (n := n) (by simp -congrConsts) hr hv
  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [coneStep_d]
      omega
  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [coneStep_d, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp -congrConsts; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp -congrConsts [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp -congrConsts only [coneStep_d, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp -congrConsts [hlen]
        rw [e2, e1]
        simp -congrConsts only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp -congrConsts, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [coneStep_d, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega
  have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char n C.gates i j
    unfold InCone cones; delta gateAt
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
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [orStep_d]
      omega
  have orSets_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [orSets_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        simp -congrConsts only [orStep_d, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp -congrConsts; omega, ?_⟩
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
          simp -congrConsts [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp -congrConsts only [orStep_d, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp -congrConsts, Or.inl h3⟩
            · refine ⟨by simp -congrConsts, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp -congrConsts only [orStep_d, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [List.mem_singleton]
          constructor
          · intro h3
            exact ⟨by simp -congrConsts, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp -congrConsts only [orStep_d, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · rintro ⟨h0, _⟩
          simp -congrConsts at h0
          omega
  have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char n C.gates g k
    unfold OrReaches orSets; delta gateAt
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
    simp -congrConsts only [orIn_d, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
      (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
      u ∈ PEqualNP.TopForm.orIn n C p := by
    simp -congrConsts only [orIn_d, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have topData {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {a : ℕ} (ha : a ∈ tops G C) :
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    simpa -congrConsts only [tops_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using ha
  have junkData {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {a : ℕ} (ha : a ∈ junk G C) :
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
    rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
    exact ⟨hal, hop, hd⟩
  have binaryInputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
      ∃ p q, (gateAt C a).inputs = [p, q] :=
    List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  have opndMem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
      opnd C a b ∈ (gateAt C a).inputs := by
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    fin_cases b <;> simp -congrConsts [opnd_d, hpq]
  have opndBound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
      opnd C a b < n + a :=
    hAO.2.1 a ha _ (opndMem hAO ha b)
  have andValBoth {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
      (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
      gateVal n C a x = true ↔
        val C (List.ofFn x) (opnd C a 0) = true ∧
        val C (List.ofFn x) (opnd C a 1) = true := by
    rw [gateVal_eq_val, val_and (n := n) (by simp -congrConsts) ha hop]
    constructor
    · intro h
      exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
    · intro h i hi
      refine ⟨hAO.2.1 a ha i hi, ?_⟩
      obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
      rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
      · simpa -congrConsts [opnd_d, hpq] using h.1
      · have e : i = q := List.mem_singleton.mp hq
        subst i
        simpa -congrConsts [opnd_d, hpq] using h.2
  have andValOperands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
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
  have operandReachCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
      {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
      InCone n C h a :=
    operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
      (orReaches_reach h _ hr).1
  have operandOrAndJunk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
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
  have inputsAsOpnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
      (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by simp -congrConsts [opnd_d, hpq]⟩
    · have e : z = q := List.mem_singleton.mp hq
      exact ⟨1, by simpa -congrConsts [opnd_d, hpq] using e⟩
  have sideVal {n : ℕ} {C : Circuit} {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
      (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
      val C (List.ofFn x) (opnd C a b) = true :=
    reach_var_val x _ t (mem_orIn_reach t ht) hx
  have andFromInputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
      (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
      {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
      (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
    (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩
  have topAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
      {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
      G.Adj u v := by
    obtain ⟨hl, ho, hb⟩ := topData ha
    exact (graphFun_pair G u v).mp
      (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))
  have acceptedTop {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
      ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
    have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
      congrFun hL.2.1 x
    obtain ⟨a, hl, ho, hr, hv⟩ :=
      edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
        hout u v ((graphFun_pair G u v).mpr hadj)
    have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
    have hb : BelowF G C a := fun x hx =>
      below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
    refine ⟨a, ?_, hv⟩
    simpa -congrConsts only [tops_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using
      And.intro hl (And.intro hand hb)
  have operandSupport {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
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
  have andRawEmpty {n : ℕ} {C : Circuit} {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
      orIn n C (n + j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    simp -congrConsts only [orIn_d, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
      · subst k
        rw [hj] at ho
        cases ho
      · rw [hj] at hof
        cases hof
  have lastOrBefore {n : ℕ} {C : Circuit} {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
      w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
        n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
        Relation.ReflTransGen (OrStep n C) w (n + m) := by
    rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
    · exact .inl eq.symm
    · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
      exact .inr ⟨m, hm, ho, hi, hb, hz⟩
  have lastOrOutside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
      (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
      (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
      m ∈ orN G C \ lam G C := by
    obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
    have hNotBelow : ¬ BelowF G C m := by
      intro h
      have hvm : gateVal n C m x = true := (val_or (n := n) (by simp -congrConsts) hm ho).mpr
        ⟨n + j, hi, hb, hjx⟩
      exact Bool.noConfusion (hx.symm.trans (h x hvm))
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · simpa -congrConsts only [orN_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using
        And.intro hm (And.intro ho hNotBelow)
    · intro hl
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
      obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
      have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← be, andRawEmpty (n := n) hjop] at hnonempty
      exact Finset.not_nonempty_empty hnonempty
  have residualTrace {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
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
        unfold starEdges
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
  have topSides {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
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
  have orData {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
      m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
    simpa -congrConsts only [orN_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using
      (Finset.mem_sdiff.mp hm).1
  have emptyInputOutside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {j m : ℕ}
      (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
      (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
      (hin : n + j ∈ (gateAt C m).inputs) :
      m ∈ orN G C \ lam G C := by
    have hbad : ¬ BelowF G C m := by
      intro hb
      apply dirty
      intro x hx
      exact hb x ((val_or (n := n) (by simp -congrConsts) hm hop).mpr
        ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa -congrConsts only [orN_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using
        And.intro hm (And.intro hop hbad)
    · intro hl
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
      obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
      have hne : (orIn n C (opnd C m b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, empty] at hne
      exact Finset.not_nonempty_empty hne
  have residualPath {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (empty : centreless G C = ∅)
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
  have mixingRaw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
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
  have singleJunkInput {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {m j k : ℕ}
      (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
      (hj : j ∈ junk G C) (hk : k ∈ junk G C)
      (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
      j = k := by
    by_contra hjk
    obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
    have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
      intro w hw
      simp -congrConsts only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
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
  have cleanAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
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
  have firingTop {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
      (ha : a ∈ tops G C)
      (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
      (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
      (hmx : gateVal n C m x = true) (hwx : x w = true) :
      graphFun G ∅ x = true := by
    obtain ⟨haLen, haOp, haBelow⟩ := topData ha
    apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
    intro c
    rcases opposite b c with rfl | rfl
    · exact orStep_up (n := n) (by simp -congrConsts) path hmx
    · exact sideVal hw hwx
  have oppositeEndpoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C)
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
      · exact orStep_up (n := n) (by simp -congrConsts) path hx
      · exact orStep_up (n := n) (by simp -congrConsts) hp hx
  have rawCoverShape {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {m w : ℕ}
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
      simpa -congrConsts only [orN_d, gatesWhere_d, Finset.mem_filter, Finset.mem_range] using
        And.intro hkl (And.intro hko hbelow)
    have hkL : k ∈ lam G C := by
      by_contra hn
      have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
      rw [only, Finset.mem_singleton] at hk
      omega
    obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
    exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
      (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩
  have falseJunkCover {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
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
  have finish {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C)
      (empty : centreless G C = ∅)
      (budget : (orN G C \ lam G C).card ≤ 1)
      (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
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
    refine ⟨t, ?_⟩
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
        (val_or (n := n) (by simp -congrConsts) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
      exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
    exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx
  have reachVal {n : ℕ} {C : Circuit} {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
      (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
    orStep_up (n := n) (by simp -congrConsts) (orReaches_reach h _ hr).1 hh
  have orInTrans {n : ℕ} {C : Circuit} {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
      orIn n C z ⊆ orIn n C w :=
    fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
  have orStepOpnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
      (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
      OrStep n C (n + m) (opnd C m b) :=
    ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
  have orInOr {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
      (hop : (gateAt C m).op = GateOp.or) :
      orIn n C (n + m) = side C m 0 ∪ side C m 1 := by
    ext x
    constructor
    · intro hx
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hst, hrem⟩
      · have := x.isLt
        omega
      · obtain ⟨k, hk, he, _, hz, _⟩ := hst
        have e : k = m := by omega
        subst k
        obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hm hz
        have hx' := reach_mem_orIn x hrem
        apply Finset.mem_union.mpr
        fin_cases b
        · exact Or.inl hx'
        · exact Or.inr hx'
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 0)) hx
      · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 1)) hx
  have orInAnd {n : ℕ} {C : Circuit} {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
      orIn n C (n + j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hs, _⟩
    · have := x.isLt
      omega
    · obtain ⟨k, _, he, hk, _, _⟩ := hs
      have e : k = j := by omega
      subst k
      rw [hop] at hk
      contradiction
  have orNOfRaw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
      (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
    letI : DecidableEq GateOp := gateOpDecEq
    obtain ⟨t, ht⟩ := hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hop, ?_⟩
    intro hb
    have hv : gateVal n C m (pairInput t t) = true :=
      reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
    exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
  have mixingNotLam {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {m : ℕ} (hm : m ∈ mixing G C) : m ∈ orN G C \ lam G C := by
    rcases Finset.mem_filter.mp hm with ⟨hm, hmix⟩
    refine Finset.mem_sdiff.mpr ⟨hm, ?_⟩
    intro hl
    rcases Finset.mem_filter.mp hl with ⟨_, h0, h1, _⟩
    apply hmix
    simp -congrConsts only [← Finset.not_nonempty_iff_eq_empty, h0, h1]
  have mixingAlong {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) {w j : ℕ} (hr : OrReaches n C w j)
      (hj : (gateAt C j).op = GateOp.and) (hw : (orIn n C w).Nonempty) :
      ∃ m ∈ mixing G C, OrReaches n C w m ∧ OrReaches n C (n + m) j ∧
        (orIn n C (n + m)).Nonempty := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      have hn : n ≤ w := hr.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      rcases (orReaches_iff n C k j).mp hr with ⟨hk, rfl | ⟨hop, z, hz, hzb, hr'⟩⟩
      · rw [orInAnd hj] at hw
        exact (Finset.not_nonempty_empty hw).elim
      · obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hk hz
        by_cases hzb' : (side (n := n) C k b).Nonempty
        · obtain ⟨m, hm, hrm, hjm, hnon⟩ := ih _ hzb hr' hzb'
          exact ⟨m, hm, (orReaches_iff n C k m).mpr ⟨hk, Or.inr ⟨hop, _, hz, hzb, hrm⟩⟩,
            hjm, hnon⟩
        · have hempty : side (n := n) C k b = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hzb'
          have hboth : (side (n := n) C k 0 ∪ side (n := n) C k 1).Nonempty :=
            orInOr hAO hk hop ▸ hw
          have hm : k ∈ mixing G C := by
            refine Finset.mem_filter.mpr ⟨orNOfRaw hk hop hw, ?_⟩
            change (side (n := n) C k 0 = ∅) ≠ (side (n := n) C k 1 = ∅)
            fin_cases b
            · change side (n := n) C k 0 = ∅ at hempty
              have h1 : side (n := n) C k 1 ≠ ∅ := by
                rwa [hempty, Finset.empty_union, Finset.nonempty_iff_ne_empty] at hboth
              simp -congrConsts [hempty, h1]
            · change side (n := n) C k 1 = ∅ at hempty
              have h0 : side (n := n) C k 0 ≠ ∅ := by
                rwa [hempty, Finset.union_empty, Finset.nonempty_iff_ne_empty] at hboth
              simp -congrConsts [hempty, h0]
          exact ⟨k, hm, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hr, hw⟩
  have memGammaInterUstar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {u v : Fin n} {g : ℕ} (he : s(u, v) ∈ Ustar G C)
      (hv : gateVal n C g (pairInput u v) = true) :
      s(u, v) ∈ gammaE G C g ∩ Ustar G C :=
    Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hv⟩, he⟩
  have cardBiUnionLeOne {α β : Type} [DecidableEq α] (S : Finset β) (f : β → Finset α)
      (h1 : ∀ x ∈ S, (f x).card ≤ 1) :
      (S.biUnion f).card ≤ S.card := by
    calc (S.biUnion f).card ≤ ∑ x ∈ S, (f x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S, 1 := Finset.sum_le_sum h1
      _ = S.card := by simp -congrConsts
  have commonUnique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h4 : NoFourCycle G) {a b p q : Fin n}
      (hab : a ≠ b) (hap : G.Adj a p) (hbp : G.Adj b p)
      (haq : G.Adj a q) (hbq : G.Adj b q) : p = q :=
    Finset.card_le_one.mp (h4 a b hab) p (by simp -congrConsts [hap,hbp]) q (by simp -congrConsts [haq,hbq])
  let Responder {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (U : Finset (Sym2 (Fin n))) (w : Fin n) : Prop :=
    ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨ ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑U).Adj y z) ∧
        (∀ p q : Fin n, s(p,q) ∈ U → p ∈ S ∨ q ∈ S) ∧ ∀ y ∈ S, x y = false
  have distinctResponse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (U : Finset (Sym2 (Fin n))) (h4 : NoFourCycle G)
      (color : Fin n → Bool) (bip : ∀ u v, G.Adj u v → color u ≠ color v)
      (c w v w' v' : Fin n)
      (cw : (G.deleteEdges ↑U).Adj c w) (cw' : (G.deleteEdges ↑U).Adj c w')
      (wv : G.Adj w v) (wv' : G.Adj w' v')
      (e : s(w,v) ∈ U) (e' : s(w',v') ∈ U) (ne : s(w,v) ≠ s(w',v'))
      (resp : Responder G U w) : False := by
    have same {p q r : Fin n} (h : G.Adj p r) (h' : G.Adj q r) : color p = color q := by
      have two : ∀ a b z : Bool, a ≠ z → b ≠ z → a = b := by decide
      exact two _ _ _ (bip _ _ h) (bip _ _ h')
    have hc := (SimpleGraph.deleteEdges_adj.mp cw).1
    have hc' := (SimpleGraph.deleteEdges_adj.mp cw').1
    by_cases ww : w = w'
    · subst w'
      have vv : v ≠ v' := fun h => ne (h ▸ rfl)
      have off : graphFun G ∅ (pairInput w w) = false :=
        Bool.eq_false_iff.mpr (fun h => G.irrefl ((graphFun_pair G w w).mp h))
      obtain ⟨S,shape,cover,avoid⟩ := resp (pairInput w w) (pairInput_left w w) off
      have out : w ∉ S := fun h => Bool.noConfusion ((pairInput_left w w).symm.trans (avoid _ h))
      have hv := (cover _ _ e).resolve_left out
      have hv' := (cover _ _ e').resolve_left out
      rcases shape with small|⟨z, hz⟩
      · exact vv (Finset.card_le_one.mp small _ hv _ hv')
      · have vz := hz v hv
        have v'z := hz v' hv'
        have wz := commonUnique h4 vv wv.symm wv'.symm (SimpleGraph.deleteEdges_adj.mp vz).1
          (SimpleGraph.deleteEdges_adj.mp v'z).1
        exact (SimpleGraph.deleteEdges_adj.mp (wz.symm ▸ vz.symm)).2 e
    · have cn : c ≠ v' := by
        rintro rfl
        exact (SimpleGraph.deleteEdges_adj.mp cw'.symm).2 e'
      have non : ¬ G.Adj w v' := fun h => ww (commonUnique h4 cn hc h.symm hc' wv'.symm)
      have off : graphFun G ∅ (pairInput w v') = false :=
        Bool.eq_false_iff.mpr (fun h => non ((graphFun_pair G w v').mp h))
      obtain ⟨S,shape,cover,avoid⟩ := resp (pairInput w v') (pairInput_left w v') off
      have out : w ∉ S := fun h => Bool.noConfusion ((pairInput_left w v').symm.trans (avoid _ h))
      have out' : v' ∉ S := fun h => Bool.noConfusion ((pairInput_right w v').symm.trans (avoid _ h))
      have hv := (cover _ _ e).resolve_left out
      have hw' := (cover _ _ e').resolve_right out'
      have different : color v ≠ color w' := by
        rw [same hc'.symm hc.symm]
        exact bip _ _ wv.symm
      rcases shape with small|⟨z,hz⟩
      · exact different (congrArg color (Finset.card_le_one.mp small _ hv _ hw'))
      · exact different (same (SimpleGraph.deleteEdges_adj.mp (hz _ hv)).1
          (SimpleGraph.deleteEdges_adj.mp (hz _ hw')).1)
  have oneOutside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C)
      (h4 : NoFourCycle G) (color : Fin n → Bool) (bip : ∀ u v, G.Adj u v → color u ≠ color v)
      (empty : centreless G C = ∅) (only : (orN G C \ lam G C).card ≤ 1) : (Ustar G C).card ≤ 1 := by
    by_contra big
    replace big := not_le.mp big
    obtain ⟨e, he, f, hf, nef⟩ := Finset.one_lt_card.mp big
    have existsEdge : ∃ u v : Fin n, s(u,v) ∈ Ustar G C := by
      induction e using Sym2.ind with
      | _ u v => exact ⟨u,v,he⟩
    obtain ⟨c,response⟩ := finish least top empty only existsEdge
    have oriented (edge : Sym2 (Fin n)) (hedge : edge ∈ Ustar G C) :
        ∃ w v : Fin n, edge = s(w,v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj c w ∧ Responder G (Ustar G C) w := by
      induction edge using Sym2.ind with
      | _ u v =>
        obtain ⟨w,eq,h,resp⟩ := response u v hedge
        rcases eq with rfl|rfl
        · exact ⟨w,v,rfl,h,resp⟩
        · exact ⟨w,u,Sym2.eq_swap,h,resp⟩
    obtain ⟨w,v,rfl,cw,resp⟩ := oriented e he
    obtain ⟨w',v',rfl,cw',_⟩ := oriented f hf
    exact distinctResponse G (Ustar G C) h4 color bip c w v w' v' cw cw'
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hf).1) he hf nef resp
  let plane := SimpleGraph.fromRel (fun p l : Fin 26 =>
    p.val < 13 ∧ 13 ≤ l.val ∧ (p.val + 26 - l.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  letI planeInst : DecidableRel plane.Adj := by unfold plane SimpleGraph.fromRel; infer_instance
  let color26 (v : Fin 26) := decide (v.val < 13)
  have planeBip : ∀ a b, plane.Adj a b → color26 a ≠ color26 b := by
    unfold plane color26 SimpleGraph.fromRel
    decide +kernel
  have planeFour : NoFourCycle plane := by
    unfold NoFourCycle plane SimpleGraph.fromRel
    decide +kernel
  have boundary {G : SimpleGraph (Fin 26)} [inst : DecidableRel G.Adj] {C : Circuit}
      (geq : G = plane) (least : IsLeastAO G C) (top : TopForm G C)
      (empty : centreless G C = ∅) (hj : 2 ≤ (junk G C).card)
      (hu : 3 ≤ (Ustar G C).card)
      (cost : (tops G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + (Ustar G C).card)
      (edges : 52 ≤ 4 * (tops G C).card + (Ustar G C).card) :
      2 ≤ (orN G C \ lam G C).card ∧ 4 ≤ (Ustar G C).card := by
    subst G
    have id : inst = (inferInstance : DecidableRel plane.Adj) := Subsingleton.elim _ _
    have no4 : NoFourCycle plane := by
      convert planeFour using 1
    have hr : 2 ≤ (orN plane C \ lam plane C).card := by
      by_contra small
      replace small := not_le.mp small
      have := oneOutside least top no4 color26 planeBip empty (by omega)
      omega
    exact ⟨hr,by omega⟩
  let matchIndex (d : Fin 4) (v : Fin 26) : Fin 13 :=
    if v.val < 13 then ⟨v.val % 13, Nat.mod_lt _ (by decide)⟩
    else ⟨(v.val + ([0,1,3,9] : List ℕ).getD d.val 0) % 13, Nat.mod_lt _ (by decide)⟩
  have matchAdj : ∀ (d : Fin 4) (v w : Fin 26),
      matchIndex d v = matchIndex d w → v ≠ w → plane.Adj v w := by
    dsimp only [matchIndex,plane]
    decide
  let badIndices (p l : Fin 26) (d : Fin 4) : Finset (Fin 13) :=
    Finset.univ.filter fun i => ∀ v : Fin 26, matchIndex d v = i → plane.Adj p v ∨ plane.Adj l v
  have missingTwo : ∀ p l : Fin 26, p.val < 13 → 13 ≤ l.val → ¬ plane.Adj p l →
      ∃ d : Fin 4, 2 ≤ (badIndices p l d).card := by
    dsimp only [badIndices,matchIndex,plane,planeInst]
    decide
  have independentMixed (K : Finset (Fin 26))
      (indep : ∀ v ∈ K, ∀ w ∈ K, ¬plane.Adj v w)
      {p l : Fin 26} (hp : p ∈ K) (hp0 : p.val < 13) (hl : l ∈ K) (hl0 : 13 ≤ l.val) :
      K.card ≤ 11 := by
    obtain ⟨d,hd⟩ := missingTwo p l hp0 hl0 (indep _ hp _ hl)
    have inj : Set.InjOn (matchIndex d) K := by
      intro v hv w hw eq
      by_contra diff
      exact indep _ hv _ hw (matchAdj d v w eq diff)
    have sub : K.image (matchIndex d) ⊆ Finset.univ \ badIndices p l d := by
      intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro bad
      rcases (Finset.mem_filter.mp bad).2 v rfl with h|h
      · exact indep _ hp _ hv h
      · exact indep _ hl _ hv h
    have hc := Finset.card_le_card sub
    rw [Finset.card_image_of_injOn inj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin] at hc
    omega
  let incidentEdges (v : Fin 26) : Finset (Sym2 (Fin 26)) :=
    (Finset.univ.filter (plane.Adj v)).image fun w => s(v,w)
  have degree_four : ∀ v, (Finset.univ.filter (plane.Adj v)).card = 4 := by decide
  have incident_count (v : Fin 26) : (incidentEdges v).card ≤ 4 :=
    Finset.card_image_le.trans (degree_four v).le
  have incident_mem {v w : Fin 26} (h : plane.Adj v w) : s(v,w) ∈ incidentEdges v :=
    Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  have edge_incident {e : Sym2 (Fin 26)} (he : e ∈ plane.edgeSet) {v : Fin 26} (hv : v ∈ e) :
      e ∈ incidentEdges v := by
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact incident_mem (show plane.Adj v b from he)
      · rw [Sym2.eq_swap]
        exact incident_mem (show plane.Adj a v from he).symm
  have two_incident_count {a b : Fin 26} (hab : plane.Adj a b) :
      (incidentEdges a ∪ incidentEdges b).card ≤ 7 := by
    have ha := incident_mem hab
    have hb : s(a,b) ∈ incidentEdges b := Sym2.eq_swap ▸ incident_mem hab.symm
    have h := Finset.card_union_add_card_inter (incidentEdges a) (incidentEdges b)
    have hi := Finset.card_pos.mpr ⟨_,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
    have hca := incident_count a
    have hcb := incident_count b
    omega
  have existsMinCover (G : SimpleGraph (Fin 26)) : ∃ K, IsMinCover G K := by
    classical
    let P (m : ℕ) := ∃ K : Finset (Fin 26), G.IsVertexCover (↑K) ∧ K.card = m
    have ex : ∃ m, P m := ⟨_, Finset.univ, by simp -congrConsts, rfl⟩
    obtain ⟨K,hK,hcard⟩ := Nat.find_spec ex
    exact ⟨K,hK,fun T hT => hcard.trans_le (Nat.find_min' ex ⟨T,hT,rfl⟩)⟩
  have planeCount : plane.edgeFinset.card = 52 := by decide +kernel
  have incidentUnion (K : Finset (Fin 26)) : (K.biUnion incidentEdges).card ≤ 4 * K.card := by
    calc
      _ ≤ ∑ k ∈ K, (incidentEdges k).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ K, 4 := Finset.sum_le_sum (fun v _ => incident_count v)
      _ = _ := by simp -congrConsts [Nat.mul_comm]
  have coverIncidence {U : Finset (Sym2 (Fin 26))} {K : Finset (Fin 26)}
      (cover : (plane.deleteEdges ↑U).IsVertexCover (K : Set (Fin 26))) :
      plane.edgeFinset \ U ⊆ K.biUnion incidentEdges := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨hadj,off⟩ := Finset.mem_sdiff.mp he
      have h := SimpleGraph.mem_edgeFinset.mp hadj
      rcases cover (SimpleGraph.deleteEdges_adj.mpr ⟨h,off⟩) with hK|hK
      · exact Finset.mem_biUnion.mpr ⟨u,hK,incident_mem h⟩
      · exact Finset.mem_biUnion.mpr ⟨v,hK,Sym2.eq_swap ▸ incident_mem h.symm⟩
  have saturatedIndependent (K : Finset (Fin 26))
      (sat : (K.biUnion incidentEdges).card = 4 * K.card) :
      ∀ v ∈ K, ∀ w ∈ K, ¬ plane.Adj v w := by
    intro v hv w hw adj
    have diff := adj.ne
    let S := (K.erase v).erase w
    have hwe : w ∈ K.erase v := Finset.mem_erase.mpr ⟨Ne.symm diff,hw⟩
    have hcard : S.card + 2 = K.card := by
      have h1 := Finset.card_erase_add_one hv
      have h2 := Finset.card_erase_add_one hwe
      dsimp [S]
      omega
    have sub : K.biUnion incidentEdges ⊆ (incidentEdges v ∪ incidentEdges w) ∪ S.biUnion incidentEdges := by
      intro e he
      obtain ⟨p,hp,he⟩ := Finset.mem_biUnion.mp he
      by_cases pv : p = v
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (pv ▸ he))
      by_cases pw : p = w
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (pw ▸ he))
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p,Finset.mem_erase.mpr ⟨pw,Finset.mem_erase.mpr ⟨pv,hp⟩⟩,he⟩)
    have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have hpair := two_incident_count adj
    have hrest := incidentUnion S
    omega
  let colorClass (c : Bool) : Finset (Fin 26) :=
    Finset.univ.filter fun v => decide (v.val < 13) = c
  have colorCount : ∀ c, (colorClass c).card = 13 := by decide +kernel
  have fourEdgeCover (U : Finset (Sym2 (Fin 26))) (subset : U ⊆ plane.edgeFinset)
      (four : U.card = 4) (bound : ∀ K, IsMinCover (plane.deleteEdges ↑U) K → K.card ≤ 12) :
      ∃ v : Fin 26, ∀ e ∈ U, v ∈ e := by
    obtain ⟨K,minimal⟩ := existsMinCover (plane.deleteEdges ↑U)
    have hc := bound K minimal
    have sub := coverIncidence minimal.1
    have edges : (plane.edgeFinset \ U).card = 48 := by
      rw [Finset.card_sdiff_of_subset subset,planeCount,four]
    have lhs := Finset.card_le_card sub
    have rhs := incidentUnion K
    have ksize : K.card = 12 := by omega
    have sat : (K.biUnion incidentEdges).card = 4 * K.card := by omega
    have equal := Finset.eq_of_subset_of_card_le sub (by omega)
    have independent := saturatedIndependent K sat
    have mono : ∃ c, K ⊆ colorClass c := by
      by_cases low : ∃ p ∈ K, p.val < 13
      · obtain ⟨p,hp,hp0⟩ := low
        refine ⟨true, fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        apply decide_eq_true
        by_contra! opp
        have := independentMixed K independent hp hp0 hl opp
        omega
      · refine ⟨false, fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        exact decide_eq_false (fun h => low ⟨p,hp,h⟩)
    obtain ⟨c,hK⟩ := mono
    have one : (colorClass c \ K).card = 1 := by rw [Finset.card_sdiff_of_subset hK,colorCount,ksize]
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp one
    refine ⟨v,fun e he => ?_⟩
    have heG := subset he
    have clean (w : Fin 26) (hw : w ∈ e) : w ∉ K := by
      intro h
      have hI := Finset.mem_biUnion.mpr ⟨w,h,edge_incident (SimpleGraph.mem_edgeFinset.mp heG) hw⟩
      rw [← equal] at hI
      exact (Finset.mem_sdiff.mp hI).2 he
    have opposite : ∃ w ∈ e, w ∈ colorClass c := by
      induction e using Sym2.ind with
      | _ a b =>
        have adj := SimpleGraph.mem_edgeFinset.mp heG
        have h := planeBip _ _ adj
        have mem (v : Fin 26) : v ∈ colorClass c ↔ color26 v = c := by
          simp -congrConsts only [colorClass, color26, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases ac : color26 a = c
        · exact ⟨a,Sym2.mem_iff.mpr (Or.inl rfl),(mem _).mpr ac⟩
        · have two : ∀ x y z : Bool, x ≠ y → x ≠ z → y = z := by decide
          exact ⟨b,Sym2.mem_iff.mpr (Or.inr rfl),(mem _).mpr (two _ _ _ h ac)⟩
    obtain ⟨w,hw,hcol⟩ := opposite
    have hw' := Finset.mem_sdiff.mpr ⟨hcol,clean w hw⟩
    rw [hv,Finset.mem_singleton] at hw'
    exact hw' ▸ hw
  have deleteAdjMono {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {V U : Finset (Sym2 (Fin n))} (sub : V ⊆ U) {u v : Fin n}
      (h : (G.deleteEdges ↑U).Adj u v) : (G.deleteEdges ↑V).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.deleteEdges_adj.mp h).1,
      fun he => (SimpleGraph.deleteEdges_adj.mp h).2 (sub he)⟩
  have activeCross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (U : Finset (Sym2 (Fin n))) (color : Fin n → Bool)
      (bip : ∀ u v, G.Adj u v → color u ≠ color v)
      {w v w' v' : Fin n} (A : G.Adj w v) (left : s(w,v) ∈ U) (right : s(w',v') ∈ U)
      (same : color w = color w') (cross : ¬G.Adj w v') (resp : Responder G U w) : False := by
    have off : graphFun G ∅ (pairInput w v') = false :=
      Bool.eq_false_iff.mpr (fun h => cross ((graphFun_pair G w v').mp h))
    obtain ⟨S,shape,cover,avoid⟩ := resp (pairInput w v') (pairInput_left w v') off
    have h1 : w ∉ S := fun h => Bool.noConfusion ((pairInput_left w v').symm.trans (avoid _ h))
    have h2 : v' ∉ S := fun h => Bool.noConfusion ((pairInput_right w v').symm.trans (avoid _ h))
    have sv := (cover _ _ left).resolve_left h1
    have sw := (cover _ _ right).resolve_right h2
    have diff : color v ≠ color w' := same ▸ bip _ _ A.symm
    rcases shape with small|⟨c,hc⟩
    · exact diff (congrArg color (Finset.card_le_one.mp small _ sv _ sw))
    · have ha := bip _ _ (SimpleGraph.deleteEdges_adj.mp (hc _ sv)).1
      have hb := bip _ _ (SimpleGraph.deleteEdges_adj.mp (hc _ sw)).1
      have sameB : ∀ p q r : Bool, p ≠ r → q ≠ r → p = q := by decide
      exact diff (sameB _ _ _ ha hb)
  have responseForcesStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (E : Finset (Sym2 (Fin n))) (color : Fin n → Bool)
      (bip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
      {w v p q : Fin n} (h : G.Adj w v) (e : s(w,v) ∈ E) (f : s(p,q) ∈ E)
      (same : color w = color p) (resp : Responder G E w) : q = v := by
    by_contra ne
    by_cases cross : G.Adj w q
    · have off : graphFun G ∅ (pairInput w p) = false := Bool.eq_false_iff.mpr
        (fun hv => bip _ _ ((graphFun_pair G w p).mp hv) same)
      obtain ⟨S,shape,cover,avoid⟩ := resp (pairInput w p) (pairInput_left w p) off
      have ow : w ∉ S := fun hx => Bool.noConfusion ((pairInput_left w p).symm.trans (avoid _ hx))
      have op : p ∉ S := fun hx => Bool.noConfusion ((pairInput_right w p).symm.trans (avoid _ hx))
      have sv := (cover _ _ e).resolve_left ow
      have sq := (cover _ _ f).resolve_left op
      rcases shape with small|⟨z,hz⟩
      · exact ne (Finset.card_le_one.mp small _ sq _ sv)
      · have eq := commonUnique h4 ne cross.symm h.symm (SimpleGraph.deleteEdges_adj.mp (hz _ sq)).1
            (SimpleGraph.deleteEdges_adj.mp (hz _ sv)).1
        exact (SimpleGraph.deleteEdges_adj.mp (eq.symm ▸ (hz _ sv).symm)).2 e
    · exact activeCross G E color bip h e f same cross resp
  let Serves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
    ∃ p q : Fin n, e = s(p,q) ∧ gateVal n C j (pairInput p q) = true ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, gateVal n C a (pairInput p q) = true ∧
        OrReaches n C (opnd C a b) j
  have sharedService {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C)
      (empty : centreless G C = ∅) (hu : 3 ≤ (Ustar G C).card)
      (cost : (tops G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + (Ustar G C).card)
      (edges : 52 ≤ 4 * (tops G C).card + (Ustar G C).card) :
      ∃ g ∈ junk G C, ∃ m ∈ mixing G C, ∃ a ∈ tops G C, ∃ b : Fin 2,
        OrReaches 26 C (opnd C a b) m ∧ OrReaches 26 C (26+m) g ∧
        (gammaE G C g ∩ Ustar G C ⊆ gammaE G C m ∩ Ustar G C) ∧
        ∃ e ∈ gammaE G C g ∩ Ustar G C, ∃ f ∈ gammaE G C g ∩ Ustar G C,
          e ≠ f ∧ Serves G C g e ∧ Serves G C g f := by
    classical
    let R := orN G C \ lam G C
    let D := (junk G C).filter (fun g => ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches 26 C (opnd C a b) g)
    let E (j : ℕ) := (Ustar G C).filter (Serves G C j)
    have sub : Ustar G C ⊆ D.biUnion E := by
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        obtain ⟨a,ha,b,j,hj,ht,hr,hv⟩ := residualTrace least top he
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,a,ha,b,hr⟩,
          Finset.mem_filter.mpr ⟨he,u,v,rfl,hv,a,ha,b,ht,hr⟩⟩
    have slots : D ⊆ (R ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2 - 26) := by
      intro j hj
      obtain ⟨hj,a,ha,b,hr⟩ := Finset.mem_filter.mp hj
      obtain ⟨r,hrR,reads,_⟩ := residualPath least.1 empty ha hj hr
      obtain ⟨k,hk⟩ := inputsAsOpnd least.1 (orData hrR).1 reads
      exact Finset.mem_image.mpr ⟨(r,k),Finset.mem_product.mpr ⟨hrR,Finset.mem_univ _⟩,by dsimp; omega⟩
    have capSlots : D.card ≤ 2 * R.card := by
      have h := (Finset.card_le_card slots).trans Finset.card_image_le
      simpa -congrConsts [Finset.card_product,Nat.mul_comm] using h
    have capJ : D.card ≤ (junk G C).card := Finset.card_le_card (Finset.filter_subset _ _)
    obtain ⟨j,hD,heavy⟩ : ∃ j ∈ D, 2 ≤ (E j).card := by
      by_contra! light
      have h := (Finset.card_le_card sub).trans
        (cardBiUnionLeOne D E (fun j hj => by have := light j hj; omega))
      change D.card ≤ 2 * (orN G C \ lam G C).card at capSlots
      omega
    obtain ⟨hj,a,ha,b,hr⟩ := Finset.mem_filter.mp hD
    obtain ⟨m,hm,hma,hjg,_⟩ := mixingAlong (G := G) least.1 hr (junkData hj).2.1 (topSides empty ha b)
    have transfer : gammaE G C j ∩ Ustar G C ⊆ gammaE G C m ∩ Ustar G C := by
      intro e he
      obtain ⟨hmem,hU⟩ := Finset.mem_inter.mp he
      obtain ⟨hE,u,v,eq,hv⟩ := Finset.mem_filter.mp hmem
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hE,u,v,eq,reachVal hjg hv⟩,hU⟩
    obtain ⟨e,he,f,hf,nef⟩ := Finset.one_lt_card.mp heavy
    have mem (t : Sym2 (Fin 26)) (ht : t ∈ E j) : t ∈ gammaE G C j ∩ Ustar G C := by
      obtain ⟨hU,u,v,eq,hv,_⟩ := Finset.mem_filter.mp ht
      subst t
      exact memGammaInterUstar hU hv
    exact ⟨j,hj,m,hm,a,ha,b,hma,hjg,transfer,e,mem e he,f,mem f hf,nef,
      (Finset.mem_filter.mp he).2,(Finset.mem_filter.mp hf).2⟩
  let Shape {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
    S.card ≤ 1 ∨ ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑U).Adj y z
  let Obstructs {n : ℕ} (G : SimpleGraph (Fin n)) (U E : Finset (Sym2 (Fin n)))
      (x : Fin n → Bool) : Prop :=
    ∃ S : Finset (Fin n), Shape G U S ∧ (∀ p q : Fin n, s(p,q) ∈ E → p ∈ S ∨ q ∈ S) ∧
      ∀ y ∈ S, x y = false
  have toResponse {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {E U : Finset (Sym2 (Fin n))} (sub : E ⊆ U) {w : Fin n}
      (cert : ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false → Obstructs G U E x) :
      Responder G E w := by
    intro x hx hf
    obtain ⟨S,shape,cover,avoid⟩ := cert x hx hf
    refine ⟨S,?_,cover,avoid⟩
    rcases shape with h|⟨z,hz⟩
    · exact .inl h
    · exact .inr ⟨z,fun y hy => deleteAdjMono sub (hz y hy)⟩
  have orientEdge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (color : Fin n → Bool) (bip : ∀ u v, G.Adj u v → color u ≠ color v)
      {e : Sym2 (Fin n)} (he : e ∈ G.edgeFinset) :
      ∃ p q : Fin n, e = s(p,q) ∧ color p = false ∧ color q = true := by
    induction e using Sym2.ind with
    | _ p q =>
      have diff := bip _ _ (SimpleGraph.mem_edgeFinset.mp he)
      cases hp : color p <;> cases hq : color q
      · exact (diff (hp.trans hq.symm)).elim
      · exact ⟨p,q,rfl,hp,hq⟩
      · exact ⟨q,p,Sym2.eq_swap,hq,hp⟩
      · exact (diff (hp.trans hq.symm)).elim
  have thinJoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h4 : NoFourCycle G) (color : Fin n → Bool)
      (bip : ∀ u v, G.Adj u v → color u ≠ color v) {U E : Finset (Sym2 (Fin n))}
      (graphSub : U ⊆ G.edgeFinset) (sub : E ⊆ U)
      (cert : ∀ x : Fin n → Bool, graphFun G ∅ x = false → Obstructs G U E x) : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨u,v,rfl,hu,hv⟩ := orientEdge color bip (graphSub (sub he))
    obtain ⟨p,q,rfl,hp,hq⟩ := orientEdge color bip (graphSub (sub hf))
    have resp (w : Fin n) : Responder G E w := toResponse sub (fun x _ h => cert x h)
    have uv := SimpleGraph.mem_edgeFinset.mp (graphSub (sub he))
    have a := responseForcesStar G E color bip h4 uv he hf (hu.trans hp.symm) (resp u)
    have b := responseForcesStar G E color bip h4 uv.symm (Sym2.eq_swap ▸ he)
      (Sym2.eq_swap ▸ hf) (hv.trans hq.symm) (resp v)
    rw [a,b]
  have thinSingle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h4 : NoFourCycle G) (color : Fin n → Bool)
      (bip : ∀ u v, G.Adj u v → color u ≠ color v) {U E : Finset (Sym2 (Fin n))}
      (graphSub : U ⊆ G.edgeFinset) (sub : E ⊆ U) (c : Fin n)
      (cert : ∀ e ∈ E, ∃ w v : Fin n, e = s(w,v) ∧ (G.deleteEdges ↑U).Adj c w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false → Obstructs G U E x) :
      E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨w,v,rfl,cw,hx⟩ := cert e he
    obtain ⟨p,q,rfl,cp,_⟩ := cert f hf
    by_contra ne
    exact distinctResponse G E h4 color bip c w v p q (deleteAdjMono sub cw) (deleteAdjMono sub cp)
      (SimpleGraph.mem_edgeFinset.mp (graphSub (sub he))) (SimpleGraph.mem_edgeFinset.mp (graphSub (sub hf)))
      he hf ne (toResponse sub hx)
  have rawShapeExcept {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {w : ℕ} (bound : w < n + C.gates.length)
      (off : ∀ k ∈ orN G C \ lam G C, w ≠ n + k) : Shape G (Ustar G C) (orIn n C w) := by
    by_cases small : (orIn n C w).card ≤ 1
    · exact .inl small
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C w).card)
    by_cases input : w < n
    · exfalso
      apply small
      apply Finset.card_le_one.mpr
      intro p hp q hq
      have eq (a : Fin n) (ha : a ∈ orIn n C w) : (a : ℕ) = w := by
        rcases Relation.ReflTransGen.cases_head (mem_orIn_reach a ha) with h|⟨_,hs,_⟩
        · exact h.symm
        · obtain ⟨k,_,he,_,_,_⟩ := hs
          omega
      exact Fin.ext ((eq _ hp).trans (eq _ hq).symm)
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have kl : k < C.gates.length := by omega
    have ko : (gateAt C k).op = GateOp.or := by
      rcases ao.1 _ (gateAt_mem kl) with h|h
      · rw [andRawEmpty h] at hu
        exact (Finset.notMem_empty _ hu).elim
      · exact h
    have kn := orNOfRaw (G := G) kl ko ⟨u, hu⟩
    have lamK : k ∈ lam G C := by
      by_contra missing
      exact off k (Finset.mem_sdiff.mpr ⟨kn,missing⟩) rfl
    obtain ⟨_,_,_,a,ha,b,one,hr⟩ := Finset.mem_filter.mp lamK
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1-b)).card)
    exact .inr ⟨z,fun t ht => cleanAdj ao ha b
      (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩
  have mixingCopies {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {r : ℕ} (hm : r ∈ mixing G C) :
      ∃ b : Fin 2, orIn n C (n+r) = orIn n C (opnd C r b) ∧ (orIn n C (n+r)).Nonempty := by
    obtain ⟨hr,mix⟩ := Finset.mem_filter.mp hm
    obtain ⟨kl,ko,_⟩ := orData (mixingNotLam hm)
    have eq := orInOr ao kl ko
    change (side (n := n) C r 0 = ∅) ≠ (side (n := n) C r 1 = ∅) at mix
    by_cases h : side (n := n) C r 0 = ∅
    · have non : side (n := n) C r 1 ≠ ∅ := by intro h'; exact mix (propext ⟨fun _ => h',fun _ => h⟩)
      rw [h, Finset.empty_union] at eq
      exact ⟨1,eq,eq ▸ Finset.nonempty_iff_ne_empty.mpr non⟩
    · have zero : side (n := n) C r 1 = ∅ := by
        by_contra h'
        exact mix (propext ⟨fun j => (h j).elim,fun j => (h' j).elim⟩)
      rw [zero,Finset.union_empty] at eq
      exact ⟨0,eq,eq ▸ Finset.nonempty_iff_ne_empty.mpr h⟩
  have rawShapesMix {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (limit : ℕ)
      (mixingOnly : ∀ r ∈ orN G C \ lam G C, r < limit → r ∈ mixing G C) :
      ∀ w < n+limit, w < n+C.gates.length → Shape G (Ustar G C) (orIn n C w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro wl wc
      by_cases exc : ∃ k ∈ orN G C \ lam G C, w = n+k
      · obtain ⟨k,hk,rfl⟩ := exc
        obtain ⟨b,eq,_⟩ := mixingCopies ao (mixingOnly k hk (by omega))
        have lt := opndBound ao (orData hk).1 b
        rw [eq]
        exact ih _ lt (lt.trans wl) (lt.trans wc)
      · exact rawShapeExcept ao wc (fun k hk h => exc ⟨k,hk,h⟩)
  have guardCover {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (top : TopForm G C) (limit : ℕ)
      (E : Finset (Sym2 (Fin n))) (x : Fin n → Bool)
      (raw : ∀ w < n+limit, w < n+C.gates.length →
        (∀ t ∈ orIn n C w, x t = false) →
        (∀ u v : Fin n, s(u,v) ∈ E → u ∈ orIn n C w ∨ v ∈ orIn n C w) →
        Obstructs G (Ustar G C) E x)
      (guard : ∀ r ∈ orN G C \ lam G C, r < limit → ∀ k ∈ junk G C,
        n+k ∈ (gateAt C r).inputs → ∀ u v : Fin n, s(u,v) ∈ E → gateVal n C k (pairInput u v) = true →
          gateVal n C k x = true) :
      ∀ j < limit, j ∈ junk G C → (∀ u v : Fin n, s(u,v) ∈ E → gateVal n C j (pairInput u v) = true) →
        gateVal n C j x = false → Obstructs G (Ustar G C) E x := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro jl hj fires off
      obtain ⟨jvalid,op,_⟩ := junkData hj
      obtain ⟨b,hb⟩ : ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
        by_contra! exc
        have on := (andValOperands ao jvalid op x).mpr (fun b => Bool.eq_true_of_not_eq_false (exc b))
        exact Bool.false_ne_true (off.symm.trans on)
      have ob := opndBound ao jvalid b
      have positive (u v : Fin n) (he : s(u,v) ∈ E) :=
        (andValOperands ao jvalid op (pairInput u v)).mp (fires u v he) b
      by_cases direct : ∃ k ∈ junk G C, opnd C j b = n+k
      · obtain ⟨k,hk,eq⟩ := direct
        have lt : k < j := by omega
        apply ih k lt (lt.trans jl) hk
        · intro u v he
          have hv := positive u v he
          rw [eq] at hv
          exact hv
        · rw [eq] at hb
          exact hb
      · apply raw (opnd C j b) (by omega) (by omega)
        · intro t ht
          apply Bool.eq_false_iff.mpr
          intro h
          exact Bool.false_ne_true (hb.symm.trans
            (reach_var_val x _ t (mem_orIn_reach t ht) h))
        · intro u v he
          rcases operandSupport ao top jvalid op (positive u v he) with ⟨t,ht,e⟩|⟨k,hk,hr,kv⟩
          · rcases e with rfl|rfl
            · exact Or.inl ht
            · exact Or.inr ht
          · rcases lastOrBefore (orReaches_reach k _ hr).1 with eq|⟨r,rv,ro,reads,lt,path⟩
            · exact (direct ⟨k,hk,eq⟩).elim
            · have rR := lastOrOutside ao hk rv ro reads lt
              have le := orStep_le path
              have on := guard r rR (by omega) k hk reads u v he kv
              exact (Bool.false_ne_true (hb.symm.trans (reachVal hr on))).elim
  let Signal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (r : ℕ) (x : Fin n → Bool) : Prop :=
    ∃ j ∈ junk G C, n+j ∈ (gateAt C r).inputs ∧ gateVal n C j x = true
  let Protect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (r : ℕ) (w : Fin n) : Prop :=
    ∀ x : Fin n → Bool, x w = true → Signal G C r x → graphFun G ∅ x = true
  let SafePair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (r s : ℕ) : Prop :=
    ∀ x : Fin n → Bool, Signal G C r x → Signal G C s x → graphFun G ∅ x = true
  let FiresOn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (r : ℕ) (e : Sym2 (Fin n)) : Prop :=
    ∃ u v : Fin n, e = s(u,v) ∧ Signal G C r (pairInput u v)
  have signalPair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {r : ℕ} {u v : Fin n} (h : FiresOn G C r s(u,v)) :
      Signal G C r (pairInput u v) := by
    obtain ⟨p,q,eq,h⟩ := h
    have swap (a b : Fin n) : pairInput a b = pairInput b a := by funext t; simp -congrConsts [pairInput_d,or_comm]
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact h
    · rw [swap] at h
      exact h
  have signalVal {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {r : ℕ} (hr : r ∈ orN G C \ lam G C)
      {x : Fin n → Bool} (h : Signal G C r x) : gateVal n C r x = true := by
    obtain ⟨j,_,reads,hj⟩ := h
    obtain ⟨rl,ro,_⟩ := orData hr
    exact (val_or (n := n) (by simp -congrConsts) rl ro).mpr ⟨_,reads,ao.2.1 r rl _ reads,hj⟩
  have sourceVal {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {r j : ℕ} (hr : r ∈ mixing G C)
      (hj : j ∈ junk G C) (reads : n+j ∈ (gateAt C r).inputs)
      {x : Fin n → Bool} (on : Signal G C r x) : gateVal n C j x = true := by
    obtain ⟨k,hk,hkr,hv⟩ := on
    obtain ⟨_,_,raw⟩ := mixingCopies ao hr
    simpa -congrConsts only [singleJunkInput ao (mixingNotLam hr) raw hk hj hkr reads] using hv
  have emptyObs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (x : Fin n → Bool) : Obstructs G (Ustar G C) ∅ x :=
    ⟨∅,Or.inl (by simp -congrConsts),by simp -congrConsts,by simp -congrConsts⟩
  have sourceCert {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (top : TopForm G C) {s : ℕ} (hs : s ∈ mixing G C)
      (E : Finset (Sym2 (Fin n))) (fires : ∀ e ∈ E, FiresOn G C s e) {x : Fin n → Bool}
      (off : ¬Signal G C s x)
      (mixingOnly : ∀ r ∈ orN G C \ lam G C, r < s → r ∈ mixing G C)
      (guard : ∀ r ∈ orN G C \ lam G C, r < s → ∀ u v : Fin n, s(u,v) ∈ E →
        Signal G C r (pairInput u v) → Signal G C r x) : Obstructs G (Ustar G C) E x := by
    by_cases non : E.Nonempty
    · obtain ⟨e,he⟩ := non
      obtain ⟨_,_,_,j,hj,reads,_⟩ := fires e he
      have jv := ao.2.1 s (orData (mixingNotLam hs)).1 _ reads
      exact guardCover ao top s E x
        (fun w wl wc avoid cover => ⟨_,rawShapesMix ao s mixingOnly w wl wc,cover,avoid⟩)
        (fun r hr lt k hk read u v he hv => sourceVal ao (mixingOnly r hr lt) hk read
          (guard r hr lt u v he ⟨k,hk,read,hv⟩)) j (by omega) hj
        (fun u v he => sourceVal ao hs hj reads (signalPair (fires _ he)))
        (Bool.eq_false_iff.mpr (fun h => off ⟨j,hj,reads,h⟩))
    · rw [Finset.not_nonempty_iff_eq_empty.mp non]
      exact emptyObs x
  let Single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (r : ℕ) (c : Fin n) (e : Sym2 (Fin n)) : Prop :=
    FiresOn G C r e ∧ ∃ w v : Fin n, e = s(w,v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj c w ∧ Protect G C r w
  have topProtect {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {a r : ℕ} {b : Fin 2}
      (ha : a ∈ tops G C) (hr : r ∈ orN G C \ lam G C)
      (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+r))
      {w : Fin n} (hw : w ∈ side C a (1-b)) : Protect G C r w :=
    fun x hx hs => firingTop ao ha path hw x (signalVal ao hr hs) hx
  have classifyTwoMix {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      {r s : ℕ} (diff : r ≠ s) (both : orN G C \ lam G C = {r,s})
      (hr : r ∈ mixing G C) (hs : s ∈ mixing G C) (c : ℕ → Fin n)
      (raw : ∀ k ∈ orN G C \ lam G C, c k ∈ orIn n C (n+k))
      {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
      Single G C r (c r) e ∨ Single G C s (c s) e ∨
        SafePair G C r s ∧ FiresOn G C r e ∧ FiresOn G C s e := by
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a,ha,b,j,hj,hav,hrj,jv⟩ := residualTrace least top he
      obtain ⟨k,hk,reads,path⟩ := residualPath least.1 empty ha hj hrj
      have fire : FiresOn G C k s(u,v) := ⟨u,v,rfl,j,hj,reads,jv⟩
      have on : Signal G C k (pairInput u v) := signalPair fire
      have rawAt : c k ∈ side C a b :=
        reach_mem_orIn _ (path.trans (mem_orIn_reach _ (raw k hk)))
      have casesR {t : ℕ} (ht : t ∈ orN G C \ lam G C) : t = r ∨ t = s := by simpa -congrConsts [both] using ht
      obtain ⟨al,op,sound⟩ := topData ha
      have ob := (andValOperands least.1 al op _).mp hav (1-b)
      rcases operandSupport least.1 top al op ob with ⟨w,hw,ends⟩|⟨l,hl,pathL,lv⟩
      · have single : Single G C k (c k) s(u,v) := by
          rcases ends with rfl|rfl
          · exact ⟨fire,_,_,rfl,cleanAdj least.1 ha b rawAt hw,topProtect least.1 ha hk path hw⟩
          · exact ⟨fire,_,_,Sym2.eq_swap,cleanAdj least.1 ha b rawAt hw,topProtect least.1 ha hk path hw⟩
        rcases casesR hk with rfl|rfl
        · exact Or.inl single
        · exact Or.inr (Or.inl single)
      · obtain ⟨q,hq,readq,pathq⟩ := residualPath least.1 empty ha hl pathL
        have fq : FiresOn G C q s(u,v) := ⟨u,v,rfl,l,hl,readq,lv⟩
        have joint (x : Fin n → Bool) (vk : gateVal n C k x = true) (vq : gateVal n C q x = true) :
            graphFun G ∅ x = true := by
          apply sound x ((andValOperands least.1 al op x).mpr ?_)
          intro z
          rcases opposite b z with rfl|rfl
          · exact orStep_up (n := n) (by simp -congrConsts) path vk
          · exact orStep_up (n := n) (by simp -congrConsts) pathq vq
        have neq : k ≠ q := by
          rintro rfl
          exact (orData hk).2.2 (fun x hx => joint _ hx hx)
        have safe : SafePair G C k q := fun x h h' => joint x (signalVal least.1 hk h) (signalVal least.1 hq h')
        right; right
        rcases casesR hk with kr|ks <;> rcases casesR hq with qr|qs
        · exact (neq (kr.trans qr.symm)).elim
        · exact kr ▸ qs ▸ ⟨safe,fire,fq⟩
        · subst k; subst q
          exact ⟨fun x vr vs => safe x vs vr,fq,fire⟩
        · exact (neq (ks.trans qs.symm)).elim
  have twoMixBound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      (h4 : NoFourCycle G) (color : Fin n → Bool) (bip : ∀ u v, G.Adj u v → color u ≠ color v)
      {r s : ℕ} (rs : r < s) (both : orN G C \ lam G C = {r,s})
      (hr : r ∈ mixing G C) (hs : s ∈ mixing G C) : (Ustar G C).card ≤ 3 := by
    classical
    obtain ⟨_,_,p,hp⟩ := mixingCopies least.1 hr
    obtain ⟨_,_,q,hq⟩ := mixingCopies least.1 hs
    let c (k : ℕ) : Fin n := if k = r then p else q
    have casesR {t : ℕ} (ht : t ∈ orN G C \ lam G C) : t = r ∨ t = s := by simpa -congrConsts [both] using ht
    have allM {t : ℕ} (ht : t ∈ orN G C \ lam G C) : t ∈ mixing G C := by
      rcases casesR ht with rfl|rfl
      · exact hr
      · exact hs
    have raw (k : ℕ) (hk : k ∈ orN G C \ lam G C) : c k ∈ orIn n C (n+k) := by
      rcases casesR hk with rfl|rfl
      · simpa -congrConsts [c] using hp
      · simpa -congrConsts [c,rs.ne'] using hq
    let U := Ustar G C
    have graphSub : U ⊆ G.edgeFinset := Finset.sdiff_subset
    let A := U.filter (Single G C r (c r))
    let B := U.filter fun e => Single G C s (c s) e ∧ ¬FiresOn G C r e
    let D := U \ (A ∪ B)
    have atD {e} (he : e ∈ D) : FiresOn G C r e ∧ FiresOn G C s e ∧ (Single G C s (c s) e ∨ SafePair G C r s) := by
      obtain ⟨hu,other⟩ := Finset.mem_sdiff.mp he
      rcases classifyTwoMix least top empty rs.ne both hr hs c raw hu with sing|sing|⟨safe,fr,fs⟩
      · exact (other (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,sing⟩))).elim
      · by_cases fr : FiresOn G C r e
        · exact ⟨fr,sing.1,Or.inl sing⟩
        · exact (other (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,sing,fr⟩))).elim
      · exact ⟨fr,fs,Or.inr safe⟩
    have certR (E : Finset (Sym2 (Fin n))) (f : ∀ e ∈ E, FiresOn G C r e)
        (x : Fin n → Bool) (off : ¬Signal G C r x) : Obstructs G U E x := by
      apply sourceCert least.1 top hr E f off (fun t ht _ => allM ht)
      intro t ht lt
      rcases casesR ht with eq|eq <;> omega
    have certS (E : Finset (Sym2 (Fin n))) (f : ∀ e ∈ E, FiresOn G C s e)
        (x : Fin n → Bool) (off : ¬Signal G C s x)
        (tr : ∀ e ∈ E, FiresOn G C r e → Signal G C r x) : Obstructs G U E x := by
      apply sourceCert least.1 top hs E f off (fun t ht _ => allM ht)
      intro t ht lt u v he on
      have eq : t = r := (casesR ht).resolve_right lt.ne
      subst t
      exact tr _ he ⟨u,v,rfl,on⟩
    have capA : A.card ≤ 1 := by
      apply thinSingle h4 color bip graphSub (Finset.filter_subset _ _) (c r)
      intro e he
      obtain ⟨_,w,v,eq,cw,protect⟩ := (Finset.mem_filter.mp he).2
      refine ⟨w,v,eq,cw,fun x wx off => certR A (fun _ h => (Finset.mem_filter.mp h).2.1) x ?_⟩
      exact fun on => Bool.false_ne_true (off.symm.trans (protect x wx on))
    have capB : B.card ≤ 1 := by
      apply thinSingle h4 color bip graphSub (Finset.filter_subset _ _) (c s)
      intro e he
      obtain ⟨_,w,v,eq,cw,protect⟩ := (Finset.mem_filter.mp he).2.1
      refine ⟨w,v,eq,cw,fun x wx off => certS B (fun _ h => (Finset.mem_filter.mp h).2.1.1) x
        (fun on => Bool.false_ne_true (off.symm.trans (protect x wx on))) ?_⟩
      exact fun _ h on => ((Finset.mem_filter.mp h).2.2 on).elim
    have jointCert (x : Fin n → Bool) (off : ¬(Signal G C r x ∧ Signal G C s x)) : Obstructs G U D x := by
      by_cases first : Signal G C r x
      · exact certS D (fun _ he => (atD he).2.1) x (fun z => off ⟨first,z⟩) (fun _ _ _ => first)
      · exact certR D (fun _ he => (atD he).1) x first
    have capD : D.card ≤ 1 := by
      by_cases safe : SafePair G C r s
      · exact thinJoint h4 color bip graphSub Finset.sdiff_subset (fun x off => jointCert x
          (fun h => Bool.false_ne_true (off.symm.trans (safe x h.1 h.2))))
      · apply thinSingle h4 color bip graphSub Finset.sdiff_subset (c s)
        intro e he
        obtain ⟨_,w,v,eq,cw,protect⟩ := ((atD he).2.2.resolve_right safe)
        exact ⟨w,v,eq,cw,fun x wx off => jointCert x (fun h => Bool.false_ne_true
          (off.symm.trans (protect x wx h.2)))⟩
    have sub : U ⊆ A ∪ B ∪ D := by
      intro e he
      by_cases h : e ∈ A ∪ B
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
    have hc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have hab := Finset.card_union_le A B
    change U.card ≤ 3
    omega
  let Pred (n : ℕ) := (Fin n → Bool) → Prop
  let Wire {n : ℕ} (C : Circuit) (w : ℕ) : Pred n :=
    fun x => val C (List.ofFn x) w = true
  let UnderAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) w
  have underOr {n : ℕ} {C : Circuit} {w z : ℕ} (h : UnderAnd n C w)
      (path : Relation.ReflTransGen (OrStep n C) w z) : UnderAnd n C z := by
    obtain ⟨a,ha,op,b,hr⟩ := h
    exact ⟨a,ha,op,b,hr.trans path⟩
  have rawValue {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {limit w : ℕ}
      (none : ∀ m ∈ mixing G C, limit ≤ m) (before : w < n+limit)
      (raw : (orIn n C w).Nonempty) (x : Fin n → Bool) :
      Wire C w x ↔ ∃ t ∈ orIn n C w, x t = true := by
    constructor
    · intro h
      obtain ⟨z,path,on,source⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp -congrConsts) w h
      rcases source with hz|⟨k,hk,rfl,notOr⟩
      · let t : Fin n := ⟨z,hz⟩
        exact ⟨t,reach_mem_orIn t path,(val_ofFn C x t) ▸ on⟩
      · have reach := reach_orReaches path k rfl hk
        have op := (ao.1 _ (gateAt_mem hk)).resolve_right notOr
        obtain ⟨m,hm,hr,_,_⟩ := mixingAlong (G := G) ao reach op raw
        have le := orStep_le (orReaches_reach m _ hr).1
        have := none m hm
        omega
    · rintro ⟨t,ht,on⟩
      exact reach_var_val x _ t (mem_orIn_reach _ ht) on
  have wireOr {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {r : ℕ} (rl : r < C.gates.length) (op : (gateAt C r).op = GateOp.or)
      (x : Fin n → Bool) :
      Wire C (n+r) x ↔ Wire C (opnd C r 0) x ∨ Wire C (opnd C r 1) x := by
    constructor
    · intro on
      obtain ⟨w,mem,_,west⟩ := (val_or (n := n) (by simp -congrConsts) rl op).mp on
      obtain ⟨b,rfl⟩ := inputsAsOpnd ao rl mem
      fin_cases b
      · exact Or.inl west
      · exact Or.inr west
    · intro on
      apply (val_or (n := n) (by simp -congrConsts) rl op).mpr
      rcases on with left|right
      · exact ⟨_,opndMem ao rl 0,opndBound ao rl 0,left⟩
      · exact ⟨_,opndMem ao rl 1,opndBound ao rl 1,right⟩
  have onlyMixEndpoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      {m a : ℕ} {b : Fin 2} (only : ∀ q ∈ mixing G C, q = m) (hm : m ∈ mixing G C)
      (ha : a ∈ tops G C) {p q : Fin n} (av : gateVal n C a (pairInput p q) = true)
      (path : OrReaches n C (opnd C a b) m) :
      ∃ w ∈ side C a (1-b), w = p ∨ w = q := by
    obtain ⟨al,op,sound⟩ := topData ha
    rcases operandSupport least.1 top al op
        ((andValOperands least.1 al op _).mp av (1-b)) with raw|⟨j,hj,reach,_⟩
    · exact raw
    obtain ⟨l,hl,ol,_,_⟩ := mixingAlong (G := G) least.1 reach (junkData hj).2.1
      (topSides empty ha (1-b))
    have eq := only l hl
    subst l
    exfalso
    apply (orData (mixingNotLam hm)).2.2
    intro x hx
    apply sound x ((andValOperands least.1 al op x).mpr ?_)
    intro k
    rcases opposite b k with rfl|rfl
    · exact reachVal path hx
    · exact reachVal ol hx
  have mixingEmptyInput {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {m : ℕ} (hm : m ∈ mixing G C) :
      ∃ b : Fin 2, ∀ d : Fin 2, side (n := n) C m d = ∅ ↔ d = b := by
    have mix := (Finset.mem_filter.mp hm).2
    change (side (n := n) C m 0 = ∅) ≠ (side (n := n) C m 1 = ∅) at mix
    by_cases h0 : side (n := n) C m 0 = ∅
    · have h1 : side (n := n) C m 1 ≠ ∅ := fun h => mix (propext ⟨fun _ => h,fun _ => h0⟩)
      exact ⟨0,fun d => by fin_cases d <;> simp -congrConsts [h0,h1]⟩
    · have h1 : side (n := n) C m 1 = ∅ := by
        by_contra hn
        exact mix (propext ⟨fun h => (h0 h).elim,fun h => (hn h).elim⟩)
      exact ⟨1,fun d => by fin_cases d <;> simp -congrConsts [h0,h1]⟩
  have onlyMixWitness {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      {m : ℕ} (hm : m ∈ mixing G C) (only : ∀ q ∈ mixing G C, q = m) {c : Fin n}
      (rawC : c ∈ orIn n C (n+m)) {b : Fin 2} (emptyAt : ∀ d : Fin 2, side (n := n) C m d = ∅ ↔ d = b)
      {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
      UnderAnd n C (opnd C m b) ∧ ∃ w v : Fin n, e = s(w,v) ∧ Wire C (opnd C m b) (pairInput w v) ∧
        (G.deleteEdges ↑(Ustar G C)).Adj c w ∧
          ∀ x : Fin n → Bool, x w = true → Wire C (opnd C m b) x → graphFun G ∅ x = true := by
    induction e using Sym2.ind with
    | _ p q =>
      obtain ⟨a,ha,d,j,hj,av,hr,jv⟩ := residualTrace least top he
      obtain ⟨k,hk,ak,kj,_⟩ := mixingAlong (G := G) least.1 hr (junkData hj).2.1
        (topSides empty ha d)
      have eq := only k hk
      subst k
      have mr := orData (mixingNotLam hm)
      have ja := junkData hj
      have jm : j ≠ m := by
        rintro rfl
        simp -congrConsts [mr.2.1] at ja
      obtain ⟨_,same|⟨_,t,ht,lt,tj⟩⟩ := (orReaches_iff n C m j).mp kj
      · exact (jm same).elim
      obtain ⟨i,rfl⟩ := inputsAsOpnd least.1 mr.1 ht
      have ei : side (n := n) C m i = ∅ := by
        by_contra non
        obtain ⟨z,hz,zr,_,_⟩ := mixingAlong (G := G) least.1 tj ja.2.1
          (Finset.nonempty_iff_ne_empty.mpr non)
        have mle := orStep_le (orReaches_reach z _ zr).1
        have := only z hz
        omega
      have ib := (emptyAt i).mp ei
      subst i
      have child : Wire C (opnd C m b) (pairInput p q) := reachVal tj jv
      have path := (orReaches_reach m _ ak).1
      have cside : c ∈ side C a d := reach_mem_orIn c (path.trans (mem_orIn_reach c rawC))
      refine ⟨⟨a,(topData ha).1,(topData ha).2.1,d,
        path.trans (Relation.ReflTransGen.single (orStepOpnd least.1 mr.1 mr.2.1 b))⟩,?_⟩
      obtain ⟨w,hw,ends⟩ := onlyMixEndpoint least top empty only hm ha av ak
      have sound (x : Fin n → Bool) (wx : x w = true) (on : Wire C (opnd C m b) x) :
          graphFun G ∅ x = true := by
        apply firingTop least.1 ha path hw x _ wx
        exact (val_or (n := n) (by simp -congrConsts) mr.1 mr.2.1).mpr
          ⟨_,opndMem least.1 mr.1 b, opndBound least.1 mr.1 b,on⟩
      rcases ends with rfl|rfl
      · exact ⟨_,_,rfl,child,cleanAdj least.1 ha d cside hw,sound⟩
      · have swap (a b : Fin n) : pairInput a b = pairInput b a := by funext t; simp -congrConsts [pairInput_d,or_comm]
        exact ⟨_,_,Sym2.eq_swap,by rwa [swap],cleanAdj least.1 ha d cside hw,sound⟩
  have traceMono {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {x y : Fin n → Bool}
      (xy : ∀ t, x t = true → y t = true) : ∀ w < n+C.gates.length, Wire C w x → Wire C w y := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro bound on
      by_cases input : w < n
      · let t : Fin n := ⟨w,input⟩
        change val C (List.ofFn y) t.val = true
        change val C (List.ofFn x) t.val = true at on
        rw [val_ofFn] at on ⊢
        exact xy t on
      obtain ⟨i,rfl⟩ : ∃ i, w = n+i := ⟨w-n,by omega⟩
      have vi : i < C.gates.length := by omega
      have child (b : Fin 2) := ih _ (opndBound ao vi b) ((opndBound ao vi b).trans bound)
      rcases ao.1 _ (gateAt_mem vi) with a|o
      · apply (andValOperands ao vi a y).mpr
        exact fun b => child b ((andValOperands ao vi a x).mp on b)
      · apply (wireOr ao vi o y).mpr
        exact ((wireOr ao vi o x).mp on).imp (child 0) (child 1)
  let crossSet {n : ℕ} (C : Circuit) (a : ℕ) : Finset (Sym2 (Fin n)) :=
    (side (n := n) C a 0 ×ˢ side (n := n) C a 1).image fun p => s(p.1,p.2)
  have orientedTopSet {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (h4 : NoFourCycle G) (empty : centreless G C = ∅)
      {a : ℕ} (ha : a ∈ tops G C) :
      ∃ b : Fin 2, ∃ c : Fin n, side C a b = {c} ∧
        crossSet (n := n) C a = (side C a (1-b)).image (fun t => s(c,t)) := by
    have non (b : Fin 2) := topSides empty ha b
    have oneSide : (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1 := by
      by_contra! bad
      obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp bad.1
      obtain ⟨u,hu,v,hv,diff⟩ := Finset.one_lt_card.mp bad.2
      exact diff (commonUnique h4 ne (topAdj ao ha hp hu) (topAdj ao ha hq hu)
        (topAdj ao ha hp hv) (topAdj ao ha hq hv))
    have get (b : Fin 2) (h : (side (n := n) C a b).card ≤ 1) : ∃ c, side (n := n) C a b = {c} :=
      Finset.card_eq_one.mp (by have := Finset.card_pos.mpr (non b); omega)
    rcases oneSide with h|h
    · obtain ⟨c,hc⟩ := get 0 h
      refine ⟨0,c,hc,?_⟩
      change crossSet C a = (side (n := n) C a 1).image _
      ext e
      simp -congrConsts [crossSet,hc]
    · obtain ⟨c,hc⟩ := get 1 h
      refine ⟨1,c,hc,?_⟩
      change crossSet C a = (side (n := n) C a 0).image _
      ext e
      simp -congrConsts [crossSet,hc,Sym2.eq_swap]
  have saturatedTops (C : Circuit) (ao : IsAO2 26 C) (empty : centreless plane C = ∅)
      (twelve : (tops plane C).card = 12) (four : (Ustar plane C).card = 4) :
      ∀ a ∈ tops plane C, ∃ b : Fin 2, ∃ c : Fin 26, side C a b = {c} ∧
        side C a (1-b) = Finset.univ.filter (plane.Adj c) := by
    let T := tops plane C
    have shape {a} (ha : a ∈ T) := orientedTopSet ao planeFour empty ha
    have leafSub {a} (ha : a ∈ T) {b : Fin 2} {c : Fin 26} (hc : side C a b = {c}) :
        side C a (1-b) ⊆ Finset.univ.filter (plane.Adj c) := fun y hy =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(SimpleGraph.deleteEdges_adj.mp
        (cleanAdj ao ha b (hc ▸ Finset.mem_singleton_self _) hy)).1⟩
    have small (a : ℕ) (ha : a ∈ T) : (crossSet (n := 26) C a).card ≤ 4 := by
      obtain ⟨b,c,hc,eq⟩ := shape ha
      rw [eq]
      exact Finset.card_image_le.trans ((Finset.card_le_card (leafSub ha hc)).trans (degree_four c).le)
    have outside : plane.edgeFinset \ Ustar plane C ⊆ T.biUnion (crossSet (n := 26) C) := by
      intro e he
      obtain ⟨graph,notU⟩ := Finset.mem_sdiff.mp he
      by_contra miss
      exact notU (Finset.mem_sdiff.mpr ⟨graph,miss⟩)
    have n48 : (plane.edgeFinset \ Ustar plane C).card = 48 := by
      rw [Finset.card_sdiff_of_subset (show Ustar plane C ⊆ plane.edgeFinset from Finset.sdiff_subset),planeCount,four]
    intro a ha
    have size : 4 ≤ (crossSet (n := 26) C a).card := by
      have all := (Finset.card_le_card outside).trans Finset.card_biUnion_le
      have ea : (T.erase a).card = 11 := by have h := Finset.card_erase_add_one (show a ∈ T from ha); change T.card = 12 at twelve; omega
      have rest : (∑ t ∈ T.erase a, (crossSet (n := 26) C t).card) ≤ 44 := by
        calc
          _ ≤ ∑ _t ∈ T.erase a, 4 := Finset.sum_le_sum (fun t ht => small t (Finset.mem_of_mem_erase ht))
          _ = _ := by simp -congrConsts [ea]
      have sum := Finset.add_sum_erase T (fun t => (crossSet (n := 26) C t).card) ha
      omega
    obtain ⟨b,c,hc,eq⟩ := shape ha
    refine ⟨b,c,hc,Finset.eq_of_subset_of_card_le (leafSub ha hc) ?_⟩
    rw [degree_four]
    rw [eq] at size
    exact size.trans Finset.card_image_le
  have supportsStar {v : Fin 26} {U : Finset (Sym2 (Fin 26))}
      (sub : U ⊆ plane.edgeFinset) (four : U.card = 4) (star : ∀ e ∈ U, v ∈ e) :
      ∀ l : Fin 26, plane.Adj v l → s(v,l) ∈ U := by
    have inside : U ⊆ incidentEdges v := fun e he => edge_incident (SimpleGraph.mem_edgeFinset.mp (sub he)) (star e he)
    have eq := Finset.eq_of_subset_of_card_le inside (four ▸ incident_count v)
    exact fun l h => eq ▸ incident_mem h
  have saturatedCenterData {C : Circuit} (ao : IsAO2 26 C)
      {a : ℕ} (ha : a ∈ tops plane C) {b : Fin 2} {c v : Fin 26}
      (center : side C a b = {c}) (leaves : side C a (1-b) = Finset.univ.filter (plane.Adj c))
      (star : ∀ l : Fin 26, plane.Adj v l → s(v,l) ∈ Ustar plane C) :
      c ≠ v ∧ ¬ plane.Adj c v ∧ val C (List.ofFn (pairInput v v)) (opnd C a b) = false := by
    have clean (y : Fin 26) (hy : plane.Adj c y) : (plane.deleteEdges ↑(Ustar plane C)).Adj c y :=
      cleanAdj ao ha b (center ▸ Finset.mem_singleton_self c) (leaves ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)
    have cv : c ≠ v := by
      rintro rfl
      obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [degree_four c]; decide : 0 < (Finset.univ.filter (plane.Adj c)).card)
      have adj := (Finset.mem_filter.mp hw).2
      exact (SimpleGraph.deleteEdges_adj.mp (clean w adj)).2 (star w adj)
    have apart : ¬plane.Adj c v := fun h => (SimpleGraph.deleteEdges_adj.mp (clean v h)).2 (Sym2.eq_swap ▸ star c h.symm)
    refine ⟨cv,apart,Bool.eq_false_iff.mpr ?_⟩
    intro on
    have all (w : Fin 26) (hw : plane.Adj c w) : plane.Adj v w := by
      have leaf : w ∈ side C a (1-b) := leaves ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
      have up : val C (List.ofFn (pairInput v w)) (opnd C a b) = true := by
        apply traceMono ao (x := pairInput v v) (y := pairInput v w) _ _ ((opndBound ao (topData ha).1 b).trans (by have := (topData ha).1; omega)) on
        intro t ht
        rcases (pairInput_true v v t).mp ht with rfl|rfl <;> exact pairInput_left _ _
      apply (graphFun_pair plane v w).mp
      apply (topData ha).2.2 _ ((andValOperands ao (topData ha).1 (topData ha).2.1 _).mpr ?_)
      intro i
      rcases opposite b i with rfl|rfl
      · exact up
      · exact sideVal leaf (pairInput_right _ _)
    obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by rw [degree_four c]; decide : 1 < (Finset.univ.filter (plane.Adj c)).card)
    exact ne (commonUnique planeFour cv (Finset.mem_filter.mp hp).2 (all _ (Finset.mem_filter.mp hp).2)
      (Finset.mem_filter.mp hq).2 (all _ (Finset.mem_filter.mp hq).2))
  have collectLeaves (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
      (empty : centreless plane C = ∅) (twelve : (tops plane C).card = 12)
      (four : (Ustar plane C).card = 4) (v : Fin 26)
      (star : ∀ l : Fin 26, plane.Adj v l → s(v,l) ∈ Ustar plane C) :
      ∃ W : Finset ℕ, W.card ≤ (junk plane C).card ∧ (∀ w ∈ W, w < 26+C.gates.length) ∧
        Finset.univ.filter (plane.Adj v) ⊆ W.biUnion (orIn 26 C) := by
    classical
    let x := pairInput v v
    have operand {j} (hj : j ∈ junk plane C) (off : gateVal 26 C j x = false) :
        ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
      by_contra hn
      obtain ⟨jl,op,_⟩ := junkData hj
      have h := (andValOperands least.1 jl op x).mpr (fun b =>
        Bool.eq_true_of_not_eq_false (fun hb => hn ⟨b,hb⟩))
      exact Bool.false_ne_true (off.symm.trans h)
    let f (j : ℕ) : Fin 2 := if h : j ∈ junk plane C ∧ gateVal 26 C j x = false then (operand h.1 h.2).choose else 0
    let W := (junk plane C).image fun j => opnd C j (f j)
    refine ⟨W,Finset.card_image_le,?_,?_⟩
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      have jl := (junkData hj).1
      exact (opndBound least.1 jl _).trans (by omega)
    · intro l hl
      have adj := (Finset.mem_filter.mp hl).2
      have hidden := star l adj
      have route : ∀ j, j ∈ junk plane C → gateVal 26 C j x = false →
          gateVal 26 C j (pairInput v l) = true → l ∈ W.biUnion (orIn 26 C) := by
        intro j
        induction j using Nat.strong_induction_on with
        | _ j ih =>
          intro hj off on
          have neg : val C (List.ofFn x) (opnd C j (f j)) = false := by
            have h := And.intro hj off
            simpa -congrConsts only [f,dif_pos h] using (operand hj off).choose_spec
          have data := junkData hj
          have pos := (andValOperands least.1 data.1 data.2.1 _).mp on (f j)
          rcases operandSupport least.1 top data.1 data.2.1 pos with ⟨t,ht,eq⟩|⟨k,hk,hr,kv⟩
          · rcases eq with rfl|rfl
            · have yes := sideVal ht (pairInput_left t t)
              exact (Bool.false_ne_true (neg.symm.trans yes)).elim
            · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image.mpr ⟨j,hj,rfl⟩,ht⟩
          · have le := orStep_le (orReaches_reach k _ hr).1
            have lt := opndBound least.1 data.1 (f j)
            exact ih k (by omega) hk (Bool.eq_false_iff.mpr
              (fun on => Bool.false_ne_true (neg.symm.trans (reachVal hr on)))) kv
      obtain ⟨a,ha,accepted⟩ := acceptedTop least adj
      obtain ⟨b,c,center,leaves⟩ := saturatedTops C least.1 empty twelve four a ha
      obtain ⟨cv,notAdj,off⟩ := saturatedCenterData least.1 ha center leaves star
      have data := topData ha
      have pos := (andValOperands least.1 data.1 data.2.1 _).mp accepted b
      rcases operandSupport least.1 top data.1 data.2.1 pos with ⟨t,ht,which⟩|⟨j,hj,hr,hv⟩
      · rw [center,Finset.mem_singleton] at ht
        subst t
        rcases which with eq|eq
        · exact (cv eq).elim
        · exact (notAdj (eq ▸ adj.symm)).elim
      · exact route j hj (Bool.eq_false_iff.mpr
          (fun on => Bool.false_ne_true (off.symm.trans (reachVal hr on)))) hv
  have shapeStarSmall {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {U : Finset (Sym2 (Fin n))} (h4 : NoFourCycle G) {v : Fin n}
      (L : Finset (Fin n)) (adj : ∀ p ∈ L, G.Adj v p) (hidden : ∀ p ∈ L, s(v,p) ∈ U)
      {S : Finset (Fin n)} (shape : Shape G U S) : (S ∩ L).card ≤ 1 := by
    rcases shape with small|⟨z,hz⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans small
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨sa,la⟩ := Finset.mem_inter.mp ha
      obtain ⟨sb,lb⟩ := Finset.mem_inter.mp hb
      by_contra ne
      have vz := commonUnique h4 ne (adj a la).symm (adj b lb).symm
        (SimpleGraph.deleteEdges_adj.mp (hz a sa)).1 (SimpleGraph.deleteEdges_adj.mp (hz b sb)).1
      exact (SimpleGraph.deleteEdges_adj.mp (vz.symm ▸ (hz a sa).symm)).2 (hidden a la)
  have collapseRaw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (q : ℕ)
      (only : ∀ k ∈ orN G C \ lam G C, k ∉ mixing G C → k = q) :
      ∀ w < n+C.gates.length, Shape G (Ustar G C) (orIn n C w) ∨ n+q ≤ w ∧ orIn n C w = orIn n C (n+q) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro wc
      by_cases eq : ∃ k ∈ orN G C \ lam G C, w = n+k
      · obtain ⟨k,hk,rfl⟩ := eq
        by_cases mix : k ∈ mixing G C
        · obtain ⟨b,he,_⟩ := mixingCopies ao mix
          have lt := opndBound ao (orData hk).1 b
          rcases ih _ lt (lt.trans wc) with shape|⟨le,same⟩
          · exact Or.inl (he ▸ shape)
          · exact Or.inr ⟨le.trans lt.le,he.trans same⟩
        · have := only k hk mix
          subst k
          exact Or.inr ⟨le_rfl,rfl⟩
      · exact Or.inl (rawShapeExcept ao wc (fun k hk h => eq ⟨k,hk,h⟩))
  have twoRoots {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (h4 : NoFourCycle G) (q : ℕ) (hq : q ∈ orN G C \ lam G C)
      (only : ∀ k ∈ orN G C \ lam G C, k ∉ mixing G C → k = q)
      (W : Finset ℕ) (two : W.card ≤ 2) (valid : ∀ w ∈ W, w < n+C.gates.length)
      (L : Finset (Fin n)) {v : Fin n} (adj : ∀ p ∈ L, G.Adj v p) (hidden : ∀ p ∈ L, s(v,p) ∈ Ustar G C)
      (cover : L ⊆ W.biUnion (orIn n C)) : L.card ≤ 3 := by
    classical
    let S (w : ℕ) := orIn n C w ∩ L
    have small {w : ℕ} (h : Shape G (Ustar G C) (orIn n C w)) : (S w).card ≤ 1 :=
      shapeStarSmall h4 L adj hidden h
    have qt := orData hq
    have child (b : Fin 2) : (S (opnd C q b)).card ≤ 1 := by
      have lt := opndBound ao qt.1 b
      rcases collapseRaw ao q only _ (lt.trans (by omega)) with h|⟨le,_⟩
      · exact small h
      · omega
    have qsize : (S (n+q)).card ≤ 2 := by
      have sub : S (n+q) ⊆ S (opnd C q 0) ∪ S (opnd C q 1) := by
        intro p hp
        obtain ⟨mem,hL⟩ := Finset.mem_inter.mp hp
        rw [orInOr ao qt.1 qt.2.1] at mem
        rcases Finset.mem_union.mp mem with a|b
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨a,hL⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨b,hL⟩)
      have hc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      have c0 := child 0
      have c1 := child 1
      omega
    have sub : L ⊆ W.biUnion S := by
      intro p hp
      obtain ⟨w,hw,mem⟩ := Finset.mem_biUnion.mp (cover hp)
      exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨mem,hp⟩⟩
    by_cases large : ∃ w ∈ W, ¬(S w).card ≤ 1
    · obtain ⟨w,hw,big⟩ := large
      have eq {k : ℕ} (hk : k ∈ W) (b : ¬(S k).card ≤ 1) : S k = S (n+q) := by
        rcases collapseRaw ao q only k (valid k hk) with h|⟨_,e⟩
        · exact (b (small h)).elim
        · exact congrArg (fun X => X ∩ L) e
      let A := (W.erase w).filter fun k => (S k).card ≤ 1
      have ac : A.card ≤ 1 := by
        have c := Finset.card_erase_add_one hw
        have s : A.card ≤ (W.erase w).card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
      have sub' : L ⊆ S (n+q) ∪ A.biUnion S := by
        intro p hp
        obtain ⟨k,hk,mem⟩ := Finset.mem_biUnion.mp (sub hp)
        by_cases b : (S k).card ≤ 1
        · have diff : k ≠ w := fun e => big (e ▸ b)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨diff,hk⟩,b⟩,mem⟩)
        · exact Finset.mem_union_left _ (eq hk b ▸ mem)
      have h := (Finset.card_le_card sub').trans (Finset.card_union_le _ _)
      have c := cardBiUnionLeOne A S (fun k hk => (Finset.mem_filter.mp hk).2)
      omega
    · have h := (Finset.card_le_card sub).trans (cardBiUnionLeOne W S (fun w hw =>
          by by_contra! b; exact large ⟨w,hw,by omega⟩))
      omega
  let Paid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
    ∃ j, w = n+j ∧ j ∈ junk G C ∪ (orN G C \ lam G C)
  let PaidStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w z : ℕ) : Prop :=
    Paid G C w ∧ ∃ b : Fin 2, z = opnd C (w-n) b
  have paidBound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {w z : ℕ} (h : PaidStep G C w z) : z < w := by
    obtain ⟨⟨j,rfl,hj⟩,b,rfl⟩ := h
    have hl : j < C.gates.length := ((Finset.mem_union.mp hj).elim (fun h => (junkData h).1) (fun h => (orData h).1))
    simpa -congrConsts using opndBound ao hl b
  have paidUnder {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) {w z : ℕ} (h : PaidStep G C w z) (under : UnderAnd n C w) :
      UnderAnd n C z := by
    obtain ⟨⟨j,rfl,hj⟩,b,rfl⟩ := h
    simp -congrConsts only [Nat.add_sub_cancel_left]
    rcases Finset.mem_union.mp hj with junk|orr
    · exact ⟨j,(junkData junk).1,(junkData junk).2.1,b,.refl⟩
    · have v := orData orr
      exact underOr under (Relation.ReflTransGen.single (orStepOpnd ao v.1 v.2.1 b))
  have terminalValue {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (top : TopForm G C) {m w : ℕ}
      (first : ∀ q ∈ mixing G C, m ≤ q) (before : w < n+m) (valid : w < n+C.gates.length)
      (under : UnderAnd n C w) (free : ¬Paid G C w) :
      Shape G (Ustar G C) (orIn n C w) ∧ (∀ x, Wire C w x ↔ ∃ t ∈ orIn n C w, x t = true) := by
    refine ⟨rawShapeExcept ao valid (fun k hk eq => free ⟨k,eq,Finset.mem_union_right _ hk⟩),?_⟩
    intro x
    by_cases non : (orIn n C w).Nonempty
    · exact rawValue ao first before non x
    refine ⟨fun on => ?_,fun h => (non (Exists.elim h fun t ht => ⟨t, ht.1⟩)).elim⟩
    exfalso
    obtain ⟨z,path,_,source⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp -congrConsts) w on
    rcases source with hz|⟨k,kl,rfl,notOr⟩
    · exact non ⟨⟨z,hz⟩,reach_mem_orIn ⟨z,hz⟩ path⟩
    have andK := (ao.1 _ (gateAt_mem kl)).resolve_right notOr
    obtain ⟨a,al,op,b,aw⟩ := under
    have hj := operandOrAndJunk ao top al op (reach_orReaches (aw.trans path) k rfl kl) andK
    have reach := reach_orReaches path k rfl kl
    obtain ⟨l,rfl⟩ : ∃ l, w = n+l := ⟨w-n,by have := reach.1; omega⟩
    have vl : l < C.gates.length := by omega
    rcases ao.1 _ (gateAt_mem vl) with hop|hop
    · have jl := operandOrAndJunk ao top al op (reach_orReaches aw l rfl vl) hop
      exact free ⟨l,rfl,Finset.mem_union_left _ jl⟩
    · have nb : ¬BelowF G C l := by
        intro hb
        obtain ⟨_,_,y,ky,off⟩ := junkData hj
        exact Bool.false_ne_true (off.symm.trans (hb y (reachVal reach ky)))
      have onN : l ∈ orN G C := by
        simpa -congrConsts only [orN_d,gatesWhere_d,Finset.mem_filter,Finset.mem_range] using And.intro vl ⟨hop,nb⟩
      have notL : l ∉ lam G C := by
        intro h
        obtain ⟨_,⟨t,ht⟩,_,_⟩ := Finset.mem_filter.mp h
        exact non ⟨t,orInTrans (Relation.ReflTransGen.single (orStepOpnd ao vl hop 0)) ht⟩
      exact free ⟨l,rfl,Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨onN,notL⟩)⟩
  have firstCut {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} (ao : IsAO2 n C) (top : TopForm G C) {m root : ℕ}
      (hm : m ∈ mixing G C) (first : ∀ q ∈ mixing G C, m ≤ q)
      (before : root < n+m) (rootUnder : UnderAnd n C root) :
      ∃ F : Finset ℕ, F.card ≤ (junk G C).card + (orN G C \ lam G C).card ∧
        (∀ z ∈ F, Shape G (Ustar G C) (orIn n C z)) ∧
        ∀ x y : Fin n → Bool, Wire C root x → ¬Wire C root y →
          ∃ z ∈ F, (∃ t ∈ orIn n C z, x t = true) ∧ ∀ t ∈ orIn n C z, y t = false := by
    classical
    let reach := Relation.ReflTransGen (PaidStep G C)
    let D := (Finset.range (root+1)).filter fun z => reach root z
    let I := D.filter (Paid G C)
    let F := D \ I
    have decreases {w z : ℕ} (h : reach w z) : z ≤ w := by
      induction h with
      | refl => exact le_rfl
      | tail _ step ih => exact (paidBound ao step).le.trans ih
    have mem {z} : z ∈ D ↔ reach root z := by
      exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (decreases h)),h⟩⟩
    have under {z} (h : reach root z) : UnderAnd n C z := by
      induction h with
      | refl => exact rootUnder
      | tail _ step ih => exact paidUnder ao step ih
    have rootIn : root ∈ D := mem.mpr .refl
    have children : D.erase root ⊆ I.biUnion (fun w => {opnd C (w-n) 0,opnd C (w-n) 1}) := by
      intro z hz
      obtain ⟨ne,hz⟩ := Finset.mem_erase.mp hz
      rcases Relation.ReflTransGen.cases_tail (mem.mp hz) with eq|⟨w,wr,step⟩
      · exact (ne eq).elim
      · obtain ⟨paid,b,rfl⟩ := step
        refine Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨mem.mpr wr,paid⟩,?_⟩
        fin_cases b <;> simp -congrConsts
    have fork := (Finset.card_le_card children).trans Finset.card_biUnion_le
    have count : (∑ w ∈ I, ({opnd C (w-n) 0,opnd C (w-n) 1} : Finset ℕ).card) ≤ 2*I.card := by
      calc
        _ ≤ ∑ _ ∈ I, 2 := Finset.sum_le_sum (fun w _ => (Finset.card_insert_le _ _).trans (by simp -congrConsts))
        _ = _ := by simp -congrConsts [Nat.mul_comm]
    have isub : I ⊆ D := Finset.filter_subset _ _
    have frontier : F.card ≤ I.card+1 := by
      have er := Finset.card_erase_add_one rootIn
      have di := Finset.card_sdiff_add_card_eq_card isub
      change (D \ I).card ≤ I.card+1
      omega
    let R := orN G C \ lam G C
    have gates : I ⊆ (junk G C ∪ R.erase m).image (fun j => n+j) := by
      intro w hw
      obtain ⟨din,j,eq,hj⟩ := Finset.mem_filter.mp hw
      have le := decreases (mem.mp din)
      refine Finset.mem_image.mpr ⟨j,?_,eq.symm⟩
      rcases Finset.mem_union.mp hj with jj|rr
      · exact Finset.mem_union_left _ jj
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by omega,rr⟩)
    have ic := (Finset.card_le_card gates).trans (Finset.card_image_le.trans (Finset.card_union_le _ _))
    have mr : m ∈ R := mixingNotLam hm
    have er := Finset.card_erase_add_one mr
    have term {z : ℕ} (hz : z ∈ F) := by
      obtain ⟨din,notI⟩ := Finset.mem_sdiff.mp hz
      have path := mem.mp din
      have le := decreases path
      have mv := (orData mr).1
      exact terminalValue ao top first (by omega : z < n+m) (by omega : z < n+C.gates.length)
        (under path) (fun paid => notI (Finset.mem_filter.mpr ⟨din,paid⟩))
    refine ⟨F,by change F.card ≤ (junk G C).card + R.card; omega,fun z hz => (term hz).1,?_⟩
    intro x y on off
    have witness : ∀ w, w ∈ D → Wire C w x → ¬Wire C w y → ∃ z ∈ F, Wire C z x ∧ ¬Wire C z y := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro din wx wy
        by_cases paid : Paid G C w
        · obtain ⟨j,rfl,hj⟩ := paid
          have down : ∃ b : Fin 2, Wire C (opnd C j b) x ∧ ¬Wire C (opnd C j b) y := by
            rcases Finset.mem_union.mp hj with jj|rr
            · have jd := junkData jj
              have tx := (andValOperands ao jd.1 jd.2.1 x).mp wx
              by_contra! missing
              exact wy ((andValOperands ao jd.1 jd.2.1 y).mpr (fun b => missing b (tx b)))
            · have rd := orData rr
              rcases (wireOr ao rd.1 rd.2.1 x).mp wx with a|b
              · exact ⟨0,a,fun h => wy ((wireOr ao rd.1 rd.2.1 y).mpr (Or.inl h))⟩
              · exact ⟨1,b,fun h => wy ((wireOr ao rd.1 rd.2.1 y).mpr (Or.inr h))⟩
          obtain ⟨b,bx,by'⟩ := down
          have step : PaidStep G C (n+j) (opnd C j b) := ⟨⟨j,rfl,hj⟩,b,by simp -congrConsts⟩
          exact ih _ (paidBound ao step) (mem.mpr ((mem.mp din).tail step)) bx by'
        · exact ⟨w,Finset.mem_sdiff.mpr ⟨din,fun h => paid (Finset.mem_filter.mp h).2⟩,wx,wy⟩
    obtain ⟨z,hz,zx,zy⟩ := witness root rootIn on off
    exact ⟨z,hz,((term hz).2 x).mp zx,fun t ht => Bool.eq_false_iff.mpr
      (fun h => zy (((term hz).2 y).mpr ⟨t,ht,h⟩))⟩
  let pointAt (i : Fin 13) : Fin 26 := ⟨i.val,by omega⟩
  let lineAt (d : Fin 4) (i : Fin 13) : Fin 26 :=
    ⟨13 + (i.val + 13 - ([0,1,3,9] : List ℕ).getD d.val 0) % 13,by omega⟩
  have matchingAll : ∀ (d : Fin 4) (i : Fin 13),
      plane.Adj (pointAt i) (lineAt d i) ∧ matchIndex d (pointAt i) = i ∧
      matchIndex d (lineAt d i) = i := by
    dsimp only [pointAt,lineAt,matchIndex,plane]
    decide
  have matchingThrough : ∀ c w : Fin 26, plane.Adj c w →
      ∃ (d : Fin 4) (i : Fin 13), s(c,w) = s(pointAt i,lineAt d i) := by
    dsimp only [pointAt,lineAt,plane]
    decide
  have coverFan {U : Finset (Sym2 (Fin 26))} {W K : Finset (Fin 26)} {c w : Fin 26}
      (hw : w ∈ W) (clean : (plane.deleteEdges ↑U).Adj c w)
      (owners : ∀ e ∈ U, ∃ u ∈ W, u ∈ e)
      (cover : (plane.deleteEdges ↑U).IsVertexCover (K : Set (Fin 26))) : 14 ≤ K.card + W.card := by
    obtain ⟨d,j,hj⟩ := matchingThrough c w (SimpleGraph.deleteEdges_adj.mp clean).1
    have val {v : Fin 26} {i : Fin 13} (h : v ∈ s(pointAt i,lineAt d i)) : matchIndex d v = i := by
      rcases Sym2.mem_iff.mp h with rfl|rfl
      · exact (matchingAll d i).2.1
      · exact (matchingAll d i).2.2
    have wj : matchIndex d w = j := val (hj ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : w ∈ s(c,w)))
    have sub : (Finset.univ : Finset (Fin 13)) ⊆ K.image (matchIndex d) ∪ (W.erase w).image (matchIndex d) := by
      intro i _
      let a := pointAt i
      let b := lineAt d i
      by_cases bad : s(a,b) ∈ U
      · obtain ⟨u,hu,uv⟩ := owners _ bad
        have vi := val uv
        have ne : u ≠ w := by
          rintro rfl
          have ij := vi.symm.trans wj
          have bad' : s(pointAt i,lineAt d i) ∈ U := bad
          rw [ij,←hj] at bad'
          exact (SimpleGraph.deleteEdges_adj.mp clean).2 bad' 
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,Finset.mem_erase.mpr ⟨ne,hu⟩,vi⟩)
      · apply Finset.mem_union_left
        rcases cover (SimpleGraph.deleteEdges_adj.mpr ⟨(matchingAll d i).1,bad⟩) with ha|hb
        · exact Finset.mem_image.mpr ⟨a,ha,(matchingAll d i).2.1⟩
        · exact Finset.mem_image.mpr ⟨b,hb,(matchingAll d i).2.2⟩
    have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have a := Finset.card_image_le (f := matchIndex d) (s := K)
    have b := Finset.card_image_le (f := matchIndex d) (s := W.erase w)
    have er := Finset.card_erase_add_one hw
    simp -congrConsts only [Finset.card_univ,Fintype.card_fin] at h
    omega
  have cardSeparation {α β : Type} [DecidableEq α] [DecidableEq β] (W : Finset α) (A : Finset β)
      (contains : β → α → Prop) [DecidableRel contains] (small : W.card ≤ 4) (two : 2 ≤ W.card)
      (sep : ∀ w ∈ W, ∀ u ∈ W, w ≠ u → ∃ z ∈ A, contains z w ∧ ¬contains z u) : W.card ≤ A.card := by
    classical
    by_contra! lt
    let k : Fin 5 := ⟨W.card,by omega⟩
    let we : W ≃ Fin W.card := Fintype.equivFinOfCardEq (Fintype.card_coe W)
    let ae : A ≃ Fin A.card := Fintype.equivFinOfCardEq (Fintype.card_coe A)
    let f (i : Fin k.val) (t : Fin (k.val-1)) := if h : t.val < A.card then
      decide (contains (ae.symm ⟨t.val,h⟩).val (we.symm i).val) else false
    apply bitSeparation k two f
    intro i j ne
    have diff : (we.symm i).val ≠ (we.symm j).val := fun h => ne (we.symm.injective (Subtype.ext h))
    obtain ⟨z,hz,yes,no⟩ := sep _ (we.symm i).property _ (we.symm j).property diff
    let t := ae ⟨z,hz⟩
    have tk : t.val < k.val-1 := by have := t.isLt; dsimp [k]; omega
    refine ⟨⟨t.val,tk⟩,?_,?_⟩ <;> simp -congrConsts [f,t,t.isLt,yes,no]
  have fanShapes {U : Finset (Sym2 (Fin 26))} {W V : Finset (Fin 26)} {c : Fin 26}
      {F : Finset ℕ} (S : ℕ → Finset (Fin 26))
      (leafCount : U.card ≤ V.card) (two : 2 ≤ W.card) (small : W.card ≤ 4)
      (center : ∀ w ∈ W, (plane.deleteEdges ↑U).Adj c w)
      (allW : ∀ w ∈ W, ∃ v ∈ V, s(w,v) ∈ U)
      (allV : ∀ v ∈ V, ∃ w ∈ W, s(w,v) ∈ U)
      (sub : U ⊆ plane.edgeFinset) (shapes : ∀ z ∈ F, Shape plane U (S z))
      (witness : ∀ w ∈ W, ∀ v ∈ V, s(w,v) ∈ U → ∀ u ∈ W,
         ∃ z ∈ F, (w ∈ S z ∨ v ∈ S z) ∧ u ∉ S z ∧ ∀ t ∈ V, ¬plane.Adj u t → t ∉ S z) :
      U.card + W.card ≤ F.card := by
    classical
    have adj {w v} (e : s(w,v) ∈ U) : plane.Adj w v := SimpleGraph.mem_edgeFinset.mp (sub e)
    have wc {w} (h : w ∈ W) := planeBip c w (SimpleGraph.deleteEdges_adj.mp (center w h)).1
    have colors {v} (h : v ∈ V) : color26 v = color26 c := by
      obtain ⟨w,hw,e⟩ := allV v h
      have cb := wc hw
      have vb := planeBip v w (adj e).symm
      have same : ∀ a b d : Bool, a ≠ b → d ≠ b → d = a := by decide
      exact same _ _ _ cb vb
    have uniq {w u v} (hw : w ∈ W) (hu : u ∈ W) (ev : s(w,v) ∈ U) (av : plane.Adj u v) : u = w := by
      have cv : c ≠ v := by
        rintro rfl
        exact (SimpleGraph.deleteEdges_adj.mp (center w hw)).2 (Sym2.eq_swap ▸ ev)
      exact commonUnique planeFour cv (SimpleGraph.deleteEdges_adj.mp (center u hu)).1 av.symm
        (SimpleGraph.deleteEdges_adj.mp (center w hw)).1 (adj ev).symm
    have mono {z p q} (hz : z ∈ F) (hp : p ∈ S z) (hq : q ∈ S z) : color26 p = color26 q := by
      rcases shapes z hz with card|⟨a,nei⟩
      · rw [Finset.card_le_one.mp card _ hp _ hq]
      · have h := planeBip p a (SimpleGraph.deleteEdges_adj.mp (nei p hp)).1
        have l := planeBip q a (SimpleGraph.deleteEdges_adj.mp (nei q hq)).1
        have same : ∀ a b d : Bool, a ≠ d → b ≠ d → a = b := by decide
        exact same _ _ _ h l
    let A := F.filter fun z => ∃ w ∈ W, w ∈ S z
    have act : W.card ≤ A.card := by
      apply cardSeparation W A (fun z w => w ∈ S z) small two
      intro w hw u hu diff
      obtain ⟨v,hv,ev⟩ := allW w hw
      obtain ⟨z,hz,used,off,none⟩ := witness w hw v hv ev u hu
      have nos := none v hv (fun h => diff (uniq hw hu ev h).symm)
      have hit := used.resolve_right nos
      exact ⟨z,Finset.mem_filter.mpr ⟨hz,w,hw,hit⟩,hit,off⟩
    have leaf (v : Fin 26) (hv : v ∈ V) :
        ∃ z ∈ F \ A, v ∈ S z ∧ ∀ t ∈ V, t ∈ S z → t = v := by
      obtain ⟨w,hw,ev⟩ := allV v hv
      obtain ⟨z,hz,used,off,none⟩ := witness w hw v hv ev w hw
      have hit := used.resolve_left off
      have notA : z ∉ A := by
        intro h
        obtain ⟨_,u,hu,uz⟩ := Finset.mem_filter.mp h
        exact wc hu ((colors hv).symm.trans (mono hz hit uz))
      refine ⟨z,Finset.mem_sdiff.mpr ⟨hz,notA⟩,hit,?_⟩
      intro t ht ts
      by_contra diff
      have at' : plane.Adj w t := by by_contra no; exact none t ht no ts
      rcases shapes z hz with low|⟨u,cl⟩
      · exact diff (Finset.card_le_one.mp low _ ts _ hit)
      have c1 := SimpleGraph.deleteEdges_adj.mp (cl v hit)
      have c2 := SimpleGraph.deleteEdges_adj.mp (cl t ts)
      have uw := commonUnique planeFour diff c2.1 c1.1 at'.symm (adj ev).symm
      exact c1.2 (uw ▸ (Sym2.eq_swap ▸ ev))
    choose get hg hh only using leaf
    have inj : Function.Injective (fun t : V => (⟨get t.val t.property,hg t.val t.property⟩ : ↥(F \ A))) := by
      intro t v eq
      have eq' := congrArg Subtype.val eq
      apply Subtype.ext
      apply only v.val v.property t.val t.property
      change get t.val t.property = get v.val v.property at eq'
      rw [←eq']
      exact hh t.val t.property
    have card := Fintype.card_le_of_injective _ inj
    simp -congrConsts only [Fintype.card_coe] at card
    have af : A ⊆ F := Finset.filter_subset _ _
    have sum := Finset.card_sdiff_add_card_eq_card af
    omega
  have uniqueMixImpossible (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
      (empty : centreless plane C = ∅) (m : ℕ) (hm : m ∈ mixing plane C)
      (only : ∀ q ∈ mixing plane C, q = m) (large : 4 ≤ (Ustar plane C).card)
      (cost : (tops plane C).card + (junk plane C).card + (orN plane C \ lam plane C).card ≤ 13 + (Ustar plane C).card)
      (covers : ∀ K, IsMinCover (plane.deleteEdges ↑(Ustar plane C)) K → K.card ≤ (tops plane C).card) : False := by
    classical
    let U := Ustar plane C
    have sub : U ⊆ plane.edgeFinset := Finset.sdiff_subset
    obtain ⟨_,_,c,hc⟩ := mixingCopies least.1 hm
    obtain ⟨b,eb⟩ := mixingEmptyInput hm
    let root := opnd C m b
    have route (e : ↥U) := onlyMixWitness least top empty hm only hc eb e.property
    have orient (e : ↥U) := (route e).2
    choose w v eq on clean sound using orient
    let W := U.attach.image w
    let V := U.attach.image v
    have wmem (e : ↥U) : w e ∈ W := Finset.mem_image.mpr ⟨e,Finset.mem_attach _ _,rfl⟩
    have vmem (e : ↥U) : v e ∈ V := Finset.mem_image.mpr ⟨e,Finset.mem_attach _ _,rfl⟩
    have edge (e : ↥U) : s(w e,v e) ∈ U := eq e ▸ e.property
    have adj (e : ↥U) : plane.Adj (w e) (v e) := SimpleGraph.mem_edgeFinset.mp (sub (edge e))
    have center (t : Fin 26) (ht : t ∈ W) : (plane.deleteEdges ↑U).Adj c t := by
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ht
      exact clean e
    have inj : Function.Injective v := by
      intro e f same
      have cv : c ≠ v e := by
        intro h
        exact (SimpleGraph.deleteEdges_adj.mp (clean e)).2 (h ▸ (Sym2.eq_swap ▸ edge e))
      have vr : plane.Adj (v e) (w f) := same ▸ (adj f).symm
      have ww := commonUnique planeFour cv (SimpleGraph.deleteEdges_adj.mp (clean e)).1 (adj e).symm
        (SimpleGraph.deleteEdges_adj.mp (clean f)).1 vr
      apply Subtype.ext
      rw [eq e,eq f,ww,same]
    have sizeV : U.card ≤ V.card := by
      change U.card ≤ (U.attach.image v).card
      rw [Finset.card_image_of_injective _ inj,Finset.card_attach]
    have small : W.card ≤ 4 := by
      calc
        _ ≤ (Finset.univ.filter (plane.Adj c)).card := Finset.card_le_card (fun t ht =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(SimpleGraph.deleteEdges_adj.mp (center t ht)).1⟩)
        _ = _ := degree_four c
    have nonU : U.Nonempty := Finset.card_pos.mp (by change 4 ≤ U.card at large; omega)
    obtain ⟨e0,he0⟩ := nonU
    let e : ↥U := ⟨e0,he0⟩
    have two : 2 ≤ W.card := by
      by_contra! few
      have all : U ⊆ incidentEdges (w e) := by
        intro z hz
        let f : ↥U := ⟨z,hz⟩
        have ww := Finset.card_le_one.mp (show W.card ≤ 1 by omega) _ (wmem f) _ (wmem e)
        have mem : w f ∈ z := by
          change w f ∈ f.val
          rw [eq f]
          exact Sym2.mem_iff.mpr (Or.inl rfl)
        exact edge_incident (SimpleGraph.mem_edgeFinset.mp (sub hz)) (ww ▸ mem)
      have ch := SimpleGraph.deleteEdges_adj.mp (clean e)
      have ic : s(c,w e) ∈ incidentEdges (w e) := Sym2.eq_swap ▸ incident_mem ch.1.symm
      have excl : U ⊆ (incidentEdges (w e)).erase s(c,w e) := fun z hz =>
        Finset.mem_erase.mpr ⟨fun eq => ch.2 (eq ▸ hz),all hz⟩
      have h := Finset.card_le_card excl
      have eq := Finset.card_erase_add_one ic
      have deg := incident_count (w e)
      change 4 ≤ U.card at large
      omega
    obtain ⟨K,hK⟩ := existsMinCover (plane.deleteEdges ↑U)
    have bound := coverFan (wmem e) (clean e) (fun z hz => by
      let f : ↥U := ⟨z,hz⟩
      refine ⟨w f,wmem f,?_⟩
      change w f ∈ f.val
      rw [eq f]
      exact Sym2.mem_iff.mpr (Or.inl rfl)) hK.1
    have cap := covers K hK
    have first (q : ℕ) (hq : q ∈ mixing plane C) : m ≤ q := (only q hq).ge
    obtain ⟨F,count,shape,separate⟩ := firstCut least.1 top hm first (opndBound least.1
      (orData (mixingNotLam hm)).1 b) (route e).1
    have colorV (l : Fin 26) (hl : l ∈ V) : color26 l = color26 c := by
      obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hl
      have bool : ∀ a d g : Bool, a ≠ d → g ≠ d → a = g := by decide
      exact bool _ _ _ (planeBip _ _ (adj f).symm) (planeBip _ _ (SimpleGraph.deleteEdges_adj.mp (clean f)).1)
    have hit (p q : Fin 26) (h : s(p,q) ∈ U) : Wire C root (pairInput p q) := by
      let f : ↥U := ⟨s(p,q),h⟩
      have h' : s(p,q) = s(w f,v f) := eq f
      rcases Sym2.eq_iff.mp h' with a|a
      · simpa -congrConsts only [a.1,a.2] using on f
      · have swap (i j : Fin 26) : pairInput i j = pairInput j i := by funext t; simp -congrConsts [pairInput_d,or_comm]
        simpa -congrConsts only [a.1,a.2,swap (v f) (w f)] using on f
    have use := fanShapes (U := U) (W := W) (V := V) (F := F) (fun z => orIn 26 C z)
      sizeV two small center (fun t ht => by
        obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp ht
        exact ⟨_,vmem f,edge f⟩) (fun t ht => by
        obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp ht
        exact ⟨_,wmem f,edge f⟩) sub shape (by
      intro t ht l hl he u hu
      let x (i : Fin 26) := decide (i = u ∨ i ∈ V ∧ ¬plane.Adj u i)
      have ux : x u = true := by simp -congrConsts [x]
      have off : graphFun plane ∅ x = false := by
        apply Bool.eq_false_iff.mpr
        intro positive
        have witness : ∃ i j : Fin 26, plane.Adj i j ∧ x i = true ∧ x j = true := by
          simpa -congrConsts only [graphFun_d,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
            decide_eq_true_eq] using positive
        obtain ⟨i,j,ij,oi,oj⟩ := witness
        have pi : i = u ∨ i ∈ V ∧ ¬plane.Adj u i := of_decide_eq_true oi
        have pj : j = u ∨ j ∈ V ∧ ¬plane.Adj u j := of_decide_eq_true oj
        rcases pi with rfl|⟨hi,noI⟩ <;> rcases pj with rfl|⟨hj,noJ⟩
        · exact plane.irrefl ij
        · exact noJ ij
        · exact noI ij.symm
        · exact planeBip i j ij ((colorV i hi).trans (colorV j hj).symm)
      obtain ⟨f,_,hu'⟩ := Finset.mem_image.mp hu
      have no : ¬Wire C root x := fun pos => Bool.false_ne_true (off.symm.trans (sound f x (hu' ▸ ux) pos))
      obtain ⟨z,hz,⟨p,hp,pv⟩,avoid⟩ := separate (pairInput t l) x (hit t l he) no
      refine ⟨z,hz,?_,fun h => Bool.false_ne_true ((avoid u h).symm.trans ux),?_⟩
      · rcases (pairInput_true t l p).mp pv with eq|eq
        · exact Or.inl (eq ▸ hp)
        · exact Or.inr (eq ▸ hp)
      · intro i hi noI mem
        have yes : x i = true := by simp -congrConsts [x,hi,noI]
        exact Bool.false_ne_true ((avoid i mem).symm.trans yes))
    change (tops plane C).card + (junk plane C).card + (orN plane C \ lam plane C).card ≤ 13 + U.card at cost
    omega
  have fourMany {G : SimpleGraph (Fin 26)} [inst : DecidableRel G.Adj] {C : Circuit}
      (eq : G = plane) (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      (hj : 2 ≤ (junk G C).card) (mix : (mixing G C).Nonempty) (four : (Ustar G C).card = 4)
      (many : 2 ≤ (mixing G C).card) (bigR : 3 ≤ (orN G C \ lam G C).card)
      (cost : (tops G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + (Ustar G C).card)
      (edges : 52 ≤ 4 * (tops G C).card + (Ustar G C).card)
      (bound : ∀ K, IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C).card) : False := by
    subst G
    have ie : inst = planeInst := Subsingleton.elim _ _
    subst inst
    have t12 : (tops plane C).card = 12 := by omega
    have j2 : (junk plane C).card = 2 := by omega
    have r3 : (orN plane C \ lam plane C).card = 3 := by omega
    obtain ⟨v,star⟩ := fourEdgeCover (Ustar plane C) Finset.sdiff_subset four (fun K h => t12 ▸ bound K h)
    have hv := supportsStar (show Ustar plane C ⊆ plane.edgeFinset from Finset.sdiff_subset) four star
    obtain ⟨m,hm⟩ := mix
    let R := orN plane C \ lam plane C
    let M := mixing plane C
    have inc : M ⊆ R := fun _ h => mixingNotLam h
    have few : (R \ M).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset inc]
      change R.card = 3 at r3
      change 1 < M.card at many
      omega
    obtain ⟨q,hq,hOnly⟩ : ∃ q ∈ R, ∀ k ∈ R, k ∉ M → k = q := by
      by_cases non : (R \ M).Nonempty
      · obtain ⟨q,hq⟩ := non
        exact ⟨q,(Finset.mem_sdiff.mp hq).1,fun k hr hm => Finset.card_le_one.mp few _ (Finset.mem_sdiff.mpr ⟨hr,hm⟩) _ hq⟩
      · exact ⟨m,inc hm,fun k hr no => (non ⟨k,Finset.mem_sdiff.mpr ⟨hr,no⟩⟩).elim⟩
    obtain ⟨W,cw,wc,cover⟩ := collectLeaves C least top empty t12 four v hv
    have h := twoRoots least.1 planeFour q hq hOnly W (cw.trans j2.le) wc (Finset.univ.filter (plane.Adj v))
      (fun _ h => (Finset.mem_filter.mp h).2) (fun _ h => hv _ (Finset.mem_filter.mp h).2) cover
    rw [degree_four] at h
    omega
  intro incident separate G dec C heq least top size
  dsimp only
  intro empty twoJ oneM threeU cost edgeBound cover
  have bump (G : SimpleGraph (Fin 26)) [di : DecidableRel G.Adj] (C : Circuit)
      (eq : G = plane) (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
      (twoJ : 2 ≤ (junk G C).card) (oneM : 1 ≤ (mixing G C).card) (threeU : 3 ≤ (Ustar G C).card)
      (cost : (tops G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 13 + (Ustar G C).card)
      (edges : 52 ≤ 4 * (tops G C).card + (Ustar G C).card)
      (cover : ∀ K, IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C).card) :
      3 ≤ (orN G C \ lam G C).card ∧ 5 ≤ (Ustar G C).card ∧ 2 ≤ (mixing G C).card := by
    have old := boundary eq least top empty twoJ threeU cost edges
    have non := Finset.card_pos.mp oneM
    subst G
    have ie : di = planeInst := Subsingleton.elim _ _
    subst di
    have many : 2 ≤ (mixing plane C).card := by
      by_contra low
      replace low := not_le.mp low
      obtain ⟨m,hm⟩ := non
      exact uniqueMixImpossible C least top empty m hm
        (fun q hq => Finset.card_le_one.mp (by omega) q hq m hm) old.2 cost cover
    have r : 3 ≤ (orN plane C \ lam plane C).card := by
      by_contra h
      replace h := not_le.mp h
      have equal : (orN plane C \ lam plane C).card = 2 := by omega
      have inc : mixing plane C ⊆ orN plane C \ lam plane C := fun _ h => mixingNotLam h
      have all := Finset.eq_of_subset_of_card_le inc (equal ▸ many)
      obtain ⟨p,q,ne,pair⟩ := Finset.card_eq_two.mp equal
      have hp : p ∈ mixing plane C := by rw [all,pair]; simp -congrConsts
      have hq : q ∈ mixing plane C := by rw [all,pair]; simp -congrConsts
      have h3 : (Ustar plane C).card ≤ 3 := by
        rcases lt_or_gt_of_ne ne with lt|lt
        · exact twoMixBound least top empty planeFour color26 planeBip lt pair hp hq
        · exact twoMixBound least top empty planeFour color26 planeBip lt (pair.trans (Finset.pair_comm _ _)) hq hp
      omega
    refine ⟨r,?_,many⟩
    by_contra small
    replace small := not_le.mp small
    exact fourMany rfl least top empty twoJ non (by omega) many r cost edges cover
  obtain ⟨bigR,bigU,bigM⟩ := bump G C heq least top empty twoJ oneM threeU cost edgeBound cover
  obtain ⟨g,hg,m,hm,a,ha,b,hmPath,hgPath,sub,e,he,f,hf,nef,se,sf⟩ := sharedService least top empty threeU cost edgeBound
  have clause : ∀ z : Sym2 (Fin 26), z = e ∨ z = f → z ∈ Ustar G C ∧ z ∈ gammaE G C g ∧
      ∃ t ∈ tops G C, ∃ d : Fin 2, z ∈ gammaE G C t ∧ OrReaches 26 C (opnd C t d) g := by
    intro z hz'
    have hzg : z ∈ gammaE G C g ∩ Ustar G C := by
      rcases hz' with rfl|rfl
      · exact he
      · exact hf
    have hs : Serves G C g z := by
      rcases hz' with rfl|rfl
      · exact se
      · exact sf
    obtain ⟨p, q, hpq, _, t, ht, d, htv, hor⟩ := hs
    have hE : z ∈ G.edgeFinset := by
      have h2 := (Finset.mem_inter.mp hzg).2
      unfold Ustar at h2
      exact (Finset.mem_sdiff.mp h2).1
    refine ⟨(Finset.mem_inter.mp hzg).2, (Finset.mem_inter.mp hzg).1, t, ht, d, ?_, hor⟩
    unfold gammaE
    exact Finset.mem_filter.mpr ⟨hE, p, q, hpq, htv⟩
  have sub' : gammaE G C g ∩ Ustar G C ⊆ gammaE G C m := fun x hx => (Finset.mem_inter.mp (sub hx)).1
  by_cases common : ∃ v : Fin 26, v ∈ e ∧ v ∈ f
  · exact @incident G dec C g m a b e f (Ustar G C) (tops G C) heq rfl rfl least top size empty twoJ
      bigR bigU bigM cost edgeBound cover hg hm ha hmPath hgPath sub' nef clause common
  · exact @separate G dec C g m a b e f (Ustar G C) (tops G C) heq rfl rfl least top size empty twoJ
      bigR bigU bigM cost edgeBound cover hg hm ha hmPath hgPath sub' nef clause common
