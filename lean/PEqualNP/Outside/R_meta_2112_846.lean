import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2112_846
    (andCase : ∀ (C : Circuit),
      IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      (∀ i : Fin C.size, let a := C.gates.get i
        (∀ w ∈ a.inputs, w < 9 + i.val) ∧ a.inputs.Nodup) →
      (let r : Fin 9 → Finset (Fin C.size) := fun v => {i : Fin C.size | v.val ∈ (C.gates.get i).inputs}
        ∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (r v).Nonempty ∧ (r v).card ≤ 2 ∧
            ((r v).card = 2 → ∀ i ∈ r v, (C.gates.get i).op = GateOp.or)) →
      ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∀ j : Fin C.size,
        (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs ↔ i = j) →
        (C.gates.get j).op = GateOp.and →
        (∃ p ≥ 9, p ∈ (C.gates.get j).inputs ∧
          ∀ x : Fin 9 → Bool, x v = false → circuitFun 9 C x = false →
            circuitFun 9 C (Function.update x v true) = true →
            (C.wires (List.ofFn x)).getD p false = true) → False)
    (notCase : ∀ (C : Circuit),
      IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      (∀ i : Fin C.size, let a := C.gates.get i
        (∀ w ∈ a.inputs, w < 9 + i.val) ∧ a.inputs.Nodup) →
      ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∀ j : Fin C.size,
        (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs ↔ i = j) →
        (C.gates.get j).op = GateOp.not →
        (∀ x : Fin 9 → Bool, let y := Function.update x v true
          x v = false → circuitFun 9 C x = false → circuitFun 9 C y = true →
          ∃ k : Fin C.size, j < k ∧ (C.gates.get k).op = GateOp.not ∧
            (C.wires (List.ofFn x)).getD (9 + k.val) false = false ∧
            (C.wires (List.ofFn y)).getD (9 + k.val) false = true) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) ||
      x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) ||
      x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
     have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs};
     have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧
          x3.size ≤ (15 : ℕ) ∧
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧
              (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;
                 (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧
      x5.inputs.Nodup ∧
      (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      x5.inputs.length = (2 : ℕ))) ∧
                ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧
      (x2 x3 x4).card ≤ (2 : ℕ) ∧
      ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or);
     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  intro postedEdge postedReaders postedNormal C hC hbad
  obtain ⟨hm, hsmall, hf, hl, hr⟩ := hC
  obtain ⟨v, hv, j, hjmem, hjop⟩ := hbad
  let edge : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have hfun : circuitFun 9 C = edge := hf
  let g (i : Fin C.size) := C.gates.get i
  let readers : Finset (Fin C.size) := {i | v.val ∈ (g i).inputs}
  have hmem : j ∈ readers := hjmem
  have hnoOr : (g j).op ≠ GateOp.or := hjop
  have hrV : readers.card ≤ 2 ∧
      (readers.card = 2 → ∀ i ∈ readers, (g i).op = GateOp.or) := (hr v hv).2
  have hcard : readers.card ≤ 1 := by
    by_contra h
    apply hnoOr
    exact hrV.2 (by omega) j hmem
  have hsole (i : Fin C.size) : v.val ∈ (g i).inputs ↔ i = j := by
    constructor
    · intro hi
      exact Finset.card_le_one.mp hcard i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) j hmem
    · rintro rfl
      exact (Finset.mem_filter.mp hmem).2
  have hback (i : Fin C.size) (p : ℕ) (hp : p ∈ (g i).inputs) :
      p < 9 + i.val := (hl i).1 p hp
  have hops (i : Fin C.size) :
      (g i).op = GateOp.and ∨ (g i).op = GateOp.or ∨ (g i).op = GateOp.not := by
    have h := (hm.1 (g i) (List.get_mem _ _)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  let read (w : List Bool) (p : ℕ) := w.getD p false
  let val (w : List Bool) (gate : Gate) := gate.op.eval (gate.inputs.map (read w))
  let step (w : List Bool) (gate : Gate) := w ++ [val w gate]
  let wire (x : Fin 9 → Bool) (p : ℕ) := read (C.wires (List.ofFn x)) p
  have appendRead (w : List Bool) (b : Bool) (p : ℕ) :
      read (w ++ [b]) p = if p = w.length then b else read w p := by
    change (w ++ [b]).getD p false = _
    simp only [read, List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases hlt : p < w.length
    · simp [hlt, show p ≠ w.length by omega]
    · by_cases heq : p = w.length
      · simp [heq]
      · have hs : p - w.length ≠ 0 := by omega
        simp [hlt, heq, hs]
  have stepLen (w : List Bool) (gate : Gate) : (step w gate).length = w.length + 1 := by
    simp [step]
  have foldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons a gs ih => simp only [List.foldl_cons, ih, stepLen, List.length_cons]; omega
  have stable (gs : List Gate) (w : List Bool) (p : ℕ) (hp : p < w.length) :
      read (gs.foldl step w) p = read w p := by
    induction gs generalizing w with
    | nil => rfl
    | cons a gs ih =>
      rw [List.foldl_cons, ih (step w a) (by rw [stepLen]; omega)]
      simp [step, appendRead, show p ≠ w.length by omega]
  have primary (x : Fin 9 → Bool) (p : Fin 9) : wire x p.val = x p := by
    change read (C.gates.foldl step (List.ofFn x)) p.val = _
    rw [stable _ _ _ (by simp)]
    change (List.ofFn x).getD p.val false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [p.isLt, dite_eq_left, Option.getD_some]
  have gateWire (x : Fin 9 → Bool) (i : Fin C.size) :
      wire x (9 + i.val) = (g i).op.eval ((g i).inputs.map (wire x)) := by
    let w := (C.gates.take i.val).foldl step (List.ofFn x)
    have hi : i.val < C.gates.length := i.isLt
    have hw : w.length = 9 + i.val := by simp [w, foldLen, hi.le]
    have htake : C.gates.take (i.val + 1) = C.gates.take i.val ++ [g i] :=
      List.take_succ_eq_append_getElem hi
    have hsplit : C.gates = (C.gates.take i.val ++ [g i]) ++ C.gates.drop (i.val + 1) := by
      rw [← htake]
      exact (List.take_append_drop _ _).symm
    have hfull : C.wires (List.ofFn x) =
        (C.gates.drop (i.val + 1)).foldl step (step w (g i)) := calc
      C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
      _ = ((C.gates.take i.val ++ [g i]) ++ C.gates.drop (i.val + 1)).foldl step
          (List.ofFn x) := congrArg (fun gs => gs.foldl step (List.ofFn x)) hsplit
      _ = _ := by simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, w]
    have hbefore (p : ℕ) (hp : p ∈ (g i).inputs) : wire x p = read w p := by
      have hb := hback i p hp
      change read (C.wires (List.ofFn x)) p = _
      rw [hfull, stable _ _ _ (by rw [stepLen, hw]; omega)]
      simp [step, appendRead, hw, show p ≠ 9 + i.val by omega]
    calc
      wire x (9 + i.val) = val w (g i) := by
        change read (C.wires (List.ofFn x)) (9 + i.val) = _
        rw [hfull, stable _ _ _ (by rw [stepLen, hw]; omega)]
        change read (w ++ [val w (g i)]) (9 + i.val) = _
        rw [appendRead, hw, ite_eq_left rfl]
      _ = _ := by
        change (g i).op.eval ((g i).inputs.map (read w)) = _
        rw [List.map_congr_left (fun p hp => (hbefore p hp).symm)]
  have noOut : C.output ≠ v.val := by
    intro hout
    let x : Fin 9 → Bool := fun i => decide (i = v)
    have hs : ∀ r : Fin 9, edge (fun i => decide (i = r)) = false := by decide
    have hc : wire x C.output = false := (congrFun hfun x).trans (hs v)
    rw [hout, primary] at hc
    simp [x] at hc
  have pastEnd (x : Fin 9 → Bool) (p : ℕ) (hp : 9 + C.size ≤ p) :
      wire x p = false := by
    change ((C.gates.foldl step (List.ofFn x))).getD p false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [foldLen, List.length_ofFn]
      exact hp)]
    rfl
  -- Before the unique reader, all computed values ignore the distinguished bit.
  have equalPrefix (x y : Fin 9 → Bool) (hxy : ∀ u ≠ v, x u = y u)
      (p : ℕ) (hp : p < 9 + j.val) (hne : p ≠ v.val) : wire x p = wire y p := by
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      by_cases hraw : p < 9
      · let u : Fin 9 := ⟨p, hraw⟩
        change wire x u.val = wire y u.val
        exact (primary x u).trans ((hxy u (fun e => hne (congrArg Fin.val e))).trans
          (primary y u).symm)
      · let i : Fin C.size := ⟨p - 9, by have := j.isLt; omega⟩
        have hi : p = 9 + i.val := by dsimp [i]; omega
        have hij : i ≠ j := by
          intro e
          rw [e] at hi
          omega
        rw [hi, gateWire, gateWire]
        congr 1
        apply List.map_congr_left
        intro q hq
        have hb := hback i q hq
        exact ih q (by omega) (by omega) (fun e => hij ((hsole i).mp (e ▸ hq)))
  -- If the reader also agrees, equality propagates to the output.
  have equalAfter (x y : Fin 9 → Bool) (hxy : ∀ u ≠ v, x u = y u)
      (hj : wire x (9 + j.val) = wire y (9 + j.val))
      (p : ℕ) (hne : p ≠ v.val) : wire x p = wire y p := by
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      by_cases hraw : p < 9
      · exact equalPrefix x y hxy p (by omega) hne
      by_cases hout : 9 + C.size ≤ p
      · rw [pastEnd _ _ hout, pastEnd _ _ hout]
      let i : Fin C.size := ⟨p - 9, by omega⟩
      have hi : p = 9 + i.val := by dsimp [i]; omega
      by_cases hij : i = j
      · simpa only [hi, hij] using hj
      rw [hi, gateWire, gateWire]
      congr 1
      apply List.map_congr_left
      intro q hq
      have hb := hback i q hq
      exact ih q (by omega) (fun e => hij ((hsole i).mp (e ▸ hq)))
  rcases hops j with ha | ho | hn
  · have hlen : (g j).inputs.length = 2 := by
      rcases (hl j).2.2 with ht | ht
      · rw [ha] at ht
        cases ht.1
      · exact ht.2
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hvj := (hsole j).mpr rfl
    rw [hab] at hvj
    have hpair : ∃ q, q ≠ v.val ∧
        ((g j).inputs = [v.val, q] ∨ (g j).inputs = [q, v.val]) := by
      have hd : a ≠ b := by
        have hd : (g j).inputs.Nodup := (hl j).2.1
        simpa [hab] using hd
      rcases List.mem_cons.mp hvj with h | h
      · exact ⟨b, fun e => hd (h.symm.trans e.symm), Or.inl (by rw [hab, h])⟩
      · have he : v.val = b := List.mem_singleton.mp h
        exact ⟨a, fun e => hd (e.trans he), Or.inr (by rw [hab, he])⟩
    obtain ⟨q, hqv, hq⟩ := hpair
    have hqm : q ∈ (g j).inputs := by rcases hq with h | h <;> simp [h]
    have qTrue (x y : Fin 9 → Bool) (hxy : ∀ u ≠ v, x u = y u)
        (hx : x v = false) (hy : y v = true)
        (hfx : circuitFun 9 C x = false) (hfy : circuitFun 9 C y = true) :
        wire x q = true := by
      by_contra h
      have hzero : wire x q = false := Bool.eq_false_of_not_eq_true h
      have hb := hback j q hqm
      have he := equalPrefix x y hxy q hb hqv
      have hre (z : Fin 9 → Bool) (hz : wire z q = false) : wire z (9 + j.val) = false := by
        rw [gateWire, ha]
        have hEval (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
        rw [hEval]
        rcases hq with hqi | hqi <;> rw [hqi] <;> simp [hz]
      have hsame := equalAfter x y hxy
        ((hre x hzero).trans (hre y (he.symm.trans hzero)).symm) C.output noOut
      exact Bool.false_ne_true (hfx.symm.trans (hsame.trans hfy))
    have hqge : 9 ≤ q := by
      by_contra h
      let a : Fin 9 := ⟨q, by omega⟩
      have examples : ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ a : Fin 9, a ≠ v →
          ∃ u : Fin 9, u ≠ v ∧ u ≠ a ∧ edge (fun i => decide (i = u)) = false ∧
            edge (fun i => decide (i = u ∨ i = v)) = true := by decide
      obtain ⟨u, huv, hua, he0, he1⟩ := examples v hv a
        (fun e => hqv (congrArg Fin.val e))
      let x : Fin 9 → Bool := fun i => decide (i = u)
      let y : Fin 9 → Bool := fun i => decide (i = u ∨ i = v)
      have ht := qTrue x y (fun i hi => by simp [x, y, hi])
        (by simp [x, Ne.symm huv]) (by simp [y])
        ((congrFun hfun x).trans he0) ((congrFun hfun y).trans he1)
      change wire x a.val = true at ht
      rw [primary] at ht
      simp [x, Ne.symm hua] at ht
    refine andCase C hm hsmall hfun (fun i => ⟨(hl i).1, (hl i).2.1⟩)
      hr v hv j hsole ha ⟨q, hqge, hqm, ?_⟩
    intro x hx hfx hfy
    exact qTrue x (Function.update x v true)
      (fun k hk => (Function.update_of_ne hk _ _).symm) hx (Function.update_self ..) hfx hfy
  · exact hnoOr ho
  · have hlen : (g j).inputs.length = 1 := by
      rcases (hl j).2.2 with ht | ht
      · exact ht.2
      · exact (ht.1 hn).elim
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    have hvj := (hsole j).mpr rfl
    have hae : (g j).inputs = [v.val] := by
      rw [ha]
      exact congrArg (fun w : ℕ => [w]) (by simpa [ha, eq_comm] using hvj)
    apply notCase C hm hsmall hfun (fun i => ⟨(hl i).1, (hl i).2.1⟩) v hv j hsole hn
    intro x y hx hfx hfy
    have hxy (k : Fin 9) (hk : k ≠ v) : x k = y k := (Function.update_of_ne hk _ _).symm
    have hy : y v = true := Function.update_self ..
    by_contra hwitness
    -- A later NOT is the only place a rise can be introduced.
    have nonrise (p : ℕ) (hne : p ≠ v.val) :
        wire y p = true → wire x p = true := by
      induction p using Nat.strong_induction_on with
      | ind p ih =>
        intro hp
        by_cases hearly : p < 9 + j.val
        · rwa [equalPrefix x y hxy p hearly hne]
        by_cases hout : 9 + C.size ≤ p
        · exact (Bool.false_ne_true ((pastEnd y p hout).symm.trans hp)).elim
        let i : Fin C.size := ⟨p - 9, by omega⟩
        have hi : p = 9 + i.val := by dsimp [i]; omega
        by_cases hij : i = j
        · have hzero : wire y p = false := by
            rw [hi, hij, gateWire, hn, hae]
            change (!wire y v.val) = false
            rw [primary, hy]
            rfl
          exact (Bool.false_ne_true (hzero.symm.trans hp)).elim
        have ih' (q : ℕ) (hq : q ∈ (g i).inputs) :
            wire y q = true → wire x q = true := by
          have hb := hback i q hq
          exact ih q (by omega) (fun e => hij ((hsole i).mp (e ▸ hq)))
        rcases hops i with ha | ho | hn'
        · rw [hi, gateWire, ha] at hp ⊢
          change ((g i).inputs.map (wire y)).all id = true at hp
          change ((g i).inputs.map (wire x)).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hp ⊢
          exact fun q hq => ih' q hq (hp q hq)
        · rw [hi, gateWire, ho] at hp ⊢
          change ((g i).inputs.map (wire y)).any id = true at hp
          change ((g i).inputs.map (wire x)).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hp ⊢
          obtain ⟨q, hq, hqv⟩ := hp
          exact ⟨q, hq, ih' q hq hqv⟩
        · by_contra h
          have hx0 := Bool.eq_false_of_not_eq_true h
          have hjlt : j < i := by
            change j.val < i.val
            have hne' : i.val ≠ j.val := fun e => hij (Fin.ext e)
            omega
          exact hwitness ⟨i, hjlt, hn', hi ▸ hx0, hi ▸ hp⟩
    exact Bool.false_ne_true (hfx.symm.trans (nonrise C.output noOut hfy))
