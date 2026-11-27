import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadTwo (fpl)
open PEqualNP.HeptadCover (singerLines3)
open PEqualNP.CircuitMoves (WireBelowOutput)

theorem PEqualNP.Outside.R_meta_4021_556
    (sameCollision : ∀ C : Circuit,
      let v := wireVal 26 C
      let g := gateAt C
      let one := fun (a i : Fin 26) => decide (i = a)
      let step := fun (a : Fin 26) (u w : ℕ) =>
        ∃ j h q, w = 26 + j ∧ C.gates[j]? = some h ∧
          (h.inputs = [u, q] ∨ h.inputs = [q, u]) ∧
          (h.op = .or ∨ h.op = .and ∧ v q (one a) = true)
      C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
      (∀ h ∈ C.gates, h.inputs.Nodup) →
      circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) →
      0 < PEqualNP.TopForm.andPairs 26 C →
      (∃ j < C.gates.length, (g j).op = .and ∧ ¬ WireBelowOutput 26 C (26 + j)) →
      ¬ (Relation.ReflTransGen (step 0) 13 C.output ∨
         Relation.ReflTransGen (step 13) 0 C.output) →
      (∃ j < C.gates.length, (g j).op = .and ∧ ∀ u ∈ (g j).inputs,
        v u (one 0) = false ∧ v u (one 13) = false ∧ v u (pairInput 0 13) = true) →
      False)
    (distinctCollisions : ∀ C : Circuit,
      let v := wireVal 26 C
      let g := gateAt C
      let one := fun (a i : Fin 26) => decide (i = a)
      let step := fun (a : Fin 26) (u w : ℕ) =>
        ∃ j h q, w = 26 + j ∧ C.gates[j]? = some h ∧
          (h.inputs = [u, q] ∨ h.inputs = [q, u]) ∧
          (h.op = .or ∨ h.op = .and ∧ v q (one a) = true)
      let collision := fun (a : Fin 26) (j : ℕ) => (g j).op = .and ∧
        ∀ u ∈ (g j).inputs, v u (one a) = false ∧ v u (pairInput 0 13) = true
      C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
      (∀ h ∈ C.gates, h.inputs.Nodup) →
      circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) →
      0 < PEqualNP.TopForm.andPairs 26 C →
      (∃ j < C.gates.length, (g j).op = .and ∧ ¬ WireBelowOutput 26 C (26 + j)) →
      ¬ (Relation.ReflTransGen (step 0) 13 C.output ∨
         Relation.ReflTransGen (step 13) 0 C.output) →
      (∃ j < C.gates.length, ∃ k < C.gates.length,
        j ≠ k ∧ collision 0 j ∧ collision 13 k) → False) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output) := by
  dsimp only
  intro C ok
  obtain ⟨size, model, nodup, computes, pairs, dirty⟩ := ok
  let one := fun (a i : Fin 26) => decide (i = a)
  let v := wireVal 26 C
  let step := fun (a : Fin 26) (u w : ℕ) =>
    ∃ j g q, w = 26 + j ∧ C.gates[j]? = some g ∧
      (g.inputs = [u, q] ∨ g.inputs = [q, u]) ∧
      (g.op = .or ∨ g.op = .and ∧ v q (one a) = true)
  change Relation.ReflTransGen (step 0) 13 C.output ∨
    Relation.ReflTransGen (step 13) 0 C.output
  have gateAtOfGet {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) : gateAt C j = g := by
    change C.gates.getD j _ = g
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  have gateShape {j : ℕ} (hj : j < C.gates.length) :
      ∃ g u q, C.gates[j]? = some g ∧ g.inputs = [u, q] ∧
        u < 26 + j ∧ q < 26 + j ∧ (g.op = .and ∨ g.op = .or) := by
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := getElem?_pos C.gates j hj
    have mem : g ∈ C.gates := List.mem_of_getElem rfl
    obtain ⟨u, q, hinputs⟩ := List.length_eq_two.mp (model.2.2 g mem)
    have back : ∀ i ∈ [u, q], i < 26 + j := by
      have back := model.2.1 j hj
      rw [gateAtOfGet hg, hinputs] at back
      exact back
    exact ⟨g, u, q, hg, hinputs, back u (by simp), back q (by simp), model.1 g mem⟩
  let addGate := fun (xs : List Bool) (g : Gate) =>
    xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have foldLength : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl addGate xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro xs
      rw [List.foldl_cons, ih]
      simp [addGate, Nat.add_comm, Nat.add_left_comm]
  have foldKeep : ∀ (gs : List Gate) (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl addGate xs).getD i false = xs.getD i false := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro xs i hi
      rw [List.foldl_cons, ih _ _ (by simpa [addGate] using Nat.lt_succ_of_lt hi)]
      exact List.getD_append _ _ _ _ hi
  have inputValue (x : Fin 26 → Bool) (i : Fin 26) : v i.val x = x i := by
    change (C.gates.foldl addGate (List.ofFn x)).getD i.val false = x i
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [foldKeep _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have wireLength (x : Fin 26 → Bool) : (C.wires (List.ofFn x)).length = 26 + C.gates.length := by
    change (C.gates.foldl addGate (List.ofFn x)).length = _
    rw [foldLength, List.length_ofFn]
  have gateValue (x : Fin 26 → Bool) {j : ℕ} {g : Gate} {u q : ℕ}
      (hj : j < C.gates.length) (hg : C.gates[j]? = some g)
      (hinputs : g.inputs = [u, q]) (hu : u < 26 + j) (hq : q < 26 + j) :
      v (26 + j) x = g.op.eval [v u x, v q x] := by
    let earlier := (C.gates.take j).foldl addGate (List.ofFn x)
    have plen : earlier.length = 26 + j := by
      dsimp only [earlier]
      rw [foldLength, List.length_ofFn, List.length_take, Nat.min_eq_left hj.le]
    have hget : C.gates[j] = g := by
      rw [getElem?_pos C.gates j hj] at hg
      exact Option.some.inj hg
    have splitGates : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
      rw [← hget, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have splitWires : C.wires (List.ofFn x) = (g :: C.gates.drop (j + 1)).foldl addGate earlier := by
      change C.gates.foldl addGate (List.ofFn x) = _
      conv_lhs => rw [splitGates]
      rw [List.foldl_append]
    have keep (i : ℕ) (hi : i < 26 + j) : v i x = earlier.getD i false := by
      change (C.wires (List.ofFn x)).getD i false = _
      rw [splitWires, foldKeep _ _ _ (plen.symm ▸ hi)]
    change (C.wires (List.ofFn x)).getD (26 + j) false = _
    rw [splitWires, List.foldl_cons, foldKeep _ _ _ (by simp [addGate, plen])]
    change (earlier ++ [g.op.eval (g.inputs.map fun i => earlier.getD i false)]).getD
      (26 + j) false = _
    rw [List.getD_append_right _ _ _ _ (by rw [plen]), plen, Nat.sub_self, hinputs,
      keep u hu, keep q hq]
    rfl
  have evAnd (s t : Bool) : GateOp.eval .and [s, t] = (s && t) := by
    cases s <;> cases t <;> rfl
  have evOr (s t : Bool) : GateOp.eval .or [s, t] = (s || t) := by
    cases s <;> cases t <;> rfl
  have pairEq (a b i : Fin 26) : pairInput a b i = decide (i = a ∨ i = b) := rfl
  have trace (a b : Fin 26) (w : ℕ) :
      v w (one a) = false → v w (pairInput a b) = true →
      Relation.ReflTransGen (step a) b.val w ∨
        ∃ j < C.gates.length, ∃ u q, C.gates[j]? = some (⟨.and, [u, q]⟩ : Gate) ∧
          v u (one a) = false ∧ v q (one a) = false ∧
          v u (pairInput a b) = true ∧ v q (pairInput a b) = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro old new
      by_cases input : w < 26
      · let i : Fin 26 := ⟨w, input⟩
        change v i.val (one a) = false at old
        change v i.val (pairInput a b) = true at new
        rw [inputValue] at old new
        have hne : i ≠ a := of_decide_eq_false old
        have hi : i = b := (of_decide_eq_true ((pairEq a b i).symm.trans new)).resolve_left hne
        have hw : w = b.val := congrArg Fin.val hi
        rw [hw]
        exact Or.inl .refl
      · have inside : w < 26 + C.gates.length := by
          by_contra past
          change (C.wires (List.ofFn (pairInput a b))).getD w false = true at new
          rw [List.getD_eq_default _ _ (by rw [wireLength]; omega)] at new
          contradiction
        let j := w - 26
        have hw : w = 26 + j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        obtain ⟨g, u, q, hg, hinputs, hu, hq, hop⟩ := gateShape hj
        rw [hw, gateValue _ hj hg hinputs hu hq] at old new
        have back (i : ℕ) (hi : i < 26 + j) (edge : step a i w)
            (oi : v i (one a) = false) (ni : v i (pairInput a b) = true) :=
          (ih i (by omega) oi ni).imp (fun path => path.tail edge) id
        rcases hop with ha | ho
        · rw [ha, evAnd] at old new
          obtain ⟨nu, nq⟩ := Bool.and_eq_true_iff.mp new
          cases ou : v u (one a) with
          | false =>
            cases oq : v q (one a) with
            | false =>
              have hg' : g = (⟨.and, [u, q]⟩ : Gate) := by
                cases g
                congr
              exact Or.inr ⟨j, hj, u, q, hg' ▸ hg, ou, oq, nu, nq⟩
            | true =>
              exact back u hu ⟨j, g, q, hw, hg, Or.inl hinputs, Or.inr ⟨ha, oq⟩⟩ ou nu
          | true =>
            have oq := (Bool.and_eq_false_iff.mp old).resolve_left (by simp [ou])
            exact back q hq ⟨j, g, u, hw, hg, Or.inr hinputs, Or.inr ⟨ha, ou⟩⟩ oq nq
        · rw [ho, evOr] at old new
          obtain ⟨ou, oq⟩ := Bool.or_eq_false_iff.mp old
          rcases Bool.or_eq_true_iff.mp new with nu | nq
          · exact back u hu ⟨j, g, q, hw, hg, Or.inl hinputs, Or.inl ho⟩ ou nu
          · exact back q hq ⟨j, g, u, hw, hg, Or.inr hinputs, Or.inl ho⟩ oq nq
  have singletonFalse (a : Fin 26) : v C.output (one a) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p, l, _, hp, hl⟩ := (computes (one a)).mp h
    have he : Fin.castAdd 13 p = Fin.natAdd 13 l :=
      (of_decide_eq_true hp).trans (of_decide_eq_true hl).symm
    have vals := congrArg Fin.val he
    change p.val = 13 + l.val at vals
    omega
  have pairTrue : v C.output (pairInput 0 13) = true := by
    apply (computes (pairInput 0 13)).mpr
    exact ⟨0, 0, by decide, by decide, by decide⟩
  have pairComm : pairInput (13 : Fin 26) 0 = pairInput 0 13 := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [pairEq, decide_eq_true_eq]
    exact or_comm
  by_contra noPath
  obtain ⟨j, hj, u, q, hg, ou, oq, nu, nq⟩ :=
    (trace 0 13 C.output (singletonFalse 0) pairTrue).resolve_left
      (fun h => noPath (Or.inl h))
  obtain ⟨k, hk, r, s, hg', pr, ps, nr, ns⟩ :=
    (trace 13 0 C.output (singletonFalse 13) (by rw [pairComm]; exact pairTrue)).resolve_left
      (fun h => noPath (Or.inr h))
  rw [pairComm] at nr ns
  have col0 : (gateAt C j).op = .and ∧ ∀ i ∈ (gateAt C j).inputs,
      v i (one 0) = false ∧ v i (pairInput 0 13) = true := by
    rw [gateAtOfGet hg]
    refine ⟨rfl, ?_⟩
    intro i hi
    have hi' : i = u ∨ i = q := by simpa using hi
    rcases hi' with rfl | rfl
    · exact ⟨ou, nu⟩
    · exact ⟨oq, nq⟩
  have col13 : (gateAt C k).op = .and ∧ ∀ i ∈ (gateAt C k).inputs,
      v i (one 13) = false ∧ v i (pairInput 0 13) = true := by
    rw [gateAtOfGet hg']
    refine ⟨rfl, ?_⟩
    intro i hi
    have hi' : i = r ∨ i = s := by simpa using hi
    rcases hi' with rfl | rfl
    · exact ⟨pr, nr⟩
    · exact ⟨ps, ns⟩
  have lines : ∀ p l : Fin 13,
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l := by decide
  have incidence : circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ decide (∃ p l : Fin 13,
      p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) = true
    simpa only [decide_eq_true_eq, ← lines] using computes x
  have dirtyGate : ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ¬ WireBelowOutput 26 C (26 + j) := by
    obtain ⟨m, hm, hand, x, hot, cold⟩ := dirty
    exact ⟨m, hm, hand, fun below => Bool.eq_false_iff.mp cold (below x hot)⟩
  by_cases same : j = k
  · subst k
    exact sameCollision C size model nodup incidence pairs dirtyGate noPath
      ⟨j, hj, col0.1, fun i hi => ⟨(col0.2 i hi).1, (col13.2 i hi).1, (col0.2 i hi).2⟩⟩
  · exact distinctCollisions C size model nodup incidence pairs dirtyGate noPath
      ⟨j, hj, k, hk, same, col0, col13⟩
