import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5353_73
    (hOneClean :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C0 C1 : PEqualNP.CircuitLowerBounds.Circuit),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) →
        C0.gates = C1.gates →
        PEqualNP.TopForm.IsAO2 (N + N) C0 →
        C0.output < N + N + C0.size →
        C1.output < N + N + C1.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C0 →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C1 →
        (∀ P S : Finset (Fin N), S.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L P S →
          C0.eval (PEqualNP.GenericRejection.incidenceInput P S) = false ∨
          C1.eval (PEqualNP.GenericRejection.incidenceInput P S) = false) →
        ∀ (E : Finset (Fin N)), E = ∅ →
        (∀ p1 p2 : Fin N,
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p1} E) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p2} E) = true → p1 = p2) →
        (∀ l1 l2 : Fin N,
          C0.eval (PEqualNP.GenericRejection.incidenceInput E {l1}) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput E {l2}) = true → l1 = l2) →
        N * q ≤ 100 * (C0.size + 1))
    (hPointsClean :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C0 C1 : PEqualNP.CircuitLowerBounds.Circuit),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) →
        C0.gates = C1.gates →
        PEqualNP.TopForm.IsAO2 (N + N) C0 →
        C0.output < N + N + C0.size →
        C1.output < N + N + C1.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C0 →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C1 →
        (∀ P S : Finset (Fin N), S.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L P S →
          C0.eval (PEqualNP.GenericRejection.incidenceInput P S) = false ∨
          C1.eval (PEqualNP.GenericRejection.incidenceInput P S) = false) →
        ∀ (E : Finset (Fin N)), E = ∅ →
        (∀ p1 p2 : Fin N,
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p1} E) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p2} E) = true → p1 = p2) →
        (∀ p1 p2 : Fin N,
          C1.eval (PEqualNP.GenericRejection.incidenceInput {p1} E) = true →
          C1.eval (PEqualNP.GenericRejection.incidenceInput {p2} E) = true → p1 = p2) →
        N * q ≤ 100 * (C0.size + 1))
    (hLinesClean :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C0 C1 : PEqualNP.CircuitLowerBounds.Circuit),
        350 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (L l).card = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) →
        C0.gates = C1.gates →
        PEqualNP.TopForm.IsAO2 (N + N) C0 →
        C0.output < N + N + C0.size →
        C1.output < N + N + C1.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C0 →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C1 →
        (∀ P S : Finset (Fin N), S.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L P S →
          C0.eval (PEqualNP.GenericRejection.incidenceInput P S) = false ∨
          C1.eval (PEqualNP.GenericRejection.incidenceInput P S) = false) →
        ∀ (E : Finset (Fin N)), E = ∅ →
        (∀ l1 l2 : Fin N,
          C0.eval (PEqualNP.GenericRejection.incidenceInput E {l1}) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput E {l2}) = true → l1 = l2) →
        (∀ l1 l2 : Fin N,
          C1.eval (PEqualNP.GenericRejection.incidenceInput E {l1}) = true →
          C1.eval (PEqualNP.GenericRejection.incidenceInput E {l2}) = true → l1 = l2) →
        N * q ≤ 100 * (C0.size + 1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (350 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * (x1 - (349 : ℕ)) ≤ (100 : ℕ) * x4.size - (349 : ℕ) * x2 := by
  classical
  intro q N L C hq hN hCard hUniq hAO2 hOutLo hOutHi hOutAnd hRight hFalse
  rcases hOutAnd with ⟨g, hgGet, hgOp⟩
  let k : ℕ := C.output - (N + N)
  have hkLt : k < C.gates.length := by
    change C.output - (N + N) < C.gates.length
    have : C.size = C.gates.length := rfl
    omega
  have hOutEq : C.output = N + N + k := by omega
  have hgEq : C.gates[k] = g := by
    have h1 : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hkLt
    have h2 : some C.gates[k] = some g := h1.symm.trans hgGet
    exact Option.some.inj h2
  have hgMem : g ∈ C.gates := by
    rw [← hgEq]
    exact List.getElem_mem hkLt
  have hgLen : g.inputs.length = 2 := hAO2.2.2 g hgMem
  rcases hIn : g.inputs with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩
  · simp [hIn] at hgLen
  · simp [hIn] at hgLen
  · let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun acc gt => acc ++ [gt.op.eval (gt.inputs.map fun i => acc.getD i false)]) w
    have wiresFrom_append (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
        wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
      simp [wiresFrom, List.foldl_append]
    have wiresFrom_ext (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons gt rest ih =>
        intro w
        let v := gt.op.eval (gt.inputs.map fun i => w.getD i false)
        obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
        refine ⟨v :: t, ?_, by simp [hl]⟩
        have hstep : wiresFrom (gt :: rest) w = wiresFrom rest (w ++ [v]) := rfl
        rw [hstep, ht]
        simp
    have length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
      rw [ht, List.length_append, hl]
    have getD_wiresFrom_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
        (hi : i < w.length) : (wiresFrom gs w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
      rw [ht, List.getD_append _ _ _ _ hi]
    have wiresFrom_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
        (hAO : ∀ gt ∈ gs, gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) :
        ∀ x y : List Bool, x.length = y.length →
        (∀ i, x.getD i false = true → y.getD i false = true) →
        ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
      induction gs with
      | nil =>
        intro x y _ hxy i hi
        exact hxy i hi
      | cons gt rest ih =>
        intro x y hlen hxy i hi
        have hgt := hAO gt (List.mem_cons_self ..)
        have hrest : ∀ g' ∈ rest, g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g'.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
          fun g' hg' => hAO g' (List.mem_cons_of_mem gt hg')
        have op_and_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
        have op_or_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
        have hstep :
            gt.op.eval (gt.inputs.map fun j => x.getD j false) = true →
            gt.op.eval (gt.inputs.map fun j => y.getD j false) = true := by
          rcases hgt with hand | hor
          · rw [hand, op_and_eval, op_and_eval]
            simp only [List.all_eq_true, List.mem_map,
              id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
            intro hx j hj
            exact hxy j (hx j hj)
          · rw [hor, op_or_eval, op_or_eval]
            simp only [List.any_eq_true, List.mem_map,
              id_eq, exists_exists_and_eq_and]
            rintro ⟨j, hj, hxj⟩
            exact ⟨j, hj, hxy j hxj⟩
        refine ih hrest
          (x ++ [gt.op.eval (gt.inputs.map fun j => x.getD j false)])
          (y ++ [gt.op.eval (gt.inputs.map fun j => y.getD j false)])
          (by simp [hlen]) ?_ i hi
        intro idx hidx
        by_cases hlt : idx < x.length
        · have hlt' : idx < y.length := by omega
          rw [List.getD_append _ _ _ _ hlt] at hidx
          rw [List.getD_append _ _ _ _ hlt']
          exact hxy idx hidx
        · have hge' : ¬ idx < y.length := by omega
          rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hlt)] at hidx
          rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hge')]
          have hsub : idx - y.length = idx - x.length := by omega
          rw [hsub]
          rcases Nat.eq_zero_or_pos (idx - x.length) with h0 | hpos
          · rw [h0] at hidx ⊢
            exact hstep hidx
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hidx
            simp at hidx
    let C0 : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take k, w0⟩
    let C1 : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take k, w1⟩
    have hGatesEq : C0.gates = C1.gates := rfl
    have hSize0 : C0.size = k := by
      change (C.gates.take k).length = k
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkLt)]
    have hSize1 : C1.size = k := hSize0
    have hGateAtK : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem?_getD, hgGet]
      rfl
    have hW0Lt : C0.output < N + N + C0.size := by
      rw [hSize0]
      exact hAO2.2.1 k hkLt w0 (by rw [hGateAtK, hIn]; simp)
    have hW1Lt : C1.output < N + N + C1.size := by
      rw [hSize1]
      exact hAO2.2.1 k hkLt w1 (by rw [hGateAtK, hIn]; simp)
    have hAO2_0 : PEqualNP.TopForm.IsAO2 (N + N) C0 := by
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        exact hAO2.1 gt (List.mem_of_mem_take hgt)
      · intro j hj i hi
        have hjk : j < k := by
          change j < (C.gates.take k).length at hj
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkLt)] at hj
          exact hj
        have hjC : j < C.gates.length := Nat.lt_trans hjk hkLt
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C0 j =
            PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
          change (C.gates.take k).getD j _ = C.gates.getD j _
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hjk]
        rw [hgat] at hi
        exact hAO2.2.1 j hjC i hi
      · intro gt hgt
        exact hAO2.2.2 gt (List.mem_of_mem_take hgt)
    have hEvalSplit : ∀ x : List Bool, x.length = N + N →
        C.eval x = (C0.eval x && C1.eval x) := by
      intro x hxlen
      have hSplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
        have hdrop : C.gates.drop k = g :: C.gates.drop (k + 1) := by
          rw [← hgEq]
          exact List.drop_eq_getElem_cons hkLt
        rw [← hdrop, List.take_append_drop]
      have hCeval : C.eval x = (wiresFrom C.gates x).getD (N + N + k) false := by
        change (C.wires x).getD C.output false = _
        rw [hOutEq]
        rfl
      rw [hCeval, hSplit, wiresFrom_append]
      let w := wiresFrom (C.gates.take k) x
      have hwlen : w.length = N + N + k := by
        rw [length_wiresFrom, hxlen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hkLt)]
      have hstep : wiresFrom (g :: C.gates.drop (k + 1)) w =
          wiresFrom (C.gates.drop (k + 1)) (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [hstep, getD_wiresFrom_lt _ _ _ (by simp [hwlen])]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hidx : N + N + k - w.length = 0 := by omega
      rw [hidx]
      have op_and_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
      rw [List.getD_cons_zero, hgOp, hIn, List.map_cons, List.map_cons, List.map_nil, op_and_eval]
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rfl
    have inc_def (P S : Finset (Fin N)) : PEqualNP.GenericRejection.incidenceInput P S =
        List.ofFn (fun p : Fin N => decide (p ∈ P)) ++ List.ofFn (fun l : Fin N => decide (l ∈ S)) := rfl
    have hIncLen : ∀ (P S : Finset (Fin N)),
        (PEqualNP.GenericRejection.incidenceInput P S).length = N + N := by
      intro P S
      rw [inc_def]
      simp
    have hRight0 : PEqualNP.GenericRejection.RightOnIncidentPairs L C0 := by
      intro l p hp
      have h := hRight l p hp
      rw [hEvalSplit _ (hIncLen {p} {l}), Bool.and_eq_true] at h
      exact h.1
    have hRight1 : PEqualNP.GenericRejection.RightOnIncidentPairs L C1 := by
      intro l p hp
      have h := hRight l p hp
      rw [hEvalSplit _ (hIncLen {p} {l}), Bool.and_eq_true] at h
      exact h.2
    have hFalsePair : ∀ (P S : Finset (Fin N)), S.card ≤ q →
        PEqualNP.GenericRejection.IsFalseInput L P S →
        C0.eval (PEqualNP.GenericRejection.incidenceInput P S) = false ∨
        C1.eval (PEqualNP.GenericRejection.incidenceInput P S) = false := by
      intro P S hS hF
      have h := hFalse P S hS hF
      rw [hEvalSplit _ (hIncLen P S), Bool.and_eq_false_iff] at h
      exact h
    have hMonoPair : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        D.gates = C.gates.take k →
        ∀ (P1 P2 S1 S2 : Finset (Fin N)), P1 ⊆ P2 → S1 ⊆ S2 →
        D.eval (PEqualNP.GenericRejection.incidenceInput P1 S1) = true →
        D.eval (PEqualNP.GenericRejection.incidenceInput P2 S2) = true := by
      intro D hDg P1 P2 S1 S2 hP hS hD1
      change (wiresFrom D.gates (PEqualNP.GenericRejection.incidenceInput P1 S1)).getD D.output false = true at hD1
      change (wiresFrom D.gates (PEqualNP.GenericRejection.incidenceInput P2 S2)).getD D.output false = true
      refine wiresFrom_mono D.gates (by rw [hDg]; exact hAO2_0.1) _ _
        (by rw [hIncLen, hIncLen]) ?_ D.output hD1
      intro i hi
      by_cases hlt : i < N
      · have h1 : (PEqualNP.GenericRejection.incidenceInput P1 S1).getD i false =
            decide (⟨i, hlt⟩ ∈ P1) := by
          rw [inc_def]
          rw [List.getD_append _ _ _ _ (by simp [hlt])]
          rw [List.getD_eq_getElem _ _ (by simp [hlt])]
          simp
        have h2 : (PEqualNP.GenericRejection.incidenceInput P2 S2).getD i false =
            decide (⟨i, hlt⟩ ∈ P2) := by
          rw [inc_def]
          rw [List.getD_append _ _ _ _ (by simp [hlt])]
          rw [List.getD_eq_getElem _ _ (by simp [hlt])]
          simp
        rw [h1, decide_eq_true_eq] at hi
        rw [h2, decide_eq_true_eq]
        exact hP hi
      · by_cases hlt2 : i < N + N
        · have hsub : i - N < N := by omega
          have h1 : (PEqualNP.GenericRejection.incidenceInput P1 S1).getD i false =
              decide (⟨i - N, hsub⟩ ∈ S1) := by
            rw [inc_def]
            rw [List.getD_append_right _ _ _ _ (by simp; omega)]
            simp only [List.length_ofFn]
            rw [List.getD_eq_getElem _ _ (by simp [hsub])]
            simp
          have h2 : (PEqualNP.GenericRejection.incidenceInput P2 S2).getD i false =
              decide (⟨i - N, hsub⟩ ∈ S2) := by
            rw [inc_def]
            rw [List.getD_append_right _ _ _ _ (by simp; omega)]
            simp only [List.length_ofFn]
            rw [List.getD_eq_getElem _ _ (by simp [hsub])]
            simp
          rw [h1, decide_eq_true_eq] at hi
          rw [h2, decide_eq_true_eq]
          exact hS hi
        · have hout : (PEqualNP.GenericRejection.incidenceInput P1 S1).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hIncLen]; omega)]
            rfl
          rw [hout] at hi
          simp at hi
    let E0 : Finset (Fin N) := ∅
    have hCross01 : ∀ p l : Fin N,
        C0.eval (PEqualNP.GenericRejection.incidenceInput {p} E0) = true →
        C1.eval (PEqualNP.GenericRejection.incidenceInput E0 {l}) = true → p ∈ L l := by
      intro p l hp hl
      by_contra hnot
      have hFalsePL : PEqualNP.GenericRejection.IsFalseInput L {p} {l} := by
        intro l' hl'
        rw [Finset.mem_singleton.mp hl']
        exact Finset.disjoint_singleton_right.mpr hnot
      have hpT : C0.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true :=
        hMonoPair C0 rfl {p} {p} E0 {l} (Finset.Subset.refl _) (Finset.empty_subset _) hp
      have hlT : C1.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true :=
        hMonoPair C1 rfl E0 {p} {l} {l} (Finset.empty_subset _) (Finset.Subset.refl _) hl
      rcases hFalsePair {p} {l} (by simp; omega) hFalsePL with h0 | h1
      · rw [hpT] at h0; simp at h0
      · rw [hlT] at h1; simp at h1
    have hCross10 : ∀ p l : Fin N,
        C1.eval (PEqualNP.GenericRejection.incidenceInput {p} E0) = true →
        C0.eval (PEqualNP.GenericRejection.incidenceInput E0 {l}) = true → p ∈ L l := by
      intro p l hp hl
      by_contra hnot
      have hFalsePL : PEqualNP.GenericRejection.IsFalseInput L {p} {l} := by
        intro l' hl'
        rw [Finset.mem_singleton.mp hl']
        exact Finset.disjoint_singleton_right.mpr hnot
      have hpT : C1.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true :=
        hMonoPair C1 rfl {p} {p} E0 {l} (Finset.Subset.refl _) (Finset.empty_subset _) hp
      have hlT : C0.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true :=
        hMonoPair C0 rfl E0 {p} {l} {l} (Finset.empty_subset _) (Finset.Subset.refl _) hl
      rcases hFalsePair {p} {l} (by simp; omega) hFalsePL with h0 | h1
      · rw [hlT] at h0; simp at h0
      · rw [hpT] at h1; simp at h1
    have hCard01 :
        (∀ p1 p2 : Fin N, C0.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true → p1 = p2) ∨
        (∀ l1 l2 : Fin N, C1.eval (PEqualNP.GenericRejection.incidenceInput E0 {l1}) = true →
          C1.eval (PEqualNP.GenericRejection.incidenceInput E0 {l2}) = true → l1 = l2) := by
      by_cases hA : ∀ p1 p2 : Fin N,
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true → p1 = p2
      · exact Or.inl hA
      · right
        intro l1 l2 hl1 hl2
        by_contra hlne
        have hex : ∃ p1 p2 : Fin N,
            C0.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true ∧
            C0.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true ∧ p1 ≠ p2 := by
          by_contra hno
          apply hA
          intro p1 p2 hp1 hp2
          by_contra hpne
          exact hno ⟨p1, p2, hp1, hp2, hpne⟩
        obtain ⟨p1, p2, hp1, hp2, hpne⟩ := hex
        obtain ⟨lStar, _, hUniqL⟩ := hUniq p1 p2 hpne
        have heq1 : l1 = lStar := hUniqL l1 ⟨hCross01 p1 l1 hp1 hl1, hCross01 p2 l1 hp2 hl1⟩
        have heq2 : l2 = lStar := hUniqL l2 ⟨hCross01 p1 l2 hp1 hl2, hCross01 p2 l2 hp2 hl2⟩
        exact hlne (heq1.trans heq2.symm)
    have hCard10 :
        (∀ p1 p2 : Fin N, C1.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true →
          C1.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true → p1 = p2) ∨
        (∀ l1 l2 : Fin N, C0.eval (PEqualNP.GenericRejection.incidenceInput E0 {l1}) = true →
          C0.eval (PEqualNP.GenericRejection.incidenceInput E0 {l2}) = true → l1 = l2) := by
      by_cases hA : ∀ p1 p2 : Fin N,
          C1.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true →
          C1.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true → p1 = p2
      · exact Or.inl hA
      · right
        intro l1 l2 hl1 hl2
        by_contra hlne
        have hex : ∃ p1 p2 : Fin N,
            C1.eval (PEqualNP.GenericRejection.incidenceInput {p1} E0) = true ∧
            C1.eval (PEqualNP.GenericRejection.incidenceInput {p2} E0) = true ∧ p1 ≠ p2 := by
          by_contra hno
          apply hA
          intro p1 p2 hp1 hp2
          by_contra hpne
          exact hno ⟨p1, p2, hp1, hp2, hpne⟩
        obtain ⟨p1, p2, hp1, hp2, hpne⟩ := hex
        obtain ⟨lStar, _, hUniqL⟩ := hUniq p1 p2 hpne
        have heq1 : l1 = lStar := hUniqL l1 ⟨hCross10 p1 l1 hp1 hl1, hCross10 p2 l1 hp2 hl1⟩
        have heq2 : l2 = lStar := hUniqL l2 ⟨hCross10 p1 l2 hp1 hl2, hCross10 p2 l2 hp2 hl2⟩
        exact hlne (heq1.trans heq2.symm)
    have hBound : N * q ≤ 100 * (C0.size + 1) := by
      rcases hCard01 with hA0 | hB1
      · rcases hCard10 with hA1 | hB0
        · exact hPointsClean q N L C0 C1 hq hN hCard hUniq hGatesEq hAO2_0 hW0Lt hW1Lt
            hRight0 hRight1 hFalsePair E0 rfl hA0 hA1
        · exact hOneClean q N L C0 C1 hq hN hCard hUniq hGatesEq hAO2_0 hW0Lt hW1Lt
            hRight0 hRight1 hFalsePair E0 rfl hA0 hB0
      · rcases hCard10 with hA1 | hB0
        · have hAO2_1 : PEqualNP.TopForm.IsAO2 (N + N) C1 := by
            refine ⟨?_, ?_, ?_⟩
            · exact hAO2_0.1
            · exact hAO2_0.2.1
            · exact hAO2_0.2.2
          have hFalseSwap : ∀ (P S : Finset (Fin N)), S.card ≤ q →
              PEqualNP.GenericRejection.IsFalseInput L P S →
              C1.eval (PEqualNP.GenericRejection.incidenceInput P S) = false ∨
              C0.eval (PEqualNP.GenericRejection.incidenceInput P S) = false :=
            fun P S hS hF => (hFalsePair P S hS hF).symm
          have hRes := hOneClean q N L C1 C0 hq hN hCard hUniq hGatesEq.symm hAO2_1 hW1Lt hW0Lt
            hRight1 hRight0 hFalseSwap E0 rfl hA1 hB1
          rwa [hSize1, ← hSize0] at hRes
        · exact hLinesClean q N L C0 C1 hq hN hCard hUniq hGatesEq hAO2_0 hW0Lt hW1Lt
            hRight0 hRight1 hFalsePair E0 rfl hB0 hB1
    have hSizeLe : C0.size + 1 ≤ C.size := by
      change C0.size + 1 ≤ C.gates.length
      omega
    have hNq : N * q ≤ 100 * C.size := le_trans hBound (Nat.mul_le_mul_left 100 hSizeLe)
    have hEq : N * (q - 349) + 349 * N = N * q := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm 349 N]
      exact Nat.sub_add_cancel (Nat.mul_le_mul_left N (by omega))
    omega
  · simp [hIn] at hgLen
