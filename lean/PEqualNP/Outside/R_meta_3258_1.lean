import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_3258_1
    (topFormNorm :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
        let sound := fun (D : Circuit) (w : ℕ) =>
          ∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
            wireValue D (incidenceInput X Y) w = false
        IsAO2 (n + n) C → C.output < n + n + C.size →
        RightOnIncidentPairs S C → sound C C.output →
        ∃ C' : Circuit, C'.size ≤ C.size ∧ IsAO2 (n + n) C' ∧
          C'.output < n + n + C'.size ∧ RightOnIncidentPairs S C' ∧ sound C' C'.output ∧
          ∀ i < C'.size, ∀ j < C'.size,
            (gateAt C' i).op = GateOp.and → sound C' (n + n + i) →
            (gateAt C' j).op = GateOp.and → ¬ InCone (n + n) C' i j)
    (starCost :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (E : Finset (Fin n × Fin n)),
        2 ≤ q →
        (∀ p r l l' : Fin n, p ≠ r → l ≠ l' → ¬ (p ∈ S l ∧ r ∈ S l ∧ p ∈ S l' ∧ r ∈ S l')) →
        IsAO2 (n + n) C →
        (∀ pl ∈ E, pl.1 ∈ S pl.2 ∧
          ∃ a < C.size, (gateAt C a).op = GateOp.and ∧
            (∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
              wireValue C (incidenceInput X Y) (n + n + a) = false) ∧
            ((Fin.castAdd n pl.1 ∈ orIn (n + n) C (opnd C a 0) ∧
              Fin.natAdd n pl.2 ∈ orIn (n + n) C (opnd C a 1)) ∨
             (Fin.natAdd n pl.2 ∈ orIn (n + n) C (opnd C a 0) ∧
              Fin.castAdd n pl.1 ∈ orIn (n + n) C (opnd C a 1)))) →
        E.card ≤ C.size)
    (topFormJunkLower :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (U : Finset (Fin n × Fin n)),
        let sound := fun (w : ℕ) =>
          ∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
            wireValue C (incidenceInput X Y) w = false
        100 < q → n = q ^ 2 + q + 1 →
        (∀ l : Fin n, (S l).card = q + 1) →
        (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
        IsAO2 (n + n) C → C.output < n + n + C.size →
        RightOnIncidentPairs S C → sound C.output →
        (∀ i < C.size, ∀ j < C.size,
          (gateAt C i).op = GateOp.and → sound (n + n + i) →
          (gateAt C j).op = GateOp.and → ¬ InCone (n + n) C i j) →
        (∀ pl ∈ U, pl.1 ∈ S pl.2 ∧
          ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ ¬ sound (n + n + j) ∧
            wireValue C (incidenceInput {pl.1} {pl.2}) (n + n + j) = true) →
        99 * (n * q) < 100 * U.card →
        n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → (∃ x13 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x14 : Finset (Fin x2)), (100 : ℕ) < x14.card ∧ have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true}; Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hdeg hjoin hAO hout hacc hrej _
  let : DecidableEq GateOp := gateOpDecEq
  obtain ⟨D, hDsize, hDAO, hDout, hDacc, hDrej, hDtop⟩ :=
    topFormNorm q n S C hAO hout hacc hrej
  by_cases hdone : n * q ≤ 100 * D.size
  · exact hdone.trans (Nat.mul_le_mul_left 100 hDsize)
  have hsmall : 100 * D.size < n * q := Nat.lt_of_not_ge hdone
  obtain ⟨hDao, hDrb, hDlen2⟩ := hDAO
  let wf : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wf_len : ∀ (gs : List Gate) (w : List Bool), (wf gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wf]
    | cons g gs ih =>
      intro w
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      simp only [wf, List.foldl_cons] at h1 ⊢
      rw [h1]
      simp
      omega
  have wf_keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wf gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
      simp only [wf, List.foldl_cons] at h1 ⊢
      rw [h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have wf_take : ∀ (gs : List Gate) (w : List Bool) (k i : ℕ),
      i < w.length + k → k ≤ gs.length →
      (wf gs w).getD i false = (wf (gs.take k) w).getD i false := by
    intro gs w k i hi hk
    conv_lhs => rw [← List.take_append_drop k gs]
    have hsplit : wf (gs.take k ++ gs.drop k) w = wf (gs.drop k) (wf (gs.take k) w) := by
      dsimp only [wf]
      rw [List.foldl_append]
    rw [hsplit]
    apply wf_keep
    rw [wf_len, List.length_take, Nat.min_eq_left hk]
    exact hi
  have wf_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (wf gs w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i => (wf (gs.take k) w).getD i false) := by
    intro gs w k hk
    rw [wf_take gs w (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk]
    have hsnoc : wf (gs.take k ++ [gs[k]]) w =
        wf (gs.take k) w ++
          [gs[k].op.eval (gs[k].inputs.map fun i => (wf (gs.take k) w).getD i false)] := by
      dsimp only [wf]
      rw [List.foldl_append]
      rfl
    rw [hsnoc]
    have hlen : (wf (gs.take k) w).length = w.length + k := by
      rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    rw [← hlen]
    simp [List.getD_eq_getElem?_getD]
  have wire_input : ∀ (x : List Bool) (w : ℕ), w < x.length → wireValue D x w = x.getD w false := by
    intro x w hw
    exact wf_keep D.gates x w hw
  have wire_gate : ∀ (x : List Bool) (k : ℕ) (hk : k < D.size), x.length = n + n →
      wireValue D x (n + n + k) =
        (gateAt D k).op.eval
          ((gateAt D k).inputs.map fun i => wireValue D x i) := by
    intro x k hk hx
    have hkl : k < D.gates.length := hk
    have hgk : gateAt D k = D.gates[k] := List.getD_eq_getElem D.gates _ hkl
    have h1 := wf_gate D.gates x k hkl
    rw [hx] at h1
    change (wf D.gates x).getD (n + n + k) false = _
    rw [h1, hgk]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hilt : i < n + n + k := by
      have := hDrb k hkl i
      rw [hgk] at this
      exact this hi
    exact (wf_take D.gates x k i (by omega) (Nat.le_of_lt hkl)).symm
  have gate_inputs_pair : ∀ (k : ℕ) (hk : k < D.size),
      (gateAt D k).inputs = [opnd D k 0, opnd D k 1] := by
    intro k hk
    have hkl : k < D.gates.length := hk
    have hgk : gateAt D k = D.gates[k] := List.getD_eq_getElem D.gates _ hkl
    have hlen : (gateAt D k).inputs.length = 2 := by
      rw [hgk]
      exact hDlen2 D.gates[k] (List.getElem_mem hkl)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    change (gateAt D k).inputs = [(gateAt D k).inputs.getD 0 0, (gateAt D k).inputs.getD 1 0]
    rw [hab]
    rfl
  have wire_or : ∀ (x : List Bool) (k : ℕ) (hk : k < D.size), x.length = n + n →
      (gateAt D k).op = GateOp.or →
      wireValue D x (n + n + k) =
        (wireValue D x (opnd D k 0) || wireValue D x (opnd D k 1)) := by
    intro x k hk hx hop
    rw [wire_gate x k hk hx, hop, gate_inputs_pair k hk]
    change ([wireValue D x (opnd D k 0), wireValue D x (opnd D k 1)].any id) = _
    simp
  have wire_and : ∀ (x : List Bool) (k : ℕ) (hk : k < D.size), x.length = n + n →
      (gateAt D k).op = GateOp.and →
      wireValue D x (n + n + k) =
        (wireValue D x (opnd D k 0) && wireValue D x (opnd D k 1)) := by
    intro x k hk hx hop
    rw [wire_gate x k hk hx, hop, gate_inputs_pair k hk]
    change ([wireValue D x (opnd D k 0), wireValue D x (opnd D k 1)].all id) = _
    simp
  have os_len : ∀ (gs : List Gate) (acc : List (List ℕ)),
      (gs.foldl (orStep (n + n)) acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      change (acc ++ [_]).length + gs.length = _
      simp
      omega
  have os_keep : ∀ (gs : List Gate) (acc : List (List ℕ)) (j : ℕ), j < acc.length →
      (gs.foldl (orStep (n + n)) acc).getD j [] = acc.getD j [] := by
    intro gs
    induction gs with
    | nil => intro acc j _; rfl
    | cons g gs ih =>
      intro acc j hj
      simp only [List.foldl_cons]
      have hlen1 : j < (orStep (n + n) acc g).length := by
        change j < (acc ++ [_]).length
        simp
        omega
      rw [ih _ j hlen1]
      change (acc ++ [_]).getD j [] = acc.getD j []
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have os_take : ∀ (gs : List Gate) (k j : ℕ), j < k → k ≤ gs.length →
      (gs.foldl (orStep (n + n)) []).getD j [] =
        ((gs.take k).foldl (orStep (n + n)) []).getD j [] := by
    intro gs k j hj hk
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.foldl_append]
    apply os_keep
    rw [os_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left hk]
    exact hj
  have os_get : ∀ (k : ℕ) (hk : k < D.size),
      (orSets (n + n) D).getD k [] =
        k :: (if (gateAt D k).op = GateOp.or then
          ((gateAt D k).inputs.filter (fun w => decide (n + n ≤ w ∧ w < n + n + k))).flatMap
            (fun w => (orSets (n + n) D).getD (w - (n + n)) [])
          else []) := by
    intro k hk
    have hkl : k < D.gates.length := hk
    change (D.gates.foldl (orStep (n + n)) []).getD k [] =
        k :: (if (gateAt D k).op = GateOp.or then
          ((gateAt D k).inputs.filter (fun w => decide (n + n ≤ w ∧ w < n + n + k))).flatMap
            (fun w => (D.gates.foldl (orStep (n + n)) []).getD (w - (n + n)) [])
          else [])
    have hgk : gateAt D k = D.gates[k] := List.getD_eq_getElem D.gates _ hkl
    rw [os_take D.gates (k + 1) k (by omega) hkl, List.take_succ_eq_append_getElem hkl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    set pre := (D.gates.take k).foldl (orStep (n + n)) []
    have hlen : pre.length = k := by
      simp only [pre, os_len, List.length_nil, Nat.zero_add, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hkl)]
    have hstep : orStep (n + n) pre D.gates[k] =
        pre ++ [k :: (if (gateAt D k).op = GateOp.or then
          ((gateAt D k).inputs.filter (fun w => decide (n + n ≤ w ∧ w < n + n + k))).flatMap
            (fun w => pre.getD (w - (n + n)) [])
          else [])] := by
      change pre ++ [pre.length :: (if D.gates[k].op = GateOp.or then
          (D.gates[k].inputs.filter (fun w => decide (n + n ≤ w ∧ w < n + n + pre.length))).flatMap
            (fun w => pre.getD (w - (n + n)) [])
          else [])] = _
      rw [hlen, hgk]
    rw [hstep]
    have hget : ∀ (xs : List (List ℕ)) (a : List ℕ), (xs ++ [a]).getD xs.length [] = a := by
      intro xs a
      simp [List.getD_eq_getElem?_getD]
    have hgetk := hget pre (k :: (if (gateAt D k).op = GateOp.or then
          ((gateAt D k).inputs.filter (fun w => decide (n + n ≤ w ∧ w < n + n + k))).flatMap
            (fun w => pre.getD (w - (n + n)) [])
          else []))
    rw [hlen] at hgetk
    rw [hgetk]
    congr 1
    by_cases hop : (gateAt D k).op = GateOp.or
    · simp only [hop, ite_true]
      apply List.flatMap_congr
      intro w hw
      rw [List.mem_filter] at hw
      have hwb : n + n ≤ w ∧ w < n + n + k := of_decide_eq_true hw.2
      exact (os_take D.gates k (w - (n + n)) (by omega) (Nat.le_of_lt hkl)).symm
    · simp only [hop, ite_false]
  have os_oob : ∀ (k : ℕ), D.size ≤ k → (orSets (n + n) D).getD k [] = [] := by
    intro k hk
    have hkl : D.gates.length ≤ k := hk
    rw [List.getD_eq_default]
    change (D.gates.foldl (orStep (n + n)) []).length ≤ k
    rw [os_len]
    simpa using hkl
  have orReaches_self : ∀ (k : ℕ), k < D.size → OrReaches (n + n) D (n + n + k) k := by
    intro k hk
    refine ⟨by omega, ?_⟩
    have hsub : n + n + k - (n + n) = k := by omega
    rw [hsub, os_get k hk]
    exact List.mem_cons_self
  have orReaches_or_step : ∀ (g : ℕ) (hg : g < D.size) (w k : ℕ),
      (gateAt D g).op = GateOp.or → w ∈ (gateAt D g).inputs →
      OrReaches (n + n) D w k → OrReaches (n + n) D (n + n + g) k := by
    intro g hg w k hop hw hr
    have hlt : w < n + n + g := hDrb g hg w hw
    refine ⟨by omega, ?_⟩
    have hsub : n + n + g - (n + n) = g := by omega
    rw [hsub, os_get g hg]
    simp only [hop, ite_true]
    apply List.mem_cons_of_mem
    rw [List.mem_flatMap]
    refine ⟨w, ?_, hr.2⟩
    rw [List.mem_filter]
    exact ⟨hw, decide_eq_true ⟨hr.1, hlt⟩⟩
  have orReaches_true : ∀ (j : ℕ), j < D.size → ∀ (x : List Bool) (k : ℕ),
      x.length = n + n → OrReaches (n + n) D (n + n + j) k →
      wireValue D x (n + n + k) = true → wireValue D x (n + n + j) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj x k hx hr htk
      have hmem : k ∈ (orSets (n + n) D).getD j [] := by
        have h1 := hr.2
        have hsub : n + n + j - (n + n) = j := by omega
        rwa [hsub] at h1
      rw [os_get j hj] at hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact htk
      · by_cases hop : (gateAt D j).op = GateOp.or
        · simp only [hop, ite_true] at htail
          rw [List.mem_flatMap] at htail
          obtain ⟨w, hwf, hwk⟩ := htail
          rw [List.mem_filter] at hwf
          obtain ⟨hwin, hwdec⟩ := hwf
          have hwb : n + n ≤ w ∧ w < n + n + j := of_decide_eq_true hwdec
          have hjeq : n + n + (w - (n + n)) = w := by omega
          have hwt : wireValue D x w = true := by
            rw [← hjeq]
            exact ih (w - (n + n)) (by omega) (by omega) x k hx ⟨by omega, by simpa [hjeq] using hwk⟩ htk
          rw [wire_gate x j hj hx, hop]
          change ((gateAt D j).inputs.map fun i => wireValue D x i).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp, id]
          exact ⟨w, hwin, hwt⟩
        · simp only [hop, ite_false] at htail
          simp at htail
  have orIn_true : ∀ (w : ℕ) (i : Fin (n + n)) (x : List Bool),
      x.length = n + n → i ∈ orIn (n + n) D w → x.getD i.val false = true →
      wireValue D x w = true := by
    intro w i x hx hi hxi
    have hilt := i.isLt
    have hi2 := (Finset.mem_filter.mp hi).2
    rcases hi2 with heq | ⟨k, hk, hr, hop, hin⟩
    · rw [← heq]
      rw [wire_input x i.val (by omega)]
      exact hxi
    · have hkt : wireValue D x (n + n + k) = true := by
        rw [wire_gate x k hk hx, hop]
        change ((gateAt D k).inputs.map fun i => wireValue D x i).any id = true
        simp only [List.any_map, List.any_eq_true, Function.comp, id]
        refine ⟨i.val, hin, ?_⟩
        rw [wire_input x i.val (by omega)]
        exact hxi
      have hwlt : w - (n + n) < D.size := by
        by_contra hge
        have hnil := os_oob (w - (n + n)) (Nat.le_of_not_lt hge)
        have h2 := hr.2
        rw [hnil] at h2
        simp at h2
      have hwge : n + n ≤ w := hr.1
      have hweq : n + n + (w - (n + n)) = w := by omega
      rw [← hweq]
      exact orReaches_true (w - (n + n)) hwlt x k hx (by rwa [hweq]) hkt
  have orIn_or_gate : ∀ (g : ℕ) (hg : g < D.size) (w : ℕ) (i : Fin (n + n)),
      (gateAt D g).op = GateOp.or → w ∈ (gateAt D g).inputs →
      i ∈ orIn (n + n) D w → i ∈ orIn (n + n) D (n + n + g) := by
    intro g hg w i hop hw hi
    have hi2 := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ?_⟩
    rcases hi2 with heq | ⟨k, hk, hr, hkop, hkin⟩
    · refine ⟨g, hg, orReaches_self g hg, hop, ?_⟩
      rwa [heq]
    · exact ⟨k, hk, orReaches_or_step g hg w k hop hw hr, hkop, hkin⟩
  have inc_len : ∀ (X Y : Finset (Fin n)), (incidenceInput X Y).length = n + n := by
    intro X Y
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))).length = n + n
    simp
  have inc_get_left : ∀ (X Y : Finset (Fin n)) (p : Fin n),
      (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
    intro X Y p
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))).getD p.val false = _
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [p.isLt]
  have inc_get_right : ∀ (X Y : Finset (Fin n)) (l : Fin n),
      (incidenceInput X Y).getD (n + l.val) false = decide (l ∈ Y) := by
    intro X Y l
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))).getD (n + l.val) false = _
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    have hsub : n + l.val - n = l.val := by omega
    rw [hsub, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [l.isLt]
  let soundD : ℕ → Prop := fun w =>
    ∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
      wireValue D (incidenceInput X Y) w = false
  let StarCov : Fin n → Fin n → Prop := fun p l =>
    ∃ a < D.size, (gateAt D a).op = GateOp.and ∧ soundD (n + n + a) ∧
      ((Fin.castAdd n p ∈ orIn (n + n) D (opnd D a 0) ∧
        Fin.natAdd n l ∈ orIn (n + n) D (opnd D a 1)) ∨
       (Fin.natAdd n l ∈ orIn (n + n) D (opnd D a 0) ∧
        Fin.castAdd n p ∈ orIn (n + n) D (opnd D a 1)))
  let JunkCov : Fin n → Fin n → Prop := fun p l =>
    ∃ j < D.size, (gateAt D j).op = GateOp.and ∧ ¬ soundD (n + n + j) ∧
      wireValue D (incidenceInput {p} {l}) (n + n + j) = true
  have sound_no_point : ∀ (w : ℕ) (p : Fin n), soundD w →
      Fin.castAdd n p ∉ orIn (n + n) D w := by
    intro w p hs hmem
    have hget : (incidenceInput ({p} : Finset (Fin n)) (∅ : Finset (Fin n))).getD (Fin.castAdd n p).val false = true := by
      have h1 := inc_get_left ({p} : Finset (Fin n)) (∅ : Finset (Fin n)) p
      rw [Fin.val_castAdd]
      simpa using h1
    have ht := orIn_true w (Fin.castAdd n p) (incidenceInput {p} ∅) (inc_len _ _) hmem hget
    have hf := hs {p} ∅ (by simp) (by intro l hl; simp at hl)
    exact Bool.noConfusion (ht.symm.trans hf)
  have sound_no_line : ∀ (w : ℕ) (l : Fin n), soundD w →
      Fin.natAdd n l ∉ orIn (n + n) D w := by
    intro w l hs hmem
    have hget : (incidenceInput (∅ : Finset (Fin n)) ({l} : Finset (Fin n))).getD (Fin.natAdd n l).val false = true := by
      have h1 := inc_get_right (∅ : Finset (Fin n)) ({l} : Finset (Fin n)) l
      have hv : (Fin.natAdd n l).val = n + l.val := Fin.val_natAdd n l
      rw [hv]
      simpa using h1
    have ht := orIn_true w (Fin.natAdd n l) (incidenceInput ∅ {l}) (inc_len _ _) hmem hget
    have hf := hs ∅ {l} (by simp; omega) (by intro l' _; exact Finset.disjoint_empty_right _)
    exact Bool.noConfusion (ht.symm.trans hf)
  have cover_each : ∀ (p l : Fin n), p ∈ S l → StarCov p l ∨ JunkCov p l := by
    intro p l hpl
    by_cases hj : JunkCov p l
    · exact Or.inr hj
    · left
      have hnoJunk : ∀ j < D.size, (gateAt D j).op = GateOp.and →
          wireValue D (incidenceInput {p} {l}) (n + n + j) = true → soundD (n + n + j) := by
        intro j hjs hop ht
        by_contra hns
        exact hj ⟨j, hjs, hop, hns, ht⟩
      have hwalk : ∀ w < n + n + D.size,
          wireValue D (incidenceInput {p} {l}) w = true →
          Fin.castAdd n p ∈ orIn (n + n) D w ∨
          Fin.natAdd n l ∈ orIn (n + n) D w ∨
          StarCov p l := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw hwt
          by_cases hwin : w < n + n
          · rw [wire_input _ w (by rw [inc_len]; exact hwin)] at hwt
            by_cases hwp : w < n
            · have h1 := inc_get_left ({p} : Finset (Fin n)) ({l} : Finset (Fin n)) ⟨w, hwp⟩
              change (incidenceInput {p} {l}).getD w false = decide (⟨w, hwp⟩ ∈ ({p} : Finset (Fin n))) at h1
              rw [h1, decide_eq_true_eq, Finset.mem_singleton] at hwt
              left
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
              have hv : w = p.val := congrArg Fin.val hwt
              simp [Fin.val_castAdd, hv]
            · have hwl : w - n < n := by omega
              have h1 := inc_get_right ({p} : Finset (Fin n)) ({l} : Finset (Fin n)) ⟨w - n, hwl⟩
              have hadd : n + (w - n) = w := by omega
              rw [hadd] at h1
              rw [h1, decide_eq_true_eq, Finset.mem_singleton] at hwt
              right
              left
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
              have hv : w - n = l.val := congrArg Fin.val hwt
              have hvn : (Fin.natAdd n l).val = n + l.val := Fin.val_natAdd n l
              omega
          · set g := w - (n + n)
            have hg : g < D.size := by omega
            have hgl : g < D.gates.length := hg
            have hweq : n + n + g = w := by omega
            have hpair := gate_inputs_pair g hg
            have hu_mem : opnd D g 0 ∈ (gateAt D g).inputs := by rw [hpair]; simp
            have hv_mem : opnd D g 1 ∈ (gateAt D g).inputs := by rw [hpair]; simp
            have hult : opnd D g 0 < w := by rw [← hweq]; exact hDrb g hgl _ hu_mem
            have hvlt : opnd D g 1 < w := by rw [← hweq]; exact hDrb g hgl _ hv_mem
            have hgk : gateAt D g = D.gates[g] := List.getD_eq_getElem D.gates _ hgl
            have hop : (gateAt D g).op = GateOp.and ∨ (gateAt D g).op = GateOp.or := by
              rw [hgk]
              exact hDao D.gates[g] (List.getElem_mem hgl)
            rw [← hweq] at hwt ⊢
            rcases hop with hand | hor
            · have hsnd : soundD (n + n + g) := hnoJunk g hg hand hwt
              rw [wire_and _ g hg (inc_len _ _) hand, Bool.and_eq_true] at hwt
              have hiu := ih (opnd D g 0) hult (by omega) hwt.1
              have hiv := ih (opnd D g 1) hvlt (by omega) hwt.2
              rcases hiu with hup | hul | hstar
              · rcases hiv with hvp | hvl | hstar
                · exfalso
                  have hgp : (incidenceInput ({p} : Finset (Fin n)) (∅ : Finset (Fin n))).getD (Fin.castAdd n p).val false = true := by
                    have h1 := inc_get_left ({p} : Finset (Fin n)) (∅ : Finset (Fin n)) p
                    rw [Fin.val_castAdd]
                    simpa using h1
                  have hu1 := orIn_true (opnd D g 0) (Fin.castAdd n p) (incidenceInput {p} ∅) (inc_len _ _) hup hgp
                  have hv1 := orIn_true (opnd D g 1) (Fin.castAdd n p) (incidenceInput {p} ∅) (inc_len _ _) hvp hgp
                  have hg1 : wireValue D (incidenceInput ({p} : Finset (Fin n)) (∅ : Finset (Fin n))) (n + n + g) = true := by
                    rw [wire_and _ g hg (inc_len _ _) hand, hu1, hv1]
                    rfl
                  have hgf := hsnd {p} ∅ (by simp) (by intro l' hl'; simp at hl')
                  exact Bool.noConfusion (hg1.symm.trans hgf)
                · exact Or.inr (Or.inr ⟨g, hg, hand, hsnd, Or.inl ⟨hup, hvl⟩⟩)
                · exact Or.inr (Or.inr hstar)
              · rcases hiv with hvp | hvl | hstar
                · exact Or.inr (Or.inr ⟨g, hg, hand, hsnd, Or.inr ⟨hul, hvp⟩⟩)
                · exfalso
                  have hgl' : (incidenceInput (∅ : Finset (Fin n)) ({l} : Finset (Fin n))).getD (Fin.natAdd n l).val false = true := by
                    have h1 := inc_get_right (∅ : Finset (Fin n)) ({l} : Finset (Fin n)) l
                    have hv : (Fin.natAdd n l).val = n + l.val := Fin.val_natAdd n l
                    rw [hv]
                    simpa using h1
                  have hu1 := orIn_true (opnd D g 0) (Fin.natAdd n l) (incidenceInput ∅ {l}) (inc_len _ _) hul hgl'
                  have hv1 := orIn_true (opnd D g 1) (Fin.natAdd n l) (incidenceInput ∅ {l}) (inc_len _ _) hvl hgl'
                  have hg1 : wireValue D (incidenceInput (∅ : Finset (Fin n)) ({l} : Finset (Fin n))) (n + n + g) = true := by
                    rw [wire_and _ g hg (inc_len _ _) hand, hu1, hv1]
                    rfl
                  have hgf := hsnd ∅ {l} (by simp; omega) (by intro l' _; exact Finset.disjoint_empty_right _)
                  exact Bool.noConfusion (hg1.symm.trans hgf)
                · exact Or.inr (Or.inr hstar)
              · exact Or.inr (Or.inr hstar)
            · rw [wire_or _ g hg (inc_len _ _) hor, Bool.or_eq_true] at hwt
              rcases hwt with hu1 | hv1
              · rcases ih (opnd D g 0) hult (by omega) hu1 with hup | hul | hstar
                · exact Or.inl (orIn_or_gate g hg _ _ hor hu_mem hup)
                · exact Or.inr (Or.inl (orIn_or_gate g hg _ _ hor hu_mem hul))
                · exact Or.inr (Or.inr hstar)
              · rcases ih (opnd D g 1) hvlt (by omega) hv1 with hvp | hvl | hstar
                · exact Or.inl (orIn_or_gate g hg _ _ hor hv_mem hvp)
                · exact Or.inr (Or.inl (orIn_or_gate g hg _ _ hor hv_mem hvl))
                · exact Or.inr (Or.inr hstar)
      have hout_res := hwalk D.output hDout (hDacc l p hpl)
      rcases hout_res with hp0 | hl0 | hstar
      · exact False.elim (sound_no_point D.output p hDrej hp0)
      · exact False.elim (sound_no_line D.output l hDrej hl0)
      · exact hstar
  classical
  let Inc : Finset (Fin n × Fin n) := Finset.univ.filter fun pl => pl.1 ∈ S pl.2
  let E : Finset (Fin n × Fin n) := Inc.filter fun pl => StarCov pl.1 pl.2
  let U : Finset (Fin n × Fin n) := Inc.filter fun pl => JunkCov pl.1 pl.2
  have hInc_card : Inc.card = n * (q + 1) := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have hinner : ∀ l : Fin n, (∑ p : Fin n, if p ∈ S l then 1 else 0) = q + 1 := by
      intro l
      rw [← Finset.card_filter]
      have hfeq : Finset.univ.filter (fun p : Fin n => p ∈ S l) = S l := by
        ext p
        simp
      rw [hfeq, hdeg l]
    simp [hinner]
  have hsub : Inc ⊆ E ∪ U := by
    intro pl hpl
    rw [Finset.mem_union]
    have hmem : pl.1 ∈ S pl.2 := (Finset.mem_filter.mp hpl).2
    rcases cover_each pl.1 pl.2 hmem with hs | hj
    · exact Or.inl (Finset.mem_filter.mpr ⟨hpl, hs⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hpl, hj⟩)
  have hsum : n * (q + 1) ≤ E.card + U.card := by
    calc n * (q + 1) = Inc.card := hInc_card.symm
      _ ≤ (E ∪ U).card := Finset.card_le_card hsub
      _ ≤ E.card + U.card := Finset.card_union_le E U
  have hnoC4 : ∀ p r l l' : Fin n, p ≠ r → l ≠ l' →
      ¬ (p ∈ S l ∧ r ∈ S l ∧ p ∈ S l' ∧ r ∈ S l') := by
    intro p r l l' hpr hll h
    exact hll ((hjoin p r hpr).unique ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩)
  have hEcard : E.card ≤ D.size := starCost q n S D E (by omega) hnoC4 ⟨hDao, hDrb, hDlen2⟩ (by
    intro pl hpl
    rw [Finset.mem_filter] at hpl
    exact ⟨(Finset.mem_filter.mp hpl.1).2, hpl.2⟩)
  have hUlarge : 99 * (n * q) < 100 * U.card := by
    have h1 : n * q + n ≤ D.size + U.card := by
      have : n * (q + 1) = n * q + n := by ring
      omega
    omega
  have hUok : ∀ pl ∈ U, pl.1 ∈ S pl.2 ∧
      ∃ j < D.size, (gateAt D j).op = GateOp.and ∧ ¬ soundD (n + n + j) ∧
        wireValue D (incidenceInput {pl.1} {pl.2}) (n + n + j) = true := by
    intro pl hpl
    rw [Finset.mem_filter] at hpl
    exact ⟨(Finset.mem_filter.mp hpl.1).2, hpl.2⟩
  have hfin := topFormJunkLower q n S D U hq hn hdeg hjoin ⟨hDao, hDrb, hDlen2⟩ hDout hDacc hDrej hDtop hUok hUlarge
  exact hfin.trans (Nat.mul_le_mul_left 100 hDsize)
