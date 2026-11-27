import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5687_521
    (hTopForm : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsAO2 x1 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x2 x8 ∧ PEqualNP.TopForm.TopForm x2 x8 ∧ x8.size ≤ x4.size ∧
        ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x2 x9 → PEqualNP.TopForm.TopForm x2 x9 →
          (PEqualNP.TopForm.Ustar x2 x8).card ≤ (PEqualNP.TopForm.Ustar x2 x9).card)
    (hLedger : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
      x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card +
        (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ≤
        x4.size + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) ∧
      ∀ (x9 : Finset (Fin x1)),
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (x2.deleteEdges ↑(PEqualNP.TopForm.Ustar x2 x4)) x9 →
        x9.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card)
    (hP9 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) →
      ∃ (x4 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn x4) ≠
          (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
           x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
           x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
           x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
           x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
           x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
           x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
           x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
           x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
           x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
           x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
           x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))))
    (hResidual :
      let P : SimpleGraph (Fin (10 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (10 : ℕ)
          [((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ)), ((2 : ℕ), (3 : ℕ)), ((3 : ℕ), (4 : ℕ)), ((4 : ℕ), (0 : ℕ)),
           ((0 : ℕ), (5 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((3 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)),
           ((5 : ℕ), (7 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((9 : ℕ), (6 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((8 : ℕ), (5 : ℕ))]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO P C → PEqualNP.TopForm.TopForm P C →
        (18 : ℕ) ≤ C.size → C.size ≤ (19 : ℕ) →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk P C).card →
        (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar P C).card →
        (4 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless P C).card + (PEqualNP.TopForm.junk P C).card +
          (PEqualNP.TopForm.orN P C \ PEqualNP.TopForm.lam P C).card →
        (∀ v : Fin (10 : ℕ), C.gates.countP (fun g => g.inputs.contains v.val) ≤ C.size - (16 : ℕ)) →
        (∀ K0 : Finset (Fin (10 : ℕ)),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (P.deleteEdges ↑(PEqualNP.TopForm.Ustar P C)) K0 →
          K0.card + (2 : ℕ) * (PEqualNP.TopForm.centreless P C).card + (PEqualNP.TopForm.junk P C).card +
            (PEqualNP.TopForm.orN P C \ PEqualNP.TopForm.lam P C).card ≤
            C.size - (14 : ℕ) + (PEqualNP.TopForm.Ustar P C).card) →
        (∀ A : Finset (Fin (10 : ℕ)),
          (∀ e ∈ PEqualNP.TopForm.Ustar P C, ∃ v ∈ A, v ∈ e) →
          (2 : ℕ) * (PEqualNP.TopForm.centreless P C).card + (PEqualNP.TopForm.junk P C).card +
            (PEqualNP.TopForm.orN P C \ PEqualNP.TopForm.lam P C).card <
            A.card + (PEqualNP.TopForm.Ustar P C).card) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).any id]) ≠ x6.2 := by
  classical
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro x1 x2 hM1 hS1 hL2
  by_contra hAllRows
  let rows : List (ℕ × Bool) :=
    [(3, true), (6, true), (12, true), (24, true), (17, true),
     (33, true), (66, true), (132, true), (264, true), (528, true),
     (160, true), (640, true), (576, true), (320, true), (288, true),
     (50, false), (69, false), (104, false), (116, false), (138, false),
     (201, false), (208, false), (276, false), (385, false), (402, false),
     (521, false), (548, false), (554, false), (770, false), (773, false)]
  have hMatchRow : ∀ r ∈ rows,
      let x7 : List Bool := List.ofFn fun (i : Fin 10) => r.1.testBit i.val
      x1.eval (x7 ++ [(x2.map (fun i => x7.getD i false)).any id]) = r.2 := by
    intro r hr
    by_contra hne
    exact hAllRows ⟨r, hr, hne⟩
  let pEdges : List (ℕ × ℕ) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  let P : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10 pEdges
  let stepWire : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have wires_def : ∀ (C' : Circuit) (x : List Bool), C'.wires x = C'.gates.foldl stepWire x :=
    fun _ _ => rfl
  have size_def : ∀ (C' : Circuit), C'.size = C'.gates.length := fun _ => rfl
  have eval_def : ∀ (C' : Circuit) (x : List Bool), C'.eval x = (C'.wires x).getD C'.output false :=
    fun _ _ => rfl
  have circuitFun_def : ∀ (k : ℕ) (C' : Circuit) (x : Fin k → Bool),
      circuitFun k C' x = (C'.wires (List.ofFn x)).getD C'.output false := fun _ _ _ => rfl
  have graphFun_def : ∀ (x : Fin 10 → Bool),
      graphFun P ∅ x = (decide (∃ a ∈ (∅ : Finset (Fin 10)), x a = true) ||
        decide (∃ u v : Fin 10, P.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  have gateAt_def : ∀ (C' : Circuit) (j : ℕ), gateAt C' j = C'.gates.getD j ⟨GateOp.or, []⟩ :=
    fun _ _ => rfl
  have gateVal_def : ∀ (C' : Circuit) (j : ℕ) (x : Fin 10 → Bool),
      gateVal 10 C' j x = (C'.wires (List.ofFn x)).getD (10 + j) false := fun _ _ _ => rfl
  have opnd_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      opnd C' a b = (gateAt C' a).inputs.getD b.val 0 := fun _ _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin 10), pairInput u v w = decide (w = u ∨ w = v) :=
    fun _ _ _ => rfl
  have pairInput_symm : ∀ (u v : Fin 10), pairInput u v = pairInput v u := fun u v =>
    funext fun w => by simp only [pairInput_def, or_comm]
  have foldl_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
        (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
        ∀ i : ℕ, (gs.foldl stepWire w1).getD i false = true →
          (gs.foldl stepWire w2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ h i hi; exact h i hi
    | cons g gs ih =>
      intro hgs w1 w2 hlen hle
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp only [stepWire, List.length_append, List.length_singleton, hlen]
      · intro i hi
        by_cases hilt : i < w1.length
        · have h1 : (stepWire w1 g).getD i false = w1.getD i false := by
            simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
          have h2 : (stepWire w2 g).getD i false = w2.getD i false := by
            simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w2.length)]
          rw [h1] at hi; rw [h2]; exact hle i hi
        · by_cases hieq : i = w1.length
          · subst i
            have h1 : (stepWire w1 g).getD w1.length false = g.op.eval (g.inputs.map fun k => w1.getD k false) := by
              simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            have h2 : (stepWire w2 g).getD w1.length false = g.op.eval (g.inputs.map fun k => w2.getD k false) := by
              simp only [stepWire, List.getD_eq_getElem?_getD, hlen, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [h1] at hi; rw [h2]
            rcases hgs g List.mem_cons_self with hand | hor
            · rw [hand, eval_and] at hi ⊢
              rw [List.all_eq_true] at hi ⊢
              intro b hb
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
              exact hle k (hi _ (List.mem_map.mpr ⟨k, hk, rfl⟩))
            · rw [hor, eval_or] at hi ⊢
              rw [List.any_eq_true] at hi ⊢
              obtain ⟨b, hb, hbt⟩ := hi
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
              exact ⟨w2.getD k false, List.mem_map.mpr ⟨k, hk, rfl⟩, hle k hbt⟩
          · have hge : (stepWire w1 g).length ≤ i := by
              simp only [stepWire, List.length_append, List.length_singleton]; omega
            rw [getD_ge _ _ hge] at hi
            exact Bool.noConfusion hi
  let C0 : Circuit := ⟨⟨GateOp.or, x2⟩ :: x1.gates, x1.output⟩
  have hC0_mono2 : Monotone2 C0 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact ⟨Or.inr rfl, hL2⟩
    · exact hM1 g hg1
  have hC0_size : C0.size ≤ 19 := by
    rw [size_def]; change x1.gates.length + 1 ≤ 19; rw [size_def] at hS1; omega
  have hC0_eval : ∀ x : Fin 10 → Bool,
      C0.eval (List.ofFn x) =
        x1.eval (List.ofFn x ++ [(x2.map (fun i => (List.ofFn x).getD i false)).any id]) := by
    intro x
    rw [eval_def, eval_def, wires_def, wires_def]
    change (List.foldl stepWire (List.ofFn x) (⟨GateOp.or, x2⟩ :: x1.gates)).getD x1.output false = _
    rw [List.foldl_cons]
    rfl
  have hC0_rows : ∀ r ∈ rows, C0.eval (List.ofFn fun i : Fin 10 => r.1.testBit i.val) = r.2 := by
    intro r hr
    rw [hC0_eval]
    exact hMatchRow r hr
  have hC0_mono : ∀ x y : Fin 10 → Bool, (∀ i : Fin 10, x i = true → y i = true) →
      C0.eval (List.ofFn x) = true → C0.eval (List.ofFn y) = true := by
    intro x y hxy hx
    rw [eval_def, wires_def] at hx ⊢
    refine foldl_mono C0.gates (fun g hg => (hC0_mono2 g hg).1) (List.ofFn x) (List.ofFn y)
      (by rw [List.length_ofFn, List.length_ofFn]) (fun i hi => ?_) C0.output hx
    by_cases hilt : i < 10
    · have h1 : (List.ofFn x).getD i false = x ⟨i, hilt⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hilt, Option.getD_some]
      have h2 : (List.ofFn y).getD i false = y ⟨i, hilt⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hilt, Option.getD_some]
      rw [h1] at hi; rw [h2]; exact hxy ⟨i, hilt⟩ hi
    · rw [getD_ge _ _ (by rw [List.length_ofFn]; omega)] at hi
      exact Bool.noConfusion hi
  have hP_hasEdge : ∀ x : Fin 10 → Bool,
      graphFun P ∅ x = true ↔ ∃ u v : Fin 10, P.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [graphFun_def]
    have hempty : ¬ (∃ a ∈ (∅ : Finset (Fin 10)), x a = true) := fun h =>
      Exists.elim h (fun a ha => Finset.notMem_empty a ha.1)
    rw [decide_eq_false hempty, Bool.false_or, decide_eq_true_eq]
  have hRowCover : ∀ m : Fin 1024,
      let f : Fin 10 → Bool := fun i => m.val.testBit i.val
      (if (pEdges.any (fun e => m.val.testBit e.1 && m.val.testBit e.2)) then
        rows.any (fun r => r.2 == true && (r.1 &&& m.val == r.1))
       else
        rows.any (fun r => r.2 == false && (m.val &&& r.1 == m.val))) = true := by
    decide +kernel
  let toMask : (Fin 10 → Bool) → ℕ := fun x =>
    (List.finRange 10).foldl (fun acc i => if x i = true then acc ||| 2 ^ i.val else acc) 0
  have toMask_bit : ∀ (x : Fin 10 → Bool) (i : Fin 10), (toMask x).testBit i.val = x i := by
    have hfold : ∀ (l : List (Fin 10)) (acc : ℕ) (x : Fin 10 → Bool) (k : ℕ),
        (l.foldl (fun a j => if x j = true then a ||| 2 ^ j.val else a) acc).testBit k =
          (acc.testBit k || l.any (fun j => x j && decide (j.val = k))) := by
      intro l
      induction l with
      | nil => intro acc x k; simp only [List.foldl_nil, List.any_nil, Bool.or_false]
      | cons j js ih =>
        intro acc x k
        rw [List.foldl_cons, ih, List.any_cons]
        cases hxj : x j
        · simp only [Bool.false_eq_true, ite_false, Bool.false_and, Bool.false_or]
        · simp only [ite_true, Nat.testBit_or, Nat.testBit_two_pow, Bool.true_and, Bool.or_assoc]
    intro x i
    change ((List.finRange 10).foldl _ 0).testBit i.val = x i
    rw [hfold, Nat.zero_testBit, Bool.false_or]
    cases hxi : x i
    · cases hany : (List.finRange 10).any (fun j => x j && decide (j.val = i.val))
      · rfl
      · obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hany
        have hj' := Bool.and_eq_true_iff.mp hj
        have hji : j = i := Fin.ext (decide_eq_true_eq.mp hj'.2)
        rw [hji, hxi] at hj'
        exact Bool.noConfusion hj'.1
    · exact List.any_eq_true.mpr ⟨i, List.mem_finRange i, by rw [hxi, decide_eq_true rfl]; rfl⟩
  have toMask_lt : ∀ x : Fin 10 → Bool, toMask x < 1024 := by
    have hfold : ∀ (l : List (Fin 10)) (acc : ℕ) (x : Fin 10 → Bool),
        acc < 2 ^ 10 →
        l.foldl (fun a j => if x j = true then a ||| 2 ^ j.val else a) acc < 2 ^ 10 := by
      intro l
      induction l with
      | nil => intro acc _ h; exact h
      | cons j js ih =>
        intro acc x h
        rw [List.foldl_cons]
        apply ih
        by_cases hxj : x j = true
        · rw [if_pos hxj]
          exact Nat.or_lt_two_pow h (Nat.pow_lt_pow_right (by omega) j.isLt)
        · rw [if_neg hxj]; exact h
    intro x
    exact hfold (List.finRange 10) 0 x (by decide)
  have hP_edges_equiv : ∀ x : Fin 10 → Bool,
      (∃ u v : Fin 10, P.Adj u v ∧ x u = true ∧ x v = true) ↔
        pEdges.any (fun e => (toMask x).testBit e.1 && (toMask x).testBit e.2) = true := by
    intro x
    have hpLt : ∀ e ∈ pEdges, e.1 < 10 ∧ e.2 < 10 ∧ e.1 ≠ e.2 := by decide
    rw [List.any_eq_true]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩
      rcases huv.2 with h1 | h2
      · refine ⟨(u.val, v.val), h1, ?_⟩
        rw [toMask_bit x u, toMask_bit x v, hxu, hxv]; rfl
      · refine ⟨(v.val, u.val), h2, ?_⟩
        rw [toMask_bit x v, toMask_bit x u, hxv, hxu]; rfl
    · rintro ⟨e, he, hbe⟩
      obtain ⟨h1, h2, hne⟩ := hpLt e he
      have hbt := Bool.and_eq_true_iff.mp hbe
      refine ⟨⟨e.1, h1⟩, ⟨e.2, h2⟩, ⟨fun h => hne (congrArg Fin.val h), Or.inl he⟩, ?_, ?_⟩
      · rw [← toMask_bit x ⟨e.1, h1⟩]; exact hbt.1
      · rw [← toMask_bit x ⟨e.2, h2⟩]; exact hbt.2
  have hC0_exact : ∀ x : Fin 10 → Bool, C0.eval (List.ofFn x) = graphFun P ∅ x := by
    intro x
    let mask : ℕ := toMask x
    have hmaskLt : mask < 1024 := toMask_lt x
    have hbit : ∀ i : Fin 10, mask.testBit i.val = x i := toMask_bit x
    have hcov := hRowCover ⟨mask, hmaskLt⟩
    dsimp only at hcov
    cases hgf : graphFun P ∅ x
    · have hno : pEdges.any (fun e => mask.testBit e.1 && mask.testBit e.2) = false := by
        cases hpa : pEdges.any (fun e => mask.testBit e.1 && mask.testBit e.2)
        · rfl
        · have ht := (hP_hasEdge x).mpr ((hP_edges_equiv x).mpr hpa)
          rw [hgf] at ht; exact Bool.noConfusion ht
      rw [hno] at hcov
      obtain ⟨r, hr, hrb⟩ := List.any_eq_true.mp hcov
      have hrb' := Bool.and_eq_true_iff.mp hrb
      have hr2 : r.2 = false := beq_iff_eq.mp hrb'.1
      have hsub : mask &&& r.1 = mask := beq_iff_eq.mp hrb'.2
      have hle : ∀ i : Fin 10, x i = true → r.1.testBit i.val = true := by
        intro i hxi
        have hb : (mask &&& r.1).testBit i.val = true := by rw [hsub, hbit i]; exact hxi
        rw [Nat.testBit_and] at hb
        exact (Bool.and_eq_true_iff.mp hb).2
      have hrval := hC0_rows r hr
      rw [hr2] at hrval
      cases hcx : C0.eval (List.ofFn x)
      · rfl
      · have hbad := hC0_mono x (fun i => r.1.testBit i.val) hle hcx
        rw [hrval] at hbad; exact Bool.noConfusion hbad
    · have hyes : pEdges.any (fun e => mask.testBit e.1 && mask.testBit e.2) = true :=
        (hP_edges_equiv x).mp ((hP_hasEdge x).mp hgf)
      rw [hyes] at hcov
      obtain ⟨r, hr, hrb⟩ := List.any_eq_true.mp hcov
      have hrb' := Bool.and_eq_true_iff.mp hrb
      have hr2 : r.2 = true := beq_iff_eq.mp hrb'.1
      have hsub : r.1 &&& mask = r.1 := beq_iff_eq.mp hrb'.2
      have hle : ∀ i : Fin 10, r.1.testBit i.val = true → x i = true := by
        intro i hri
        have hb : (r.1 &&& mask).testBit i.val = true := by rw [hsub]; exact hri
        rw [Nat.testBit_and, hbit i] at hb
        exact (Bool.and_eq_true_iff.mp hb).2
      have hrval := hC0_rows r hr
      rw [hr2] at hrval
      exact hC0_mono (fun i => r.1.testBit i.val) x hle hrval
  let evalTag : List Bool → ℕ → Bool := fun w t =>
    if t = 0 then false else if t = 1 then true else w.getD (t - 2) false
  let combTag : GateOp → ℕ → ℕ → ℕ → ℕ × List Gate := fun op a b nextW =>
    if op = GateOp.and then
      if a = 0 ∨ b = 0 then (0, [])
      else if a = 1 then (b, [])
      else if b = 1 then (a, [])
      else (nextW + 2, [⟨GateOp.and, [a - 2, b - 2]⟩])
    else
      if a = 1 ∨ b = 1 then (1, [])
      else if a = 0 then (b, [])
      else if b = 0 then (a, [])
      else (nextW + 2, [⟨GateOp.or, [a - 2, b - 2]⟩])
  have combTag_spec : ∀ (op : GateOp) (a b nextW : ℕ),
      (op = GateOp.and ∨ op = GateOp.or) →
      (a < 2 ∨ a - 2 < nextW) → (b < 2 ∨ b - 2 < nextW) →
      let r := combTag op a b nextW
      (r.1 < 2 ∨ r.1 - 2 < nextW + r.2.length) ∧
      r.2.length ≤ 1 ∧
      ((a = 0 ∨ b = 0) → r.2 = [] ∧ (op = GateOp.and → r.1 = 0)) ∧
      (∀ g' ∈ r.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 ∧ ∀ u ∈ g'.inputs, u < nextW) ∧
      (∀ w : List Bool, w.length = nextW →
        evalTag (r.2.foldl stepWire w) r.1 = op.eval [evalTag w a, evalTag w b] ∧
        ∀ i < nextW, (r.2.foldl stepWire w).getD i false = w.getD i false) := by
    intro op a b nextW hop ha hb
    rcases hop with rfl | rfl
    · dsimp only [combTag]
      rw [if_pos rfl]
      by_cases hz : a = 0 ∨ b = 0
      · rw [if_pos hz]
        refine ⟨Or.inl (by omega), by simp only [List.length_nil, Nat.zero_le], fun _ => ⟨rfl, fun _ => rfl⟩,
          fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
        rw [List.foldl_nil, eval_and]
        dsimp only [evalTag]
        rcases hz with rfl | rfl
        · simp only [ite_true, List.all_cons, List.all_nil, id_eq, Bool.false_and]
        · simp only [ite_true, List.all_cons, List.all_nil, id_eq, Bool.and_false, Bool.and_true]
      · rw [if_neg hz]
        by_cases ha1 : a = 1
        · rw [if_pos ha1]
          refine ⟨by rcases hb with h | h; exact Or.inl h; exact Or.inr (by simp only [List.length_nil, Nat.add_zero]; exact h),
            by simp only [List.length_nil, Nat.zero_le], fun h => False.elim (hz h),
            fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
          rw [List.foldl_nil, eval_and, ha1]
          dsimp only [evalTag]
          simp only [Nat.one_ne_zero, ite_false, ite_true, List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
        · rw [if_neg ha1]
          by_cases hb1 : b = 1
          · rw [if_pos hb1]
            refine ⟨by rcases ha with h | h; exact Or.inl h; exact Or.inr (by simp only [List.length_nil, Nat.add_zero]; exact h),
              by simp only [List.length_nil, Nat.zero_le], fun h => False.elim (hz h),
              fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
            rw [List.foldl_nil, eval_and, hb1]
            dsimp only [evalTag]
            simp only [Nat.one_ne_zero, ite_false, ite_true, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · rw [if_neg hb1]
            have ha2 : 2 ≤ a := by omega
            have hb2 : 2 ≤ b := by omega
            have halt : a - 2 < nextW := ha.resolve_left (by omega)
            have hblt : b - 2 < nextW := hb.resolve_left (by omega)
            refine ⟨Or.inr (by simp only [List.length_singleton]; omega), by simp only [List.length_singleton, le_refl],
              fun h => False.elim (hz h), ?_, fun w hw => ⟨?_, fun i hi => ?_⟩⟩
            · intro g' hg'
              rw [List.mem_singleton.mp hg']
              refine ⟨Or.inl rfl, rfl, fun u hu => ?_⟩
              rcases List.mem_cons.mp hu with rfl | hu2
              · exact halt
              · rw [List.mem_singleton.mp hu2]; exact hblt
            · rw [List.foldl_cons, List.foldl_nil]
              dsimp only [evalTag, stepWire]
              rw [if_neg (by omega : nextW + 2 ≠ 0), if_neg (by omega : nextW + 2 ≠ 1),
                if_neg (by omega : a ≠ 0), if_neg (by omega : a ≠ 1),
                if_neg (by omega : b ≠ 0), if_neg (by omega : b ≠ 1)]
              have hsub : nextW + 2 - 2 = w.length := by omega
              rw [hsub, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some]
              rfl
            · rw [List.foldl_cons, List.foldl_nil]
              simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w.length)]
    · dsimp only [combTag]
      have hne : GateOp.or ≠ GateOp.and := GateOp.noConfusion
      rw [if_neg hne]
      by_cases h1 : a = 1 ∨ b = 1
      · rw [if_pos h1]
        refine ⟨Or.inl (by omega), by simp only [List.length_nil, Nat.zero_le], fun _ => ⟨rfl, fun h => False.elim (hne h)⟩,
          fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
        rw [List.foldl_nil, eval_or]
        dsimp only [evalTag]
        rcases h1 with rfl | rfl
        · simp only [Nat.one_ne_zero, ite_false, ite_true, List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_false]
        · simp only [Nat.one_ne_zero, ite_false, ite_true, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_true]
      · rw [if_neg h1]
        by_cases ha0 : a = 0
        · rw [if_pos ha0]
          refine ⟨by rcases hb with h | h; exact Or.inl h; exact Or.inr (by simp only [List.length_nil, Nat.add_zero]; exact h),
            by simp only [List.length_nil, Nat.zero_le], fun _ => ⟨rfl, fun h => False.elim (hne h)⟩,
            fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
          rw [List.foldl_nil, eval_or, ha0]
          dsimp only [evalTag]
          simp only [ite_true, List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
        · rw [if_neg ha0]
          by_cases hb0 : b = 0
          · rw [if_pos hb0]
            refine ⟨by rcases ha with h | h; exact Or.inl h; exact Or.inr (by simp only [List.length_nil, Nat.add_zero]; exact h),
              by simp only [List.length_nil, Nat.zero_le], fun _ => ⟨rfl, fun h => False.elim (hne h)⟩,
              fun _ h => False.elim (List.not_mem_nil h), fun w _ => ⟨?_, fun _ _ => rfl⟩⟩
            rw [List.foldl_nil, eval_or, hb0]
            dsimp only [evalTag]
            simp only [ite_true, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · rw [if_neg hb0]
            have ha2 : 2 ≤ a := by omega
            have hb2 : 2 ≤ b := by omega
            have halt : a - 2 < nextW := ha.resolve_left (by omega)
            have hblt : b - 2 < nextW := hb.resolve_left (by omega)
            refine ⟨Or.inr (by simp only [List.length_singleton]; omega), by simp only [List.length_singleton, le_refl],
              fun h => False.elim (h.elim ha0 hb0), ?_, fun w hw => ⟨?_, fun i hi => ?_⟩⟩
            · intro g' hg'
              rw [List.mem_singleton.mp hg']
              refine ⟨Or.inr rfl, rfl, fun u hu => ?_⟩
              rcases List.mem_cons.mp hu with rfl | hu2
              · exact halt
              · rw [List.mem_singleton.mp hu2]; exact hblt
            · rw [List.foldl_cons, List.foldl_nil]
              dsimp only [evalTag, stepWire]
              rw [if_neg (by omega : nextW + 2 ≠ 0), if_neg (by omega : nextW + 2 ≠ 1),
                if_neg (by omega : a ≠ 0), if_neg (by omega : a ≠ 1),
                if_neg (by omega : b ≠ 0), if_neg (by omega : b ≠ 1)]
              have hsub : nextW + 2 - 2 = w.length := by omega
              rw [hsub, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some]
              rfl
            · rw [List.foldl_cons, List.foldl_nil]
              simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w.length)]
  have hNormAO2 : ∃ C1 : Circuit, IsAO2 10 C1 ∧ C1.size ≤ 19 ∧ circuitFun 10 C1 = graphFun P ∅ := by
    have hBuild : ∀ (gs : List Gate), (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        ∃ (env : List ℕ) (outGs : List Gate),
          env.length = 10 + gs.length ∧
          outGs.length ≤ gs.length ∧
          (∀ g' ∈ outGs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2) ∧
          ReadsBack 10 ⟨outGs, 0⟩ ∧
          (∀ t ∈ env, t < 2 ∨ t - 2 < 10 + outGs.length) ∧
          ∀ (x : Fin 10 → Bool) (i : ℕ),
            evalTag (outGs.foldl stepWire (List.ofFn x)) (env.getD i 0) =
              (gs.foldl stepWire (List.ofFn x)).getD i false := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨(List.range 10).map (fun i => i + 2), [], by simp only [List.length_map, List.length_range, List.length_nil, Nat.add_zero],
          le_refl 0, fun _ h => False.elim (List.not_mem_nil h), fun j hj => by simp only [List.length_nil] at hj; omega, ?_, ?_⟩
        · intro t ht
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
          have hilt := List.mem_range.mp hi
          right; simp only [List.length_nil, Nat.add_zero]; omega
        · intro x i
          rw [List.foldl_nil]
          by_cases hilt : i < 10
          · have hget : ((List.range 10).map (fun j => j + 2)).getD i 0 = i + 2 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hilt]; rfl
            rw [hget]
            dsimp only [evalTag]
            rw [if_neg (by omega : i + 2 ≠ 0), if_neg (by omega : i + 2 ≠ 1)]
            have hsub : i + 2 - 2 = i := by omega
            rw [hsub]
          · have hget : ((List.range 10).map (fun j => j + 2)).getD i 0 = 0 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]; rfl
            rw [hget]
            dsimp only [evalTag]
            rw [if_pos rfl, getD_ge _ _ (by rw [List.length_ofFn]; omega)]
      | append_singleton gs g ih =>
        intro hall
        have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hall g' (List.mem_append_left [g] hg')
        obtain ⟨hgop, hglen⟩ := hall g (List.mem_append_right gs List.mem_cons_self)
        obtain ⟨env, outGs, henvLen, houtLen, houtAO, houtRB, henvBnd, heval⟩ := ih hgs
        have hEnvValid : ∀ i : ℕ, env.getD i 0 < 2 ∨ env.getD i 0 - 2 < 10 + outGs.length := by
          intro i
          by_cases hilt : i < env.length
          · exact henvBnd _ (by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some]
              exact List.getElem_mem hilt)
          · left
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
            omega
        have hStepRes : ∃ (tag : ℕ) (added : List Gate),
            (tag < 2 ∨ tag - 2 < 10 + (outGs ++ added).length) ∧
            added.length ≤ 1 ∧
            (∀ g' ∈ added, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 ∧
              ∀ u ∈ g'.inputs, u < 10 + outGs.length) ∧
            ∀ x : Fin 10 → Bool,
              evalTag ((outGs ++ added).foldl stepWire (List.ofFn x)) tag =
                g.op.eval (g.inputs.map fun k => (gs.foldl stepWire (List.ofFn x)).getD k false) ∧
              ∀ i < 10 + outGs.length,
                ((outGs ++ added).foldl stepWire (List.ofFn x)).getD i false =
                  (outGs.foldl stepWire (List.ofFn x)).getD i false := by
          cases hins : g.inputs with
          | nil =>
            refine ⟨if g.op = GateOp.and then 1 else 0, [], Or.inl (by split_ifs <;> omega),
              by simp only [List.length_nil, Nat.zero_le], fun _ h => False.elim (List.not_mem_nil h), fun x => ⟨?_, fun _ _ => by rw [List.append_nil]⟩⟩
            rw [List.append_nil, List.map_nil]
            rcases hgop with hand | hor
            · rw [hand, if_pos rfl, eval_and]; rfl
            · rw [hor, if_neg GateOp.noConfusion, eval_or]; rfl
          | cons i0 rest =>
            cases rest with
            | nil =>
              refine ⟨env.getD i0 0, [], ?_, by simp only [List.length_nil, Nat.zero_le],
                fun _ h => False.elim (List.not_mem_nil h), fun x => ⟨?_, fun _ _ => by rw [List.append_nil]⟩⟩
              · rw [List.append_nil]; exact hEnvValid i0
              · rw [List.append_nil, List.map_cons, List.map_nil, heval x i0]
                rcases hgop with hand | hor
                · rw [hand, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                · rw [hor, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            | cons i1 rest2 =>
              cases rest2 with
              | nil =>
                let r := combTag g.op (env.getD i0 0) (env.getD i1 0) (10 + outGs.length)
                obtain ⟨h1, h2, _, h4, h5⟩ := combTag_spec g.op (env.getD i0 0) (env.getD i1 0) (10 + outGs.length) hgop (hEnvValid i0) (hEnvValid i1)
                refine ⟨r.1, r.2, by
                  rcases h1 with h | h
                  · exact Or.inl h
                  · have h' : r.1 - 2 < 10 + outGs.length + r.2.length := h
                    exact Or.inr (by rw [List.length_append]; omega), h2, h4, fun x => ?_⟩
                rw [List.foldl_append]
                have hlenW : (outGs.foldl stepWire (List.ofFn x)).length = 10 + outGs.length := by
                  rw [foldl_length, List.length_ofFn]
                obtain ⟨ha, hb⟩ := h5 _ hlenW
                refine ⟨?_, hb⟩
                rw [ha, heval x i0, heval x i1, List.map_cons, List.map_cons, List.map_nil]
              | cons _ _ =>
                rw [hins] at hglen
                simp only [List.length_cons] at hglen
                omega
        obtain ⟨tag, added, htagBnd, haddLen, haddOk, haddEval⟩ := hStepRes
        refine ⟨env ++ [tag], outGs ++ added, by simp only [List.length_append, List.length_singleton]; omega,
          by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h1 | h2
          · exact houtAO g' h1
          · exact ⟨(haddOk g' h2).1, (haddOk g' h2).2.1⟩
        · intro j hj u hu
          have hjlen : j < (outGs ++ added).length := hj
          by_cases hjold : j < outGs.length
          · have hge : gateAt ⟨outGs ++ added, 0⟩ j = gateAt ⟨outGs, 0⟩ j := by
              rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_append_left hjold]
            rw [hge] at hu
            exact houtRB j hjold u hu
          · have hjeq : j = outGs.length := by rw [List.length_append] at hjlen; omega
            have hadd1 : added.length = 1 := by rw [List.length_append] at hjlen; omega
            obtain ⟨g0, rfl⟩ := List.length_eq_one_iff.mp hadd1
            have hge : gateAt ⟨outGs ++ [g0], 0⟩ j = g0 := by
              rw [gateAt_def, List.getD_eq_getElem?_getD, hjeq, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hge] at hu
            have hlt := (haddOk g0 List.mem_cons_self).2.2 u hu
            omega
        · intro t ht
          rcases List.mem_append.mp ht with h1 | h2
          · rcases henvBnd t h1 with hlt | hlt
            · exact Or.inl hlt
            · exact Or.inr (by rw [List.length_append]; omega)
          · rw [List.mem_singleton.mp h2]; exact htagBnd
        · intro x i
          conv_rhs => rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hgsLen : (gs.foldl stepWire (List.ofFn x)).length = 10 + gs.length := by
            rw [foldl_length, List.length_ofFn]
          by_cases hilt : i < env.length
          · have hgetE : (env ++ [tag]).getD i 0 = env.getD i 0 := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
            have hgetW : (stepWire (gs.foldl stepWire (List.ofFn x)) g).getD i false =
                (gs.foldl stepWire (List.ofFn x)).getD i false := by
              change (gs.foldl stepWire (List.ofFn x) ++ [_]).getD i false = _
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
            rw [hgetE, hgetW, ← heval x i]
            have hti := hEnvValid i
            dsimp only [evalTag]
            by_cases h0 : env.getD i 0 = 0
            · rw [if_pos h0, if_pos h0]
            · rw [if_neg h0, if_neg h0]
              by_cases h1 : env.getD i 0 = 1
              · rw [if_pos h1, if_pos h1]
              · rw [if_neg h1, if_neg h1]
                exact (haddEval x).2 (env.getD i 0 - 2) (hti.resolve_left (by omega))
          · by_cases hieq : i = env.length
            · subst i
              have hgetE : (env ++ [tag]).getD env.length 0 = tag := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              have hgetW : (stepWire (gs.foldl stepWire (List.ofFn x)) g).getD env.length false =
                  g.op.eval (g.inputs.map fun k => (gs.foldl stepWire (List.ofFn x)).getD k false) := by
                simp only [stepWire, List.getD_eq_getElem?_getD, show env.length = (gs.foldl stepWire (List.ofFn x)).length by omega,
                  List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hgetE, hgetW]
              exact (haddEval x).1
            · have hgetE : (env ++ [tag]).getD i 0 = 0 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]; rfl
              have hgetW : (stepWire (gs.foldl stepWire (List.ofFn x)) g).getD i false = false :=
                getD_ge _ _ (by simp only [stepWire, List.length_append, List.length_singleton, hgsLen]; omega)
              rw [hgetE, hgetW]; rfl
    obtain ⟨env, outGs, _, houtLen, houtAO, houtRB, _, heval⟩ := hBuild C0.gates hC0_mono2
    let tOut := env.getD C0.output 0
    have ht0 : tOut ≠ 0 := by
      intro h0
      have h1 := heval (pairInput 0 1) C0.output
      change evalTag _ tOut = C0.eval (List.ofFn (pairInput 0 1)) at h1
      rw [h0, hC0_exact] at h1
      have hadj01 : graphFun P ∅ (pairInput 0 1) = true :=
        (hP_hasEdge _).mpr ⟨0, 1, ⟨by decide, Or.inl (by decide)⟩, by decide, by decide⟩
      rw [hadj01] at h1
      exact Bool.noConfusion h1
    have ht1 : tOut ≠ 1 := by
      intro h1'
      have h1 := heval (fun _ => false) C0.output
      change evalTag _ tOut = C0.eval (List.ofFn (fun _ => false)) at h1
      rw [h1', hC0_exact] at h1
      have hno0 : graphFun P ∅ (fun _ => false) = false := by
        cases h : graphFun P ∅ (fun _ => false)
        · rfl
        · obtain ⟨_, _, _, hxu, _⟩ := (hP_hasEdge _).mp h; exact Bool.noConfusion hxu
      rw [hno0] at h1
      exact Bool.noConfusion h1
    refine ⟨⟨outGs, tOut - 2⟩, ⟨fun g hg => (houtAO g hg).1, houtRB, fun g hg => (houtAO g hg).2⟩,
      by change outGs.length ≤ 19; rw [size_def] at hC0_size; omega, funext fun x => ?_⟩
    rw [circuitFun_def, wires_def, ← hC0_exact x, eval_def, wires_def, ← heval x C0.output]
    change _ = evalTag _ tOut
    dsimp only [evalTag]
    rw [if_neg ht0, if_neg ht1]
  obtain ⟨C1, hC1AO2, hC1Size, hC1Fun⟩ := hNormAO2
  have hpLtAll : ∀ e ∈ pEdges, e.1 < 10 ∧ e.2 < 10 ∧ e.1 ≠ e.2 := by decide
  let pAdjMask : List ℕ := [50, 69, 138, 276, 521, 385, 770, 548, 104, 208]
  have hpMaskFwd : ∀ e ∈ pEdges,
      (pAdjMask.getD e.1 0).testBit e.2 = true ∧ (pAdjMask.getD e.2 0).testBit e.1 = true := by decide
  have hpMaskAdj : ∀ a b : Fin 10, P.Adj a b → (pAdjMask.getD a.val 0).testBit b.val = true := by
    intro a b hab
    rcases hab.2 with h1 | h2
    · exact (hpMaskFwd (a.val, b.val) h1).1
    · exact (hpMaskFwd (b.val, a.val) h2).2
  have hpMaskBwd : ∀ a b : Fin 10, (pAdjMask.getD a.val 0).testBit b.val = true →
      a.val ≠ b.val ∧ pEdges.any (fun e => (e.1 == a.val && e.2 == b.val) || (e.1 == b.val && e.2 == a.val)) = true := by
    decide +kernel
  have hpMaskIff : ∀ a b : Fin 10, P.Adj a b ↔ (pAdjMask.getD a.val 0).testBit b.val = true := by
    intro a b
    refine ⟨hpMaskAdj a b, fun hb => ?_⟩
    obtain ⟨hne, hany⟩ := hpMaskBwd a b hb
    obtain ⟨e, he, hbe⟩ := List.any_eq_true.mp hany
    refine ⟨fun hfin => hne (congrArg Fin.val hfin), ?_⟩
    rcases Bool.or_eq_true_iff.mp hbe with h1 | h2
    · have h1' := Bool.and_eq_true_iff.mp h1
      have heq : e = (a.val, b.val) := Prod.ext (beq_iff_eq.mp h1'.1) (beq_iff_eq.mp h1'.2)
      exact Or.inl (heq ▸ he)
    · have h2' := Bool.and_eq_true_iff.mp h2
      have heq : e = (b.val, a.val) := Prod.ext (beq_iff_eq.mp h2'.1) (beq_iff_eq.mp h2'.2)
      exact Or.inr (heq ▸ he)
  have hPne : P.edgeFinset.Nonempty := ⟨s(0, 1), SimpleGraph.mem_edgeFinset.mpr ⟨by decide, Or.inl (by decide)⟩⟩
  have hPno4 : NoFourCycle P := by
    have h4mask : ∀ u v : Fin 10, u ≠ v →
        let c := (pAdjMask.getD u.val 0) &&& (pAdjMask.getD v.val 0)
        (c == 0 || (List.finRange 10).any (fun w => c == 2 ^ w.val)) = true := by decide +kernel
    intro u v huv
    apply Finset.card_le_one.mpr
    intro w1 hw1 w2 hw2
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    let c := (pAdjMask.getD u.val 0) &&& (pAdjMask.getD v.val 0)
    have hc1 : c.testBit w1.val = true := by
      dsimp only [c]; rw [Nat.testBit_and, hpMaskAdj u w1 h1.1, hpMaskAdj v w1 h1.2]; rfl
    have hc2 : c.testBit w2.val = true := by
      dsimp only [c]; rw [Nat.testBit_and, hpMaskAdj u w2 h2.1, hpMaskAdj v w2 h2.2]; rfl
    rcases Bool.or_eq_true_iff.mp (h4mask u v huv) with hz | hpow
    · have hc0 : c = 0 := beq_iff_eq.mp hz
      rw [hc0, Nat.zero_testBit] at hc1; exact Bool.noConfusion hc1
    · obtain ⟨w0, _, hw0⟩ := List.any_eq_true.mp hpow
      have hcw0 : c = 2 ^ w0.val := beq_iff_eq.mp hw0
      rw [hcw0, Nat.testBit_two_pow] at hc1 hc2
      have e1 : w0.val = w1.val := decide_eq_true_eq.mp hc1
      have e2 : w0.val = w2.val := decide_eq_true_eq.mp hc2
      exact Fin.ext (e1.symm.trans e2)
  have hPtri : ∀ u v w : Fin 10, P.Adj u v → P.Adj v w → ¬ P.Adj u w := by
    have hTriMask : ∀ e ∈ pEdges, ((pAdjMask.getD e.1 0) &&& (pAdjMask.getD e.2 0)) = 0 := by decide
    intro u v w huv hvw huw
    have hc0 : ((pAdjMask.getD u.val 0) &&& (pAdjMask.getD v.val 0)) = 0 := by
      rcases huv.2 with h1 | h2
      · exact hTriMask (u.val, v.val) h1
      · rw [Nat.and_comm]; exact hTriMask (v.val, u.val) h2
    have hbit : (((pAdjMask.getD u.val 0) &&& (pAdjMask.getD v.val 0))).testBit w.val = true := by
      rw [Nat.testBit_and, hpMaskAdj u w huw, hpMaskAdj v w hvw]; rfl
    rw [hc0, Nat.zero_testBit] at hbit
    exact Bool.noConfusion hbit
  have hPcard : P.edgeFinset.card = 15 := by
    let toSym : ℕ × ℕ → Sym2 (Fin 10) := fun e =>
      if h : e.1 < 10 ∧ e.2 < 10 then s(⟨e.1, h.1⟩, ⟨e.2, h.2⟩) else s(0, 0)
    have hpNormNd : (pEdges.map (fun e => (min e.1 e.2, max e.1 e.2))).Nodup := by decide
    have hNodup : (pEdges.map toSym).Nodup := by
      rw [List.nodup_map_iff_inj_on (List.Nodup.of_map _ hpNormNd)]
      intro e1 he1 e2 he2 heq
      obtain ⟨h1a, h1b, _⟩ := hpLtAll e1 he1
      obtain ⟨h2a, h2b, _⟩ := hpLtAll e2 he2
      dsimp only [toSym] at heq
      rw [dif_pos ⟨h1a, h1b⟩, dif_pos ⟨h2a, h2b⟩] at heq
      have hpair : (min e1.1 e1.2, max e1.1 e1.2) = (min e2.1 e2.2, max e2.1 e2.2) := by
        rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have h1 : e1.1 = e2.1 := congrArg Fin.val ha
          have h2 : e1.2 = e2.2 := congrArg Fin.val hb
          rw [h1, h2]
        · have h1 : e1.1 = e2.2 := congrArg Fin.val ha
          have h2 : e1.2 = e2.1 := congrArg Fin.val hb
          rw [h1, h2, min_comm, max_comm]
      exact (List.nodup_map_iff_inj_on (List.Nodup.of_map _ hpNormNd)).mp hpNormNd e1 he1 e2 he2 hpair
    have hSetEq : (pEdges.map toSym).toFinset = P.edgeFinset := by
      apply Finset.ext; intro e
      induction e using Sym2.ind with
      | _ u v =>
        rw [List.mem_toFinset, SimpleGraph.mem_edgeFinset]
        constructor
        · intro hm
          obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
          obtain ⟨h1, h2, hne⟩ := hpLtAll p hp
          dsimp only [toSym] at hpe; rw [dif_pos ⟨h1, h2⟩] at hpe
          rcases Sym2.eq_iff.mp hpe with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [← ha, ← hb]; exact ⟨fun h => hne (congrArg Fin.val h), Or.inl hp⟩
          · rw [← ha, ← hb]; exact ⟨fun h => hne (congrArg Fin.val h).symm, Or.inr hp⟩
        · intro huv
          rcases huv.2 with h1 | h2
          · refine List.mem_map.mpr ⟨(u.val, v.val), h1, ?_⟩
            dsimp only [toSym]; rw [dif_pos ⟨u.isLt, v.isLt⟩]
          · refine List.mem_map.mpr ⟨(v.val, u.val), h2, ?_⟩
            dsimp only [toSym]; rw [dif_pos ⟨v.isLt, u.isLt⟩]; exact Sym2.eq_swap
    rw [← hSetEq, List.toFinset_card_of_nodup hNodup, List.length_map]
    rfl
  have hPminVC : ∀ S : Finset (Fin 10), (∀ u v : Fin 10, P.Adj u v → u ∈ S ∨ v ∈ S) → 6 ≤ S.card := by
    have hRowMax4 : ∀ r ∈ rows, r.2 = false →
        (List.finRange 10).countP (fun i => r.1.testBit i.val) ≤ 4 := by decide
    intro S hS
    let I : Finset (Fin 10) := Finset.univ \ S
    let xI : Fin 10 → Bool := fun i => decide (i ∈ I)
    let mI : Fin 1024 := ⟨toMask xI, toMask_lt xI⟩
    have hNoEdgeI : pEdges.any (fun e => mI.val.testBit e.1 && mI.val.testBit e.2) = false := by
      cases hpa : pEdges.any (fun e => mI.val.testBit e.1 && mI.val.testBit e.2)
      · rfl
      · obtain ⟨u, v, huv, hxu, hxv⟩ := (hP_edges_equiv xI).mpr hpa
        have huI : u ∈ I := decide_eq_true_eq.mp hxu
        have hvI : v ∈ I := decide_eq_true_eq.mp hxv
        rcases hS u v huv with huS | hvS
        · exact False.elim ((Finset.mem_sdiff.mp huI).2 huS)
        · exact False.elim ((Finset.mem_sdiff.mp hvI).2 hvS)
    have hcov := hRowCover mI
    rw [hNoEdgeI] at hcov
    obtain ⟨r, hr, hrb⟩ := List.any_eq_true.mp hcov
    have hrb' := Bool.and_eq_true_iff.mp hrb
    have hr2 : r.2 = false := beq_iff_eq.mp hrb'.1
    have hsub : mI.val &&& r.1 = mI.val := beq_iff_eq.mp hrb'.2
    have hIsubR : I ⊆ Finset.univ.filter (fun i : Fin 10 => r.1.testBit i.val = true) := by
      intro i hi
      have h1 : (mI.val &&& r.1).testBit i.val = true := by
        rw [hsub, toMask_bit xI i]; exact decide_eq_true hi
      rw [Nat.testBit_and] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Bool.and_eq_true_iff.mp h1).2⟩
    have hRcard : (Finset.univ.filter (fun i : Fin 10 => r.1.testBit i.val = true)).card =
        (List.finRange 10).countP (fun i => r.1.testBit i.val) := by
      rw [List.countP_eq_length_filter]
      have hNodup : ((List.finRange 10).filter (fun i => r.1.testBit i.val)).Nodup := (List.nodup_finRange 10).filter _
      have hEq : ((List.finRange 10).filter (fun i => r.1.testBit i.val)).toFinset =
          Finset.univ.filter (fun i : Fin 10 => r.1.testBit i.val = true) := by
        apply Finset.ext; intro i
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hEq, List.toFinset_card_of_nodup hNodup]
    have hI4 : I.card ≤ 4 := by
      have h1 := Finset.card_le_card hIsubR
      have h2 := hRowMax4 r hr hr2
      omega
    have hIsdiff : I.card = 10 - S.card := by
      have h1 : (Finset.univ \ S).card = (Finset.univ : Finset (Fin 10)).card - (S ∩ Finset.univ).card := Finset.card_sdiff
      rw [Finset.inter_univ, Finset.card_fin] at h1; exact h1
    omega
  obtain ⟨C, hLeast, hTop, hCsizeLe, _⟩ := hTopForm 10 P C1 hPne hC1AO2 hC1Fun
  have hCsize19 : C.size ≤ 19 := le_trans hCsizeLe hC1Size
  obtain ⟨hLedIneq, hMinCov⟩ := hLedger 10 P C hPno4 hPne hLeast hTop
  rw [hPcard] at hLedIneq
  have hRestrictV : ∀ (v : Fin 10),
      16 + C.gates.countP (fun g => g.inputs.contains v.val) ≤ C.size ∧
      (∀ h0 : 0 < C.gates.length, (gateAt C 0).op = GateOp.and → v.val ∈ (gateAt C 0).inputs →
        (∃ r, 0 < r ∧ r < C.gates.length ∧ 10 ∈ (gateAt C r).inputs) → 18 ≤ C.size) := by
    let autTbl : List (List ℕ) :=
      [[2,3,8,6,1,7,4,5,9,0], [3,4,9,7,2,8,0,6,5,1], [0,4,9,6,1,5,3,7,8,2],
       [0,1,6,9,4,5,2,8,7,3], [1,2,7,5,0,6,3,9,8,4], [1,2,3,4,0,6,7,8,9,5],
       [0,4,3,2,1,5,9,8,7,6], [0,1,6,8,5,4,2,9,3,7], [0,1,2,7,5,4,6,3,9,8],
       [0,1,2,3,4,5,6,7,8,9]]
    let p9Fn : (Fin 9 → Bool) → Bool := fun x4 =>
      x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 ||
      x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 ||
      x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5
    have hAutLt : ∀ (v j : Fin 10), (autTbl.getD v.val []).getD j.val 0 < 10 := by decide +kernel
    have hAutLast : ∀ (v : Fin 10), (autTbl.getD v.val []).getD 9 0 = v.val := by decide +kernel
    have hAutInj : ∀ (v j1 j2 : Fin 10),
        (autTbl.getD v.val []).getD j1.val 0 = (autTbl.getD v.val []).getD j2.val 0 → j1 = j2 := by decide +kernel
    let p9Edges : List (ℕ × ℕ) :=
      [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
    let p9AdjMask : List ℕ := [50, 69, 138, 276, 9, 385, 258, 36, 104]
    have hp9MaskFwd : ∀ e ∈ p9Edges,
        (p9AdjMask.getD e.1 0).testBit e.2 = true ∧ (p9AdjMask.getD e.2 0).testBit e.1 = true := by decide
    have hp9MaskBwd : ∀ i j : Fin 9, (p9AdjMask.getD i.val 0).testBit j.val = true →
        p9Edges.any (fun e => (e.1 == i.val && e.2 == j.val) || (e.1 == j.val && e.2 == i.val)) = true := by
      decide +kernel
    have hAutAdjBool : ∀ (v : Fin 10) (i j : Fin 9),
        (pAdjMask.getD ((autTbl.getD v.val []).getD i.val 0) 0).testBit ((autTbl.getD v.val []).getD j.val 0) =
        (p9AdjMask.getD i.val 0).testBit j.val := by
      decide +kernel
    have hAutAdj : ∀ (v : Fin 10) (i j : Fin 9),
        P.Adj ⟨(autTbl.getD v.val []).getD i.val 0, hAutLt v ⟨i.val, by omega⟩⟩
              ⟨(autTbl.getD v.val []).getD j.val 0, hAutLt v ⟨j.val, by omega⟩⟩ ↔
        ((i.val, j.val) ∈ p9Edges ∨ (j.val, i.val) ∈ p9Edges) := by
      intro v i j
      rw [hpMaskIff, hAutAdjBool v i j]
      constructor
      · intro hb
        obtain ⟨e, he, hbe⟩ := List.any_eq_true.mp (hp9MaskBwd i j hb)
        rcases Bool.or_eq_true_iff.mp hbe with h1 | h2
        · have h1' := Bool.and_eq_true_iff.mp h1
          have heq : e = (i.val, j.val) := Prod.ext (beq_iff_eq.mp h1'.1) (beq_iff_eq.mp h1'.2)
          exact Or.inl (heq ▸ he)
        · have h2' := Bool.and_eq_true_iff.mp h2
          have heq : e = (j.val, i.val) := Prod.ext (beq_iff_eq.mp h2'.1) (beq_iff_eq.mp h2'.2)
          exact Or.inr (heq ▸ he)
      · rintro (h1 | h2)
        · exact (hp9MaskFwd (i.val, j.val) h1).1
        · exact (hp9MaskFwd (j.val, i.val) h2).2
    intro v
    let invIdx : Fin 10 → ℕ := fun u =>
      if h : ∃ j : Fin 9, (autTbl.getD v.val []).getD j.val 0 = u.val then (Classical.choose h).val else 9
    have hInvV : invIdx v = 9 := by
      dsimp only [invIdx]
      rw [dif_neg]
      rintro ⟨j, hj⟩
      have h9 := hAutLast v
      have heq := hAutInj v ⟨j.val, by omega⟩ 9 (hj.trans h9.symm)
      have hval : j.val = 9 := congrArg Fin.val heq
      have hjlt := j.isLt
      omega
    have hInvAut : ∀ j : Fin 9, invIdx ⟨(autTbl.getD v.val []).getD j.val 0, hAutLt v ⟨j.val, by omega⟩⟩ = j.val := by
      intro j
      dsimp only [invIdx]
      have hex : ∃ k : Fin 9, (autTbl.getD v.val []).getD k.val 0 = (autTbl.getD v.val []).getD j.val 0 := ⟨j, rfl⟩
      rw [dif_pos hex]
      have hch := Classical.choose_spec hex
      have heq := hAutInj v ⟨(Classical.choose hex).val, by omega⟩ ⟨j.val, by omega⟩ hch
      have hval : (Classical.choose hex).val = j.val := congrArg (Fin.val (n := 10)) heq
      exact hval
    have hInvNe : ∀ u : Fin 10, u ≠ v → invIdx u < 9 := by
      intro u huv
      have hsurj : ∀ w : Fin 10, ∃ j : Fin 10, (autTbl.getD v.val []).getD j.val 0 = w.val := by
        have hall : ∀ (v0 w0 : Fin 10), (List.finRange 10).any (fun j => (autTbl.getD v0.val []).getD j.val 0 == w0.val) = true := by decide +kernel
        intro w
        obtain ⟨j, _, hj⟩ := List.any_eq_true.mp (hall v w)
        exact ⟨j, beq_iff_eq.mp hj⟩
      obtain ⟨j, hj⟩ := hsurj u
      have hj9 : j.val ≠ 9 := by
        intro h9
        have hjeq : j = 9 := Fin.ext h9
        subst j
        change (autTbl.getD v.val []).getD 9 0 = u.val at hj
        rw [hAutLast v] at hj
        exact huv (Fin.ext hj.symm)
      have hjlt : j.val < 9 := by omega
      have h1 := hInvAut ⟨j.val, hjlt⟩
      have huEq : (⟨(autTbl.getD v.val []).getD j.val 0, hAutLt v ⟨j.val, by omega⟩⟩ : Fin 10) = u := Fin.ext hj
      rw [huEq] at h1
      omega
    let liftY : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y u =>
      if h : invIdx u < 9 then y ⟨invIdx u, h⟩ else false
    have hLiftV : ∀ y : Fin 9 → Bool, liftY y v = false := by
      intro y; dsimp only [liftY]; rw [dif_neg (by rw [hInvV]; omega)]
    have hLiftAut : ∀ (y : Fin 9 → Bool) (j : Fin 9),
        liftY y ⟨(autTbl.getD v.val []).getD j.val 0, hAutLt v ⟨j.val, by omega⟩⟩ = y j := by
      intro y j; dsimp only [liftY]; rw [dif_pos (by rw [hInvAut j]; exact j.isLt)]
      congr 1; exact Fin.ext (hInvAut j)
    have hLiftP : ∀ y : Fin 9 → Bool, graphFun P ∅ (liftY y) = p9Fn y := by
      intro y
      have hiff : graphFun P ∅ (liftY y) = true ↔ p9Fn y = true := by
        rw [hP_hasEdge]
        constructor
        · rintro ⟨u1, u2, hadj, hu1, hu2⟩
          have hu1ne : u1 ≠ v := fun h => by rw [h, hLiftV] at hu1; exact Bool.noConfusion hu1
          have hu2ne : u2 ≠ v := fun h => by rw [h, hLiftV] at hu2; exact Bool.noConfusion hu2
          have h1lt := hInvNe u1 hu1ne
          have h2lt := hInvNe u2 hu2ne
          let j1 : Fin 9 := ⟨invIdx u1, h1lt⟩
          let j2 : Fin 9 := ⟨invIdx u2, h2lt⟩
          have hsurj : ∀ (u : Fin 10) (huv : u ≠ v),
              (⟨(autTbl.getD v.val []).getD (invIdx u) 0, hAutLt v ⟨invIdx u, by have := hInvNe u huv; omega⟩⟩ : Fin 10) = u := by
            intro u huv
            have hex : ∃ j : Fin 9, (autTbl.getD v.val []).getD j.val 0 = u.val := by
              have hlt := hInvNe u huv
              dsimp only [invIdx] at hlt
              by_contra hno
              rw [dif_neg hno] at hlt; omega
            have hch := Classical.choose_spec hex
            have heq : invIdx u = (Classical.choose hex).val := by dsimp only [invIdx]; rw [dif_pos hex]
            exact Fin.ext (show (autTbl.getD v.val []).getD (invIdx u) 0 = u.val by rw [heq]; exact hch)
          have hadj' := (hAutAdj v j1 j2).mp (by rw [hsurj u1 hu1ne, hsurj u2 hu2ne]; exact hadj)
          have hy1 : y j1 = true := by dsimp only [liftY] at hu1; rw [dif_pos h1lt] at hu1; exact hu1
          have hy2 : y j2 = true := by dsimp only [liftY] at hu2; rw [dif_pos h2lt] at hu2; exact hu2
          have hcheckOne : ∀ (a b : Fin 9), (a.val, b.val) ∈ p9Edges →
              y a = true → y b = true → p9Fn y = true := by
            intro a b hab hya hyb
            dsimp only [p9Fn, p9Edges] at hab ⊢
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
            rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
            · have ha' : a = 0 := Fin.ext ha; have hb' : b = 1 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or]
            · have ha' : a = 1 := Fin.ext ha; have hb' : b = 2 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 2 := Fin.ext ha; have hb' : b = 3 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 3 := Fin.ext ha; have hb' : b = 4 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 4 := Fin.ext ha; have hb' : b = 0 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 0 := Fin.ext ha; have hb' : b = 5 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 1 := Fin.ext ha; have hb' : b = 6 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 2 := Fin.ext ha; have hb' : b = 7 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 3 := Fin.ext ha; have hb' : b = 8 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 5 := Fin.ext ha; have hb' : b = 7 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 6 := Fin.ext ha; have hb' : b = 8 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.true_or, Bool.or_true]
            · have ha' : a = 8 := Fin.ext ha; have hb' : b = 5 := Fin.ext hb; subst ha'; subst hb'; simp only [hya, hyb, Bool.true_and, Bool.or_true]
          rcases hadj' with h1 | h2
          · exact hcheckOne j1 j2 h1 hy1 hy2
          · exact hcheckOne j2 j1 h2 hy2 hy1
        · intro hp9
          have hex : ∃ (a b : Fin 9),
              ((a.val, b.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] ∨
               (b.val, a.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]) ∧
              y a = true ∧ y b = true := by
            dsimp only [p9Fn] at hp9
            rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
            · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
              · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                  · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                    · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                      · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                        · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                          · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                            · rcases Bool.or_eq_true_iff.mp hp9 with hp9 | h
                              · rcases Bool.or_eq_true_iff.mp hp9 with h | h
                                · exact ⟨0, 1, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                                · exact ⟨1, 2, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                              · exact ⟨2, 3, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                            · exact ⟨3, 4, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                          · exact ⟨4, 0, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                        · exact ⟨0, 5, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                      · exact ⟨1, 6, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                    · exact ⟨2, 7, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                  · exact ⟨3, 8, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
                · exact ⟨5, 7, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
              · exact ⟨6, 8, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
            · exact ⟨8, 5, Or.inl (by decide), (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
          obtain ⟨a, b, hab, hya, hyb⟩ := hex
          exact ⟨⟨(autTbl.getD v.val []).getD a.val 0, hAutLt v ⟨a.val, by omega⟩⟩,
                 ⟨(autTbl.getD v.val []).getD b.val 0, hAutLt v ⟨b.val, by omega⟩⟩,
                 (hAutAdj v a b).mpr hab, by rw [hLiftAut y a]; exact hya, by rw [hLiftAut y b]; exact hyb⟩
      cases h1 : graphFun P ∅ (liftY y) <;> cases h2 : p9Fn y
      · rfl
      · exact False.elim (Bool.noConfusion (h1.symm.trans (hiff.mpr h2)))
      · exact False.elim (Bool.noConfusion (h2.symm.trans (hiff.mp h1)))
      · rfl
    let env0 : List ℕ := List.ofFn (fun u : Fin 10 => if invIdx u < 9 then invIdx u + 2 else 0)
    have hBuildR : ∀ (gs : List Gate), (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
        ∃ (env : List ℕ) (outGs : List Gate),
          env.length = 10 + gs.length ∧
          (∀ i < 10, env.getD i 0 = env0.getD i 0) ∧
          outGs.length + gs.countP (fun g => g.inputs.contains v.val) ≤ gs.length ∧
          (∀ h0 : 0 < gs.length, (gs.getD 0 ⟨GateOp.or, []⟩).op = GateOp.and → v.val ∈ (gs.getD 0 ⟨GateOp.or, []⟩).inputs →
            env.getD 10 0 = 0 ∧
            (∀ h2 : (∃ r, 0 < r ∧ r < gs.length ∧ 10 ∈ (gs.getD r ⟨GateOp.or, []⟩).inputs),
              outGs.length + 2 ≤ gs.length)) ∧
          (∀ g' ∈ outGs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2) ∧
          (∀ t ∈ env, t < 2 ∨ t - 2 < 9 + outGs.length) ∧
          ∀ (y : Fin 9 → Bool) (i : ℕ),
            evalTag (outGs.foldl stepWire (List.ofFn y)) (env.getD i 0) =
              (gs.foldl stepWire (List.ofFn (liftY y))).getD i false := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨env0, [], by simp only [env0, List.length_ofFn, List.length_nil, Nat.add_zero],
          fun _ _ => rfl, by simp only [List.length_nil, List.countP_nil, Nat.add_zero, le_refl],
          fun h0 => by simp only [List.length_nil] at h0; omega,
          fun _ h => False.elim (List.not_mem_nil h), ?_, ?_⟩
        · intro t ht
          dsimp only [env0] at ht
          obtain ⟨u, rfl⟩ := List.mem_ofFn.mp ht
          by_cases hlt : invIdx u < 9
          · rw [if_pos hlt]; right; simp only [List.length_nil, Nat.add_zero]; omega
          · rw [if_neg hlt]; left; omega
        · intro y i
          rw [List.foldl_nil, List.foldl_nil]
          by_cases hilt : i < 10
          · have hgetE : env0.getD i 0 = if invIdx ⟨i, hilt⟩ < 9 then invIdx ⟨i, hilt⟩ + 2 else 0 := by
              simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hilt, Option.getD_some]
            have hgetL : (List.ofFn (liftY y)).getD i false = liftY y ⟨i, hilt⟩ := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hilt, Option.getD_some]
            rw [hgetE, hgetL]
            dsimp only [evalTag, liftY]
            by_cases hlt : invIdx ⟨i, hilt⟩ < 9
            · rw [if_pos hlt, dif_pos hlt, if_neg (by omega : invIdx ⟨i, hilt⟩ + 2 ≠ 0),
                if_neg (by omega : invIdx ⟨i, hilt⟩ + 2 ≠ 1)]
              have hsub : invIdx ⟨i, hilt⟩ + 2 - 2 = invIdx ⟨i, hilt⟩ := by omega
              rw [hsub]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt, Option.getD_some]
            · rw [if_neg hlt, dif_neg hlt, if_pos rfl]
          · have hgetE : env0.getD i 0 = 0 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [env0, List.length_ofFn]; omega)]; rfl
            rw [hgetE, getD_ge _ _ (by rw [List.length_ofFn]; omega)]; rfl
      | append_singleton gs g ih =>
        intro hall
        have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
          fun g' hg' => hall g' (List.mem_append_left [g] hg')
        obtain ⟨hgop, hglen⟩ := hall g (List.mem_append_right gs List.mem_cons_self)
        obtain ⟨i0, i1, hi01⟩ := List.length_eq_two.mp hglen
        obtain ⟨env, outGs, henvLen, henvPrefix, houtCnt, hG0, houtAO, henvBnd, heval⟩ := ih hgs
        have hEnvValid : ∀ i : ℕ, env.getD i 0 < 2 ∨ env.getD i 0 - 2 < 9 + outGs.length := by
          intro i
          by_cases hilt : i < env.length
          · exact henvBnd _ (by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some]
              exact List.getElem_mem hilt)
          · left
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
            omega
        let r := combTag g.op (env.getD i0 0) (env.getD i1 0) (9 + outGs.length)
        obtain ⟨hr1, hr2, hrZ, hr4, hr5⟩ :=
          combTag_spec g.op (env.getD i0 0) (env.getD i1 0) (9 + outGs.length) hgop (hEnvValid i0) (hEnvValid i1)
        have hEnvV0 : env.getD v.val 0 = 0 := by
          rw [henvPrefix v.val v.isLt]
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos v.isLt, Option.getD_some, hInvV]
          rw [if_neg (by omega : ¬ 9 < 9)]
        have hZeroIfV : g.inputs.contains v.val = true → r.2 = [] ∧ (g.op = GateOp.and → r.1 = 0) := by
          intro hc
          have hvmem : v.val ∈ g.inputs := List.contains_iff_mem.mp hc
          rw [hi01] at hvmem
          apply hrZ
          rcases List.mem_cons.mp hvmem with h1 | h2
          · exact Or.inl (h1 ▸ hEnvV0)
          · exact Or.inr ((List.mem_singleton.mp h2) ▸ hEnvV0)
        have hr2le : r.2.length ≤ 1 := hr2
        refine ⟨env ++ [r.1], outGs ++ r.2,
          by simp only [List.length_append, List.length_singleton]; omega,
          fun i hi => by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < env.length), ← List.getD_eq_getElem?_getD]
            exact henvPrefix i hi,
          ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, List.countP_append, List.countP_cons, List.countP_nil, List.length_append, List.length_singleton]
          by_cases hc : g.inputs.contains v.val = true
          · rw [hc, (hZeroIfV hc).1, List.length_nil]
            simp only [ite_true]; omega
          · have hcf : g.inputs.contains v.val = false := Bool.eq_false_iff.mpr hc
            rw [hcf]
            simp only [Bool.false_eq_true, ite_false]; omega
        · intro h0 hg0op hg0in
          by_cases hgs0 : gs.length = 0
          · have hgsNil : gs = [] := List.length_eq_zero_iff.mp hgs0
            subst gs
            rw [List.nil_append] at hg0op hg0in
            have hge0 : ([g] : List Gate).getD 0 ⟨GateOp.or, []⟩ = g := rfl
            rw [hge0] at hg0op hg0in
            have hvc : g.inputs.contains v.val = true := List.contains_iff_mem.mpr hg0in
            have hr0 := (hZeroIfV hvc).2 hg0op
            refine ⟨by
              have he10 : env.length = 10 := by simp only [List.length_nil, Nat.add_zero] at henvLen; exact henvLen
              rw [List.getD_eq_getElem?_getD, ← he10, List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some]; exact hr0,
              fun h => by obtain ⟨r', hr'0, hr'lt, _⟩ := h; simp only [List.nil_append, List.length_singleton] at hr'lt; omega⟩
          · have hgsPos : 0 < gs.length := by omega
            have hge0 : (gs ++ [g]).getD 0 ⟨GateOp.or, []⟩ = gs.getD 0 ⟨GateOp.or, []⟩ := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hgsPos]
            rw [hge0] at hg0op hg0in
            obtain ⟨he10, hgs2⟩ := hG0 hgsPos hg0op hg0in
            refine ⟨by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : 10 < env.length), ← List.getD_eq_getElem?_getD]
              exact he10, fun h => ?_⟩
            obtain ⟨r', hr'0, hr'lt, hr'in⟩ := h
            by_cases hr'old : r' < gs.length
            · have hger : (gs ++ [g]).getD r' ⟨GateOp.or, []⟩ = gs.getD r' ⟨GateOp.or, []⟩ := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hr'old]
              rw [hger] at hr'in
              have h2 := hgs2 ⟨r', hr'0, hr'old, hr'in⟩
              rw [List.length_append, List.length_append, List.length_singleton]; omega
            · have hr'eq : r' = gs.length := by rw [List.length_append, List.length_singleton] at hr'lt; omega
              have hger : (gs ++ [g]).getD r' ⟨GateOp.or, []⟩ = g := by
                rw [hr'eq]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hger, hi01] at hr'in
              have hr2nil : r.2 = [] := (hrZ (by
                rcases List.mem_cons.mp hr'in with h10 | h10'
                · exact Or.inl (h10 ▸ he10)
                · exact Or.inr ((List.mem_singleton.mp h10') ▸ he10))).1
              have hcnt1 : 1 ≤ gs.countP (fun g => g.inputs.contains v.val) := by
                have hmem0 : gs.getD 0 ⟨GateOp.or, []⟩ ∈ gs := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgsPos, Option.getD_some]
                  exact List.getElem_mem hgsPos
                exact List.countP_pos_iff.mpr ⟨gs.getD 0 ⟨GateOp.or, []⟩, hmem0, List.contains_iff_mem.mpr hg0in⟩
              rw [List.length_append, hr2nil, List.length_nil, List.length_append, List.length_singleton]
              omega
        · intro g' hg'
          rcases List.mem_append.mp hg' with h1 | h2
          · exact houtAO g' h1
          · exact ⟨(hr4 g' h2).1, (hr4 g' h2).2.1⟩
        · intro t ht
          rcases List.mem_append.mp ht with h1 | h2
          · rcases henvBnd t h1 with hlt | hlt
            · exact Or.inl hlt
            · exact Or.inr (by rw [List.length_append]; omega)
          · rw [List.mem_singleton.mp h2]
            rcases hr1 with h | h
            · exact Or.inl h
            · have h' : r.1 - 2 < 9 + outGs.length + r.2.length := h
              exact Or.inr (by rw [List.length_append]; omega)
        · intro y i
          rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hgsLen : (gs.foldl stepWire (List.ofFn (liftY y))).length = 10 + gs.length := by
            rw [foldl_length, List.length_ofFn]
          have houtLenW : (outGs.foldl stepWire (List.ofFn y)).length = 9 + outGs.length := by
            rw [foldl_length, List.length_ofFn]
          obtain ⟨hra, hrb⟩ := hr5 _ houtLenW
          by_cases hilt : i < env.length
          · have hgetE : (env ++ [r.1]).getD i 0 = env.getD i 0 := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
            have hgetW : (stepWire (gs.foldl stepWire (List.ofFn (liftY y))) g).getD i false =
                (gs.foldl stepWire (List.ofFn (liftY y))).getD i false := by
              change (gs.foldl stepWire (List.ofFn (liftY y)) ++ [_]).getD i false = _
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
            rw [hgetE, hgetW, ← heval y i]
            have hti := hEnvValid i
            dsimp only [evalTag]
            by_cases h0 : env.getD i 0 = 0
            · rw [if_pos h0, if_pos h0]
            · rw [if_neg h0, if_neg h0]
              by_cases h1 : env.getD i 0 = 1
              · rw [if_pos h1, if_pos h1]
              · rw [if_neg h1, if_neg h1]
                exact hrb (env.getD i 0 - 2) (hti.resolve_left (by omega))
          · by_cases hieq : i = env.length
            · subst i
              have hgetE : (env ++ [r.1]).getD env.length 0 = r.1 := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              have hgetW : (stepWire (gs.foldl stepWire (List.ofFn (liftY y))) g).getD env.length false =
                  g.op.eval (g.inputs.map fun k => (gs.foldl stepWire (List.ofFn (liftY y))).getD k false) := by
                change ((gs.foldl stepWire (List.ofFn (liftY y))) ++ [g.op.eval (g.inputs.map fun k => (gs.foldl stepWire (List.ofFn (liftY y))).getD k false)]).getD env.length false = _
                rw [List.getD_eq_getElem?_getD,
                  show env.length = (gs.foldl stepWire (List.ofFn (liftY y))).length by omega,
                  List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hgetE, hgetW, hra, hi01, heval y i0, heval y i1, List.map_cons, List.map_cons, List.map_nil]
            · have hgetE : (env ++ [r.1]).getD i 0 = 0 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]; rfl
              have hgetW : (stepWire (gs.foldl stepWire (List.ofFn (liftY y))) g).getD i false = false :=
                getD_ge _ _ (by
                  change (gs.foldl stepWire (List.ofFn (liftY y)) ++ [_]).length ≤ i
                  rw [List.length_append, List.length_singleton, hgsLen]; omega)
              rw [hgetE, hgetW]; rfl
    obtain ⟨env, outGs, _, _, houtCnt, hG0, houtAO, _, heval⟩ :=
      hBuildR C.gates (fun g hg => ⟨hLeast.1.1 g hg, hLeast.1.2.2 g hg⟩)
    let tOut := env.getD C.output 0
    have hD16 : 16 ≤ outGs.length := by
      by_contra hlt16
      have hle15 : outGs.length ≤ 15 := by omega
      have ht0 : tOut ≠ 0 := by
        intro h0
        let y0 : Fin 9 → Bool := fun i => i == 0 || i == 1
        have h1 := heval y0 C.output
        have h2a : (C.gates.foldl stepWire (List.ofFn (liftY y0))).getD C.output false = graphFun P ∅ (liftY y0) :=
          congrFun hLeast.2.1 (liftY y0)
        have h2 : (C.gates.foldl stepWire (List.ofFn (liftY y0))).getD C.output false = p9Fn y0 :=
          h2a.trans (hLiftP y0)
        rw [h2] at h1
        change evalTag _ tOut = _ at h1
        rw [h0] at h1
        have hp9t : p9Fn y0 = true := rfl
        rw [hp9t] at h1
        exact Bool.noConfusion h1
      have ht1 : tOut ≠ 1 := by
        intro h1'
        let y1 : Fin 9 → Bool := fun _ => false
        have h1 := heval y1 C.output
        have h2a : (C.gates.foldl stepWire (List.ofFn (liftY y1))).getD C.output false = graphFun P ∅ (liftY y1) :=
          congrFun hLeast.2.1 (liftY y1)
        have h2 : (C.gates.foldl stepWire (List.ofFn (liftY y1))).getD C.output false = p9Fn y1 :=
          h2a.trans (hLiftP y1)
        rw [h2] at h1
        change evalTag _ tOut = _ at h1
        rw [h1'] at h1
        have hp9f : p9Fn y1 = false := rfl
        rw [hp9f] at h1
        exact Bool.noConfusion h1
      let D : Circuit := ⟨outGs, tOut - 2⟩
      have hDFan : FanInTwo D := by
        intro g hg
        refine ⟨?_, by have := (houtAO g hg).2; omega⟩
        rcases (houtAO g hg).1 with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
      obtain ⟨y, hy⟩ := hP9 D hDFan hle15
      apply hy
      have h1 := heval y C.output
      have h2a : (C.gates.foldl stepWire (List.ofFn (liftY y))).getD C.output false = graphFun P ∅ (liftY y) :=
        congrFun hLeast.2.1 (liftY y)
      have h2 : (C.gates.foldl stepWire (List.ofFn (liftY y))).getD C.output false = p9Fn y :=
        h2a.trans (hLiftP y)
      rw [h2] at h1
      change evalTag (outGs.foldl stepWire (List.ofFn y)) tOut = p9Fn y at h1
      dsimp only [evalTag] at h1
      rw [if_neg ht0, if_neg ht1] at h1
      exact h1
    refine ⟨by rw [size_def]; omega, fun h0 hg0op hg0in hex => ?_⟩
    have h2 := (hG0 h0 hg0op hg0in).2 hex
    rw [size_def]; omega
  have hFanBound : ∀ v : Fin 10, C.gates.countP (fun g => g.inputs.contains v.val) ≤ C.size - 16 := by
    intro v; have := (hRestrictV v).1; omega
  have hCpos : 0 < C.gates.length := by
    by_contra h0
    have hnil : C.gates = [] := List.length_eq_zero_iff.mp (by omega)
    have h1 := congrFun hLeast.2.1 (pairInput 0 1)
    have h2 := congrFun hLeast.2.1 (pairInput 2 3)
    have h3 := congrFun hLeast.2.1 (fun _ => false)
    rw [circuitFun_def, wires_def, hnil, List.foldl_nil] at h1 h2 h3
    have hp1 : graphFun P ∅ (pairInput 0 1) = true :=
      (hP_hasEdge _).mpr ⟨0, 1, ⟨by decide, Or.inl (by decide)⟩, by decide, by decide⟩
    have hp2 : graphFun P ∅ (pairInput 2 3) = true :=
      (hP_hasEdge _).mpr ⟨2, 3, ⟨by decide, Or.inl (by decide)⟩, by decide, by decide⟩
    rw [hp1] at h1; rw [hp2] at h2
    by_cases hlt : C.output < 10
    · have hget1 : (List.ofFn (pairInput (0 : Fin 10) 1)).getD C.output false = pairInput (0 : Fin 10) 1 ⟨C.output, hlt⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt, Option.getD_some]
      have hget2 : (List.ofFn (pairInput (2 : Fin 10) 3)).getD C.output false = pairInput (2 : Fin 10) 3 ⟨C.output, hlt⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt, Option.getD_some]
      rw [hget1, pairInput_def] at h1
      rw [hget2, pairInput_def] at h2
      have ha := decide_eq_true_eq.mp h1
      have hb := decide_eq_true_eq.mp h2
      rcases ha with h | h <;> rcases hb with h' | h' <;>
        exact False.elim ((by decide : ¬ _) (h.symm.trans h'))
    · rw [getD_ge _ _ (by rw [List.length_ofFn]; omega)] at h1
      exact Bool.noConfusion h1
  have hK0Bound : ∀ K0 : Finset (Fin 10), IsMinCover (P.deleteEdges ↑(Ustar P C)) K0 →
      K0.card + 2 * (centreless P C).card + (junk P C).card + (orN P C \ lam P C).card ≤
        C.size - 14 + (Ustar P C).card := by
    intro K0 hK0
    have hle := hMinCov K0 hK0
    have hge16 : 16 ≤ C.size := by have := (hRestrictV 0).1; omega
    omega
  have hBudgetLtCov : ∀ A : Finset (Fin 10), (∀ e ∈ Ustar P C, ∃ v ∈ A, v ∈ e) →
      2 * (centreless P C).card + (junk P C).card + (orN P C \ lam P C).card <
        A.card + (Ustar P C).card := by
    intro A hA
    let H : SimpleGraph (Fin 10) := P.deleteEdges ↑(Ustar P C)
    let covers : Finset (Finset (Fin 10)) :=
      Finset.univ.filter (fun T : Finset (Fin 10) => ∀ u v : Fin 10, H.Adj u v → u ∈ T ∨ v ∈ T)
    have hCoversNe : covers.Nonempty :=
      ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
    obtain ⟨K0, hK0mem, hK0min⟩ := Finset.exists_min_image covers Finset.card hCoversNe
    have hK0cov : ∀ u v : Fin 10, H.Adj u v → u ∈ K0 ∨ v ∈ K0 := (Finset.mem_filter.mp hK0mem).2
    have hIsMin : IsMinCover H K0 := ⟨hK0cov, fun T' hT' => hK0min T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩
    have hK0le := hMinCov K0 hIsMin
    have hVC : ∀ u v : Fin 10, P.Adj u v → u ∈ K0 ∪ A ∨ v ∈ K0 ∪ A := by
      intro u v huv
      by_cases hu : s(u, v) ∈ Ustar P C
      · obtain ⟨w, hwA, hwe⟩ := hA s(u, v) hu
        rcases Sym2.mem_iff.mp hwe with rfl | rfl
        · exact Or.inl (Finset.mem_union_right K0 hwA)
        · exact Or.inr (Finset.mem_union_right K0 hwA)
      · rcases hK0cov u v (SimpleGraph.deleteEdges_adj.mpr ⟨huv, Finset.mem_coe.not.mpr hu⟩) with h1 | h2
        · exact Or.inl (Finset.mem_union_left A h1)
        · exact Or.inr (Finset.mem_union_left A h2)
    have h6 := hPminVC (K0 ∪ A) hVC
    have hun := Finset.card_union_le K0 A
    omega

  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep 10 cs g = cs ++ [(g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + cs.length))).flatMap
        (fun w => (w - 10) :: cs.getD (w - 10) [])] := by
    intro cs g
    change cs ++ [(g.inputs.filter (fun w => @decide (10 ≤ w ∧ w < 10 + cs.length) _)).flatMap
      (fun w => (w - 10) :: cs.getD (w - 10) [])] = _
    congr 2
  have cones_def : ∀ (C' : Circuit), cones 10 C' = C'.gates.foldl (coneStep 10) [] := fun _ => rfl
  have inCone_def : ∀ (C' : Circuit) (i j : ℕ), InCone 10 C' i j = (i ∈ (cones 10 C').getD j []) :=
    fun _ _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      orStep 10 cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + cs.length))).flatMap
          (fun w => cs.getD (w - 10) [])
        else [])] := by
    intro cs g
    change cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
      ((g.inputs.filter (fun w => @decide (10 ≤ w ∧ w < 10 + cs.length) _)).flatMap
        (fun w => cs.getD (w - 10) [])) [])] = _
    by_cases hop : g.op = GateOp.or
    · rw [if_pos hop]
    · rw [if_neg hop]
  have orSets_def : ∀ (C' : Circuit), orSets 10 C' = C'.gates.foldl (orStep 10) [] := fun _ => rfl
  have orReaches_def : ∀ (C' : Circuit) (w g : ℕ),
      OrReaches 10 C' w g = (10 ≤ w ∧ g ∈ (orSets 10 C').getD (w - 10) []) := fun _ _ _ => rfl
  have orIn_def : ∀ (C' : Circuit) (w : ℕ) (i : Fin 10),
      i ∈ orIn 10 C' w ↔ ((i : ℕ) = w ∨ ∃ k < C'.gates.length,
        OrReaches 10 C' w k ∧ (gateAt C' k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C' k).inputs) := by
    intro C' w i
    exact (@Finset.mem_filter _ _ _ Finset.univ i).trans (by simp only [Finset.mem_univ, true_and])
  have side_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      side (n := 10) C' a b = orIn 10 C' (opnd C' a b) := fun _ _ _ => rfl
  have tops_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ tops P C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧ BelowF P C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have junk_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ junk P C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧
        ∃ x : Fin 10 → Bool, gateVal 10 C' j x = true ∧ graphFun P ∅ x = false := by
    intro C' j
    refine (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans ?_
    rw [Finset.mem_range]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.1, h.2.2⟩⟩
  have orN_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ orN P C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.or ∧ ¬ BelowF P C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have lam_mem : ∀ (C' : Circuit) (h : ℕ),
      h ∈ lam P C' ↔ h ∈ orN P C' ∧ (orIn 10 C' (opnd C' h 0)).Nonempty ∧
        (orIn 10 C' (opnd C' h 1)).Nonempty ∧ ∃ a ∈ tops P C', ∃ b : Fin 2,
          (side (n := 10) C' a (1 - b)).card = 1 ∧ OrReaches 10 C' (opnd C' a b) h := by
    intro C' h
    exact @Finset.mem_filter _ _ _ (orN P C') h
  have centreless_mem : ∀ (C' : Circuit) (a : ℕ),
      a ∈ centreless P C' ↔ a ∈ tops P C' ∧ (side (n := 10) C' a 0 = ∅ ∨ side (n := 10) C' a 1 = ∅) := by
    intro C' a
    exact @Finset.mem_filter _ _ _ (tops P C') a
  have readers_mem : ∀ (C' : Circuit) (j k : ℕ),
      k ∈ readers 10 C' j ↔ k < C'.gates.length ∧ 10 + j ∈ (gateAt C' k).inputs := by
    intro C' j k
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) k).trans (by rw [Finset.mem_range])
  have starEdges_def : ∀ (C' : Circuit),
      starEdges P C' = (tops P C').biUnion (fun a => (side (n := 10) C' a 0 ×ˢ side (n := 10) C' a 1).image (fun p => s(p.1, p.2))) :=
    fun _ => rfl
  have Ustar_def : ∀ (C' : Circuit), Ustar P C' = P.edgeFinset \ starEdges P C' := fun _ => rfl
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ hj; simp only [List.length_nil] at hj; omega
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp only [stepWire, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val : Circuit → List Bool → ℕ → Bool := fun C' x u => (C'.wires x).getD u false
  have gateAt_eq : ∀ {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length), gateAt C' j = C'.gates[j] := by
    intro C' j hj
    rw [gateAt_def]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have gateAt_mem : ∀ {C' : Circuit} {j : ℕ}, j < C'.gates.length → gateAt C' j ∈ C'.gates := by
    intro C' j hj
    rw [gateAt_eq hj]
    exact List.getElem_mem hj
  have val_input : ∀ {C' : Circuit} {x : List Bool}, x.length = 10 → ∀ {u : ℕ}, u < 10 →
      val C' x u = x.getD u false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = _
    rw [wires_def]
    exact foldl_getD_lt _ _ _ (by omega)
  have val_ge : ∀ {C' : Circuit} {x : List Bool}, x.length = 10 → ∀ {u : ℕ}, 10 + C'.gates.length ≤ u →
      val C' x u = false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = false
    apply getD_ge
    rw [wires_def, foldl_length]
    omega
  have val_gate : ∀ {C' : Circuit} {x : List Bool}, x.length = 10 → ∀ {j : ℕ}, j < C'.gates.length →
      val C' x (10 + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
        if i < 10 + j then val C' x i else false) := by
    intro C' x hx j hj
    rw [← hx]
    change (C'.wires x).getD (x.length + j) false = _
    rw [wires_def, gateAt_eq hj]
    exact foldl_getD_gate C'.gates x j hj
  have val_or : ∀ {C' : Circuit} {x : List Bool}, x.length = 10 → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.or →
      (val C' x (10 + r) = true ↔ ∃ i ∈ (gateAt C' r).inputs, i < 10 + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_or]
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < 10 + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; exact Bool.noConfusion h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
  have val_and : ∀ {C' : Circuit} {x : List Bool}, x.length = 10 → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.and →
      (val C' x (10 + r) = true ↔ ∀ i ∈ (gateAt C' r).inputs, i < 10 + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_and]
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < 10 + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; exact Bool.noConfusion h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2
  have val_ofFn : ∀ (C' : Circuit) (x : Fin 10 → Bool) (u : Fin 10),
      val C' (List.ofFn x) u.val = x u := by
    intro C' x u
    rw [val_input List.length_ofFn u.isLt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos u.isLt, Option.getD_some]
  have gateVal_eq_val : ∀ (C' : Circuit) (j : ℕ) (x : Fin 10 → Bool),
      gateVal 10 C' j x = val C' (List.ofFn x) (10 + j) := fun _ _ _ => rfl
  have pairInput_left : ∀ u v : Fin 10, pairInput u v u = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inl rfl)
  have pairInput_right : ∀ u v : Fin 10, pairInput u v v = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inr rfl)
  have pairInput_true : ∀ u v w : Fin 10, pairInput u v w = true ↔ w = u ∨ w = v := by
    intro u v w; rw [pairInput_def, decide_eq_true_eq]
  have graphFun_pair : ∀ u v : Fin 10, graphFun P ∅ (pairInput u v) = true ↔ P.Adj u v := by
    intro u v
    rw [hP_hasEdge]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have ha' := (pairInput_true u v a).mp ha
      have hb' := (pairInput_true u v b).mp hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact (P.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (P.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, pairInput_left u v, pairInput_right u v⟩
  have hOutLt : C.output < 10 + C.gates.length := by
    by_contra hge
    have hv : val C (List.ofFn (pairInput (0 : Fin 10) (1 : Fin 10))) C.output = true := by
      have h : val C (List.ofFn (pairInput (0 : Fin 10) (1 : Fin 10))) C.output = graphFun P ∅ (pairInput (0 : Fin 10) (1 : Fin 10)) :=
        congrFun hLeast.2.1 (pairInput (0 : Fin 10) (1 : Fin 10))
      rw [h]
      exact (graphFun_pair (0 : Fin 10) (1 : Fin 10)).mpr ⟨by decide, Or.inl (by decide)⟩
    rw [val_ge List.length_ofFn (by omega)] at hv
    exact Bool.noConfusion hv
  let shiftW : ℕ → ℕ → ℕ := fun k w => if w < 10 + k then w else w - 1
  let unshiftW : ℕ → ℕ → ℕ := fun k w => if w < 10 + k then w else w + 1
  let unshiftG : ℕ → ℕ → ℕ := fun k j => if j < k then j else j + 1
  let shiftGate : ℕ → Gate → Gate := fun k g => ⟨g.op, g.inputs.map (shiftW k)⟩
  let delDead : ℕ → Circuit → Circuit := fun k C' =>
    ⟨(C'.gates.eraseIdx k).map (shiftGate k), shiftW k C'.output⟩
  have unshiftW_shiftW : ∀ (k w : ℕ), w ≠ 10 + k → unshiftW k (shiftW k w) = w := by
    intro k w hne; dsimp only [unshiftW, shiftW]; split_ifs <;> omega
  have delDead_length : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      (delDead k C').gates.length = C'.gates.length - 1 := by
    intro k C' hk; dsimp only [delDead]; rw [List.length_map, List.length_eraseIdx_of_lt hk]
  have delDead_gateAt : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      ∀ j, j < (delDead k C').gates.length →
      gateAt (delDead k C') j = shiftGate k (gateAt C' (unshiftG k j)) := by
    intro k C' hk j hj
    have hj_lt : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj_e : j < (C'.gates.eraseIdx k).length := by rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
    rw [gateAt_eq hj]
    dsimp only [delDead, unshiftG]
    rw [List.getElem_map]
    split_ifs with hjk
    · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (by omega)]
    · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
  have delDead_readsBack : ∀ (k : ℕ) (C' : Circuit), ReadsBack 10 C' →
      k < C'.gates.length → (∀ j < C'.gates.length, 10 + k ∉ (gateAt C' j).inputs) →
      ReadsBack 10 (delDead k C') := by
    intro k C' hRB hk hno j hj w' hw'
    rw [delDead_gateAt k C' hk j hj] at hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    have hj_len : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
    have hw_lt : w < 10 + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
    have hw_ne : w ≠ 10 + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
    dsimp only [shiftW]
    dsimp only [unshiftG] at hw_lt
    split_ifs at hw_lt ⊢ <;> omega
  have delDead_ao2 : ∀ (k : ℕ) (C' : Circuit), IsAO2 10 C' →
      k < C'.gates.length → (∀ j < C'.gates.length, 10 + k ∉ (gateAt C' j).inputs) →
      IsAO2 10 (delDead k C') := by
    intro k C' h hk hno
    have mapped : ∀ g ∈ (delDead k C').gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hm := List.mem_of_mem_eraseIdx hg'
      exact ⟨h.1 g' hm, by dsimp only [shiftGate]; rw [List.length_map]; exact h.2.2 g' hm⟩
    exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack k C' h.2.1 hk hno,
      fun g hg => (mapped g hg).2⟩
  have delDead_wires_eq : ∀ (k : ℕ) (C' : Circuit) (l : List Bool), l.length = 10 →
      ReadsBack 10 C' → k < C'.gates.length → (∀ j < C'.gates.length, 10 + k ∉ (gateAt C' j).inputs) →
      ∀ w : ℕ, val (delDead k C') l w = val C' l (unshiftW k w) := by
    intro k C' l hl hRB hk hno w
    have hRB' : ReadsBack 10 (delDead k C') := delDead_readsBack k C' hRB hk hno
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw_oob : 10 + (delDead k C').gates.length ≤ w
      · have hdl := delDead_length k C' hk
        have huw : 10 + C'.gates.length ≤ unshiftW k w := by dsimp only [unshiftW]; split_ifs <;> omega
        rw [val_ge hl hw_oob, val_ge hl huw]
      · by_cases hwn : w < 10
        · have huw : unshiftW k w = w := by dsimp only [unshiftW]; split_ifs <;> omega
          rw [huw, val_input hl hwn, val_input hl hwn]
        · let j := w - 10
          have hw_eq : w = 10 + j := by omega
          have hj_lt : j < (delDead k C').gates.length := by omega
          have hdl := delDead_length k C' hk
          have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
          have huw : unshiftW k (10 + j) = 10 + unshiftG k j := by
            dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
          rw [hw_eq, huw, val_gate hl hj_lt, val_gate hl hj0_lt, delDead_gateAt k C' hk j hj_lt]
          dsimp only [shiftGate]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hu_lt' : shiftW k u < 10 + j := by
            have hmem : shiftW k u ∈ (gateAt (delDead k C') j).inputs := by
              rw [delDead_gateAt k C' hk j hj_lt]
              exact List.mem_map.mpr ⟨u, hu, rfl⟩
            exact hRB' j hj_lt (shiftW k u) hmem
          have hu_lt0 : u < 10 + unshiftG k j := hRB (unshiftG k j) hj0_lt u hu
          have hu_ne : u ≠ 10 + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
          simp only [Function.comp_apply]
          rw [if_pos hu_lt', if_pos hu_lt0, ih (shiftW k u) (by omega), unshiftW_shiftW k u hu_ne]
  have leastReadAny : ∀ {j : ℕ}, j < C.gates.length → C.output ≠ 10 + j → (readers 10 C j).Nonempty := by
    intro j hj hout
    by_contra hnot
    have hno : ∀ k < C.gates.length, 10 + j ∉ (gateAt C k).inputs := by
      intro k hk hin
      exact hnot ⟨k, (readers_mem C j k).mpr ⟨hk, hin⟩⟩
    have heq : circuitFun 10 (delDead j C) = circuitFun 10 C := by
      funext x
      rw [circuitFun_def, circuitFun_def]
      change val (delDead j C) (List.ofFn x) (shiftW j C.output) = val C (List.ofFn x) C.output
      rw [delDead_wires_eq j C (List.ofFn x) List.length_ofFn hLeast.1.2.1 hj hno,
        unshiftW_shiftW j C.output hout]
    have hle := hLeast.2.2 (delDead j C) (delDead_ao2 j C hLeast.1 hj hno) (heq.trans hLeast.2.1)
    have hlen := delDead_length j C hj
    rw [size_def, size_def] at hle
    omega
  have leastRead : ∀ {j : ℕ}, j < C.gates.length → ¬ BelowF P C j → (readers 10 C j).Nonempty := by
    intro j hj hd
    refine leastReadAny hj ?_
    intro heq
    apply hd
    intro x hx
    have h : val C (List.ofFn x) C.output = graphFun P ∅ x := congrFun hLeast.2.1 x
    rw [heq] at h
    exact h.symm.trans hx
  have replace_gate_by_wire : ∀ (a w0 : ℕ), a < C.gates.length → w0 < 10 + a →
      (∀ x : Fin 10 → Bool, val C (List.ofFn x) w0 = gateVal 10 C a x) → False := by
    intro a w0 ha hw0 hEq
    let repW : ℕ → ℕ := fun w => if w = 10 + a then w0 else if w < 10 + a then w else w - 1
    let repGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map repW⟩
    let D : Circuit := ⟨(C.gates.eraseIdx a).map repGate, repW C.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by
      dsimp only [D]; rw [List.length_map, List.length_eraseIdx_of_lt ha]
    have hDgate : ∀ j, j < D.gates.length → gateAt D j = repGate (gateAt C (unshiftG a j)) := by
      intro j hj
      have hj_lt : j < C.gates.length - 1 := by omega
      have hj_e : j < (C.gates.eraseIdx a).length := by rw [List.length_eraseIdx_of_lt ha]; exact hj_lt
      rw [gateAt_eq hj]
      dsimp only [D, unshiftG]
      rw [List.getElem_map]
      split_ifs with hja
      · rw [List.getElem_eraseIdx_of_lt hj_e hja, gateAt_eq (by omega)]
      · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
    have hDRB : ReadsBack 10 D := by
      intro j hj w' hw'
      rw [hDgate j hj] at hw'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
      have hj0 : unshiftG a j < C.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
      have hwlt : w < 10 + unshiftG a j := hLeast.1.2.1 (unshiftG a j) hj0 w hw
      dsimp only [repW]
      dsimp only [unshiftG] at hwlt
      split_ifs at hwlt ⊢ <;> omega
    have hDAO : IsAO2 10 D := by
      have mapped : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have hm := List.mem_of_mem_eraseIdx hg'
        exact ⟨hLeast.1.1 g' hm, by dsimp only [repGate]; rw [List.length_map]; exact hLeast.1.2.2 g' hm⟩
      exact ⟨fun g hg => (mapped g hg).1, hDRB, fun g hg => (mapped g hg).2⟩
    have hValEq : ∀ (x : Fin 10 → Bool) (w : ℕ), w < 10 + C.gates.length →
        val D (List.ofFn x) (repW w) = val C (List.ofFn x) w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt
        by_cases hwn : w < 10
        · have hrw : repW w = w := by dsimp only [repW]; split_ifs <;> omega
          rw [hrw, val_input List.length_ofFn hwn, val_input List.length_ofFn hwn]
        · by_cases hwa : w = 10 + a
          · subst w
            have hrw : repW (10 + a) = w0 := by dsimp only [repW]; rw [if_pos rfl]
            have hrw0 : repW w0 = w0 := by dsimp only [repW]; split_ifs <;> omega
            rw [hrw, ← hrw0, ih w0 hw0 (by omega)]
            exact hEq x
          · let j0 := w - 10
            have hweq : w = 10 + j0 := by omega
            have hj0 : j0 < C.gates.length := by omega
            let j := if j0 < a then j0 else j0 - 1
            have hj : j < D.gates.length := by dsimp only [j]; split_ifs <;> omega
            have hrw : repW w = 10 + j := by dsimp only [repW, j]; split_ifs <;> omega
            have hun : unshiftG a j = j0 := by dsimp only [unshiftG, j]; split_ifs <;> omega
            rw [hrw, hweq, val_gate List.length_ofFn hj, val_gate List.length_ofFn hj0, hDgate j hj, hun]
            dsimp only [repGate]
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult : u < 10 + j0 := hLeast.1.2.1 j0 hj0 u hu
            have hrult : repW u < 10 + j :=
              hDRB j hj (repW u) (by rw [hDgate j hj, hun]; exact List.mem_map.mpr ⟨u, hu, rfl⟩)
            simp only [Function.comp_apply]
            rw [if_pos hrult, if_pos hult]
            exact ih u (by omega) (by omega)
    have hDcomp : circuitFun 10 D = graphFun P ∅ := by
      funext x
      rw [circuitFun_def]
      change val D (List.ofFn x) (repW C.output) = graphFun P ∅ x
      rw [hValEq x C.output hOutLt]
      exact congrFun hLeast.2.1 x
    have hle := hLeast.2.2 D hDAO hDcomp
    rw [size_def, size_def, hDlen] at hle
    omega
  let OrStep : ℕ → ℕ → Prop := fun w w' =>
    ∃ k, k < C.gates.length ∧ w = 10 + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < 10 + k
  have orStep_up : ∀ {x : List Bool}, x.length = 10 → ∀ {w w' : ℕ},
      Relation.ReflTransGen OrStep w w' → val C x w' = true → val C x w = true := by
    intro x hx w w' h hv
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
  have or_trace : ∀ {x : List Bool}, x.length = 10 → ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen OrStep w w' ∧ val C x w' = true ∧
        (w' < 10 ∨ ∃ h, h < C.gates.length ∧ w' = 10 + h ∧ (gateAt C h).op ≠ GateOp.or) := by
    intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < 10
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : 10 + C.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; exact Bool.noConfusion hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = 10 + k := ⟨w - 10, by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hop : (gateAt C k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨10 + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
  have operand_trace : ∀ (u v : Fin 10) (p : ℕ), val C (List.ofFn (pairInput u v)) p = true →
      (∃ t : Fin 10, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val) ∨
      (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
        Relation.ReflTransGen OrStep p (10 + h) ∧
        val C (List.ofFn (pairInput u v)) (10 + h) = true) := by
    intro u v p hv
    obtain ⟨w', hr, hv', hw'⟩ := or_trace List.length_ofFn p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left
      refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin 10).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right
      exact ⟨h, hh, hop, hr, hv'⟩
  have reach_var_val : ∀ (x : Fin 10 → Bool) (p : ℕ) (t : Fin 10),
      Relation.ReflTransGen OrStep p t.val → x t = true → val C (List.ofFn x) p = true :=
    fun x p t hr ht => orStep_up List.length_ofFn hr (by rw [val_ofFn]; exact ht)
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 10) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, coneStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep 10) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 10 ≤ w ∧ w < 10 + j ∧
          (i = w - 10 ∨ i ∈ (gs.foldl (coneStep 10) []).getD (w - 10) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, List.length_nil, Nat.not_lt_zero, false_and]
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 10) []).length = gs.length := by rw [cones_len, List.length_nil, Nat.zero_add]
      have key : ∀ k, k < gs.length →
          (coneStep 10 (gs.foldl (coneStep 10) []) g).getD k [] =
            (gs.foldl (coneStep 10) []).getD k [] := by
        intro k hk
        rw [coneStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp only [List.length_append, List.length_singleton]; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 10) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 10) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        have e2 : (coneStep 10 (gs.foldl (coneStep 10) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + gs.length))).flatMap
              (fun w => (w - 10) :: (gs.foldl (coneStep 10) []).getD (w - 10) []) := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp only [List.length_append, List.length_singleton]; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 10) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 10) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep 10 (gs.foldl (coneStep 10) []) g).getD j [] = [] := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; exact False.elim (List.not_mem_nil h0)
        · rintro ⟨h0, _⟩; simp only [List.length_append, List.length_singleton] at h0; omega
  have inCone_iff : ∀ i j : ℕ, InCone 10 C i j ↔
      j < C.gates.length ∧ ∃ k, k < j ∧ 10 + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone 10 C i k) := by
    intro i j
    have h := cones_char C.gates i j
    rw [inCone_def, cones_def, gateAt_def, h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - 10, by omega, ?_, ?_⟩
      · have he : 10 + (w - 10) = w := by omega
        rw [he]; exact hw
      · rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by rw [inCone_def, cones_def]; exact h3)
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, 10 + k, hw, by omega, by omega, ?_⟩
      have he : 10 + k - 10 = k := by omega
      rw [he]
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by rw [inCone_def, cones_def] at h3; exact h3)
  have inCone_trans : ∀ {i j k : ℕ}, InCone 10 C i j → InCone 10 C j k → InCone 10 C i k := by
    intro i j k hij
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hjk
      obtain ⟨hklen, r, hr, hrin, rfl | hjr⟩ := (inCone_iff j k).mp hjk
      · exact (inCone_iff i k).mpr ⟨hklen, j, hr, hrin, Or.inr hij⟩
      · exact (inCone_iff i k).mpr ⟨hklen, r, hr, hrin, Or.inr (ih r hr hjr)⟩
  have orStep_le : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' → w' ≤ w := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_refl _
    | head hstep _ ih => obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep; omega
  have orStep_cone : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
      ∀ k h', w = 10 + k → w' = 10 + h' → h' = k ∨ InCone 10 C h' k := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = 10 + k1 := ⟨c - 10, by omega⟩
      subst hk1
      right
      exact (inCone_iff h' k0).mpr ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
  have operand_cone : ∀ {a p h : ℕ}, a < C.gates.length → p ∈ (gateAt C a).inputs → p < 10 + a →
      Relation.ReflTransGen OrStep p (10 + h) → InCone 10 C h a := by
    intro a p h ha hin hp hr
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = 10 + k1 := ⟨p - 10, by omega⟩
    exact (inCone_iff h a).mpr ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 10) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, orStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (orStep 10) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 10 ≤ w ∧ w < 10 + j ∧
            i ∈ (gs.foldl (orStep 10) []).getD (w - 10) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, List.length_nil, Nat.not_lt_zero, false_and]
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 10) []).length = gs.length := by rw [orSets_len, List.length_nil, Nat.zero_add]
      have key : ∀ k, k < gs.length →
          (orStep 10 (gs.foldl (orStep 10) []) g).getD k [] =
            (gs.foldl (orStep 10) []).getD k [] := by
        intro k hk
        rw [orStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - 10) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - 10) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep 10 (gs.foldl (orStep 10) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + gs.length))).flatMap
                (fun w => (gs.foldl (orStep 10) []).getD (w - 10) []) := by
            rw [orStep_def, if_pos hop]
            simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inl h3⟩
            · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - 10) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - 10) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep 10 (gs.foldl (orStep 10) []) g).getD gs.length [] = [gs.length] := by
            rw [orStep_def, if_neg hop]
            simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp only [List.length_append, List.length_singleton]; omega, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact False.elim (hop hop2)
      · have e0 : (orStep 10 (gs.foldl (orStep 10) []) g).getD j [] = [] := by
          rw [orStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; exact False.elim (List.not_mem_nil h0)
        · rintro ⟨h0, _⟩; simp only [List.length_append, List.length_singleton] at h0; omega
  have orReaches_iff : ∀ k g : ℕ, OrReaches 10 C (10 + k) g ↔
      k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < 10 + k ∧ OrReaches 10 C i g)) := by
    intro k g
    have h := orSets_char C.gates g k
    rw [orReaches_def, orSets_def, gateAt_def]
    have e : 10 + k - 10 = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, by rw [orReaches_def, orSets_def]; exact ⟨h1, h3⟩⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1⟩
      · exact Or.inl h3
      · rw [orReaches_def, orSets_def] at h1
        exact Or.inr ⟨hop, w, hw, h1.1, h2, h1.2⟩
  have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStep w w2 →
      ∀ g, w2 = 10 + g → g < C.gates.length → OrReaches 10 C w g := by
    intro w w2 h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg; subst h1
      exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
  have orReaches_reach : ∀ (g w : ℕ), OrReaches 10 C w g →
      Relation.ReflTransGen OrStep w (10 + g) ∧ g < C.gates.length := by
    intro g w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      rw [orReaches_def] at h
      have hnw : 10 ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 10 + k := ⟨w - 10, by omega⟩
      have h' : OrReaches 10 C (10 + k) g := by rw [orReaches_def]; exact h
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h'
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
  have orReaches_le : ∀ {w g : ℕ}, OrReaches 10 C w g → 10 + g ≤ w :=
    fun hr => orStep_le (orReaches_reach _ _ hr).1
  have orReaches_trans : ∀ {w k g : ℕ}, OrReaches 10 C w k → OrReaches 10 C (10 + k) g → OrReaches 10 C w g := by
    intro w k g h1 h2
    obtain ⟨r1, _⟩ := orReaches_reach k w h1
    obtain ⟨r2, hg⟩ := orReaches_reach g (10 + k) h2
    exact reach_orReaches (r1.trans r2) g rfl hg
  have mem_orIn_reach : ∀ {p : ℕ} (u : Fin 10), u ∈ orIn 10 C p → Relation.ReflTransGen OrStep p u.val := by
    intro p u hu
    rcases (orIn_def C p u).mp hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn : ∀ {p : ℕ} (u : Fin 10), Relation.ReflTransGen OrStep p u.val → u ∈ orIn 10 C p := by
    intro p u hr
    apply (orIn_def C p u).mpr
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have orIn_mono : ∀ {w g : ℕ}, OrReaches 10 C w g → orIn 10 C (10 + g) ⊆ orIn 10 C w := by
    intro w g hr u hu
    exact reach_mem_orIn u ((orReaches_reach g w hr).1.trans (mem_orIn_reach u hu))
  have orIn_leaf : ∀ (v : Fin 10), orIn 10 C v.val = {v} := by
    intro v
    apply Finset.ext
    intro u
    rw [orIn_def, Finset.mem_singleton]
    constructor
    · rintro (h | ⟨k, _, hr, _, _⟩)
      · exact Fin.ext h
      · rw [orReaches_def] at hr; have := v.isLt; omega
    · rintro rfl; exact Or.inl rfl
  have topData : ∀ {a : ℕ}, a ∈ tops P C → a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF P C a :=
    fun ha => (tops_mem C _).mp ha
  have junkData : ∀ {a : ℕ}, a ∈ junk P C →
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        ∃ x : Fin 10 → Bool, gateVal 10 C a x = true ∧ graphFun P ∅ x = false :=
    fun ha => (junk_mem C _).mp ha
  have junkNotBelow : ∀ {j : ℕ}, j ∈ junk P C → ¬ BelowF P C j := by
    intro j hj h
    obtain ⟨_, _, x, hx, hf⟩ := junkData hj
    exact Bool.false_ne_true (hf.symm.trans (h x hx))
  have fin2_or : ∀ b : Fin 2, b = 0 ∨ b = 1 := by
    intro b
    rcases b with ⟨v, hv⟩
    cases v with
    | zero => exact Or.inl rfl
    | succ m =>
      cases m with
      | zero => exact Or.inr rfl
      | succ _ => omega
  have fin2_ne_eq : ∀ (d idx : Fin 2), idx ≠ d → idx = 1 - d := by decide
  have fin3_or : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i
    rcases i with ⟨v, hv⟩
    cases v with
    | zero => exact Or.inl rfl
    | succ m =>
      cases m with
      | zero => exact Or.inr (Or.inl rfl)
      | succ k =>
        cases k with
        | zero => exact Or.inr (Or.inr rfl)
        | succ _ => omega
  have binaryInputs : ∀ {a : ℕ}, a < C.gates.length → ∃ p q, (gateAt C a).inputs = [p, q] :=
    fun ha => List.length_eq_two.mp (hLeast.1.2.2 _ (gateAt_mem ha))
  have opndMem : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b ∈ (gateAt C a).inputs := by
    intro a ha b
    obtain ⟨p, q, hpq⟩ := binaryInputs ha
    rw [opnd_def, hpq]
    rcases fin2_or b with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem p List.mem_cons_self
  have opndBound : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b < 10 + a :=
    fun ha b => hLeast.1.2.1 _ ha _ (opndMem ha b)
  have inputsAsOpnd : ∀ {k z : ℕ}, k < C.gates.length → z ∈ (gateAt C k).inputs → ∃ b : Fin 2, z = opnd C k b := by
    intro k z hk hz
    obtain ⟨p, q, hpq⟩ := binaryInputs hk
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by rw [opnd_def, hpq]; rfl⟩
    · have e : z = q := List.mem_singleton.mp hq
      exact ⟨1, by rw [opnd_def, hpq]; exact e⟩
  have andValBoth : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ x : Fin 10 → Bool, gateVal 10 C a x = true ↔
        val C (List.ofFn x) (opnd C a 0) = true ∧ val C (List.ofFn x) (opnd C a 1) = true := by
    intro a ha hop x
    rw [gateVal_eq_val, val_and List.length_ofFn ha hop]
    constructor
    · intro h; exact ⟨(h _ (opndMem ha 0)).2, (h _ (opndMem ha 1)).2⟩
    · intro h i hi
      refine ⟨hLeast.1.2.1 a ha i hi, ?_⟩
      obtain ⟨b, rfl⟩ := inputsAsOpnd ha hi
      rcases fin2_or b with rfl | rfl
      · exact h.1
      · exact h.2
  have andValOperands : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ x : Fin 10 → Bool, gateVal 10 C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
    intro a ha hop x
    rw [andValBoth ha hop]
    constructor
    · intro h b; rcases fin2_or b with rfl | rfl; exact h.1; exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  have orValOperands : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.or →
      ∀ x : Fin 10 → Bool, gateVal 10 C a x = true ↔ ∃ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
    intro a ha hop x
    rw [gateVal_eq_val, val_or List.length_ofFn ha hop]
    constructor
    · rintro ⟨i, hi, _, hvi⟩
      obtain ⟨b, rfl⟩ := inputsAsOpnd ha hi
      exact ⟨b, hvi⟩
    · rintro ⟨b, hvb⟩
      exact ⟨opnd C a b, opndMem ha b, opndBound ha b, hvb⟩
  have orIn_or_union : ∀ {r : ℕ}, r < C.gates.length → (gateAt C r).op = GateOp.or →
      orIn 10 C (10 + r) = orIn 10 C (opnd C r 0) ∪ orIn 10 C (opnd C r 1) := by
    intro r hr hop
    apply Finset.ext
    intro v
    rw [Finset.mem_union]
    constructor
    · intro hv
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with h | ⟨w, hstep, hrest⟩
      · have := v.isLt; omega
      · obtain ⟨k, _, heq, _, hin, _⟩ := hstep
        have hkr : k = r := by omega
        subst hkr
        obtain ⟨b, rfl⟩ := inputsAsOpnd hr hin
        rcases fin2_or b with rfl | rfl
        · exact Or.inl (reach_mem_orIn v hrest)
        · exact Or.inr (reach_mem_orIn v hrest)
    · rintro (h0 | h1)
      · exact reach_mem_orIn v (Relation.ReflTransGen.head ⟨r, hr, rfl, hop, opndMem hr 0, opndBound hr 0⟩ (mem_orIn_reach v h0))
      · exact reach_mem_orIn v (Relation.ReflTransGen.head ⟨r, hr, rfl, hop, opndMem hr 1, opndBound hr 1⟩ (mem_orIn_reach v h1))
  have operandReachCone : ∀ {a h : ℕ}, a < C.gates.length → ∀ {b : Fin 2},
      OrReaches 10 C (opnd C a b) h → InCone 10 C h a := by
    intro a h ha b hr
    exact operand_cone ha (opndMem ha b) (opndBound ha b) (orReaches_reach h _ hr).1
  have operandOrAndJunk : ∀ {a h : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ {b : Fin 2}, OrReaches 10 C (opnd C a b) h → (gateAt C h).op = GateOp.and → h ∈ junk P C := by
    intro a h ha hop b hr hh
    have hlen := (orReaches_reach h _ hr).2
    have hnb : ¬ BelowF P C h := fun hb => hTop h hlen a ha hh hb hop (operandReachCone ha hr)
    have hdirty : ∃ x : Fin 10 → Bool, gateVal 10 C h x = true ∧ graphFun P ∅ x = false := by
      by_contra hne
      apply hnb
      intro x hx
      by_contra hf
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact (junk_mem C h).mpr ⟨hlen, hh, hdirty⟩
  have sideVal : ∀ {a : ℕ} {b : Fin 2} {x : Fin 10 → Bool} {t : Fin 10},
      t ∈ side (n := 10) C a b → x t = true → val C (List.ofFn x) (opnd C a b) = true := by
    intro a b x t ht hx
    rw [side_def] at ht
    exact reach_var_val x _ t (mem_orIn_reach t ht) hx
  have topAdj : ∀ {a : ℕ}, a ∈ tops P C → ∀ {u v : Fin 10},
      u ∈ side (n := 10) C a 0 → v ∈ side (n := 10) C a 1 → P.Adj u v := by
    intro a ha u v hu hv
    obtain ⟨hl, ho, hb⟩ := topData ha
    exact (graphFun_pair u v).mp
      (hb _ ((andValBoth hl ho _).mpr ⟨sideVal hu (pairInput_left u v), sideVal hv (pairInput_right u v)⟩))
  have topAdj_side : ∀ {t : ℕ}, t ∈ tops P C → ∀ {d : Fin 2} {u v : Fin 10},
      u ∈ side (n := 10) C t d → v ∈ side (n := 10) C t (1 - d) → P.Adj u v := by
    intro t ht d u v hu hv
    rcases fin2_or d with rfl | rfl
    · exact topAdj ht hu hv
    · exact (topAdj ht hv hu).symm
  have side_mem_starEdges : ∀ {t : ℕ}, t ∈ tops P C → ∀ {d : Fin 2} {u v : Fin 10},
      u ∈ side (n := 10) C t d → v ∈ side (n := 10) C t (1 - d) → s(u, v) ∈ starEdges P C := by
    intro t ht d u v hu hv
    rw [starEdges_def]
    refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
    rcases fin2_or d with rfl | rfl
    · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hv, hu⟩, Sym2.eq_swap⟩
  have emptySide_mem_centreless : ∀ {t : ℕ}, t ∈ tops P C → ∀ {d : Fin 2},
      side (n := 10) C t d = ∅ → t ∈ centreless P C := by
    intro t ht d h
    refine (centreless_mem C t).mpr ⟨ht, ?_⟩
    rcases fin2_or d with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have acceptedTop : ∀ {u v : Fin 10}, P.Adj u v → ∃ a ∈ tops P C, gateVal 10 C a (pairInput u v) = true := by
    intro u v hadj'
    have hout : ∀ x : Fin 10 → Bool, val C (List.ofFn x) C.output = graphFun P ∅ x :=
      fun x => congrFun hLeast.2.1 x
    have huv : val C (List.ofFn (pairInput u v)) C.output = true := by
      rw [hout]; exact (graphFun_pair u v).mpr hadj'
    rcases operand_trace u v C.output huv with ⟨t, _, hr⟩ | ⟨a, hl, ho, hr, hv⟩
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact P.irrefl ((graphFun_pair t t).mp h1)
    · have hand := (hLeast.1.1 _ (gateAt_mem hl)).resolve_right ho
      have hb : BelowF P C a := fun x hx => by
        rw [← hout x]
        exact orStep_up List.length_ofFn hr (gateVal_eq_val C a x ▸ hx)
      exact ⟨a, (tops_mem C a).mpr ⟨hl, hand, hb⟩, hv⟩
  have operandSupport : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ {b : Fin 2} {u v : Fin 10}, val C (List.ofFn (pairInput u v)) (opnd C a b) = true →
      (∃ t ∈ side (n := 10) C a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk P C, OrReaches 10 C (opnd C a b) j ∧ gateVal 10 C j (pairInput u v) = true := by
    intro a ha ho b u v h
    rcases operand_trace u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
    · exact Or.inl ⟨t, by rw [side_def]; exact reach_mem_orIn t hr, ht⟩
    · have hr' := reach_orReaches hr j rfl hj
      exact Or.inr ⟨j, operandOrAndJunk ha ho hr' ((hLeast.1.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
  have andRawEmpty : ∀ {j : ℕ}, (gateAt C j).op = GateOp.and → orIn 10 C (10 + j) = ∅ := by
    intro j hj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rcases (orIn_def C (10 + j) v).mp hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt; omega
    · rcases (orReaches_iff j k).mp hr with ⟨_, rfl | ⟨hof, _⟩⟩
      · rw [hj] at ho; exact GateOp.noConfusion ho
      · rw [hj] at hof; exact GateOp.noConfusion hof
  have residualTrace : ∀ {u v : Fin 10}, s(u, v) ∈ Ustar P C →
      ∃ a ∈ tops P C, gateVal 10 C a (pairInput u v) = true ∧ ∃ b : Fin 2, ∃ j ∈ junk P C,
        OrReaches 10 C (opnd C a b) j ∧ gateVal 10 C j (pairInput u v) = true := by
    intro u v he
    rw [Ustar_def] at he
    obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
    have adj' : P.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
    obtain ⟨a, ha, hv⟩ := acceptedTop adj'
    obtain ⟨hl, ho, _⟩ := topData ha
    have h := (andValOperands hl ho _).mp hv
    rcases operandSupport hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
    · rcases operandSupport hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
      · have hxy : x ≠ y := (topAdj ha hx hy).ne
        apply False.elim (miss ?_)
        rw [starEdges_def]
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
        rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
        · exact (hxy rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hxy rfl).elim
      · exact ⟨a, ha, hv, 1, j, hj, hr, hjv⟩
    · exact ⟨a, ha, hv, 0, j, hj, hr, hjv⟩
  have readData : ∀ {j k : ℕ}, k ∈ readers 10 C j → k < C.gates.length ∧ 10 + j ∈ (gateAt C k).inputs :=
    fun hk => (readers_mem C _ _).mp hk
  have readLt : ∀ {j k : ℕ}, k ∈ readers 10 C j → j < k := by
    intro j k hk
    have hlt := hLeast.1.2.1 k (readData hk).1 _ (readData hk).2
    omega
  have val_allTrue : ∀ w, w < 10 + C.gates.length → val C (List.ofFn (fun _ : Fin 10 => true)) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwn : w < 10
      · exact val_ofFn C (fun _ => true) ⟨w, hwn⟩
      · obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
        have hj : j < C.gates.length := by omega
        rcases hLeast.1.1 _ (gateAt_mem hj) with hand | hor
        · exact (val_and List.length_ofFn hj hand).mpr (fun i hi => by
            have hilt := hLeast.1.2.1 j hj i hi
            exact ⟨hilt, ih i hilt (by omega)⟩)
        · have hi0 := opndMem hj 0
          have hlt0 := opndBound hj 0
          exact (val_or List.length_ofFn hj hor).mpr ⟨opnd C j 0, hi0, hlt0, ih _ hlt0 (by omega)⟩
  have not_belowF_inCone_and : ∀ {k j : ℕ}, k < C.gates.length → BelowF P C k →
      j < C.gates.length → (gateAt C j).op = GateOp.and → ¬ InCone 10 C k j := by
    intro k j hk hbk hj hjo hkj
    have htk := val_allTrue (10 + k) (by omega)
    obtain ⟨w', hstep, _, hw'⟩ := or_trace List.length_ofFn (10 + k) htk
    rcases hw' with hlt | ⟨t, htlen, rfl, htop⟩
    · have hvar := reach_var_val (pairInput ⟨w', hlt⟩ ⟨w', hlt⟩) (10 + k) ⟨w', hlt⟩ hstep (pairInput_left _ _)
      exact P.irrefl ((graphFun_pair _ _).mp (hbk _ hvar))
    · have htand := (hLeast.1.1 _ (gateAt_mem htlen)).resolve_right htop
      have htb : BelowF P C t := fun x hx => hbk x (orStep_up List.length_ofFn hstep (gateVal_eq_val C t x ▸ hx))
      rcases orStep_cone hstep k t rfl rfl with rfl | htkc
      · exact hTop t htlen j hj htand htb hjo hkj
      · exact hTop t htlen j hj htand htb hjo (inCone_trans htkc hkj)
  have no_bothNonempty_R_below_lam : ∀ {m0 h : ℕ}, m0 ∈ orN P C \ lam P C → h ∈ lam P C →
      (orIn 10 C (opnd C m0 0)).Nonempty → (orIn 10 C (opnd C m0 1)).Nonempty →
      ¬ OrReaches 10 C (10 + h) m0 := by
    intro m0 h hm0 hh h0 h1 hreach
    obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
    have hm0N := (Finset.mem_sdiff.mp hm0).1
    have hm0len := ((orN_mem C m0).mp hm0N).1
    have htm0 : OrReaches 10 C (opnd C t d) m0 :=
      reach_orReaches ((orReaches_reach h _ hth).1.trans (orReaches_reach m0 _ hreach).1) m0 rfl hm0len
    exact (Finset.mem_sdiff.mp hm0).2 ((lam_mem C m0).mpr ⟨hm0N, h0, h1, t, ht, d, hcard, htm0⟩)
  have noncentreless_witness : ∀ {w j : ℕ}, j ∈ junk P C →
      OrReaches 10 C w j → (orIn 10 C w).Nonempty →
      ∃ m ∈ orN P C \ lam P C, OrReaches 10 C w m ∧ OrReaches 10 C (10 + m) j ∧ (orIn 10 C (10 + m)).Nonempty := by
    intro w j hj hreach hne
    obtain ⟨hpath, _⟩ := orReaches_reach j w hreach
    obtain ⟨hjlen, hjop, _⟩ := junkData hj
    have hjnb := junkNotBelow hj
    have hwalk : ∀ {u : ℕ}, Relation.ReflTransGen OrStep u (10 + j) → (orIn 10 C u).Nonempty →
        ∃ m ∈ orN P C \ lam P C, OrReaches 10 C u m ∧ OrReaches 10 C (10 + m) j ∧ (orIn 10 C (10 + m)).Nonempty := by
      intro u hu
      induction hu using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro hne'
        rw [andRawEmpty hjop] at hne'
        exact False.elim (Finset.not_nonempty_empty hne')
      | @head a c hstep hrest ih =>
        intro hnea
        obtain ⟨k, hklen, rfl, hkop, hcin, hclt⟩ := hstep
        by_cases hnec : (orIn 10 C c).Nonempty
        · obtain ⟨m, hmR, hcm, hmj, hmne⟩ := ih hnec
          have hkm : OrReaches 10 C (10 + k) m :=
            (orReaches_iff k m).mpr ⟨hklen, Or.inr ⟨hkop, c, hcin, hclt, hcm⟩⟩
          exact ⟨m, hmR, hkm, hmj, hmne⟩
        · have hce : orIn 10 C c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnec
          have hkj : OrReaches 10 C (10 + k) j :=
            reach_orReaches (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hcin, hclt⟩ hrest) j rfl hjlen
          have hknb : ¬ BelowF P C k := by
            intro hkb
            apply hjnb
            intro x hx
            exact hkb x (orStep_up List.length_ofFn (orReaches_reach j (10 + k) hkj).1 (gateVal_eq_val C j x ▸ hx))
          have hkN : k ∈ orN P C := (orN_mem C k).mpr ⟨hklen, hkop, hknb⟩
          have hkNotLam : k ∉ lam P C := by
            intro hkl
            obtain ⟨_, h0, h1, _⟩ := (lam_mem C k).mp hkl
            obtain ⟨b, hb⟩ := inputsAsOpnd hklen hcin
            have hnb : (orIn 10 C (opnd C k b)).Nonempty := by rcases fin2_or b with rfl | rfl; exact h0; exact h1
            rw [← hb, hce] at hnb
            exact Finset.not_nonempty_empty hnb
          exact ⟨k, Finset.mem_sdiff.mpr ⟨hkN, hkNotLam⟩, (orReaches_iff k k).mpr ⟨hklen, Or.inl rfl⟩, hkj, hnea⟩
    exact hwalk hpath hne
  have no_lam_two_Ustar_nbrs : ∀ (c : Fin 10) (T : Finset (Fin 10)),
      (∀ x ∈ T, P.Adj c x) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → s(c, x) ∈ Ustar P C ∨ s(c, y) ∈ Ustar P C) →
      ∀ h ∈ lam P C, ∀ x ∈ T, ∀ y ∈ T,
        x ∈ orIn 10 C (10 + h) → y ∈ orIn 10 C (10 + h) → x = y := by
    intro c T hAdj hU h hh x hx y hy hxh hyh
    by_contra hxy
    obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hxs : x ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth hxh
    have hys : y ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth hyh
    have hzs : z ∈ side (n := 10) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self z
    have hzx : P.Adj z x := (topAdj_side ht hxs hzs).symm
    have hzy : P.Adj z y := (topAdj_side ht hys hzs).symm
    have hzc : z = c := by
      by_contra hne
      have hc4 := hPno4 z c hne
      have h1 : x ∈ Finset.univ.filter (fun p => P.Adj z p ∧ P.Adj c p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx, hAdj x hx⟩
      have h2 : y ∈ Finset.univ.filter (fun p => P.Adj z p ∧ P.Adj c p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy, hAdj y hy⟩
      exact hxy (Finset.card_le_one.mp hc4 x h1 y h2)
    subst z
    have hstar : ∀ w : Fin 10, w ∈ side (n := 10) C t d → s(c, w) ∈ starEdges P C :=
      fun w hw => Sym2.eq_swap ▸ side_mem_starEdges ht hw hzs
    rcases hU x hx y hy hxy with hux | huy
    · rw [Ustar_def] at hux; exact (Finset.mem_sdiff.mp hux).2 (hstar x hxs)
    · rw [Ustar_def] at huy; exact (Finset.mem_sdiff.mp huy).2 (hstar y hys)
  have hCsize18 : 18 ≤ C.size := by
    let a := opnd C 0 0
    let b := opnd C 0 1
    have haLt : a < 10 := opndBound hCpos 0
    have hbLt : b < 10 := opndBound hCpos 1
    let va : Fin 10 := ⟨a, haLt⟩
    let vb : Fin 10 := ⟨b, hbLt⟩
    have hOutNe10 : C.output ≠ 10 := by
      intro h10
      have hDisjEdgeB : ∀ u v : Fin 10,
          pEdges.any (fun e => e.1 != u.val && e.1 != v.val && e.2 != u.val && e.2 != v.val) = true := by decide +kernel
      obtain ⟨e, he, hbe⟩ := List.any_eq_true.mp (hDisjEdgeB va vb)
      obtain ⟨h1, h2, hne⟩ := hpLtAll e he
      have hbe1 := Bool.and_eq_true_iff.mp hbe
      have hbe2 := Bool.and_eq_true_iff.mp hbe1.1
      have hbe3 := Bool.and_eq_true_iff.mp hbe2.1
      let p : Fin 10 := ⟨e.1, h1⟩
      let q : Fin 10 := ⟨e.2, h2⟩
      have hpq : P.Adj p q := ⟨fun h => hne (congrArg Fin.val h), Or.inl he⟩
      have hpu : p ≠ va := fun h => (bne_iff_ne.mp hbe3.1) (congrArg Fin.val h)
      have hpv : p ≠ vb := fun h => (bne_iff_ne.mp hbe3.2) (congrArg Fin.val h)
      have hqu : q ≠ va := fun h => (bne_iff_ne.mp hbe2.2) (congrArg Fin.val h)
      have hqv : q ≠ vb := fun h => (bne_iff_ne.mp hbe1.2) (congrArg Fin.val h)
      have hT : val C (List.ofFn (pairInput p q)) C.output = true := by
        rw [show val C (List.ofFn (pairInput p q)) C.output = graphFun P ∅ (pairInput p q) from congrFun hLeast.2.1 _]
        exact (graphFun_pair p q).mpr hpq
      rw [h10] at hT
      have hfa : val C (List.ofFn (pairInput p q)) a = false := by
        rw [show a = va.val from rfl, val_ofFn, pairInput_def]
        exact decide_eq_false (fun h => h.elim hpu.symm hqu.symm)
      have hfb : val C (List.ofFn (pairInput p q)) b = false := by
        rw [show b = vb.val from rfl, val_ofFn, pairInput_def]
        exact decide_eq_false (fun h => h.elim hpv.symm hqv.symm)
      rcases hLeast.1.1 _ (gateAt_mem hCpos) with hand | hor
      · have h0 := ((andValBoth hCpos hand (pairInput p q)).mp hT).1
        rw [hfa] at h0; exact Bool.noConfusion h0
      · rcases (orValOperands hCpos hor (pairInput p q)).mp hT with ⟨idx, hidx⟩
        rcases fin2_or idx with rfl | rfl
        · change val C (List.ofFn (pairInput p q)) a = true at hidx; rw [hfa] at hidx; exact Bool.noConfusion hidx
        · change val C (List.ofFn (pairInput p q)) b = true at hidx; rw [hfb] at hidx; exact Bool.noConfusion hidx
    obtain ⟨r0, hr0⟩ := leastReadAny hCpos hOutNe10
    have hr0len := (readData hr0).1
    have hr0in := (readData hr0).2
    have hr0pos : 0 < r0 := readLt hr0
    rcases hLeast.1.1 _ (gateAt_mem hCpos) with hand | hor
    · exact (hRestrictV va).2 hCpos hand (opndMem hCpos 0) ⟨r0, hr0pos, hr0len, hr0in⟩
    · have hne : va ≠ vb := by
        intro heq
        have hab : a = b := congrArg Fin.val heq
        apply replace_gate_by_wire 0 a hCpos (by omega)
        intro x
        cases hxa : val C (List.ofFn x) a
        · cases hg0 : gateVal 10 C 0 x
          · rfl
          · rcases (orValOperands hCpos hor x).mp hg0 with ⟨idx, hidx⟩
            rcases fin2_or idx with rfl | rfl
            · exact Bool.noConfusion (hxa.symm.trans hidx)
            · change val C (List.ofFn x) b = true at hidx; rw [← hab, hxa] at hidx; exact Bool.noConfusion hidx
        · exact ((orValOperands hCpos hor x).mpr ⟨0, hxa⟩).symm
      have hWitUB : ∀ u v : Fin 10, u ≠ v →
          (List.finRange 10).any (fun w =>
            (pAdjMask.getD u.val 0).testBit w.val &&
            (w.val != v.val) &&
            !((pAdjMask.getD v.val 0).testBit w.val)) = true := by
        decide +kernel
      obtain ⟨u, _, huB⟩ := List.any_eq_true.mp (hWitUB va vb hne)
      have huB1 := Bool.and_eq_true_iff.mp huB
      have huB2 := Bool.and_eq_true_iff.mp huB1.1
      have hau : P.Adj va u := (hpMaskIff va u).mpr huB2.1
      have hub : u ≠ vb := fun h => (bne_iff_ne.mp huB2.2) (congrArg Fin.val h)
      have hnvF : (pAdjMask.getD vb.val 0).testBit u.val = false := by
        rw [← Bool.not_not ((pAdjMask.getD vb.val 0).testBit u.val), huB1.2]; rfl
      have hnvu : ¬ P.Adj vb u := fun hadj =>
        Bool.noConfusion (hnvF.symm.trans (hpMaskAdj vb u hadj))
      let x0 : Fin 10 → Bool := pairInput vb u
      let x1 : Fin 10 → Bool := fun w => pairInput vb u w || decide (w = va)
      have hx0F : graphFun P ∅ x0 = false :=
        Bool.eq_false_iff.mpr (fun h => hnvu ((graphFun_pair vb u).mp h))
      have hx1T : graphFun P ∅ x1 = true :=
        (hP_hasEdge x1).mpr ⟨va, u, hau, by dsimp only [x1]; rw [decide_eq_true rfl, Bool.or_true],
          by dsimp only [x1]; rw [pairInput_right vb u, Bool.true_or]⟩
      have hOutNeA : C.output ≠ a := by
        intro heq
        have h1 : val C (List.ofFn (pairInput va va)) C.output = graphFun P ∅ (pairInput va va) :=
          congrFun hLeast.2.1 (pairInput va va)
        rw [heq, show a = va.val from rfl, val_ofFn, pairInput_left] at h1
        exact P.irrefl ((graphFun_pair va va).mp h1.symm)
      have hHasLaterA : ∃ k, 0 < k ∧ k < C.gates.length ∧ a ∈ (gateAt C k).inputs := by
        by_contra hno
        have hEqW : ∀ w : ℕ, w < 10 + C.gates.length → w ≠ a →
            val C (List.ofFn x0) w = val C (List.ofFn x1) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hwlt hwa
            by_cases hwn : w < 10
            · rw [show w = (⟨w, hwn⟩ : Fin 10).val from rfl, val_ofFn, val_ofFn]
              dsimp only [x1]
              have hneW : (⟨w, hwn⟩ : Fin 10) ≠ va := fun h => hwa (congrArg Fin.val h)
              rw [decide_eq_false hneW, Bool.or_false]
            · by_cases hw10 : w = 10
              · subst w
                have ht0 : val C (List.ofFn x0) 10 = true :=
                  (orValOperands hCpos hor x0).mpr ⟨1, by rw [show opnd C 0 1 = vb.val from rfl, val_ofFn]; exact pairInput_left vb u⟩
                have ht1 : val C (List.ofFn x1) 10 = true :=
                  (orValOperands hCpos hor x1).mpr ⟨1, by rw [show opnd C 0 1 = vb.val from rfl, val_ofFn]; dsimp only [x1]; rw [pairInput_left vb u, Bool.true_or]⟩
                rw [ht0, ht1]
              · let k := w - 10
                have hweq : w = 10 + k := by omega
                have hkpos : 0 < k := by omega
                have hklt : k < C.gates.length := by omega
                rw [hweq, val_gate List.length_ofFn hklt, val_gate List.length_ofFn hklt]
                congr 1
                apply List.map_congr_left
                intro i hi
                have hilt : i < 10 + k := hLeast.1.2.1 k hklt i hi
                have hia : i ≠ a := fun heq => hno ⟨k, hkpos, hklt, heq ▸ hi⟩
                rw [if_pos hilt, if_pos hilt]
                exact ih i (by omega) (by omega) hia
        have heqOut := hEqW C.output hOutLt hOutNeA
        have h0 : val C (List.ofFn x0) C.output = false := (congrFun hLeast.2.1 x0).trans hx0F
        have h1 : val C (List.ofFn x1) C.output = true := (congrFun hLeast.2.1 x1).trans hx1T
        rw [h0, h1] at heqOut
        exact Bool.noConfusion heqOut
      obtain ⟨k, hkpos, hklt, hka⟩ := hHasLaterA
      have hCountP_ge2 : ∀ (gs : List Gate) (p : Gate → Bool) (k' : ℕ),
          0 < k' → k' < gs.length → p (gs.getD 0 ⟨GateOp.or, []⟩) = true →
          p (gs.getD k' ⟨GateOp.or, []⟩) = true → 2 ≤ gs.countP p := by
        intro gs p k' hk'pos hk'lt hp0 hpk
        cases gs with
        | nil => simp only [List.length_nil] at hk'lt; omega
        | cons g0 rest =>
          rw [List.countP_cons]
          have h0eq : (g0 :: rest).getD 0 ⟨GateOp.or, []⟩ = g0 := rfl
          rw [h0eq] at hp0
          rw [hp0, if_pos rfl]
          have hk1 : k' - 1 < rest.length := by simp only [List.length_cons] at hk'lt; omega
          have hmem : rest.getD (k' - 1) ⟨GateOp.or, []⟩ ∈ rest := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
            exact List.getElem_mem hk1
          have hpk' : p (rest.getD (k' - 1) ⟨GateOp.or, []⟩) = true := by
            have heq : (g0 :: rest).getD k' ⟨GateOp.or, []⟩ = rest.getD (k' - 1) ⟨GateOp.or, []⟩ := by
              cases k' with
              | zero => omega
              | succ m => rfl
            rw [← heq]; exact hpk
          have hpos : 0 < rest.countP p := List.countP_pos_iff.mpr ⟨_, hmem, hpk'⟩
          omega
      have hc2 : 2 ≤ C.gates.countP (fun g => g.inputs.contains va.val) :=
        hCountP_ge2 C.gates (fun g => g.inputs.contains va.val) k hkpos hklt
          (List.contains_iff_mem.mpr (opndMem hCpos 0)) (List.contains_iff_mem.mpr hka)
      have hfb := hFanBound va
      omega
  have hUstarNe : (Ustar P C).Nonempty := by
    by_contra hne
    have hE : Ustar P C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hlt := hBudgetLtCov ∅ (fun e he => by rw [hE] at he; exact False.elim (Finset.notMem_empty e he))
    rw [hE, Finset.card_empty, Finset.card_empty] at hlt
    omega
  have hJunkGe2 : 2 ≤ (junk P C).card := by
    have hJunkPos : 0 < (junk P C).card := by
      obtain ⟨e, he⟩ := hUstarNe
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨_, _, _, _, j, hj, _, _⟩ := residualTrace he
        exact Finset.card_pos.mpr ⟨j, hj⟩
    by_contra hlt2
    have hJ1 : (junk P C).card = 1 := by omega
    obtain ⟨j, hjSet⟩ := Finset.card_eq_one.mp hJ1
    have hjMem : j ∈ junk P C := by rw [hjSet]; exact Finset.mem_singleton_self j
    have hjUniq : ∀ j' ∈ junk P C, j' = j := fun j' hj' => Finset.mem_singleton.mp (hjSet ▸ hj')
    obtain ⟨hjlen, hjop, _⟩ := junkData hjMem
    have hjnb : ¬ BelowF P C j := junkNotBelow hjMem
    let R : Finset ℕ := orN P C \ lam P C
    have hRcard_eq : R.card = (orN P C \ lam P C).card := rfl
    let NoAnd : ℕ → Prop := fun w => ∀ k, OrReaches 10 C w k → (gateAt C k).op = GateOp.or
    have noAnd_val : ∀ {w : ℕ}, w < 10 + C.gates.length → NoAnd w →
        ∀ x : Fin 10 → Bool, val C (List.ofFn x) w = true ↔ ∃ v ∈ orIn 10 C w, x v = true := by
      intro w hw hna x
      constructor
      · intro hv
        obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn w hv
        rcases hcase with hlt | ⟨h, hh, rfl, hneOr⟩
        · refine ⟨⟨w', hlt⟩, reach_mem_orIn ⟨w', hlt⟩ hpath, ?_⟩
          rw [← val_ofFn C x ⟨w', hlt⟩]; exact hvw'
        · exact False.elim (hneOr (hna h (reach_orReaches hpath h rfl hh)))
      · rintro ⟨v, hv, hxv⟩
        exact reach_var_val x w v (mem_orIn_reach v hv) hxv
    have noAnd_nonempty : ∀ {w : ℕ}, w < 10 + C.gates.length → NoAnd w → (orIn 10 C w).Nonempty := by
      intro w hw hna
      obtain ⟨v, hv, _⟩ := (noAnd_val hw hna (fun _ => true)).mp (val_allTrue w hw)
      exact ⟨v, hv⟩
    have noAnd_reach_orN : ∀ {w k : ℕ}, NoAnd w → OrReaches 10 C w k → k ∈ orN P C ∧ NoAnd (10 + k) := by
      intro w k hna hr
      have hklen := (orReaches_reach k w hr).2
      have hkop := hna k hr
      have hnak : NoAnd (10 + k) := fun k' hk' => hna k' (orReaches_trans hr hk')
      obtain ⟨v, hv⟩ := noAnd_nonempty (by omega : 10 + k < 10 + C.gates.length) hnak
      have hknb : ¬ BelowF P C k := by
        intro hkb
        have h1 : gateVal 10 C k (pairInput v v) = true :=
          (noAnd_val (by omega) hnak (pairInput v v)).mpr ⟨v, hv, pairInput_left v v⟩
        exact P.irrefl ((graphFun_pair v v).mp (hkb _ h1))
      exact ⟨(orN_mem C k).mpr ⟨hklen, hkop, hknb⟩, hnak⟩
    have noAnd_opnd_or : ∀ {k : ℕ}, k < C.gates.length → NoAnd (10 + k) → ∀ b : Fin 2, NoAnd (opnd C k b) := by
      intro k hk hnak b r hr
      have hkop : (gateAt C k).op = GateOp.or := hnak k ((orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩)
      exact hnak r ((orReaches_iff k r).mpr ⟨hk, Or.inr ⟨hkop, opnd C k b, opndMem hk b, opndBound hk b, hr⟩⟩)
    have noAnd_card_ge2 : ∀ {k : ℕ}, k < C.gates.length → NoAnd (10 + k) → 2 ≤ (orIn 10 C (10 + k)).card := by
      intro k hk hnak
      obtain ⟨v0, hv0⟩ := noAnd_nonempty (by omega : 10 + k < 10 + C.gates.length) hnak
      by_contra hlt
      have hcard1 : (orIn 10 C (10 + k)).card = 1 := by
        have hpos : 0 < (orIn 10 C (10 + k)).card := Finset.card_pos.mpr ⟨v0, hv0⟩
        omega
      obtain ⟨u0, hu0⟩ := Finset.card_eq_one.mp hcard1
      apply replace_gate_by_wire k u0.val hk (by have := u0.isLt; omega)
      intro x
      cases hxu : val C (List.ofFn x) u0.val
      · cases hgk : gateVal 10 C k x
        · rfl
        · obtain ⟨v, hv, hxv⟩ := (noAnd_val (by omega) hnak x).mp hgk
          rw [hu0] at hv
          rw [Finset.mem_singleton.mp hv, ← val_ofFn C x u0] at hxv
          exact Bool.noConfusion (hxu.symm.trans hxv)
      · exact ((noAnd_val (by omega) hnak x).mpr ⟨u0, by rw [hu0]; exact Finset.mem_singleton_self u0, by rw [← val_ofFn C x u0]; exact hxu⟩).symm
    have noAnd_opnd_and : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
        ∀ {b : Fin 2}, ¬ OrReaches 10 C (opnd C a b) j → NoAnd (opnd C a b) := by
      intro a ha hop b hnr k hr
      have hklen := (orReaches_reach k _ hr).2
      rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
      · have hkj := hjUniq k (operandOrAndJunk ha hop hr hkand)
        subst k; exact False.elim (hnr hr)
      · exact hkor
    let Rw : ℕ → Finset ℕ := fun w => R.filter (fun r => OrReaches 10 C w r)
    let Rabove : Finset ℕ := R.filter (fun r => OrReaches 10 C (10 + r) j)
    have noAnd_disj_Rabove : ∀ {w : ℕ}, NoAnd w → Disjoint (Rw w) Rabove := by
      intro w hna
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      have hwr := (Finset.mem_filter.mp hr1).2
      have hrj := (Finset.mem_filter.mp hr2).2
      have hop := hna j (orReaches_trans hwr hrj)
      rw [hjop] at hop; exact GateOp.noConfusion hop
    have noAnd_disj_Rw : ∀ {w1 w2 : ℕ}, NoAnd w1 → NoAnd w2 →
        (orIn 10 C w1 ∩ orIn 10 C w2).card ≤ 1 → Disjoint (Rw w1) (Rw w2) := by
      intro w1 w2 hna1 _ hcap
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      have h1 := (Finset.mem_filter.mp hr1).2
      have h2 := (Finset.mem_filter.mp hr2).2
      have hrlen := (orReaches_reach r w1 h1).2
      have hnar := (noAnd_reach_orN hna1 h1).2
      have hge2 := noAnd_card_ge2 hrlen hnar
      have hsub : orIn 10 C (10 + r) ⊆ orIn 10 C w1 ∩ orIn 10 C w2 :=
        Finset.subset_inter (orIn_mono h1) (orIn_mono h2)
      have hle := Finset.card_le_card hsub
      omega
    have pure_or_R_count : ∀ (Roots : Finset ℕ),
        (∀ w ∈ Roots, w < 10 + C.gates.length ∧ NoAnd w) →
        ∃ L : Finset ℕ,
          L.card ≤ Roots.card + (R.filter (fun r => ∃ w ∈ Roots, OrReaches 10 C w r)).card ∧
          (∀ w ∈ L, w < 10 ∨ ∃ h ∈ lam P C, w = 10 + h) ∧
          (∀ w ∈ Roots, orIn 10 C w ⊆ L.biUnion (orIn 10 C)) := by
      have hInd : ∀ (k : ℕ) (Roots : Finset ℕ),
          (R.filter (fun r => ∃ w ∈ Roots, OrReaches 10 C w r)).card = k →
          (∀ w ∈ Roots, w < 10 + C.gates.length ∧ NoAnd w) →
          ∃ L : Finset ℕ,
            L.card ≤ Roots.card + k ∧
            (∀ w ∈ L, w < 10 ∨ ∃ h ∈ lam P C, w = 10 + h) ∧
            (∀ w ∈ Roots, orIn 10 C w ⊆ L.biUnion (orIn 10 C)) := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro Roots hcard hRoots
          let X := R.filter (fun r => ∃ w ∈ Roots, OrReaches 10 C w r)
          by_cases hXne : X.Nonempty
          · let rMax := X.max' hXne
            have hrMaxMem : rMax ∈ X := Finset.max'_mem X hXne
            have hrMaxR : rMax ∈ R := (Finset.mem_filter.mp hrMaxMem).1
            obtain ⟨w0, hw0R, hw0r⟩ := (Finset.mem_filter.mp hrMaxMem).2
            have hrMaxLen : rMax < C.gates.length := ((orN_mem C rMax).mp (Finset.mem_sdiff.mp hrMaxR).1).1
            have hrMaxOp : (gateAt C rMax).op = GateOp.or := ((orN_mem C rMax).mp (Finset.mem_sdiff.mp hrMaxR).1).2.1
            have hrMaxNoAnd : NoAnd (10 + rMax) := (noAnd_reach_orN (hRoots w0 hw0R).2 hw0r).2
            have hOnlySelf : ∀ w ∈ Roots, OrReaches 10 C w rMax → w = 10 + rMax := by
              intro w hwR hwr
              by_contra hneW
              have hle := orReaches_le hwr
              have hltW : 10 + rMax < w := by omega
              let g0 := w - 10
              have hwEq : w = 10 + g0 := by omega
              have hg0len : g0 < C.gates.length := by have := (hRoots w hwR).1; omega
              have hg0Self : OrReaches 10 C w g0 := by rw [hwEq]; exact (orReaches_iff g0 g0).mpr ⟨hg0len, Or.inl rfl⟩
              have hg0N : g0 ∈ orN P C := (noAnd_reach_orN (hRoots w hwR).2 hg0Self).1
              have hg0NotR : g0 ∉ R := by
                intro hg0R
                have hg0X : g0 ∈ X := Finset.mem_filter.mpr ⟨hg0R, w, hwR, hg0Self⟩
                have hleM : g0 ≤ rMax := Finset.le_max' X g0 hg0X
                omega
              have hg0Lam : g0 ∈ lam P C := by
                by_contra hnl
                exact hg0NotR (Finset.mem_sdiff.mpr ⟨hg0N, hnl⟩)
              have hne0 := noAnd_nonempty (by have := opndBound hrMaxLen 0; omega) (noAnd_opnd_or hrMaxLen hrMaxNoAnd 0)
              have hne1 := noAnd_nonempty (by have := opndBound hrMaxLen 1; omega) (noAnd_opnd_or hrMaxLen hrMaxNoAnd 1)
              rw [hwEq] at hwr
              exact no_bothNonempty_R_below_lam hrMaxR hg0Lam hne0 hne1 hwr
            have hSelfMem : 10 + rMax ∈ Roots := hOnlySelf w0 hw0R hw0r ▸ hw0R
            let Roots' : Finset ℕ := (Roots.erase (10 + rMax)) ∪ {opnd C rMax 0, opnd C rMax 1}
            have hRoots'Ok : ∀ w ∈ Roots', w < 10 + C.gates.length ∧ NoAnd w := by
              intro w hw
              rcases Finset.mem_union.mp hw with h1 | h2
              · exact hRoots w (Finset.mem_of_mem_erase h1)
              · rcases Finset.mem_insert.mp h2 with rfl | h2'
                · exact ⟨by have := opndBound hrMaxLen 0; omega, noAnd_opnd_or hrMaxLen hrMaxNoAnd 0⟩
                · rw [Finset.mem_singleton.mp h2']
                  exact ⟨by have := opndBound hrMaxLen 1; omega, noAnd_opnd_or hrMaxLen hrMaxNoAnd 1⟩
            let X' := R.filter (fun r => ∃ w ∈ Roots', OrReaches 10 C w r)
            have hX'Sub : X' ⊆ X.erase rMax := by
              intro r hr
              have hrR := (Finset.mem_filter.mp hr).1
              obtain ⟨w, hw', hwr⟩ := (Finset.mem_filter.mp hr).2
              have hrNe : r ≠ rMax := by
                intro heq; subst r
                rcases Finset.mem_union.mp hw' with h1 | h2
                · exact (Finset.mem_erase.mp h1).1 (hOnlySelf w (Finset.mem_of_mem_erase h1) hwr)
                · have hwLt : w < 10 + rMax := by
                    rcases Finset.mem_insert.mp h2 with rfl | h2'
                    · exact opndBound hrMaxLen 0
                    · rw [Finset.mem_singleton.mp h2']; exact opndBound hrMaxLen 1
                  have hge := orReaches_le hwr
                  omega
              refine Finset.mem_erase.mpr ⟨hrNe, Finset.mem_filter.mpr ⟨hrR, ?_⟩⟩
              rcases Finset.mem_union.mp hw' with h1 | h2
              · exact ⟨w, Finset.mem_of_mem_erase h1, hwr⟩
              · refine ⟨10 + rMax, hSelfMem, (orReaches_iff rMax r).mpr ⟨hrMaxLen, Or.inr ⟨hrMaxOp, w, ?_, ?_, hwr⟩⟩⟩
                · rcases Finset.mem_insert.mp h2 with rfl | h2'
                  · exact opndMem hrMaxLen 0
                  · rw [Finset.mem_singleton.mp h2']; exact opndMem hrMaxLen 1
                · rcases Finset.mem_insert.mp h2 with rfl | h2'
                  · exact opndBound hrMaxLen 0
                  · rw [Finset.mem_singleton.mp h2']; exact opndBound hrMaxLen 1
            have hX'Lt : X'.card < k := by
              have h1 := Finset.card_le_card hX'Sub
              have h2 := Finset.card_erase_of_mem hrMaxMem
              have h3 : 0 < X.card := Finset.card_pos.mpr hXne
              have hXk : X.card = k := hcard
              omega
            obtain ⟨L, hLcard, hLok, hLcov⟩ := ih X'.card hX'Lt Roots' rfl hRoots'Ok
            have hR'Card : Roots'.card ≤ Roots.card + 1 := by
              have h1 : Roots'.card ≤ (Roots.erase (10 + rMax)).card + ({opnd C rMax 0, opnd C rMax 1} : Finset ℕ).card :=
                Finset.card_union_le _ _
              have h2 : ({opnd C rMax 0, opnd C rMax 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
              have h3 := Finset.card_erase_of_mem hSelfMem
              have h4 : 0 < Roots.card := Finset.card_pos.mpr ⟨10 + rMax, hSelfMem⟩
              omega
            refine ⟨L, by omega, hLok, fun w hw => ?_⟩
            by_cases hweq : w = 10 + rMax
            · subst w
              rw [orIn_or_union hrMaxLen hrMaxOp]
              refine Finset.union_subset
                (hLcov (opnd C rMax 0) (Finset.mem_union_right _ (Finset.mem_insert_self _ _)))
                (hLcov (opnd C rMax 1) (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
            · exact hLcov w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hweq, hw⟩))
          · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXne
            refine ⟨Roots, by omega, fun w hw => ?_, fun w hw v hv => Finset.mem_biUnion.mpr ⟨w, hw, hv⟩⟩
            by_cases hw10 : w < 10
            · exact Or.inl hw10
            · let h := w - 10
              have hwEq : w = 10 + h := by omega
              have hlen : h < C.gates.length := by have := (hRoots w hw).1; omega
              have hSelf : OrReaches 10 C w h := by rw [hwEq]; exact (orReaches_iff h h).mpr ⟨hlen, Or.inl rfl⟩
              have hN : h ∈ orN P C := (noAnd_reach_orN (hRoots w hw).2 hSelf).1
              have hLam : h ∈ lam P C := by
                by_contra hnl
                have hmX : h ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hN, hnl⟩, w, hw, hSelf⟩
                rw [hXe] at hmX; exact Finset.notMem_empty h hmX
              exact Or.inr ⟨h, hLam, hwEq⟩
      intro Roots hRoots
      exact hInd _ Roots rfl hRoots
    have pure_or_no_pair_bound : ∀ (Roots : Finset ℕ) (T : Finset (Fin 10)),
        (∀ w ∈ Roots, w < 10 + C.gates.length ∧ NoAnd w) →
        T ⊆ Roots.biUnion (orIn 10 C) →
        (∀ h ∈ lam P C, ∀ x ∈ T, ∀ y ∈ T, x ∈ orIn 10 C (10 + h) → y ∈ orIn 10 C (10 + h) → x = y) →
        T.card ≤ Roots.card + (R.filter (fun r => ∃ w ∈ Roots, OrReaches 10 C w r)).card := by
      intro Roots T hRoots hTsub hNoPair
      obtain ⟨L, hLcard, hLok, hLcov⟩ := pure_or_R_count Roots hRoots
      have hTL : T ⊆ L.biUnion (fun u => T ∩ orIn 10 C u) := by
        intro v hv
        obtain ⟨w, hwR, hvw⟩ := Finset.mem_biUnion.mp (hTsub hv)
        obtain ⟨u, huL, hvu⟩ := Finset.mem_biUnion.mp (hLcov w hwR hvw)
        exact Finset.mem_biUnion.mpr ⟨u, huL, Finset.mem_inter.mpr ⟨hv, hvu⟩⟩
      have hEachLe1 : ∀ u ∈ L, (T ∩ orIn 10 C u).card ≤ 1 := by
        intro u hu
        apply Finset.card_le_one.mpr
        intro x hx y hy
        obtain ⟨hxT, hxu⟩ := Finset.mem_inter.mp hx
        obtain ⟨hyT, hyu⟩ := Finset.mem_inter.mp hy
        rcases hLok u hu with hlt | ⟨h, hh, rfl⟩
        · rw [show u = (⟨u, hlt⟩ : Fin 10).val from rfl, orIn_leaf] at hxu hyu
          exact (Finset.mem_singleton.mp hxu).trans (Finset.mem_singleton.mp hyu).symm
        · exact hNoPair h hh x hxT y hyT hxu hyu
      have h1 := Finset.card_le_card hTL
      have h2 := Finset.card_biUnion_le (s := L) (t := fun u => T ∩ orIn 10 C u)
      have h3 : L.sum (fun u => (T ∩ orIn 10 C u).card) ≤ L.sum (fun _ => 1) := Finset.sum_le_sum hEachLe1
      rw [Finset.sum_const, smul_eq_mul, mul_one] at h3
      omega
    have single_wire_no_pair : ∀ (w : ℕ) (T : Finset (Fin 10)),
        w < 10 + C.gates.length → NoAnd w → T ⊆ orIn 10 C w →
        (∀ h ∈ lam P C, ∀ x ∈ T, ∀ y ∈ T, x ∈ orIn 10 C (10 + h) → y ∈ orIn 10 C (10 + h) → x = y) →
        T.card ≤ 1 + (Rw w).card := by
      intro w T hw hna hTsub hNoPair
      have h1 := pure_or_no_pair_bound {w} T
        (fun u hu => by rw [Finset.mem_singleton.mp hu]; exact ⟨hw, hna⟩)
        (by intro v hv; exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_singleton_self w, hTsub hv⟩)
        hNoPair
      have hEqF : R.filter (fun r => ∃ u ∈ ({w} : Finset ℕ), OrReaches 10 C u r) = Rw w := by
        apply Finset.ext; intro r; simp only [Rw, Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
      rw [Finset.card_singleton, hEqF] at h1
      exact h1
    let wA := opnd C j 0
    let wB := opnd C j 1
    have hwALt : wA < 10 + C.gates.length := by have := opndBound hjlen 0; omega
    have hwBLt : wB < 10 + C.gates.length := by have := opndBound hjlen 1; omega
    have hnaA : NoAnd wA := noAnd_opnd_and hjlen hjop (fun hr => by have := orReaches_le hr; have := opndBound hjlen 0; omega)
    have hnaB : NoAnd wB := noAnd_opnd_and hjlen hjop (fun hr => by have := orReaches_le hr; have := opndBound hjlen 1; omega)
    let A : Finset (Fin 10) := orIn 10 C wA
    let B : Finset (Fin 10) := orIn 10 C wB
    have hjVal : ∀ x : Fin 10 → Bool, gateVal 10 C j x = true ↔ (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) := by
      intro x
      rw [andValBoth hjlen hjop, noAnd_val hwALt hnaA, noAnd_val hwBLt hnaB]
    have hAne : A.Nonempty := noAnd_nonempty hwALt hnaA
    have hBne : B.Nonempty := noAnd_nonempty hwBLt hnaB
    have hNotAsubB : ¬ A ⊆ B := by
      intro hsub
      apply replace_gate_by_wire j wA hjlen (opndBound hjlen 0)
      intro x
      cases h1 : val C (List.ofFn x) wA
      · cases h2 : gateVal 10 C j x
        · rfl
        · have h3 := ((andValBoth hjlen hjop x).mp h2).1
          exact Bool.noConfusion (h1.symm.trans h3)
      · obtain ⟨a, haA, hxa⟩ := (noAnd_val hwALt hnaA x).mp h1
        exact ((hjVal x).mpr ⟨⟨a, haA, hxa⟩, ⟨a, hsub haA, hxa⟩⟩).symm
    have hNotBsubA : ¬ B ⊆ A := by
      intro hsub
      apply replace_gate_by_wire j wB hjlen (opndBound hjlen 1)
      intro x
      cases h1 : val C (List.ofFn x) wB
      · cases h2 : gateVal 10 C j x
        · rfl
        · have h3 := ((andValBoth hjlen hjop x).mp h2).2
          exact Bool.noConfusion (h1.symm.trans h3)
      · obtain ⟨b, hbB, hxb⟩ := (noAnd_val hwBLt hnaB x).mp h1
        exact ((hjVal x).mpr ⟨⟨b, hsub hbB, hxb⟩, ⟨b, hbB, hxb⟩⟩).symm
    let validZ : Finset (Fin 10) := Finset.univ.filter (fun z =>
      ∀ x : Fin 10 → Bool, x z = true → gateVal 10 C j x = true → graphFun P ∅ x = true)
    have hValidNotInter : ∀ z ∈ validZ, ¬ (z ∈ A ∧ z ∈ B) := by
      intro z hz hAB
      have hfire := (Finset.mem_filter.mp hz).2 (pairInput z z) (pairInput_left z z)
        ((hjVal _).mpr ⟨⟨z, hAB.1, pairInput_left z z⟩, ⟨z, hAB.2, pairInput_left z z⟩⟩)
      exact P.irrefl ((graphFun_pair z z).mp hfire)
    have hValidA_adjB : ∀ z ∈ validZ, z ∈ A → ∀ b ∈ B, P.Adj z b := by
      intro z hz hzA b hbB
      exact (graphFun_pair z b).mp ((Finset.mem_filter.mp hz).2 (pairInput z b) (pairInput_left z b)
        ((hjVal _).mpr ⟨⟨z, hzA, pairInput_left z b⟩, ⟨b, hbB, pairInput_right z b⟩⟩))
    have hValidB_adjA : ∀ z ∈ validZ, z ∈ B → ∀ a ∈ A, P.Adj z a := by
      intro z hz hzB a haA
      exact (graphFun_pair z a).mp ((Finset.mem_filter.mp hz).2 (pairInput z a) (pairInput_left z a)
        ((hjVal _).mpr ⟨⟨a, haA, pairInput_right z a⟩, ⟨z, hzB, pairInput_left z a⟩⟩))
    have hValid_adjAB : ∀ z ∈ validZ, ∀ w ∈ A ∩ B, P.Adj z w := by
      intro z hz w hw
      obtain ⟨hwA, hwB⟩ := Finset.mem_inter.mp hw
      exact (graphFun_pair z w).mp ((Finset.mem_filter.mp hz).2 (pairInput z w) (pairInput_left z w)
        ((hjVal _).mpr ⟨⟨w, hwA, pairInput_right z w⟩, ⟨w, hwB, pairInput_right z w⟩⟩))
    let ZU : Finset ℕ := (centreless P C).filter (fun t => ∃ d : Fin 2, OrReaches 10 C (opnd C t d) j)
    let covZ : Finset (Fin 10) := ZU.biUnion (fun t => side (n := 10) C t 0 ∪ side (n := 10) C t 1)
    have hZ_other_side : ∀ t ∈ ZU, ∃ d : Fin 2,
        OrReaches 10 C (opnd C t d) j ∧ ¬ OrReaches 10 C (opnd C t (1 - d)) j ∧
        NoAnd (opnd C t (1 - d)) ∧ side (n := 10) C t d = ∅ ∧
        side (n := 10) C t 0 ∪ side (n := 10) C t 1 = side (n := 10) C t (1 - d) ∧
        side (n := 10) C t (1 - d) ⊆ validZ := by
      intro t ht
      obtain ⟨htZ, d, hd⟩ := Finset.mem_filter.mp ht
      obtain ⟨htT, htEmpty⟩ := (centreless_mem C t).mp htZ
      obtain ⟨htlen, htop, htb⟩ := topData htT
      have hnr : ¬ OrReaches 10 C (opnd C t (1 - d)) j := by
        intro h1d
        apply hjnb
        intro x hx
        exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
          by_cases hidx : idx = d
          · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ hd).1 (gateVal_eq_val C j x ▸ hx)
          · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ h1d).1 (gateVal_eq_val C j x ▸ hx)))
      have hna := noAnd_opnd_and htlen htop hnr
      have hne1d : (side (n := 10) C t (1 - d)).Nonempty := by
        rw [side_def]; exact noAnd_nonempty (by have := opndBound htlen (1 - d); omega) hna
      have hemptyD : side (n := 10) C t d = ∅ := by
        rcases htEmpty with h0 | h1
        · rcases fin2_or d with rfl | rfl
          · exact h0
          · rw [show (1 - (1 : Fin 2)) = 0 from rfl, h0] at hne1d
            exact False.elim (Finset.not_nonempty_empty hne1d)
        · rcases fin2_or d with rfl | rfl
          · rw [show (1 - (0 : Fin 2)) = 1 from rfl, h1] at hne1d
            exact False.elim (Finset.not_nonempty_empty hne1d)
          · exact h1
      have hunion : side (n := 10) C t 0 ∪ side (n := 10) C t 1 = side (n := 10) C t (1 - d) := by
        rcases fin2_or d with rfl | rfl
        · rw [hemptyD, Finset.empty_union]; rfl
        · rw [hemptyD, Finset.union_empty]; rfl
      have hsubV : side (n := 10) C t (1 - d) ⊆ validZ := by
        intro z hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hxz hxj => ?_⟩
        exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
          by_cases hidx : idx = d
          · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ hd).1 (gateVal_eq_val C j x ▸ hxj)
          · rw [fin2_ne_eq d idx hidx]; exact sideVal hz hxz))
      exact ⟨d, hd, hnr, hna, hemptyD, hunion, hsubV⟩
    have hUstar_struct : ∀ {u v : Fin 10}, s(u, v) ∈ Ustar P C →
        gateVal 10 C j (pairInput u v) = true ∧
        ∃ t ∈ tops P C, ∃ d : Fin 2, OrReaches 10 C (opnd C t d) j ∧
          (u ∈ side (n := 10) C t (1 - d) ∨ v ∈ side (n := 10) C t (1 - d)) ∧
          side (n := 10) C t (1 - d) ⊆ validZ := by
      intro u v he
      obtain ⟨t, ht, htv, d, j', hj', htd, hj'v⟩ := residualTrace he
      have hj'eq : j' = j := hjUniq j' hj'
      subst j'
      obtain ⟨htlen, htop, htb⟩ := topData ht
      have hnr : ¬ OrReaches 10 C (opnd C t (1 - d)) j := by
        intro h1d
        apply hjnb
        intro x hx
        exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
          by_cases hidx : idx = d
          · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ htd).1 (gateVal_eq_val C j x ▸ hx)
          · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ h1d).1 (gateVal_eq_val C j x ▸ hx)))
      have hna := noAnd_opnd_and htlen htop hnr
      have h1dVal : val C (List.ofFn (pairInput u v)) (opnd C t (1 - d)) = true :=
        ((andValOperands htlen htop _).mp htv) (1 - d)
      obtain ⟨z, hzSide, hzp⟩ := (noAnd_val (by have := opndBound htlen (1 - d); omega) hna _).mp h1dVal
      have hsubV : side (n := 10) C t (1 - d) ⊆ validZ := by
        intro w hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hxw hxj => ?_⟩
        exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
          by_cases hidx : idx = d
          · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j _ htd).1 (gateVal_eq_val C j x ▸ hxj)
          · rw [fin2_ne_eq d idx hidx]; exact sideVal hw hxw))
      refine ⟨hj'v, t, ht, d, htd, ?_, hsubV⟩
      rcases (pairInput_true u v z).mp hzp with rfl | rfl
      · exact Or.inl hzSide
      · exact Or.inr hzSide
    have hRabove_pos_of_Z0 : (centreless P C).card = 0 → 1 ≤ Rabove.card := by
      intro hZ0
      obtain ⟨e, he⟩ := hUstarNe
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨_, t, ht, d, htd, _, _⟩ := hUstar_struct he
        have htNotZ : t ∉ centreless P C := fun h => by
          have := Finset.card_pos.mpr ⟨t, h⟩; omega
        have hneD : (orIn 10 C (opnd C t d)).Nonempty := by
          by_contra hne
          exact htNotZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
        obtain ⟨m, hmR, _, hmj, _⟩ := noncentreless_witness hjMem htd hneD
        exact Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨hmR, hmj⟩⟩
    have hStar_Rabove_bound : ∀ (c : Fin 10) (T : Finset (Fin 10)),
        (∀ z ∈ T, s(c, z) ∈ Ustar P C ∧ z ∉ covZ ∧ c ∉ validZ) →
        ∃ f : Fin 10 → ℕ,
          (∀ z ∈ T, f z ∈ Rabove ∧ (orIn 10 C (10 + f z)).Nonempty ∧
            ∀ q ∈ orIn 10 C (10 + f z), P.Adj z q ∧ s(z, q) ∈ starEdges P C) ∧
          Set.InjOn f ↑T := by
      intro c T hT
      have hEx : ∀ z : Fin 10, z ∈ T →
          ∃ m ∈ Rabove, (orIn 10 C (10 + m)).Nonempty ∧
            ∀ q ∈ orIn 10 C (10 + m), P.Adj z q ∧ s(z, q) ∈ starEdges P C := by
        intro z hz
        obtain ⟨heU, hzNotCov, hcNotV⟩ := hT z hz
        obtain ⟨_, t, ht, d, htd, hSideOr, hSubV⟩ := hUstar_struct heU
        have hzSide : z ∈ side (n := 10) C t (1 - d) := by
          rcases hSideOr with hcS | hzS
          · exact False.elim (hcNotV (hSubV hcS))
          · exact hzS
        have htNotZ : t ∉ centreless P C := by
          intro htZ
          have htZU : t ∈ ZU := Finset.mem_filter.mpr ⟨htZ, d, htd⟩
          apply hzNotCov
          refine Finset.mem_biUnion.mpr ⟨t, htZU, ?_⟩
          rcases fin2_or d with rfl | rfl
          · exact Finset.mem_union_right _ hzSide
          · exact Finset.mem_union_left _ hzSide
        have hneD : (orIn 10 C (opnd C t d)).Nonempty := by
          by_contra hne
          exact htNotZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
        obtain ⟨m, hmR, htm, hmj, hmne⟩ := noncentreless_witness hjMem htd hneD
        refine ⟨m, Finset.mem_filter.mpr ⟨hmR, hmj⟩, hmne, fun q hq => ?_⟩
        have hqSide : q ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono htm hq
        exact ⟨(topAdj_side ht hqSide hzSide).symm, Sym2.eq_swap ▸ side_mem_starEdges ht hqSide hzSide⟩
      let f : Fin 10 → ℕ := fun z => if h : z ∈ T then Classical.choose (hEx z h) else 0
      refine ⟨f, fun z hz => ?_, fun z1 hz1 z2 hz2 hfeq => ?_⟩
      · dsimp only [f]; rw [dif_pos hz]; exact Classical.choose_spec (hEx z hz)
      · by_contra hne
        have h1 : f z1 ∈ Rabove ∧ (orIn 10 C (10 + f z1)).Nonempty ∧
            ∀ q ∈ orIn 10 C (10 + f z1), P.Adj z1 q ∧ s(z1, q) ∈ starEdges P C := by
          dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hz1)]; exact Classical.choose_spec (hEx z1 (Finset.mem_coe.mp hz1))
        have h2 : f z2 ∈ Rabove ∧ (orIn 10 C (10 + f z2)).Nonempty ∧
            ∀ q ∈ orIn 10 C (10 + f z2), P.Adj z2 q ∧ s(z2, q) ∈ starEdges P C := by
          dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hz2)]; exact Classical.choose_spec (hEx z2 (Finset.mem_coe.mp hz2))
        obtain ⟨q, hq⟩ := h1.2.1
        have hq1 := h1.2.2 q hq
        have hq2 := h2.2.2 q (hfeq ▸ hq)
        have hc1 : P.Adj c z1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (hT z1 hz1).1)).1
        have hc2 : P.Adj c z2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (hT z2 hz2).1)).1
        have hqc : q = c := by
          by_contra hqne
          have hc4 := hPno4 q c hqne
          have hm1 : z1 ∈ Finset.univ.filter (fun p => P.Adj q p ∧ P.Adj c p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq1.1.symm, hc1⟩
          have hm2 : z2 ∈ Finset.univ.filter (fun p => P.Adj q p ∧ P.Adj c p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq2.1.symm, hc2⟩
          exact hne (Finset.card_le_one.mp hc4 z1 hm1 z2 hm2)
        subst q
        have hu1 := (hT z1 hz1).1
        rw [Ustar_def] at hu1
        exact (Finset.mem_sdiff.mp hu1).2 (Sym2.eq_swap ▸ hq1.2)
    have hCovZ_bound : ∀ (c : Fin 10) (T : Finset (Fin 10)),
        (∀ z ∈ T, P.Adj c z ∧ s(c, z) ∈ Ustar P C ∧ z ∈ covZ) →
        ∃ RZ : Finset ℕ, RZ ⊆ R ∧
          (∀ r ∈ RZ, ∃ t ∈ ZU, ∃ d : Fin 2, ¬ OrReaches 10 C (opnd C t d) j ∧ OrReaches 10 C (opnd C t d) r) ∧
          T.card ≤ (centreless P C).card + RZ.card := by
      intro c T hT
      let nonJ : ℕ → ℕ := fun t => if h : t ∈ ZU then opnd C t (1 - Classical.choose (hZ_other_side t h)) else 0
      let Roots : Finset ℕ := ZU.image nonJ
      have hRootsOk : ∀ w ∈ Roots, w < 10 + C.gates.length ∧ NoAnd w := by
        intro w hw
        obtain ⟨t, htZU, rfl⟩ := Finset.mem_image.mp hw
        dsimp only [nonJ]; rw [dif_pos htZU]
        have htSpec := Classical.choose_spec (hZ_other_side t htZU)
        have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
        exact ⟨by have := opndBound htlen (1 - Classical.choose (hZ_other_side t htZU)); omega, htSpec.2.2.1⟩
      have hTsub : T ⊆ Roots.biUnion (orIn 10 C) := by
        intro z hz
        obtain ⟨t, htZU, hzt⟩ := Finset.mem_biUnion.mp (hT z hz).2.2
        have htSpec := Classical.choose_spec (hZ_other_side t htZU)
        rw [htSpec.2.2.2.2.1, side_def] at hzt
        refine Finset.mem_biUnion.mpr ⟨nonJ t, Finset.mem_image_of_mem nonJ htZU, ?_⟩
        dsimp only [nonJ]; rw [dif_pos htZU]; exact hzt
      have hBnd := pure_or_no_pair_bound Roots T hRootsOk hTsub
        (no_lam_two_Ustar_nbrs c T (fun z hz => (hT z hz).1) (fun z hz _ _ _ => Or.inl (hT z hz).2.1))
      let RZ := R.filter (fun r => ∃ w ∈ Roots, OrReaches 10 C w r)
      refine ⟨RZ, Finset.filter_subset _ R, fun r hr => ?_, ?_⟩
      · obtain ⟨w, hwR, hwr⟩ := (Finset.mem_filter.mp hr).2
        obtain ⟨t, htZU, rfl⟩ := Finset.mem_image.mp hwR
        dsimp only [nonJ] at hwr; rw [dif_pos htZU] at hwr
        have htSpec := Classical.choose_spec (hZ_other_side t htZU)
        exact ⟨t, htZU, 1 - Classical.choose (hZ_other_side t htZU), htSpec.2.1, hwr⟩
      · have hBnd' : T.card ≤ Roots.card + RZ.card := hBnd
        have h1 : Roots.card ≤ ZU.card := Finset.card_image_le
        have h2 : ZU.card ≤ (centreless P C).card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
    have hRZ_disj_all : ∀ (RZ : Finset ℕ),
        (∀ r ∈ RZ, ∃ t ∈ ZU, ∃ d : Fin 2, ¬ OrReaches 10 C (opnd C t d) j ∧ OrReaches 10 C (opnd C t d) r) →
        Disjoint RZ Rabove ∧
        ((validZ ∩ A).card ≤ 1 → Disjoint RZ (Rw wA)) ∧
        ((validZ ∩ B).card ≤ 1 → Disjoint RZ (Rw wB)) := by
      intro RZ hRZ
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro r hr1 hr2
        obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
        have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
        have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
        have hna := noAnd_opnd_and htlen htop hnr
        have hop := hna j (orReaches_trans htr (Finset.mem_filter.mp hr2).2)
        rw [hjop] at hop; exact GateOp.noConfusion hop
      · intro hVA
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
        obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
        have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
        subst d
        have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
        have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
        have hna := noAnd_opnd_and htlen htop hnr
        have hcap : (orIn 10 C (opnd C t (1 - d0)) ∩ A).card ≤ 1 := by
          have hsub : orIn 10 C (opnd C t (1 - d0)) ∩ A ⊆ validZ ∩ A := by
            intro v hv; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
            exact Finset.mem_inter.mpr ⟨hsubV h1, h2⟩
          exact le_trans (Finset.card_le_card hsub) hVA
        exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hnaA hcap)
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
      · intro hVB
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        obtain ⟨t, htZU, d, hnr, htr⟩ := hRZ r hr1
        obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
        have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
        subst d
        have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
        have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
        have hna := noAnd_opnd_and htlen htop hnr
        have hcap : (orIn 10 C (opnd C t (1 - d0)) ∩ B).card ≤ 1 := by
          have hsub : orIn 10 C (opnd C t (1 - d0)) ∩ B ⊆ validZ ∩ B := by
            intro v hv; obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
            exact Finset.mem_inter.mpr ⟨hsubV h1, h2⟩
          exact le_trans (Finset.card_le_card hsub) hVB
        exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hnaB hcap)
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
    have hSingletonStarContra : ∀ (c : Fin 10) (w : ℕ),
        w < 10 + C.gates.length → NoAnd w →
        (∀ e ∈ Ustar P C, c ∈ e) →
        (∀ u : Fin 10, s(c, u) ∈ Ustar P C → u ∈ orIn 10 C w) → False := by
      intro c w hw hna hCov hInW
      have hBnd := hBudgetLtCov {c} (fun e he => ⟨c, Finset.mem_singleton_self c, hCov e he⟩)
      rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hBnd
      let TU : Finset (Fin 10) := (orIn 10 C w).filter (fun u => s(c, u) ∈ Ustar P C)
      have hTUcard : (Ustar P C).card ≤ TU.card := by
        have hsub : Ustar P C ⊆ TU.image (fun u => s(c, u)) := by
          intro e he
          induction e using Sym2.ind with
          | _ p q =>
            rcases Sym2.mem_iff.mp (hCov s(p, q) he) with rfl | rfl
            · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hInW q he, he⟩, rfl⟩
            · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hInW p (Sym2.eq_swap ▸ he), Sym2.eq_swap ▸ he⟩, Sym2.eq_swap⟩
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hRw := single_wire_no_pair w TU hw hna (Finset.filter_subset _ _)
        (no_lam_two_Ustar_nbrs c TU
          (fun u hu => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ (Finset.mem_filter.mp hu).2)).1)
          (fun u hu _ _ _ => Or.inl (Finset.mem_filter.mp hu).2))
      by_cases hZ0 : (centreless P C).card = 0
      · have hRa := hRabove_pos_of_Z0 hZ0
        have hDisj := noAnd_disj_Rabove hna
        have hUn : (Rw w ∪ Rabove).card ≤ R.card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R))
        rw [Finset.card_union_of_disjoint hDisj] at hUn
        omega
      · have hSub : (Rw w).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ R)
        omega
    have hAge2 : 2 ≤ A.card := by
      by_contra hlt
      have hA1 : A.card = 1 := by have := Finset.card_pos.mpr hAne; omega
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hA1
      have hw0NotB : w0 ∉ B := fun h => hNotAsubB (fun a ha => by rw [hw0] at ha; rw [Finset.mem_singleton.mp ha]; exact h)
      exact hSingletonStarContra w0 wB hwBLt hnaB
        (fun e he => Sym2.ind (fun u v he' => by
          obtain ⟨a, haA, hpa⟩ := ((hjVal _).mp (hUstar_struct he').1).1
          rw [hw0] at haA; rw [Finset.mem_singleton.mp haA] at hpa
          rcases (pairInput_true u v w0).mp hpa with rfl | rfl
          · exact Sym2.mem_mk_left _ _
          · exact Sym2.mem_mk_right _ _) e he)
        (fun u hu => by
          obtain ⟨b, hbB, hpb⟩ := ((hjVal _).mp (hUstar_struct hu).1).2
          rcases (pairInput_true w0 u b).mp hpb with rfl | rfl
          · exact False.elim (hw0NotB hbB)
          · exact hbB)
    have hBge2 : 2 ≤ B.card := by
      by_contra hlt
      have hB1 : B.card = 1 := by have := Finset.card_pos.mpr hBne; omega
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hB1
      have hw0NotA : w0 ∉ A := fun h => hNotBsubA (fun b hb => by rw [hw0] at hb; rw [Finset.mem_singleton.mp hb]; exact h)
      exact hSingletonStarContra w0 wA hwALt hnaA
        (fun e he => Sym2.ind (fun u v he' => by
          obtain ⟨b, hbB, hpb⟩ := ((hjVal _).mp (hUstar_struct he').1).2
          rw [hw0] at hbB; rw [Finset.mem_singleton.mp hbB] at hpb
          rcases (pairInput_true u v w0).mp hpb with rfl | rfl
          · exact Sym2.mem_mk_left _ _
          · exact Sym2.mem_mk_right _ _) e he)
        (fun u hu => by
          obtain ⟨a, haA, hpa⟩ := ((hjVal _).mp (hUstar_struct hu).1).1
          rcases (pairInput_true w0 u a).mp hpa with rfl | rfl
          · exact False.elim (hw0NotA haA)
          · exact haA)
    have hVA_le1 : (validZ ∩ A).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z1 hz1 z2 hz2
      by_contra hne
      have hc4 := hPno4 z1 z2 hne
      have hsub : B ⊆ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z2 p) := fun b hb =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValidA_adjB z1 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2 b hb,
          hValidA_adjB z2 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2 b hb⟩
      have hle := le_trans (Finset.card_le_card hsub) hc4
      omega
    have hVB_le1 : (validZ ∩ B).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z1 hz1 z2 hz2
      by_contra hne
      have hc4 := hPno4 z1 z2 hne
      have hsub : A ⊆ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z2 p) := fun a ha =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValidB_adjA z1 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2 a ha,
          hValidB_adjA z2 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2 a ha⟩
      have hle := le_trans (Finset.card_le_card hsub) hc4
      omega
    have hCase2Sym : ∀ (w1 w2 : ℕ), w1 < 10 + C.gates.length → w2 < 10 + C.gates.length →
        NoAnd w1 → NoAnd w2 →
        (∀ x : Fin 10 → Bool, gateVal 10 C j x = true ↔ (∃ a ∈ orIn 10 C w1, x a = true) ∧ (∃ b ∈ orIn 10 C w2, x b = true)) →
        (validZ ∩ orIn 10 C w1).Nonempty → (validZ ∩ orIn 10 C w2) = ∅ →
        (validZ ∩ orIn 10 C w1).card ≤ 1 → False := by
      intro w1 w2 hw1 hw2 hna1 hna2 hjV12 hV1ne hV2e hV1le1
      let S1 := orIn 10 C w1
      let S2 := orIn 10 C w2
      have hV1card : (validZ ∩ S1).card = 1 := by
        have h1 : (validZ ∩ S1).card ≤ 1 := hV1le1
        have h2 : 0 < (validZ ∩ S1).card := Finset.card_pos.mpr hV1ne
        omega
      obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hV1card
      have hz1V : z1 ∈ validZ := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).1
      have hz1S1 : z1 ∈ S1 := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).2
      have hS2adj : ∀ b ∈ S2, P.Adj z1 b := fun b hb =>
        (graphFun_pair z1 b).mp ((Finset.mem_filter.mp hz1V).2 (pairInput z1 b) (pairInput_left z1 b)
          ((hjV12 _).mpr ⟨⟨z1, hz1S1, pairInput_left z1 b⟩, ⟨b, hb, pairInput_right z1 b⟩⟩))
      have hz1NotS2 : z1 ∉ S2 := fun h => P.irrefl (hS2adj z1 h)
      have hNotInV : ∀ b ∈ S2, b ∉ validZ := fun b hb hbv => by
        have hm : b ∈ validZ ∩ S2 := Finset.mem_inter.mpr ⟨hbv, hb⟩
        rw [hV2e] at hm; exact Finset.notMem_empty b hm
      have hV_adjInter : ∀ z ∈ validZ, ∀ w ∈ S1 ∩ S2, P.Adj z w := fun z hz w hw =>
        (graphFun_pair z w).mp ((Finset.mem_filter.mp hz).2 (pairInput z w) (pairInput_left z w)
          ((hjV12 _).mpr ⟨⟨w, (Finset.mem_inter.mp hw).1, pairInput_right z w⟩, ⟨w, (Finset.mem_inter.mp hw).2, pairInput_right z w⟩⟩))
      by_cases hInter1 : (S1 ∩ S2).card = 1
      · obtain ⟨w0, hw0Set⟩ := Finset.card_eq_one.mp hInter1
        have hw0S1 : w0 ∈ S1 := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).1
        have hw0S2 : w0 ∈ S2 := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).2
        have hadjZW : P.Adj z1 w0 := hS2adj w0 hw0S2
        have hw0NotV : w0 ∉ validZ := hNotInV w0 hw0S2
        have hz1NeW0 : z1 ≠ w0 := hadjZW.ne
        have hRw1Pos : 1 ≤ (Rw w1).card := by
          have hw1NotLt10 : ¬ w1 < 10 := by
            intro hlt
            have h1 := orIn_leaf ⟨w1, hlt⟩
            have hz1' : z1 ∈ ({⟨w1, hlt⟩} : Finset (Fin 10)) := h1 ▸ hz1S1
            have hw0' : w0 ∈ ({⟨w1, hlt⟩} : Finset (Fin 10)) := h1 ▸ hw0S1
            exact hz1NeW0 ((Finset.mem_singleton.mp hz1').trans (Finset.mem_singleton.mp hw0').symm)
          let r1 := w1 - 10
          have hw1Eq : w1 = 10 + r1 := by omega
          have hr1len : r1 < C.gates.length := by omega
          have hr1Self : OrReaches 10 C w1 r1 := by rw [hw1Eq]; exact (orReaches_iff r1 r1).mpr ⟨hr1len, Or.inl rfl⟩
          have hr1N : r1 ∈ orN P C := (noAnd_reach_orN hna1 hr1Self).1
          have hr1NotLam : r1 ∉ lam P C := by
            intro hlam
            obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C r1).mp hlam
            obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
            have hqs : q ∈ side (n := 10) C t (1 - d) := by rw [hq]; exact Finset.mem_singleton_self q
            have hz1s : z1 ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth (hw1Eq ▸ hz1S1)
            have hw0s : w0 ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth (hw1Eq ▸ hw0S1)
            have hqz1 : P.Adj q z1 := (topAdj_side ht hz1s hqs).symm
            have hqw0 : P.Adj q w0 := (topAdj_side ht hw0s hqs).symm
            exact hPtri q z1 w0 hqz1 hadjZW hqw0
          exact Finset.card_pos.mpr ⟨r1, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr1N, hr1NotLam⟩, hr1Self⟩⟩
        let TB : Finset (Fin 10) := (S2.erase w0).filter (fun b => s(z1, b) ∈ Ustar P C)
        let TW : Finset (Fin 10) := (validZ.erase z1).filter (fun z => s(w0, z) ∈ Ustar P C)
        let δ : ℕ := if s(z1, w0) ∈ Ustar P C then 1 else 0
        have hEdgeClass : ∀ e ∈ Ustar P C,
            e = s(z1, w0) ∨ (∃ b ∈ TB, e = s(z1, b)) ∨ (∃ z ∈ TW, e = s(w0, z)) := by
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨hjv, t, _, d, _, hSide, hSubV⟩ := hUstar_struct he
            obtain ⟨⟨a, ha1, hpa⟩, ⟨b, hb2, hpb⟩⟩ := (hjV12 _).mp hjv
            have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
            have hCaseUV : ∀ p q : Fin 10, s(p, q) ∈ Ustar P C → p ∈ validZ →
                gateVal 10 C j (pairInput p q) = true →
                s(p, q) = s(z1, w0) ∨ (∃ b' ∈ TB, s(p, q) = s(z1, b')) ∨ (∃ z' ∈ TW, s(p, q) = s(w0, z')) := by
              intro p q hpqU hpV hjvpq
              obtain ⟨⟨a', ha'1, hpa'⟩, ⟨b', hb'2, hpb'⟩⟩ := (hjV12 _).mp hjvpq
              by_cases hpz1 : p = z1
              · subst p
                have hqb' : q = b' := by
                  rcases (pairInput_true z1 q b').mp hpb' with rfl | rfl
                  · exact False.elim (hz1NotS2 hb'2)
                  · rfl
                subst q
                by_cases hbw : b' = w0
                · subst b'; exact Or.inl rfl
                · exact Or.inr (Or.inl ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hbw, hb'2⟩, hpqU⟩, rfl⟩)
              · have hpNotS1 : p ∉ S1 := fun h => hpz1 (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, h⟩))
                have hpNotS2 : p ∉ S2 := fun h => hNotInV p h hpV
                have hqa' : q = a' := by
                  rcases (pairInput_true p q a').mp hpa' with rfl | rfl
                  · exact False.elim (hpNotS1 ha'1)
                  · rfl
                have hqb' : q = b' := by
                  rcases (pairInput_true p q b').mp hpb' with rfl | rfl
                  · exact False.elim (hpNotS2 hb'2)
                  · rfl
                have hqInter : q ∈ S1 ∩ S2 := Finset.mem_inter.mpr ⟨hqa' ▸ ha'1, hqb' ▸ hb'2⟩
                have hqw0 : q = w0 := Finset.mem_singleton.mp (hw0Set ▸ hqInter)
                rw [hqw0] at hpqU ⊢
                exact Or.inr (Or.inr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpz1, hpV⟩, Sym2.eq_swap ▸ hpqU⟩, Sym2.eq_swap⟩)
            rcases hOneV with huV | hvV
            · exact hCaseUV u v he huV hjv
            · have hres := hCaseUV v u (Sym2.eq_swap ▸ he) hvV (pairInput_symm u v ▸ hjv)
              rcases hres with h | ⟨b', hb', h⟩ | ⟨z', hz', h⟩
              · exact Or.inl (Sym2.eq_swap.trans h)
              · exact Or.inr (Or.inl ⟨b', hb', Sym2.eq_swap.trans h⟩)
              · exact Or.inr (Or.inr ⟨z', hz', Sym2.eq_swap.trans h⟩)
        have hUstarCard : (Ustar P C).card ≤ δ + TB.card + TW.card := by
          let E0 : Finset (Sym2 (Fin 10)) := if s(z1, w0) ∈ Ustar P C then {s(z1, w0)} else ∅
          have hsub : Ustar P C ⊆ E0 ∪ (TB.image (fun b => s(z1, b)) ∪ TW.image (fun z => s(w0, z))) := by
            intro e he
            rcases hEdgeClass e he with rfl | ⟨b, hb, rfl⟩ | ⟨z, hz, rfl⟩
            · exact Finset.mem_union_left _ (by dsimp only [E0]; rw [if_pos he]; exact Finset.mem_singleton_self _)
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz))
          have hE0 : E0.card = δ := by
            dsimp only [E0, δ]
            by_cases h : s(z1, w0) ∈ Ustar P C
            · rw [if_pos h, if_pos h, Finset.card_singleton]
            · rw [if_neg h, if_neg h, Finset.card_empty]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_union_le E0 (TB.image (fun b => s(z1, b)) ∪ TW.image (fun z => s(w0, z)))
          have h3 := Finset.card_union_le (TB.image (fun b => s(z1, b))) (TW.image (fun z => s(w0, z)))
          have h4 : (TB.image (fun b => s(z1, b))).card ≤ TB.card := Finset.card_image_le
          have h5 : (TW.image (fun z => s(w0, z))).card ≤ TW.card := Finset.card_image_le
          omega
        have hTB_Rw2 : TB.card ≤ (Rw w2).card := by
          have hw0NotTB : w0 ∉ TB := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
          have hsub2 : insert w0 TB ⊆ S2 := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxTB
            · exact hw0S2
            · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTB).1
          have hBnd := single_wire_no_pair w2 (insert w0 TB) hw2 hna2 hsub2
            (no_lam_two_Ustar_nbrs z1 (insert w0 TB) (fun x hx => hS2adj x (hsub2 hx))
              (fun x hx y hy hxy => by
                rcases Finset.mem_insert.mp hx with rfl | hxTB
                · rcases Finset.mem_insert.mp hy with rfl | hyTB
                  · exact False.elim (hxy rfl)
                  · exact Or.inr (Finset.mem_filter.mp hyTB).2
                · exact Or.inl (Finset.mem_filter.mp hxTB).2))
          rw [Finset.card_insert_of_notMem hw0NotTB] at hBnd
          omega
        let TWZ := TW.filter (fun z => z ∈ covZ)
        let TWN := TW.filter (fun z => z ∉ covZ)
        have hTWsplit : TW.card = TWZ.card + TWN.card := by
          have hDisjZ : Disjoint TWZ TWN := Finset.disjoint_left.mpr (fun z h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2)
          have hUnZ : TWZ ∪ TWN = TW := by
            apply Finset.ext; intro z; simp only [TWZ, TWN, Finset.mem_union, Finset.mem_filter]
            exact ⟨fun h => h.elim And.left And.left, fun h => (em (z ∈ covZ)).elim (fun hc => Or.inl ⟨h, hc⟩) (fun hc => Or.inr ⟨h, hc⟩)⟩
          rw [← hUnZ, Finset.card_union_of_disjoint hDisjZ]
        obtain ⟨RZ, hRZsub, hRZspec, hTWZ_bnd⟩ := hCovZ_bound w0 TWZ (fun z hz => by
          obtain ⟨hzTW, hzCov⟩ := Finset.mem_filter.mp hz
          have hu := (Finset.mem_filter.mp hzTW).2
          exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu)).1, hu, hzCov⟩)
        obtain ⟨fN, hfNspec, hfNinj⟩ := hStar_Rabove_bound w0 TWN (fun z hz => by
          obtain ⟨hzTW, hzNotCov⟩ := Finset.mem_filter.mp hz
          exact ⟨(Finset.mem_filter.mp hzTW).2, hzNotCov, hw0NotV⟩)
        have hTWN_bnd : TWN.card ≤ Rabove.card := by
          have hsub : TWN.image fN ⊆ Rabove := fun m hm => by
            obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1
          rw [← Finset.card_image_of_injOn hfNinj]
          exact Finset.card_le_card hsub
        have hDisj12 : Disjoint (Rw w1) (Rw w2) := noAnd_disj_Rw hna1 hna2 (le_of_eq hInter1)
        have hDisj1A : Disjoint (Rw w1) Rabove := noAnd_disj_Rabove hna1
        have hDisj2A : Disjoint (Rw w2) Rabove := noAnd_disj_Rabove hna2
        have hDisjRZ_A : Disjoint RZ Rabove := (hRZ_disj_all RZ hRZspec).1
        have hDisjRZ_1 : Disjoint RZ (Rw w1) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          obtain ⟨t, htZU, d, hnr, htr⟩ := hRZspec r hr1
          obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
          have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
          subst d
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
          have hna := noAnd_opnd_and htlen htop hnr
          have hcap : (orIn 10 C (opnd C t (1 - d0)) ∩ S1).card ≤ 1 :=
            le_trans (Finset.card_le_card (fun v hv => Finset.mem_inter.mpr ⟨hsubV (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩)) hV1le1
          exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hna1 hcap)
            (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
        have hDisjRZ_2 : Disjoint RZ (Rw w2) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          obtain ⟨t, htZU, d, hnr, htr⟩ := hRZspec r hr1
          obtain ⟨d0, hd0, _, _, _, _, hsubV⟩ := hZ_other_side t htZU
          have hdeq : d = 1 - d0 := fin2_ne_eq d0 d (fun h => hnr (h ▸ hd0))
          subst d
          have htlen := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).1
          have htop := (topData ((centreless_mem C t).mp (Finset.mem_filter.mp htZU).1).1).2.1
          have hna := noAnd_opnd_and htlen htop hnr
          have hcap : (orIn 10 C (opnd C t (1 - d0)) ∩ S2).card ≤ 1 := by
            have hsub : orIn 10 C (opnd C t (1 - d0)) ∩ S2 ⊆ validZ ∩ S2 :=
              fun v hv => Finset.mem_inter.mpr ⟨hsubV (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
            rw [hV2e] at hsub
            have := Finset.card_le_card hsub; simp only [Finset.card_empty] at this; omega
          exact Finset.disjoint_left.mp (noAnd_disj_Rw hna hna2 hcap)
            (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr2).1, htr⟩) hr2
        have hRsum : (Rw w1).card + (Rw w2).card + RZ.card + Rabove.card ≤ R.card := by
          have hsub : ((Rw w1 ∪ Rw w2) ∪ RZ) ∪ Rabove ⊆ R :=
            Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R)) hRZsub)
              (Finset.filter_subset _ R)
          have h1 := Finset.card_le_card hsub
          have hd1 : Disjoint (Rw w1 ∪ Rw w2) RZ := Finset.disjoint_union_left.mpr ⟨hDisjRZ_1.symm, hDisjRZ_2.symm⟩
          have hd2 : Disjoint ((Rw w1 ∪ Rw w2) ∪ RZ) Rabove :=
            Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hDisj1A, hDisj2A⟩, hDisjRZ_A⟩
          rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hDisj12] at h1
          exact h1
        have hDeltaLe1 : δ ≤ 1 := by
          dsimp only [δ]
          by_cases h : s(z1, w0) ∈ Ustar P C
          · rw [if_pos h]
          · rw [if_neg h]; omega
        by_cases hTW0 : TW.card = 0
        · have hCov1 : ∀ e ∈ Ustar P C, ∃ v ∈ ({z1} : Finset (Fin 10)), v ∈ e := by
            intro e he
            rcases hEdgeClass e he with rfl | ⟨_, _, rfl⟩ | ⟨z, hz, _⟩
            · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
            · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
            · have := Finset.card_pos.mpr ⟨z, hz⟩; omega
          have hLt := hBudgetLtCov {z1} hCov1
          rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
          omega
        · by_cases hTB0 : TB.card = 0
          · have hCov1 : ∀ e ∈ Ustar P C, ∃ v ∈ ({w0} : Finset (Fin 10)), v ∈ e := by
              intro e he
              rcases hEdgeClass e he with rfl | ⟨b, hb, _⟩ | ⟨_, _, rfl⟩
              · exact ⟨w0, Finset.mem_singleton_self w0, Sym2.mem_mk_right _ _⟩
              · have := Finset.card_pos.mpr ⟨b, hb⟩; omega
              · exact ⟨w0, Finset.mem_singleton_self w0, Sym2.mem_mk_left _ _⟩
            have hLt := hBudgetLtCov {w0} hCov1
            rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
            omega
          · have hCov2 : ∀ e ∈ Ustar P C, ∃ v ∈ ({z1, w0} : Finset (Fin 10)), v ∈ e := by
              intro e he
              rcases hEdgeClass e he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
              · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
              · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
              · exact ⟨w0, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
            have hLt := hBudgetLtCov {z1, w0} hCov2
            rw [Finset.card_pair hz1NeW0, hjSet, Finset.card_singleton] at hLt
            by_cases hZ0 : (centreless P C).card = 0
            · have hTWZ0 : TWZ.card = 0 := by
                by_contra hpos
                obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < TWZ.card)
                obtain ⟨t, htZU, _⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hz).2
                have := Finset.card_pos.mpr ⟨t, (Finset.mem_filter.mp htZU).1⟩
                omega
              obtain ⟨b1, hb1⟩ := Finset.card_pos.mp (by omega : 0 < TB.card)
              have hb1U : s(z1, b1) ∈ Ustar P C := (Finset.mem_filter.mp hb1).2
              have hb1S2 : b1 ∈ S2 := Finset.mem_of_mem_erase (Finset.mem_filter.mp hb1).1
              have hb1NotV : b1 ∉ validZ := hNotInV b1 hb1S2
              obtain ⟨_, tB, htB, dB, htBd, hSideB, hSubVB⟩ := hUstar_struct hb1U
              have hz1SideB : z1 ∈ side (n := 10) C tB (1 - dB) := by
                rcases hSideB with hz1S | hb1S
                · exact hz1S
                · exact False.elim (hb1NotV (hSubVB hb1S))
              have htBNotZ : tB ∉ centreless P C := fun h => by have := Finset.card_pos.mpr ⟨tB, h⟩; omega
              have hneDB : (orIn 10 C (opnd C tB dB)).Nonempty := by
                by_contra hne
                exact htBNotZ (emptySide_mem_centreless htB (Finset.not_nonempty_iff_eq_empty.mp hne))
              obtain ⟨mB, hmBR, htBmB, hmBj, hmBne⟩ := noncentreless_witness hjMem htBd hneDB
              have hmBMem : mB ∈ Rabove := Finset.mem_filter.mpr ⟨hmBR, hmBj⟩
              have hmBNotImg : mB ∉ TWN.image fN := by
                intro hmem
                obtain ⟨z, hzN, hfz⟩ := Finset.mem_image.mp hmem
                obtain ⟨q, hq⟩ := hmBne
                have hqSideB : q ∈ side (n := 10) C tB dB := by rw [side_def]; exact orIn_mono htBmB hq
                have hqz1 : P.Adj z1 q := (topAdj_side htB hqSideB hz1SideB).symm
                have hqz : P.Adj z q ∧ s(z, q) ∈ starEdges P C := (hfNspec z hzN).2.2 q (hfz.symm ▸ hq)
                have hzTW : z ∈ TW := (Finset.mem_filter.mp hzN).1
                have hzNeZ1 : z ≠ z1 := (Finset.mem_erase.mp (Finset.mem_filter.mp hzTW).1).1
                have hzw0U : s(w0, z) ∈ Ustar P C := (Finset.mem_filter.mp hzTW).2
                have hzw0 : P.Adj w0 z := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hzw0U)).1
                have hqNeW0 : q ≠ w0 := by
                  intro heq; subst q
                  rw [Ustar_def] at hzw0U
                  exact (Finset.mem_sdiff.mp hzw0U).2 (Sym2.eq_swap ▸ hqz.2)
                have hc4 := hPno4 z1 z hzNeZ1.symm
                have hm1 : w0 ∈ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z p) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadjZW, hzw0.symm⟩
                have hm2 : q ∈ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z p) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqz1, hqz.1⟩
                exact hqNeW0.symm (Finset.card_le_one.mp hc4 w0 hm1 q hm2)
              have hRabovePlus : TWN.card + 1 ≤ Rabove.card := by
                have hsub : insert mB (TWN.image fN) ⊆ Rabove :=
                  Finset.insert_subset_iff.mpr ⟨hmBMem, fun m hm => by
                    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1⟩
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_insert_of_notMem hmBNotImg, Finset.card_image_of_injOn hfNinj] at h1
                exact h1
              omega
            · omega
      · have hAllZ1 : ∀ e ∈ Ustar P C, z1 ∈ e := by
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
            obtain ⟨⟨a, ha1, hpa⟩, ⟨b, hb2, hpb⟩⟩ := (hjV12 _).mp hjv
            have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
            have hCheck : ∀ p q : Fin 10, p ∈ validZ → gateVal 10 C j (pairInput p q) = true → p = z1 := by
              intro p q hpV hjvpq
              by_contra hpne
              have hpNotS1 : p ∉ S1 := fun h => hpne (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, h⟩))
              have hpNotS2 : p ∉ S2 := fun h => hNotInV p h hpV
              obtain ⟨⟨a', ha'1, hpa'⟩, ⟨b', hb'2, hpb'⟩⟩ := (hjV12 _).mp hjvpq
              have hqa' : q = a' := by rcases (pairInput_true p q a').mp hpa' with rfl | rfl; exact False.elim (hpNotS1 ha'1); rfl
              have hqb' : q = b' := by rcases (pairInput_true p q b').mp hpb' with rfl | rfl; exact False.elim (hpNotS2 hb'2); rfl
              have hqInter : q ∈ S1 ∩ S2 := Finset.mem_inter.mpr ⟨hqa' ▸ ha'1, hqb' ▸ hb'2⟩
              have hge2 : 2 ≤ (S1 ∩ S2).card := by have := Finset.card_pos.mpr ⟨q, hqInter⟩; omega
              obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (S1 ∩ S2).card)
              have hc4 := hPno4 p z1 hpne
              have hm1 : x1 ∈ Finset.univ.filter (fun w => P.Adj p w ∧ P.Adj z1 w) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_adjInter p hpV x1 hx1, hV_adjInter z1 hz1V x1 hx1⟩
              have hm2 : x2 ∈ Finset.univ.filter (fun w => P.Adj p w ∧ P.Adj z1 w) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_adjInter p hpV x2 hx2, hV_adjInter z1 hz1V x2 hx2⟩
              exact hxne (Finset.card_le_one.mp hc4 x1 hm1 x2 hm2)
            rcases hOneV with huV | hvV
            · rw [hCheck u v huV hjv]; exact Sym2.mem_mk_left _ _
            · rw [hCheck v u hvV (pairInput_symm u v ▸ hjv)]; exact Sym2.mem_mk_right _ _
        exact hSingletonStarContra z1 w2 hw2 hna2 hAllZ1 (fun u hu => by
          obtain ⟨b, hb2, hpb⟩ := ((hjV12 _).mp (hUstar_struct hu).1).2
          rcases (pairInput_true z1 u b).mp hpb with rfl | rfl
          · exact False.elim (hz1NotS2 hb2)
          · exact hb2)
    by_cases hVA : (validZ ∩ A).Nonempty
    · by_cases hVB : (validZ ∩ B).Nonempty
      · have hVA1 : (validZ ∩ A).card = 1 := by have := Finset.card_pos.mpr hVA; omega
        have hVB1 : (validZ ∩ B).card = 1 := by have := Finset.card_pos.mpr hVB; omega
        obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hVA1
        obtain ⟨z2, hz2Set⟩ := Finset.card_eq_one.mp hVB1
        have hz1V : z1 ∈ validZ := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).1
        have hz1A : z1 ∈ A := (Finset.mem_inter.mp (hz1Set ▸ Finset.mem_singleton_self z1)).2
        have hz2V : z2 ∈ validZ := (Finset.mem_inter.mp (hz2Set ▸ Finset.mem_singleton_self z2)).1
        have hz2B : z2 ∈ B := (Finset.mem_inter.mp (hz2Set ▸ Finset.mem_singleton_self z2)).2
        have hadj12 : P.Adj z1 z2 := hValidA_adjB z1 hz1V hz1A z2 hz2B
        have hABempty : A ∩ B = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hwA, hwB⟩ := Finset.mem_inter.mp hw
          exact hPtri z1 z2 w hadj12 (hValidB_adjA z2 hz2V hz2B w hwA) (hValidA_adjB z1 hz1V hz1A w hwB)
        let TA : Finset (Fin 10) := (A.erase z1).filter (fun a => s(z2, a) ∈ Ustar P C)
        let TB : Finset (Fin 10) := (B.erase z2).filter (fun b => s(z1, b) ∈ Ustar P C)
        let δ : ℕ := if s(z1, z2) ∈ Ustar P C then 1 else 0
        have hEdge1 : ∀ e ∈ Ustar P C,
            e = s(z1, z2) ∨ (∃ a ∈ TA, e = s(z2, a)) ∨ (∃ b ∈ TB, e = s(z1, b)) := by
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
            have hOneV : u ∈ validZ ∨ v ∈ validZ := hSide.elim (fun h => Or.inl (hSubV h)) (fun h => Or.inr (hSubV h))
            have hCase : ∀ p q : Fin 10, s(p, q) ∈ Ustar P C → p ∈ validZ → gateVal 10 C j (pairInput p q) = true →
                s(p, q) = s(z1, z2) ∨ (∃ a ∈ TA, s(p, q) = s(z2, a)) ∨ (∃ b ∈ TB, s(p, q) = s(z1, b)) := by
              intro p q hpqU hpV hjvpq
              obtain ⟨⟨a', ha'A, hpa'⟩, ⟨b', hb'B, hpb'⟩⟩ := (hjVal _).mp hjvpq
              by_cases hpA : p ∈ A
              · have hp1 : p = z1 := Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨hpV, hpA⟩)
                subst p
                have hqb' : q = b' := by
                  rcases (pairInput_true z1 q b').mp hpb' with hb'z1 | rfl
                  · have hm : b' ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb'z1 ▸ hz1A, hb'B⟩
                    rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
                  · rfl
                subst q
                by_cases hb2 : b' = z2
                · subst b'; exact Or.inl rfl
                · exact Or.inr (Or.inr ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hb2, hb'B⟩, hpqU⟩, rfl⟩)
              · by_cases hpB : p ∈ B
                · have hp2 : p = z2 := Finset.mem_singleton.mp (hz2Set ▸ Finset.mem_inter.mpr ⟨hpV, hpB⟩)
                  subst p
                  have hqa' : q = a' := by
                    rcases (pairInput_true z2 q a').mp hpa' with ha'z2 | rfl
                    · have hm : a' ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha'A, ha'z2 ▸ hz2B⟩
                      rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
                    · rfl
                  subst q
                  by_cases ha1 : a' = z1
                  · subst a'; exact Or.inl Sym2.eq_swap
                  · exact Or.inr (Or.inl ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ha1, ha'A⟩, hpqU⟩, rfl⟩)
                · have hqa' : q = a' := by rcases (pairInput_true p q a').mp hpa' with rfl | rfl; exact False.elim (hpA ha'A); rfl
                  have hqb' : q = b' := by rcases (pairInput_true p q b').mp hpb' with rfl | rfl; exact False.elim (hpB hb'B); rfl
                  have hm : q ∈ A ∩ B := Finset.mem_inter.mpr ⟨hqa' ▸ ha'A, hqb' ▸ hb'B⟩
                  rw [hABempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
            rcases hOneV with huV | hvV
            · exact hCase u v he huV hjv
            · rcases hCase v u (Sym2.eq_swap ▸ he) hvV (pairInput_symm u v ▸ hjv) with h | ⟨a, ha, h⟩ | ⟨b, hb, h⟩
              · exact Or.inl (Sym2.eq_swap.trans h)
              · exact Or.inr (Or.inl ⟨a, ha, Sym2.eq_swap.trans h⟩)
              · exact Or.inr (Or.inr ⟨b, hb, Sym2.eq_swap.trans h⟩)
        have hUcard : (Ustar P C).card ≤ δ + TA.card + TB.card := by
          let E0 : Finset (Sym2 (Fin 10)) := if s(z1, z2) ∈ Ustar P C then {s(z1, z2)} else ∅
          have hsub : Ustar P C ⊆ E0 ∪ (TA.image (fun a => s(z2, a)) ∪ TB.image (fun b => s(z1, b))) := by
            intro e he
            rcases hEdge1 e he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
            · exact Finset.mem_union_left _ (by dsimp only [E0]; rw [if_pos he]; exact Finset.mem_singleton_self _)
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
          have hE0 : E0.card = δ := by
            dsimp only [E0, δ]
            by_cases h : s(z1, z2) ∈ Ustar P C
            · rw [if_pos h, if_pos h, Finset.card_singleton]
            · rw [if_neg h, if_neg h, Finset.card_empty]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_union_le E0 (TA.image (fun a => s(z2, a)) ∪ TB.image (fun b => s(z1, b)))
          have h3 := Finset.card_union_le (TA.image (fun a => s(z2, a))) (TB.image (fun b => s(z1, b)))
          have h4 : (TA.image (fun a => s(z2, a))).card ≤ TA.card := Finset.card_image_le
          have h5 : (TB.image (fun b => s(z1, b))).card ≤ TB.card := Finset.card_image_le
          omega
        have hTA_RwA : TA.card ≤ (Rw wA).card := by
          have hz1NotTA : z1 ∉ TA := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
          have hsub : insert z1 TA ⊆ A := fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hxTA
            · exact hz1A
            · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTA).1
          have hBnd := single_wire_no_pair wA (insert z1 TA) hwALt hnaA hsub
            (no_lam_two_Ustar_nbrs z2 (insert z1 TA) (fun x hx => hValidB_adjA z2 hz2V hz2B x (hsub hx))
              (fun x hx y hy hxy => by
                rcases Finset.mem_insert.mp hx with rfl | hxTA
                · rcases Finset.mem_insert.mp hy with rfl | hyTA
                  · exact False.elim (hxy rfl)
                  · exact Or.inr (Finset.mem_filter.mp hyTA).2
                · exact Or.inl (Finset.mem_filter.mp hxTA).2))
          rw [Finset.card_insert_of_notMem hz1NotTA] at hBnd; omega
        have hTB_RwB : TB.card ≤ (Rw wB).card := by
          have hz2NotTB : z2 ∉ TB := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
          have hsub : insert z2 TB ⊆ B := fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hxTB
            · exact hz2B
            · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxTB).1
          have hBnd := single_wire_no_pair wB (insert z2 TB) hwBLt hnaB hsub
            (no_lam_two_Ustar_nbrs z1 (insert z2 TB) (fun x hx => hValidA_adjB z1 hz1V hz1A x (hsub hx))
              (fun x hx y hy hxy => by
                rcases Finset.mem_insert.mp hx with rfl | hxTB
                · rcases Finset.mem_insert.mp hy with rfl | hyTB
                  · exact False.elim (hxy rfl)
                  · exact Or.inr (Finset.mem_filter.mp hyTB).2
                · exact Or.inl (Finset.mem_filter.mp hxTB).2))
          rw [Finset.card_insert_of_notMem hz2NotTB] at hBnd; omega
        have hDisjAB : Disjoint (Rw wA) (Rw wB) := noAnd_disj_Rw hnaA hnaB (by rw [hABempty]; simp only [Finset.card_empty, Nat.zero_le])
        have hDisjA_Ra : Disjoint (Rw wA) Rabove := noAnd_disj_Rabove hnaA
        have hDisjB_Ra : Disjoint (Rw wB) Rabove := noAnd_disj_Rabove hnaB
        have hRsum : (Rw wA).card + (Rw wB).card + Rabove.card ≤ R.card := by
          have hsub : (Rw wA ∪ Rw wB) ∪ Rabove ⊆ R :=
            Finset.union_subset (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R)) (Finset.filter_subset _ R)
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDisjA_Ra, hDisjB_Ra⟩),
            Finset.card_union_of_disjoint hDisjAB] at h1
          exact h1
        have hDeltaLe1 : δ ≤ 1 := by
          dsimp only [δ]
          by_cases h : s(z1, z2) ∈ Ustar P C
          · rw [if_pos h]
          · rw [if_neg h]; omega
        by_cases hTA0 : TA.card = 0
        · have hCov1 : ∀ e ∈ Ustar P C, ∃ v ∈ ({z1} : Finset (Fin 10)), v ∈ e := fun e he => by
            rcases hEdge1 e he with rfl | ⟨a, ha, _⟩ | ⟨_, _, rfl⟩
            · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
            · have := Finset.card_pos.mpr ⟨a, ha⟩; omega
            · exact ⟨z1, Finset.mem_singleton_self z1, Sym2.mem_mk_left _ _⟩
          have hLt := hBudgetLtCov {z1} hCov1
          rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
          by_cases hZ0 : (centreless P C).card = 0
          · have hRa := hRabove_pos_of_Z0 hZ0; omega
          · omega
        · by_cases hTB0 : TB.card = 0
          · have hCov1 : ∀ e ∈ Ustar P C, ∃ v ∈ ({z2} : Finset (Fin 10)), v ∈ e := fun e he => by
              rcases hEdge1 e he with rfl | ⟨_, _, rfl⟩ | ⟨b, hb, _⟩
              · exact ⟨z2, Finset.mem_singleton_self z2, Sym2.mem_mk_right _ _⟩
              · exact ⟨z2, Finset.mem_singleton_self z2, Sym2.mem_mk_left _ _⟩
              · have := Finset.card_pos.mpr ⟨b, hb⟩; omega
            have hLt := hBudgetLtCov {z2} hCov1
            rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
            by_cases hZ0 : (centreless P C).card = 0
            · have hRa := hRabove_pos_of_Z0 hZ0; omega
            · omega
          · have hCov2 : ∀ e ∈ Ustar P C, ∃ v ∈ ({z1, z2} : Finset (Fin 10)), v ∈ e := fun e he => by
              rcases hEdge1 e he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
              · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
              · exact ⟨z2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
              · exact ⟨z1, Finset.mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
            have hLt := hBudgetLtCov {z1, z2} hCov2
            rw [Finset.card_pair hadj12.ne, hjSet, Finset.card_singleton] at hLt
            by_cases hZ0 : (centreless P C).card = 0
            · obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < TA.card)
              obtain ⟨b1, hb1⟩ := Finset.card_pos.mp (by omega : 0 < TB.card)
              have ha1NotV : a1 ∉ validZ := fun h =>
                (Finset.mem_erase.mp (Finset.mem_filter.mp ha1).1).1
                  (Finset.mem_singleton.mp (hz1Set ▸ Finset.mem_inter.mpr ⟨h, Finset.mem_of_mem_erase (Finset.mem_filter.mp ha1).1⟩))
              have hb1NotV : b1 ∉ validZ := fun h =>
                (Finset.mem_erase.mp (Finset.mem_filter.mp hb1).1).1
                  (Finset.mem_singleton.mp (hz2Set ▸ Finset.mem_inter.mpr ⟨h, Finset.mem_of_mem_erase (Finset.mem_filter.mp hb1).1⟩))
              obtain ⟨_, t2, ht2, d2, ht2d, hSide2, hSubV2⟩ := hUstar_struct (Finset.mem_filter.mp ha1).2
              obtain ⟨_, t1, ht1, d1, ht1d, hSide1, hSubV1⟩ := hUstar_struct (Finset.mem_filter.mp hb1).2
              have hz2Side : z2 ∈ side (n := 10) C t2 (1 - d2) := hSide2.elim id (fun h => False.elim (ha1NotV (hSubV2 h)))
              have hz1Side : z1 ∈ side (n := 10) C t1 (1 - d1) := hSide1.elim id (fun h => False.elim (hb1NotV (hSubV1 h)))
              have hneD2 : (orIn 10 C (opnd C t2 d2)).Nonempty := by
                by_contra hne
                have ht2Z : t2 ∈ centreless P C := emptySide_mem_centreless ht2 (Finset.not_nonempty_iff_eq_empty.mp hne)
                have := Finset.card_pos.mpr ⟨t2, ht2Z⟩; omega
              have hneD1 : (orIn 10 C (opnd C t1 d1)).Nonempty := by
                by_contra hne
                have ht1Z : t1 ∈ centreless P C := emptySide_mem_centreless ht1 (Finset.not_nonempty_iff_eq_empty.mp hne)
                have := Finset.card_pos.mpr ⟨t1, ht1Z⟩; omega
              obtain ⟨m2, hm2R, ht2m2, hm2j, hm2ne⟩ := noncentreless_witness hjMem ht2d hneD2
              obtain ⟨m1, hm1R, ht1m1, hm1j, _⟩ := noncentreless_witness hjMem ht1d hneD1
              have hmNe : m1 ≠ m2 := by
                intro heq; subst m1
                obtain ⟨q, hq⟩ := hm2ne
                have hq2 : q ∈ side (n := 10) C t2 d2 := by rw [side_def]; exact orIn_mono ht2m2 hq
                have hq1 : q ∈ side (n := 10) C t1 d1 := by rw [side_def]; exact orIn_mono ht1m1 hq
                have hadj2q : P.Adj z2 q := (topAdj_side ht2 hq2 hz2Side).symm
                have hadj1q : P.Adj z1 q := (topAdj_side ht1 hq1 hz1Side).symm
                exact hPtri z1 z2 q hadj12 hadj2q hadj1q
              have hRa2 : 2 ≤ Rabove.card := by
                have hsub : ({m1, m2} : Finset ℕ) ⊆ Rabove := fun m hm => by
                  rcases Finset.mem_insert.mp hm with rfl | hm'
                  · exact Finset.mem_filter.mpr ⟨hm1R, hm1j⟩
                  · rw [Finset.mem_singleton.mp hm']; exact Finset.mem_filter.mpr ⟨hm2R, hm2j⟩
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_pair hmNe] at h1; exact h1
              omega
            · omega
      · exact hCase2Sym wA wB hwALt hwBLt hnaA hnaB hjVal hVA (Finset.not_nonempty_iff_eq_empty.mp hVB) hVA_le1
    · by_cases hVB : (validZ ∩ B).Nonempty
      · exact hCase2Sym wB wA hwBLt hwALt hnaB hnaA (fun x => (hjVal x).trans and_comm) hVB (Finset.not_nonempty_iff_eq_empty.mp hVA) hVB_le1
      · have hVAe : validZ ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVA
        have hVBe : validZ ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVB
        have hNotA : ∀ z ∈ validZ, z ∉ A := fun z hz h => by
          have hm : z ∈ validZ ∩ A := Finset.mem_inter.mpr ⟨hz, h⟩
          rw [hVAe] at hm; exact Finset.notMem_empty z hm
        have hNotB : ∀ z ∈ validZ, z ∉ B := fun z hz h => by
          have hm : z ∈ validZ ∩ B := Finset.mem_inter.mpr ⟨hz, h⟩
          rw [hVBe] at hm; exact Finset.notMem_empty z hm
        have hEdge3 : ∀ {u v : Fin 10}, s(u, v) ∈ Ustar P C →
            (u ∈ validZ ∧ v ∈ A ∩ B) ∨ (v ∈ validZ ∧ u ∈ A ∩ B) := by
          intro u v he
          obtain ⟨hjv, _, _, _, _, hSide, hSubV⟩ := hUstar_struct he
          obtain ⟨⟨a, haA, hpa⟩, ⟨b, hbB, hpb⟩⟩ := (hjVal _).mp hjv
          rcases hSide with huS | hvS
          · have huV := hSubV huS
            have hva : v = a := by rcases (pairInput_true u v a).mp hpa with hau | rfl; exact False.elim (hNotA u huV (hau ▸ haA)); rfl
            have hvb : v = b := by rcases (pairInput_true u v b).mp hpb with hbu | rfl; exact False.elim (hNotB u huV (hbu ▸ hbB)); rfl
            exact Or.inl ⟨huV, Finset.mem_inter.mpr ⟨hva ▸ haA, hvb ▸ hbB⟩⟩
          · have hvV := hSubV hvS
            have hua : u = a := by rcases (pairInput_true u v a).mp hpa with rfl | hav; rfl; exact False.elim (hNotA v hvV (hav ▸ haA))
            have hub : u = b := by rcases (pairInput_true u v b).mp hpb with rfl | hbv; rfl; exact False.elim (hNotB v hvV (hbv ▸ hbB))
            exact Or.inr ⟨hvV, Finset.mem_inter.mpr ⟨hua ▸ haA, hub ▸ hbB⟩⟩
        by_cases hAB0 : (A ∩ B).card = 0
        · obtain ⟨e, he⟩ := hUstarNe
          induction e using Sym2.ind with
          | _ u v =>
            rcases hEdge3 he with ⟨_, hv⟩ | ⟨_, hu⟩
            · have := Finset.card_pos.mpr ⟨v, hv⟩; omega
            · have := Finset.card_pos.mpr ⟨u, hu⟩; omega
        · by_cases hAB1 : (A ∩ B).card = 1
          · obtain ⟨w0, hw0Set⟩ := Finset.card_eq_one.mp hAB1
            have hw0A : w0 ∈ A := (Finset.mem_inter.mp (hw0Set ▸ Finset.mem_singleton_self w0)).1
            have hw0NotV : w0 ∉ validZ := fun h => hNotA w0 h hw0A
            have hCov1 : ∀ e ∈ Ustar P C, w0 ∈ e := fun e he => Sym2.ind (fun u v he' => by
              rcases hEdge3 he' with ⟨_, hv⟩ | ⟨_, hu⟩
              · have hvw : v = w0 := Finset.mem_singleton.mp (hw0Set ▸ hv); rw [hvw]; exact Sym2.mem_mk_right _ _
              · have huw : u = w0 := Finset.mem_singleton.mp (hw0Set ▸ hu); rw [huw]; exact Sym2.mem_mk_left _ _) e he
            have hLt := hBudgetLtCov {w0} (fun e he => ⟨w0, Finset.mem_singleton_self w0, hCov1 e he⟩)
            rw [Finset.card_singleton, hjSet, Finset.card_singleton] at hLt
            let TW := validZ.filter (fun z => s(w0, z) ∈ Ustar P C)
            have hTWcard : (Ustar P C).card ≤ TW.card := by
              have hsub : Ustar P C ⊆ TW.image (fun z => s(w0, z)) := fun e he => Sym2.ind (fun u v he' => by
                rcases hEdge3 he' with ⟨huV, hv⟩ | ⟨hvV, hu⟩
                · have hvw : v = w0 := Finset.mem_singleton.mp (hw0Set ▸ hv); subst v
                  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huV, Sym2.eq_swap ▸ he'⟩, Sym2.eq_swap⟩
                · have huw : u = w0 := Finset.mem_singleton.mp (hw0Set ▸ hu); subst u
                  exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvV, he'⟩, rfl⟩) e he
              exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
            let TWZ := TW.filter (fun z => z ∈ covZ)
            let TWN := TW.filter (fun z => z ∉ covZ)
            have hSplit : TW.card = TWZ.card + TWN.card := by
              have hDisjZ : Disjoint TWZ TWN := Finset.disjoint_left.mpr (fun z h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2)
              have hUnZ : TWZ ∪ TWN = TW := by
                apply Finset.ext; intro z; simp only [TWZ, TWN, Finset.mem_union, Finset.mem_filter]
                exact ⟨fun h => h.elim And.left And.left, fun h => (em (z ∈ covZ)).elim (fun hc => Or.inl ⟨h, hc⟩) (fun hc => Or.inr ⟨h, hc⟩)⟩
              rw [← hUnZ, Finset.card_union_of_disjoint hDisjZ]
            obtain ⟨RZ, hRZsub, hRZspec, hTWZ_bnd⟩ := hCovZ_bound w0 TWZ (fun z hz => by
              obtain ⟨hzTW, hzCov⟩ := Finset.mem_filter.mp hz
              have hu := (Finset.mem_filter.mp hzTW).2
              exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ hu)).1, hu, hzCov⟩)
            obtain ⟨fN, hfNspec, hfNinj⟩ := hStar_Rabove_bound w0 TWN (fun z hz => by
              obtain ⟨hzTW, hzNotCov⟩ := Finset.mem_filter.mp hz
              exact ⟨(Finset.mem_filter.mp hzTW).2, hzNotCov, hw0NotV⟩)
            have hTWN_bnd : TWN.card ≤ Rabove.card := by
              have hsub : TWN.image fN ⊆ Rabove := fun m hm => by
                obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm; exact (hfNspec z hz).1
              rw [← Finset.card_image_of_injOn hfNinj]
              exact Finset.card_le_card hsub
            have hDisj := (hRZ_disj_all RZ hRZspec).1
            have hRsum : RZ.card + Rabove.card ≤ R.card := by
              have hsub : RZ ∪ Rabove ⊆ R := Finset.union_subset hRZsub (Finset.filter_subset _ R)
              have h1 := Finset.card_le_card hsub
              rw [Finset.card_union_of_disjoint hDisj] at h1; exact h1
            omega
          · have hABge2 : 1 < (A ∩ B).card := by omega
            obtain ⟨w1, hw1, w2, hw2, hwne⟩ := Finset.one_lt_card.mp hABge2
            have hValidLe1 : validZ.card ≤ 1 := Finset.card_le_one.mpr (fun z1 hz1 z2 hz2 => by
              by_contra hne
              have hc4 := hPno4 z1 z2 hne
              have hm1 : w1 ∈ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z2 p) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValid_adjAB z1 hz1 w1 hw1, hValid_adjAB z2 hz2 w1 hw1⟩
              have hm2 : w2 ∈ Finset.univ.filter (fun p => P.Adj z1 p ∧ P.Adj z2 p) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValid_adjAB z1 hz1 w2 hw2, hValid_adjAB z2 hz2 w2 hw2⟩
              exact hwne (Finset.card_le_one.mp hc4 w1 hm1 w2 hm2))
            have hValidPos : validZ.Nonempty := by
              obtain ⟨e, he⟩ := hUstarNe
              induction e using Sym2.ind with
              | _ u v =>
                rcases hEdge3 he with ⟨huV, _⟩ | ⟨hvV, _⟩
                · exact ⟨u, huV⟩
                · exact ⟨v, hvV⟩
            have hV1 : validZ.card = 1 := by have := Finset.card_pos.mpr hValidPos; omega
            obtain ⟨z1, hz1Set⟩ := Finset.card_eq_one.mp hV1
            exact hSingletonStarContra z1 wA hwALt hnaA
              (fun e he => Sym2.ind (fun u v he' => by
                rcases hEdge3 he' with ⟨huV, _⟩ | ⟨hvV, _⟩
                · have huz : u = z1 := Finset.mem_singleton.mp (hz1Set ▸ huV); rw [huz]; exact Sym2.mem_mk_left _ _
                · have hvz : v = z1 := Finset.mem_singleton.mp (hz1Set ▸ hvV); rw [hvz]; exact Sym2.mem_mk_right _ _) e he)
              (fun u hu => by
                rcases hEdge3 hu with ⟨_, huAB⟩ | ⟨huV, hz1AB⟩
                · exact (Finset.mem_inter.mp huAB).1
                · have hz1V : z1 ∈ validZ := hz1Set ▸ Finset.mem_singleton_self z1
                  exact False.elim (hNotA z1 hz1V (Finset.mem_inter.mp hz1AB).1))
  have hZorR : 1 ≤ (centreless P C).card ∨ 1 ≤ (orN P C \ lam P C).card := by
    obtain ⟨e, he⟩ := hUstarNe
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨t, ht, _, d, j, hj, htd, _⟩ := residualTrace he
      by_cases htZ : t ∈ centreless P C
      · exact Or.inl (Finset.card_pos.mpr ⟨t, htZ⟩)
      · have hneD : (orIn 10 C (opnd C t d)).Nonempty := by
          by_contra hne
          exact htZ (emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne))
        obtain ⟨m, hmR, _, _, _⟩ := noncentreless_witness hj htd hneD
        exact Or.inr (Finset.card_pos.mpr ⟨m, hmR⟩)
  have hUstarGe3 : 3 ≤ (Ustar P C).card := by
    by_contra hlt3
    let H : SimpleGraph (Fin 10) := P.deleteEdges ↑(Ustar P C)
    let covers : Finset (Finset (Fin 10)) :=
      Finset.univ.filter (fun T : Finset (Fin 10) => ∀ u v : Fin 10, H.Adj u v → u ∈ T ∨ v ∈ T)
    have hCoversNe : covers.Nonempty :=
      ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
    obtain ⟨K0, hK0mem, hK0min⟩ := Finset.exists_min_image covers Finset.card hCoversNe
    have hK0cov : ∀ u v : Fin 10, H.Adj u v → u ∈ K0 ∨ v ∈ K0 := (Finset.mem_filter.mp hK0mem).2
    have hIsMin : IsMinCover H K0 := ⟨hK0cov, fun T' hT' => hK0min T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩
    have hK05 : 5 ≤ K0.card := by
      by_contra hKlt5
      let I : Finset (Fin 10) := Finset.univ \ K0
      have hIcard : 6 ≤ I.card := by
        have h1 : I.card = (Finset.univ : Finset (Fin 10)).card - (K0 ∩ Finset.univ).card := Finset.card_sdiff
        rw [Finset.inter_univ, Finset.card_fin] at h1; omega
      have h6_3 : ∀ m : Fin 1024, 6 ≤ (List.finRange 10).countP (fun i => m.val.testBit i.val) →
          3 ≤ pEdges.countP (fun e => m.val.testBit e.1 && m.val.testBit e.2) := by decide +kernel
      let xI : Fin 10 → Bool := fun i => decide (i ∈ I)
      let mI : Fin 1024 := ⟨toMask xI, toMask_lt xI⟩
      have hCntI : (List.finRange 10).countP (fun i => mI.val.testBit i.val) = I.card := by
        have hEqP : ∀ i : Fin 10, mI.val.testBit i.val = decide (i ∈ I) := fun i => toMask_bit xI i
        have hMap : (List.finRange 10).countP (fun i => mI.val.testBit i.val) =
            (List.finRange 10).countP (fun i => decide (i ∈ I)) := by
          congr 1; funext i; exact hEqP i
        rw [hMap, List.countP_eq_length_filter]
        have hNodup : ((List.finRange 10).filter (fun i => decide (i ∈ I))).Nodup :=
          (List.nodup_finRange 10).filter _
        have hToFin : ((List.finRange 10).filter (fun i => decide (i ∈ I))).toFinset = I := by
          apply Finset.ext; intro i
          simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        rw [← List.toFinset_card_of_nodup hNodup, hToFin]
      have h3p := h6_3 mI (by omega)
      let hitList := pEdges.filter (fun e => mI.val.testBit e.1 && mI.val.testBit e.2)
      have hHitLen : 3 ≤ hitList.length := by rw [← List.countP_eq_length_filter]; exact h3p
      have hpLt : ∀ e ∈ pEdges, e.1 < 10 ∧ e.2 < 10 ∧ e.1 ≠ e.2 := by decide
      have hpNodupSym : (pEdges.map (fun e => (min e.1 e.2, max e.1 e.2))).Nodup := by decide
      let toSym : ℕ × ℕ → Sym2 (Fin 10) := fun e =>
        if h : e.1 < 10 ∧ e.2 < 10 then s(⟨e.1, h.1⟩, ⟨e.2, h.2⟩) else s(0, 0)
      have hHitNodup : (hitList.map toSym).Nodup := by
        have hsub : hitList.Sublist pEdges := List.filter_sublist
        have hNormNd : (hitList.map (fun e => (min e.1 e.2, max e.1 e.2))).Nodup :=
          hpNodupSym.sublist (hsub.map _)
        rw [List.nodup_map_iff_inj_on (List.Nodup.of_map _ hNormNd)]
        intro e1 he1 e2 he2 heq
        have he1p := List.mem_of_mem_filter he1
        have he2p := List.mem_of_mem_filter he2
        obtain ⟨h1a, h1b, _⟩ := hpLt e1 he1p
        obtain ⟨h2a, h2b, _⟩ := hpLt e2 he2p
        dsimp only [toSym] at heq
        rw [dif_pos ⟨h1a, h1b⟩, dif_pos ⟨h2a, h2b⟩] at heq
        have hpair : (min e1.1 e1.2, max e1.1 e1.2) = (min e2.1 e2.2, max e2.1 e2.2) := by
          rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · have h1 : e1.1 = e2.1 := congrArg Fin.val ha
            have h2 : e1.2 = e2.2 := congrArg Fin.val hb
            rw [h1, h2]
          · have h1 : e1.1 = e2.2 := congrArg Fin.val ha
            have h2 : e1.2 = e2.1 := congrArg Fin.val hb
            rw [h1, h2, min_comm, max_comm]
        exact (List.nodup_map_iff_inj_on (List.Nodup.of_map _ hNormNd)).mp hNormNd e1 he1 e2 he2 hpair
      have hSubU : (hitList.map toSym).toFinset ⊆ Ustar P C := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
        have hpp := List.mem_of_mem_filter hp
        have hpb := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
        obtain ⟨h1, h2, hne⟩ := hpLt p hpp
        dsimp only [toSym]; rw [dif_pos ⟨h1, h2⟩]
        have huI : (⟨p.1, h1⟩ : Fin 10) ∈ I := decide_eq_true_eq.mp ((toMask_bit xI ⟨p.1, h1⟩).symm.trans hpb.1)
        have hvI : (⟨p.2, h2⟩ : Fin 10) ∈ I := decide_eq_true_eq.mp ((toMask_bit xI ⟨p.2, h2⟩).symm.trans hpb.2)
        have hadj : P.Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ := ⟨fun h => hne (congrArg Fin.val h), Or.inl hpp⟩
        by_contra hnotU
        have hH : H.Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, Finset.mem_coe.not.mpr hnotU⟩
        rcases hK0cov _ _ hH with huK | hvK
        · exact (Finset.mem_sdiff.mp huI).2 huK
        · exact (Finset.mem_sdiff.mp hvI).2 hvK
      have hleU := Finset.card_le_card hSubU
      rw [List.toFinset_card_of_nodup hHitNodup, List.length_map] at hleU
      omega
    have hK0B := hK0Bound K0 hIsMin
    rcases hZorR with hZ1 | hR1 <;> omega
  have hBudgetGe4 : 4 ≤ 2 * (centreless P C).card + (junk P C).card + (orN P C \ lam P C).card := by
    by_contra hlt4
    have hZ0 : (centreless P C).card = 0 := by omega
    have hJ2 : (junk P C).card = 2 := by rcases hZorR with hZ1 | hR1 <;> omega
    have hR1 : (orN P C \ lam P C).card = 1 := by rcases hZorR with hZ1 | hR1 <;> omega
    obtain ⟨m, hmSet⟩ := Finset.card_eq_one.mp hR1
    have hmR : m ∈ orN P C \ lam P C := hmSet ▸ Finset.mem_singleton_self m
    have hmN : m ∈ orN P C := (Finset.mem_sdiff.mp hmR).1
    obtain ⟨hmlen, hmop, hmnb⟩ := (orN_mem C m).mp hmN
    have hNoLamBelowM : ∀ k : ℕ, k < m → k ∈ orN P C → ∀ j' ∈ junk P C, ¬ OrReaches 10 C (10 + k) j' := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hkm hkN j' hj' hkj
        have hkLam : k ∈ lam P C := by
          by_contra hnl
          have hm' := Finset.mem_singleton.mp (hmSet ▸ Finset.mem_sdiff.mpr ⟨hkN, hnl⟩)
          omega
        obtain ⟨_, hne0, hne1, _⟩ := (lam_mem C k).mp hkLam
        obtain ⟨hklen, hkop, _⟩ := (orN_mem C k).mp hkN
        obtain ⟨_, hj'op, _⟩ := junkData hj'
        have hkj'Ne : k ≠ j' := fun h => by rw [h, hj'op] at hkop; exact GateOp.noConfusion hkop
        rcases ((orReaches_iff k j').mp hkj).2 with hEq | ⟨_, w, hwin, hwlt, hwj⟩
        · exact hkj'Ne hEq.symm
        · obtain ⟨b, rfl⟩ := inputsAsOpnd hklen hwin
          have hneb : (orIn 10 C (opnd C k b)).Nonempty := by rcases fin2_or b with rfl | rfl; exact hne0; exact hne1
          have hge10 : 10 ≤ opnd C k b := (orReaches_def C _ _ ▸ hwj).1
          let k' := opnd C k b - 10
          have hweq : opnd C k b = 10 + k' := by omega
          have hk'lt : k' < k := by omega
          rw [hweq] at hwj hneb
          have hk'len : k' < C.gates.length := by omega
          have hk'op : (gateAt C k').op = GateOp.or := by
            rcases hLeast.1.1 _ (gateAt_mem hk'len) with hand | hor
            · rw [andRawEmpty hand] at hneb; exact False.elim (Finset.not_nonempty_empty hneb)
            · exact hor
          have hk'nb : ¬ BelowF P C k' := by
            intro hkb
            apply junkNotBelow hj'
            intro x hx
            exact hkb x (orStep_up List.length_ofFn (orReaches_reach j' (10 + k') hwj).1 (gateVal_eq_val C j' x ▸ hx))
          exact ih k' hk'lt (by omega) ((orN_mem C k').mpr ⟨hk'len, hk'op, hk'nb⟩) j' hj' hwj
    have hBelowM_noJunk : ∀ w : ℕ, w < 10 + m → (orIn 10 C w).Nonempty →
        ∀ j' ∈ junk P C, ¬ OrReaches 10 C w j' := by
      intro w hw hne j' hj' hwj
      have hge10 : 10 ≤ w := (orReaches_def C w j' ▸ hwj).1
      let k := w - 10
      have hweq : w = 10 + k := by omega
      have hkm : k < m := by omega
      have hklen : k < C.gates.length := by omega
      rw [hweq] at hwj hne
      have hkop : (gateAt C k).op = GateOp.or := by
        rcases hLeast.1.1 _ (gateAt_mem hklen) with hand | hor
        · rw [andRawEmpty hand] at hne; exact False.elim (Finset.not_nonempty_empty hne)
        · exact hor
      have hknb : ¬ BelowF P C k := by
        intro hkb
        apply junkNotBelow hj'
        intro x hx
        exact hkb x (orStep_up List.length_ofFn (orReaches_reach j' (10 + k) hwj).1 (gateVal_eq_val C j' x ▸ hx))
      exact hNoLamBelowM k hkm ((orN_mem C k).mpr ⟨hklen, hkop, hknb⟩) j' hj' hwj
    have hM_unique_junk : ∃ j1 ∈ junk P C, ∃ z0 ∈ orIn 10 C (10 + m),
        j1 < m ∧ OrReaches 10 C (10 + m) j1 ∧
        ∀ j' ∈ junk P C, OrReaches 10 C (10 + m) j' → j' = j1 := by
      obtain ⟨e0, he0⟩ := hUstarNe
      induction e0 using Sym2.ind with
      | _ u0 v0 =>
        obtain ⟨t0, ht0, _, d0, j1, hj1, ht0d, _⟩ := residualTrace he0
        have hneD0 : (orIn 10 C (opnd C t0 d0)).Nonempty := by
          by_contra hne
          have ht0Z : t0 ∈ centreless P C := emptySide_mem_centreless ht0 (Finset.not_nonempty_iff_eq_empty.mp hne)
          have := Finset.card_pos.mpr ⟨t0, ht0Z⟩; omega
        obtain ⟨m0, hm0R, _, hm0j1, hm0ne⟩ := noncentreless_witness hj1 ht0d hneD0
        have hm0eq : m0 = m := Finset.mem_singleton.mp (hmSet ▸ hm0R)
        subst m0
        obtain ⟨z0, hz0⟩ := hm0ne
        have hz0U : z0 ∈ orIn 10 C (opnd C m 0) ∨ z0 ∈ orIn 10 C (opnd C m 1) :=
          Finset.mem_union.mp (orIn_or_union hmlen hmop ▸ hz0)
        obtain ⟨b0, hb0ne⟩ : ∃ b0 : Fin 2, (orIn 10 C (opnd C m b0)).Nonempty :=
          hz0U.elim (fun h => ⟨0, z0, h⟩) (fun h => ⟨1, z0, h⟩)
        have hOtherIsJ1 : ∀ j' ∈ junk P C, OrReaches 10 C (10 + m) j' → opnd C m (1 - b0) = 10 + j' := by
          intro j' hj' hmj'
          obtain ⟨_, hj'op, _⟩ := junkData hj'
          have hneM : m ≠ j' := fun h => by rw [h, hj'op] at hmop; exact GateOp.noConfusion hmop
          rcases ((orReaches_iff m j').mp hmj').2 with hEq | ⟨_, w, hwin, hwlt, hwj'⟩
          · exact False.elim (hneM hEq.symm)
          · obtain ⟨b, rfl⟩ := inputsAsOpnd hmlen hwin
            have hbne : b ≠ b0 := fun h => hBelowM_noJunk (opnd C m b0) (opndBound hmlen b0) hb0ne j' hj' (h ▸ hwj')
            have hbeq : b = 1 - b0 := fin2_ne_eq b0 b hbne
            rw [hbeq] at hwj' hwlt
            have hge10 : 10 ≤ opnd C m (1 - b0) := (orReaches_def C _ _ ▸ hwj').1
            let k := opnd C m (1 - b0) - 10
            have hweq : opnd C m (1 - b0) = 10 + k := by omega
            have hkm : k < m := by omega
            have hklen : k < C.gates.length := by omega
            rw [hweq] at hwj'
            rcases hLeast.1.1 _ (gateAt_mem hklen) with hand | hor
            · rcases ((orReaches_iff k j').mp hwj').2 with hEq | ⟨hop', _⟩
              · rw [hweq, hEq]
              · rw [hand] at hop'; exact GateOp.noConfusion hop'
            · have hknb : ¬ BelowF P C k := by
                intro hkb; apply junkNotBelow hj'; intro x hx
                exact hkb x (orStep_up List.length_ofFn (orReaches_reach j' (10 + k) hwj').1 (gateVal_eq_val C j' x ▸ hx))
              exact False.elim (hNoLamBelowM k hkm ((orN_mem C k).mpr ⟨hklen, hor, hknb⟩) j' hj' hwj')
        have heq1 := hOtherIsJ1 j1 hj1 hm0j1
        have hj1lt : j1 < m := by have := opndBound hmlen (1 - b0); omega
        refine ⟨j1, hj1, z0, hz0, hj1lt, hm0j1, fun j' hj' hmj' => ?_⟩
        have heq2 := hOtherIsJ1 j' hj' hmj'
        omega
    obtain ⟨j1, hj1, z0, hz0, hj1lt, hmj1, hMuniqJ⟩ := hM_unique_junk
    obtain ⟨hj1len, hj1op, _⟩ := junkData hj1
    let LamOrSing : Finset (Fin 10) → Prop := fun S =>
      (∃ v0 : Fin 10, S = {v0}) ∨ (∃ h ∈ lam P C, S = orIn 10 C (10 + h))
    let setsEval : Finset (Finset (Fin 10)) → (Fin 10 → Bool) → Prop := fun Fs x =>
      ∀ S ∈ Fs, ∃ v ∈ S, x v = true
    have hLamOrSing_indep : ∀ S, LamOrSing S → ∀ x ∈ S, ∀ y ∈ S, ¬ P.Adj x y := by
      intro S hS x hx y hy hadj
      rcases hS with ⟨v0, rfl⟩ | ⟨h, hh, rfl⟩
      · have hxy : x = y := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
        rw [hxy] at hadj; exact P.irrefl hadj
      · obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
        obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
        have hqs : q ∈ side (n := 10) C t (1 - d) := by rw [hq]; exact Finset.mem_singleton_self q
        have hxs : x ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth hx
        have hys : y ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono hth hy
        have hqx : P.Adj q x := (topAdj_side ht hxs hqs).symm
        have hqy : P.Adj q y := (topAdj_side ht hys hqs).symm
        exact hPtri q x y hqx hadj hqy
    have hLamOrSing_noPairU : ∀ S, LamOrSing S → ∀ u1 u2 v : Fin 10,
        u1 ≠ u2 → u1 ∈ S → u2 ∈ S → P.Adj u1 v → P.Adj u2 v → s(u1, v) ∉ Ustar P C := by
      intro S hS u1 u2 v hne hu1 hu2 ha1 ha2 hu1U
      rcases hS with ⟨v0, rfl⟩ | ⟨h, hh, rfl⟩
      · exact hne ((Finset.mem_singleton.mp hu1).trans (Finset.mem_singleton.mp hu2).symm)
      · exact hne (no_lam_two_Ustar_nbrs v {u1, u2}
          (fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact ha1.symm
            · rw [Finset.mem_singleton.mp hx']; exact ha2.symm)
          (fun x hx y hy hxy => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact Or.inl (Sym2.eq_swap ▸ hu1U)
            · rw [Finset.mem_singleton.mp hx'] at hxy
              rcases Finset.mem_insert.mp hy with rfl | hy'
              · exact Or.inr (Sym2.eq_swap ▸ hu1U)
              · exact False.elim (hxy (Finset.mem_singleton.mp hy').symm))
          h hh u1 (Finset.mem_insert_self _ _) u2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hu1 hu2)
    have hPureBelowM_val : ∀ (a : ℕ) (b : Fin 2), a < m → a < C.gates.length → (gateAt C a).op = GateOp.and →
        (∃ S : Finset (Fin 10), LamOrSing S ∧ ∀ x : Fin 10 → Bool, val C (List.ofFn x) (opnd C a b) = true ↔ ∃ v ∈ S, x v = true) ∨
        (∃ j' ∈ junk P C, j' < a ∧ opnd C a b = 10 + j') := by
      intro a b ham ha haop
      let w := opnd C a b
      have hwlt : w < 10 + a := opndBound ha b
      by_cases hw10 : w < 10
      · left
        refine ⟨{⟨w, hw10⟩}, Or.inl ⟨⟨w, hw10⟩, rfl⟩, fun x => ?_⟩
        change val C (List.ofFn x) w = true ↔ _
        have hval : val C (List.ofFn x) w = x ⟨w, hw10⟩ := val_ofFn C x ⟨w, hw10⟩
        rw [hval]
        constructor
        · intro h; exact ⟨⟨w, hw10⟩, Finset.mem_singleton_self _, h⟩
        · rintro ⟨v, hv, hxv⟩; rw [Finset.mem_singleton.mp hv] at hxv; exact hxv
      · let k := w - 10
        have hweq : w = 10 + k := by omega
        have hka : k < a := by omega
        have hklen : k < C.gates.length := by omega
        have hknb : ¬ BelowF P C k := fun hkb =>
          not_belowF_inCone_and hklen hkb ha haop ((inCone_iff k a).mpr ⟨ha, k, hka, hweq ▸ opndMem ha b, Or.inl rfl⟩)
        rcases hLeast.1.1 _ (gateAt_mem hklen) with hkand | hkor
        · right
          have hdirty : ∃ x : Fin 10 → Bool, gateVal 10 C k x = true ∧ graphFun P ∅ x = false := by
            by_contra hnone; apply hknb; intro x hx; by_contra hf; exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
          exact ⟨k, (junk_mem C k).mpr ⟨hklen, hkand, hdirty⟩, hka, hweq⟩
        · left
          have hkN : k ∈ orN P C := (orN_mem C k).mpr ⟨hklen, hkor, hknb⟩
          have hkLam : k ∈ lam P C := by
            by_contra hnl
            have hkm := Finset.mem_singleton.mp (hmSet ▸ Finset.mem_sdiff.mpr ⟨hkN, hnl⟩)
            omega
          refine ⟨orIn 10 C (10 + k), Or.inr ⟨k, hkLam, rfl⟩, fun x => ?_⟩
          change val C (List.ofFn x) w = true ↔ _
          rw [hweq]
          constructor
          · intro hv
            obtain ⟨w', hpath, hvw', hcase⟩ := or_trace List.length_ofFn (10 + k) hv
            rcases hcase with hlt | ⟨h, hh, rfl, hneOr⟩
            · refine ⟨⟨w', hlt⟩, reach_mem_orIn ⟨w', hlt⟩ hpath, ?_⟩
              rw [← val_ofFn C x ⟨w', hlt⟩]; exact hvw'
            · have hhand := (hLeast.1.1 _ (gateAt_mem hh)).resolve_right hneOr
              have hkh : OrReaches 10 C (10 + k) h := reach_orReaches hpath h rfl hh
              have hhJ : h ∈ junk P C := operandOrAndJunk ha haop (hweq ▸ hkh) hhand
              exact False.elim (hNoLamBelowM k (by omega) hkN h hhJ hkh)
          · rintro ⟨v, hv, hxv⟩
            exact reach_var_val x (10 + k) v (mem_orIn_reach v hv) hxv
    have hJ1_conj : ∃ Fs : Finset (Finset (Fin 10)), Fs.card ≤ 3 ∧
        (∀ S ∈ Fs, LamOrSing S) ∧
        (∀ x : Fin 10 → Bool, gateVal 10 C j1 x = true ↔ setsEval Fs x) := by
      have hJ2_conj : ∀ j2 ∈ junk P C, j2 < j1 →
          ∃ Fs2 : Finset (Finset (Fin 10)), Fs2.card ≤ 2 ∧
            (∀ S ∈ Fs2, LamOrSing S) ∧
            (∀ x : Fin 10 → Bool, gateVal 10 C j2 x = true ↔ setsEval Fs2 x) := by
        intro j2 hj2 hj2lt
        obtain ⟨hj2len, hj2op, _⟩ := junkData hj2
        have hNoSmaller : ∀ j' ∈ junk P C, ¬ j' < j2 := by
          intro j' hj' hlt
          have hsub : ({j', j2, j1} : Finset ℕ) ⊆ junk P C := fun g hg => by
            rcases Finset.mem_insert.mp hg with rfl | hg1
            · exact hj'
            · rcases Finset.mem_insert.mp hg1 with rfl | hg2
              · exact hj2
              · rw [Finset.mem_singleton.mp hg2]; exact hj1
          have hc := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.card_pair (by omega : j2 ≠ j1)] at hc
          omega
        rcases hPureBelowM_val j2 0 (by omega) hj2len hj2op with ⟨S0, hS0, hV0⟩ | ⟨j', hj', hlt, _⟩
        · rcases hPureBelowM_val j2 1 (by omega) hj2len hj2op with ⟨S1, hS1, hV1⟩ | ⟨j', hj', hlt, _⟩
          · refine ⟨{S0, S1}, Finset.card_le_two, fun S hS => ?_, fun x => ?_⟩
            · rcases Finset.mem_insert.mp hS with rfl | hS'
              · exact hS0
              · rw [Finset.mem_singleton.mp hS']; exact hS1
            · rw [andValBoth hj2len hj2op, hV0, hV1]
              constructor
              · intro h S hS
                rcases Finset.mem_insert.mp hS with rfl | hS'
                · exact h.1
                · rw [Finset.mem_singleton.mp hS']; exact h.2
              · intro h
                exact ⟨h S0 (Finset.mem_insert_self _ _), h S1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
          · exact False.elim (hNoSmaller j' hj' hlt)
        · exact False.elim (hNoSmaller j' hj' hlt)
      rcases hPureBelowM_val j1 0 hj1lt hj1len hj1op with ⟨S0, hS0, hV0⟩ | ⟨j2, hj2, hj2lt, h0eq⟩
      · rcases hPureBelowM_val j1 1 hj1lt hj1len hj1op with ⟨S1, hS1, hV1⟩ | ⟨j2, hj2, hj2lt, h1eq⟩
        · refine ⟨{S0, S1}, le_trans Finset.card_le_two (by omega), fun S hS => ?_, fun x => ?_⟩
          · rcases Finset.mem_insert.mp hS with rfl | hS'
            · exact hS0
            · rw [Finset.mem_singleton.mp hS']; exact hS1
          · rw [andValBoth hj1len hj1op, hV0, hV1]
            constructor
            · intro h S hS
              rcases Finset.mem_insert.mp hS with rfl | hS'
              · exact h.1
              · rw [Finset.mem_singleton.mp hS']; exact h.2
            · intro h
              exact ⟨h S0 (Finset.mem_insert_self _ _), h S1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
        · obtain ⟨Fs2, hFs2c, hFs2L, hFs2v⟩ := hJ2_conj j2 hj2 hj2lt
          refine ⟨insert S0 Fs2, le_trans (Finset.card_insert_le _ _) (by omega), fun S hS => ?_, fun x => ?_⟩
          · rcases Finset.mem_insert.mp hS with rfl | hS2
            · exact hS0
            · exact hFs2L S hS2
          · rw [andValBoth hj1len hj1op, hV0, h1eq, ← gateVal_eq_val, hFs2v]
            constructor
            · intro h S hS
              rcases Finset.mem_insert.mp hS with rfl | hS2
              · exact h.1
              · exact h.2 S hS2
            · intro h
              exact ⟨h S0 (Finset.mem_insert_self _ _), fun S hS2 => h S (Finset.mem_insert_of_mem hS2)⟩
      · obtain ⟨Fs2, hFs2c, hFs2L, hFs2v⟩ := hJ2_conj j2 hj2 hj2lt
        rcases hPureBelowM_val j1 1 hj1lt hj1len hj1op with ⟨S1, hS1, hV1⟩ | ⟨j2', hj2', hj2'lt, h1eq⟩
        · refine ⟨insert S1 Fs2, le_trans (Finset.card_insert_le _ _) (by omega), fun S hS => ?_, fun x => ?_⟩
          · rcases Finset.mem_insert.mp hS with rfl | hS2
            · exact hS1
            · exact hFs2L S hS2
          · rw [andValBoth hj1len hj1op, h0eq, ← gateVal_eq_val, hFs2v, hV1]
            constructor
            · intro h S hS
              rcases Finset.mem_insert.mp hS with rfl | hS2
              · exact h.2
              · exact h.1 S hS2
            · intro h
              exact ⟨fun S hS2 => h S (Finset.mem_insert_of_mem hS2), h S1 (Finset.mem_insert_self _ _)⟩
        · have hj2eq : j2' = j2 := by
            by_contra hne
            have hsub : ({j2', j2, j1} : Finset ℕ) ⊆ junk P C := fun g hg => by
              rcases Finset.mem_insert.mp hg with rfl | hg1
              · exact hj2'
              · rcases Finset.mem_insert.mp hg1 with rfl | hg2
                · exact hj2
                · rw [Finset.mem_singleton.mp hg2]; exact hj1
            have hc := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
              Finset.card_pair (by omega : j2 ≠ j1)] at hc
            omega
          subst j2'
          refine ⟨Fs2, by omega, hFs2L, fun x => ?_⟩
          rw [andValBoth hj1len hj1op, h0eq, h1eq, ← gateVal_eq_val, hFs2v]
          exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
    obtain ⟨Fs1, hFs1c, hFs1L, hFs1v⟩ := hJ1_conj
    have hEdgeInfo : ∀ e ∈ Ustar P C, ∃ u v : Fin 10,
        e = s(u, v) ∧ P.Adj u v ∧ P.Adj z0 v ∧ u ≠ z0 ∧
        setsEval Fs1 (pairInput u v) ∧
        (∀ x : Fin 10 → Bool, x v = true → setsEval Fs1 x → graphFun P ∅ x = true) := by
      intro e he
      induction e using Sym2.ind with
      | _ p q =>
        have hpq : P.Adj p q := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Ustar_def C ▸ he)).1
        obtain ⟨t, ht, htv, d, j', hj', htd, _⟩ := residualTrace he
        obtain ⟨htlen, htop, htb⟩ := topData ht
        have hneSide : ∀ b : Fin 2, (orIn 10 C (opnd C t b)).Nonempty := fun b => by
          by_contra hne
          have htZ : t ∈ centreless P C := emptySide_mem_centreless ht (Finset.not_nonempty_iff_eq_empty.mp hne)
          have := Finset.card_pos.mpr ⟨t, htZ⟩; omega
        obtain ⟨m0, hm0R, htm0, hm0j', _⟩ := noncentreless_witness hj' htd (hneSide d)
        have hm0eq : m0 = m := Finset.mem_singleton.mp (hmSet ▸ hm0R)
        subst m0
        have hj'eq : j' = j1 := hMuniqJ j' hj' hm0j'
        subst j'
        have h1dNoJunk : ∀ j2 ∈ junk P C, ¬ OrReaches 10 C (opnd C t (1 - d)) j2 := by
          intro j2 hj2 h1d
          obtain ⟨m2, hm2R, _, hm2j2, _⟩ := noncentreless_witness hj2 h1d (hneSide (1 - d))
          have hm2eq : m2 = m := Finset.mem_singleton.mp (hmSet ▸ hm2R)
          subst m2
          have hj2eq : j2 = j1 := hMuniqJ j2 hj2 hm2j2
          subst j2
          apply junkNotBelow hj1
          intro x hx
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j1 _ htd).1 (gateVal_eq_val C j1 x ▸ hx)
            · rw [fin2_ne_eq d idx hidx]; exact orStep_up List.length_ofFn (orReaches_reach j1 _ h1d).1 (gateVal_eq_val C j1 x ▸ hx)))
        have h1dVal : val C (List.ofFn (pairInput p q)) (opnd C t (1 - d)) = true :=
          ((andValOperands htlen htop _).mp htv) (1 - d)
        obtain ⟨v, hvSide, hvp⟩ : ∃ v ∈ side (n := 10) C t (1 - d), v = p ∨ v = q := by
          rcases operandSupport htlen htop h1dVal with h1 | ⟨j2, hj2, h1d, _⟩
          · exact h1
          · exact False.elim (h1dNoJunk j2 hj2 h1d)
        have hz0Side : z0 ∈ side (n := 10) C t d := by rw [side_def]; exact orIn_mono htm0 hz0
        have hzv : P.Adj z0 v := topAdj_side ht hz0Side hvSide
        have hStarZ0V : s(z0, v) ∈ starEdges P C := side_mem_starEdges ht hz0Side hvSide
        have hFire : ∀ x : Fin 10 → Bool, x v = true → setsEval Fs1 x → graphFun P ∅ x = true := by
          intro x hxv hxFs
          have hxj1 : gateVal 10 C j1 x = true := (hFs1v x).mpr hxFs
          exact htb x ((andValOperands htlen htop x).mpr (fun idx => by
            by_cases hidx : idx = d
            · rw [hidx]; exact orStep_up List.length_ofFn (orReaches_reach j1 _ htd).1 (gateVal_eq_val C j1 x ▸ hxj1)
            · rw [fin2_ne_eq d idx hidx]; exact sideVal hvSide hxv))
        rcases hvp with rfl | rfl
        · have hqNeZ0 : q ≠ z0 := fun h => by
            subst q; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ hStarZ0V)
          have hFsPQ : setsEval Fs1 (pairInput q v) := by
            have h1 : val C (List.ofFn (pairInput v q)) (opnd C t d) = true := ((andValOperands htlen htop _).mp htv) d
            rcases operandSupport htlen htop h1 with ⟨w, hwSide, hwp⟩ | ⟨j', hj', htd', hj'v⟩
            · exfalso
              rcases hwp with rfl | rfl
              · exact P.irrefl (topAdj_side ht hwSide hvSide)
              · rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (Sym2.eq_swap ▸ side_mem_starEdges ht hwSide hvSide)
            · obtain ⟨m', hm'R, _, hm'j', _⟩ := noncentreless_witness hj' htd' (hneSide d)
              have hm'eq : m' = m := Finset.mem_singleton.mp (hmSet ▸ hm'R)
              have hj'eq' : j' = j1 := hMuniqJ j' hj' (hm'eq ▸ hm'j')
              rw [hj'eq'] at hj'v
              exact (hFs1v _).mp (pairInput_symm v q ▸ hj'v)
          exact ⟨q, v, Sym2.eq_swap, hpq.symm, hzv, hqNeZ0, hFsPQ, hFire⟩
        · have hpNeZ0 : p ≠ z0 := fun h => by
            subst p; rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 hStarZ0V
          have hFsPQ : setsEval Fs1 (pairInput p v) := by
            have h1 : val C (List.ofFn (pairInput p v)) (opnd C t d) = true := ((andValOperands htlen htop _).mp htv) d
            rcases operandSupport htlen htop h1 with ⟨w, hwSide, hwp⟩ | ⟨j', hj', htd', hj'v⟩
            · exfalso
              rcases hwp with rfl | rfl
              · rw [Ustar_def] at he; exact (Finset.mem_sdiff.mp he).2 (side_mem_starEdges ht hwSide hvSide)
              · exact P.irrefl (topAdj_side ht hwSide hvSide)
            · obtain ⟨m', hm'R, _, hm'j', _⟩ := noncentreless_witness hj' htd' (hneSide d)
              have hm'eq : m' = m := Finset.mem_singleton.mp (hmSet ▸ hm'R)
              have hj'eq' : j' = j1 := hMuniqJ j' hj' (hm'eq ▸ hm'j')
              rw [hj'eq'] at hj'v
              exact (hFs1v _).mp hj'v
          exact ⟨p, v, rfl, hpq, hzv, hpNeZ0, hFsPQ, hFire⟩
    obtain ⟨e0, he0⟩ := Finset.card_pos.mp (by omega : 0 < (Ustar P C).card)
    have hR1card : 2 ≤ ((Ustar P C).erase e0).card := by rw [Finset.card_erase_of_mem he0]; omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.mp (by omega : 1 < ((Ustar P C).erase e0).card)
    have he1U : e1 ∈ Ustar P C := Finset.mem_of_mem_erase he1
    have he2U : e2 ∈ Ustar P C := Finset.mem_of_mem_erase he2
    have he01 : e0 ≠ e1 := (Finset.mem_erase.mp he1).1.symm
    have he02 : e0 ≠ e2 := (Finset.mem_erase.mp he2).1.symm
    obtain ⟨u0, v0, h0e, h0a, h0z, h0nz, h0fs, h0f⟩ := hEdgeInfo e0 he0
    obtain ⟨u1, v1, h1e, h1a, h1z, h1nz, h1fs, h1f⟩ := hEdgeInfo e1 he1U
    obtain ⟨u2, v2, h2e, h2a, h2z, h2nz, h2fs, h2f⟩ := hEdgeInfo e2 he2U
    let us : Fin 3 → Fin 10 := fun i => Nat.casesOn i.val u0 (fun m => Nat.casesOn m u1 (fun _ => u2))
    let vs : Fin 3 → Fin 10 := fun i => Nat.casesOn i.val v0 (fun m => Nat.casesOn m v1 (fun _ => v2))
    have hE_in_U : ∀ i : Fin 3, s(us i, vs i) ∈ Ustar P C := by
      intro i; rcases fin3_or i with rfl | rfl | rfl
      · exact h0e ▸ he0
      · exact h1e ▸ he1U
      · exact h2e ▸ he2U
    have hE_ne : ∀ i k : Fin 3, i ≠ k → s(us i, vs i) ≠ s(us k, vs k) := by
      intro i k hik
      rcases fin3_or i with rfl | rfl | rfl <;> rcases fin3_or k with rfl | rfl | rfl
      · exact False.elim (hik rfl)
      · exact h0e ▸ h1e ▸ he01
      · exact h0e ▸ h2e ▸ he02
      · exact h0e ▸ h1e ▸ he01.symm
      · exact False.elim (hik rfl)
      · exact h1e ▸ h2e ▸ he12
      · exact h0e ▸ h2e ▸ he02.symm
      · exact h1e ▸ h2e ▸ he12.symm
      · exact False.elim (hik rfl)
    have hAdj_uv : ∀ i : Fin 3, P.Adj (us i) (vs i) := by intro i; rcases fin3_or i with rfl | rfl | rfl; exact h0a; exact h1a; exact h2a
    have hAdj_zv : ∀ i : Fin 3, P.Adj z0 (vs i) := by intro i; rcases fin3_or i with rfl | rfl | rfl; exact h0z; exact h1z; exact h2z
    have hNe_uz : ∀ i : Fin 3, us i ≠ z0 := by intro i; rcases fin3_or i with rfl | rfl | rfl; exact h0nz; exact h1nz; exact h2nz
    have hFs_uv : ∀ i : Fin 3, setsEval Fs1 (pairInput (us i) (vs i)) := by intro i; rcases fin3_or i with rfl | rfl | rfl; exact h0fs; exact h1fs; exact h2fs
    have hFire_v : ∀ i : Fin 3, ∀ x : Fin 10 → Bool, x (vs i) = true → setsEval Fs1 x → graphFun P ∅ x = true := by
      intro i; rcases fin3_or i with rfl | rfl | rfl; exact h0f; exact h1f; exact h2f
    have hPigeon : ∀ (us vs : Fin 3 → Fin 10),
        (∀ i : Fin 3, s(us i, vs i) ∈ Ustar P C) →
        (∀ i k : Fin 3, i ≠ k → s(us i, vs i) ≠ s(us k, vs k)) →
        (∀ i : Fin 3, P.Adj (us i) (vs i)) →
        (∀ i : Fin 3, P.Adj z0 (vs i)) →
        (∀ i : Fin 3, us i ≠ z0) →
        (∀ i : Fin 3, setsEval Fs1 (pairInput (us i) (vs i))) →
        (∀ i : Fin 3, ∀ x : Fin 10 → Bool, x (vs i) = true → setsEval Fs1 x → graphFun P ∅ x = true) →
        False := by
      intro us vs hE_in_U hE_ne hAdj_uv hAdj_zv hNe_uz hFs_uv hFire_v
      classical
      have hv_inj : ∀ i k : Fin 3, i ≠ k → vs i ≠ vs k := by
        intro i k hik hveq
        have hune : us i ≠ us k := fun h => hE_ne i k hik (by rw [h, hveq])
        have hSame : setsEval Fs1 (pairInput (vs i) (vs i)) := by
          intro S hS
          obtain ⟨a, haS, hap⟩ := hFs_uv i S hS
          obtain ⟨b, hbS, hbp⟩ := hFs_uv k S hS
          rcases (pairInput_true (us i) (vs i) a).mp hap with rfl | rfl
          · rcases (pairInput_true (us k) (vs k) b).mp hbp with rfl | rfl
            · exact False.elim (hLamOrSing_noPairU S (hFs1L S hS) (us i) (us k) (vs i) hune haS hbS
                (hAdj_uv i) (hveq ▸ hAdj_uv k) (hE_in_U i))
            · exact ⟨vs i, hveq ▸ hbS, pairInput_left _ _⟩
          · exact ⟨vs i, haS, pairInput_left _ _⟩
        exact P.irrefl ((graphFun_pair (vs i) (vs i)).mp (hFire_v i (pairInput (vs i) (vs i)) (pairInput_left _ _) hSame))
      have hCrossNonAdj : ∀ i k : Fin 3, i ≠ k → ¬ P.Adj (us i) (vs k) := by
        intro i k hik hadj
        have hc4 := hPno4 (us i) z0 (hNe_uz i)
        have hm1 : vs i ∈ Finset.univ.filter (fun p : Fin 10 => P.Adj (us i) p ∧ P.Adj z0 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj_uv i, hAdj_zv i⟩
        have hm2 : vs k ∈ Finset.univ.filter (fun p : Fin 10 => P.Adj (us i) p ∧ P.Adj z0 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, hAdj_zv k⟩
        exact hv_inj i k hik (Finset.card_le_one.mp hc4 (vs i) hm1 (vs k) hm2)
      let xV : Fin 10 → Bool := fun w => decide (w = vs 0 ∨ w = vs 1 ∨ w = vs 2)
      have hxV_false : graphFun P ∅ xV = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        obtain ⟨a, b, hab, hxa, hxb⟩ := (hP_hasEdge xV).mp ht
        have ha : a = vs 0 ∨ a = vs 1 ∨ a = vs 2 := decide_eq_true_eq.mp hxa
        have hb : b = vs 0 ∨ b = vs 1 ∨ b = vs 2 := decide_eq_true_eq.mp hxb
        have hzv_of : ∀ w, (w = vs 0 ∨ w = vs 1 ∨ w = vs 2) → P.Adj z0 w := by
          intro w hw
          rcases hw with rfl | rfl | rfl
          · exact hAdj_zv 0
          · exact hAdj_zv 1
          · exact hAdj_zv 2
        exact hPtri z0 a b (hzv_of a ha) hab (hzv_of b hb)
      have hNotFsV : ¬ setsEval Fs1 xV := by
        intro hfs
        have ht := hFire_v 0 xV (decide_eq_true (Or.inl rfl)) hfs
        rw [hxV_false] at ht; exact Bool.noConfusion ht
      obtain ⟨S0, hS0mem, hS0miss⟩ : ∃ S0 ∈ Fs1, ∀ w ∈ S0, xV w = false := by
        by_contra hno
        apply hNotFsV
        intro S hS
        by_contra hnone
        apply hno
        refine ⟨S, hS, fun w hw => Bool.eq_false_iff.mpr (fun ht => hnone ⟨w, hw, ht⟩)⟩
      have hS0_has_all_u : ∀ i : Fin 3, us i ∈ S0 := by
        intro i
        obtain ⟨w, hwS0, hwp⟩ := hFs_uv i S0 hS0mem
        rcases (pairInput_true (us i) (vs i) w).mp hwp with rfl | rfl
        · exact hwS0
        · have htrue : xV (vs i) = true := by
            rcases fin3_or i with rfl | rfl | rfl
            · exact decide_eq_true (Or.inl rfl)
            · exact decide_eq_true (Or.inr (Or.inl rfl))
            · exact decide_eq_true (Or.inr (Or.inr rfl))
          exact False.elim (Bool.noConfusion ((hS0miss (vs i) hwS0).symm.trans htrue))
      let pairs6 : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2)
      have hPairs6Ne : ∀ p ∈ pairs6, p.1 ≠ p.2 := fun _ hp => (Finset.mem_filter.mp hp).2
      have hPairs6Card : pairs6.card = 6 := by
        have hdiag : (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = p.2)) =
            (Finset.univ : Finset (Fin 3)).image (fun i => (i, i)) := by
          apply Finset.ext; intro p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨fun h => ⟨p.1, Prod.ext rfl h⟩, fun h => by obtain ⟨i, hi⟩ := h; rw [← hi]⟩
        have hdisj : Disjoint pairs6 (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = p.2)) :=
          Finset.disjoint_left.mpr (fun _ h1 h2 => (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
        have hun : pairs6 ∪ Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = p.2) = Finset.univ := by
          apply Finset.ext; intro p
          simp only [pairs6, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
          exact ⟨fun _ => trivial, fun _ => (em (p.1 = p.2)).symm⟩
        have hsum : pairs6.card + (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = p.2)).card =
            (Finset.univ : Finset (Fin 3 × Fin 3)).card := by
          rw [← Finset.card_union_of_disjoint hdisj, hun]
        have hdiagCard : (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = p.2)).card = 3 := by
          rw [hdiag, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_fin]
        have hunivCard : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        omega
      let blk : Finset (Fin 10) → Finset (Fin 3 × Fin 3) := fun S =>
        (Finset.univ.filter (fun i : Fin 3 => us i ∉ S)) ×ˢ (Finset.univ.filter (fun k : Fin 3 => vs k ∉ S))
      have hPairs6Sub : pairs6 ⊆ (Fs1.erase S0).biUnion blk := by
        intro p hp
        have hne : p.1 ≠ p.2 := hPairs6Ne p hp
        have hNotFs : ¬ setsEval Fs1 (pairInput (us p.1) (vs p.2)) := fun hfs =>
          hCrossNonAdj p.1 p.2 hne ((graphFun_pair _ _).mp (hFire_v p.2 _ (pairInput_right _ _) hfs))
        obtain ⟨S, hSm, hSmiss⟩ : ∃ S ∈ Fs1, ∀ w ∈ S, pairInput (us p.1) (vs p.2) w = false := by
          by_contra hno; apply hNotFs; intro S hS; by_contra hnone
          exact hno ⟨S, hS, fun w hw => Bool.eq_false_iff.mpr (fun ht => hnone ⟨w, hw, ht⟩)⟩
        have hSnotU : us p.1 ∉ S := fun h => Bool.noConfusion ((hSmiss _ h).symm.trans (pairInput_left _ _))
        have hSnotV : vs p.2 ∉ S := fun h => Bool.noConfusion ((hSmiss _ h).symm.trans (pairInput_right _ _))
        have hSne : S ≠ S0 := fun h => hSnotU (h ▸ hS0_has_all_u p.1)
        exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_erase.mpr ⟨hSne, hSm⟩,
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSnotU⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSnotV⟩⟩⟩
      have hBlockLe2 : ∀ S ∈ Fs1.erase S0, (blk S).card ≤ 2 := by
        intro S hS
        have hSm : S ∈ Fs1 := Finset.mem_of_mem_erase hS
        let US := Finset.univ.filter (fun i : Fin 3 => us i ∈ S)
        have hVnotEq : Finset.univ.filter (fun k : Fin 3 => vs k ∉ S) = US := by
          apply Finset.ext; intro k
          simp only [US, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hvn
            obtain ⟨w, hwS, hwp⟩ := hFs_uv k S hSm
            rcases (pairInput_true (us k) (vs k) w).mp hwp with rfl | rfl
            · exact hwS
            · exact False.elim (hvn hwS)
          · intro huk hvk
            exact hLamOrSing_indep S (hFs1L S hSm) (us k) huk (vs k) hvk (hAdj_uv k)
        have hUnotEq : Finset.univ.filter (fun i : Fin 3 => us i ∉ S) = Finset.univ \ US := by
          apply Finset.ext; intro i
          simp only [US, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        dsimp only [blk]
        rw [Finset.card_product, hVnotEq, hUnotEq, Finset.card_sdiff, Finset.inter_univ, Finset.card_fin]
        have hle3 : US.card ≤ 3 := by
          have := Finset.card_le_card (Finset.subset_univ US); rw [Finset.card_fin] at this; exact this
        have hmul : ∀ n : ℕ, n ≤ 3 → (3 - n) * n ≤ 2 := by
          intro n hn
          cases n with
          | zero => omega
          | succ n1 =>
            cases n1 with
            | zero => omega
            | succ n2 =>
              cases n2 with
              | zero => omega
              | succ n3 =>
                cases n3 with
                | zero => omega
                | succ _ => omega
        exact hmul US.card hle3
      have hCard6 := Finset.card_le_card hPairs6Sub
      have hBiU := Finset.card_biUnion_le (s := Fs1.erase S0) (t := blk)
      have hSum2 : (Fs1.erase S0).sum (fun S => (blk S).card) ≤
          (Fs1.erase S0).sum (fun _ => 2) := Finset.sum_le_sum hBlockLe2
      rw [Finset.sum_const, smul_eq_mul] at hSum2
      have hEraseLe2 : (Fs1.erase S0).card ≤ 2 := by rw [Finset.card_erase_of_mem hS0mem]; omega
      omega
    exact hPigeon us vs hE_in_U hE_ne hAdj_uv hAdj_zv hNe_uz hFs_uv hFire_v
  exact hResidual C hLeast hTop hCsize18 hCsize19 hJunkGe2 hUstarGe3 hBudgetGe4 hFanBound hK0Bound hBudgetLtCov
