import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Remove the output gate. Redundant pins and unused suffixes give the smaller circuit.
-- At a proper OR each pin has a private edge. At a proper AND each pin has a
-- private maximal negative. Dirtiness also has a maximal negative witness.
set_option maxHeartbeats 3600000 in
theorem PEqualNP.Outside.R_meta_5208_628
    (small : ∀ D : Circuit,
      let S : Finset (Fin 13) := {0,1,3,9}
      IsAO2 26 D → (∀ g ∈ D.gates, g.inputs.Nodup) → D.size ≤ 63 →
      (∃ k < D.gates.length, (gateAt D k).op = .and ∧ gateVal 26 D k (pairInput 0 13) = true ∧
        ∀ b : Fin 2, wireVal 26 D (opnd D k b) (pairInput 0 0) = false) →
      ∃ z : Fin 26 → Bool, ¬ (D.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
        p-l ∈ S ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true))
    (lower : ∀ (gs : List Gate) (u v : ℕ),
      let C : Circuit := ⟨gs ++ [⟨.or,[u,v]⟩],26+gs.length⟩
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        (p-l)^4 = p-l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let w := wireVal 26 C
      let cone := InCone 26 C
      let bad := fun (k : ℕ) (s : Fin 26) => (gateAt C k).op = .and ∧
        (k = gs.length ∨ cone k gs.length) ∧ w (26+k) (pairInput 0 13) = true ∧
        ∀ b : Fin 2, w (opnd C k b) (pairInput s s) = false
      gs.length = 63 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∃ d < gs.length, (gateAt C d).op = .and ∧
        ∃ z, Maximal (fun x => ¬ F x) z ∧ w (26+d) z = true) →
      (∃ i j, cone i j ∧ bad i 0 ∧ bad j 13) →
      (∀ z, Minimal F z → (w u z || w v z) = true) →
      (∀ z, Maximal (fun x => ¬ F x) z → w u z = false ∧ w v z = false) →
      (∀ b : Bool, ∃ z, Minimal F z ∧ w u z = b ∧ w v z = !b) → False)
    (upper : ∀ (gs : List Gate) (u v : ℕ),
      let C : Circuit := ⟨gs ++ [⟨.and,[u,v]⟩],26+gs.length⟩
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        (p-l)^4 = p-l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let w := wireVal 26 C
      let cone := InCone 26 C
      let bad := fun (k : ℕ) (s : Fin 26) => (gateAt C k).op = .and ∧
        (k = gs.length ∨ cone k gs.length) ∧ w (26+k) (pairInput 0 13) = true ∧
        ∀ b : Fin 2, w (opnd C k b) (pairInput s s) = false
      gs.length = 63 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∃ d < gs.length, (gateAt C d).op = .and ∧
        ∃ z, Maximal (fun x => ¬ F x) z ∧ w (26+d) z = true) →
      (∃ i j, cone i j ∧ bad i 0 ∧ bad j 13) →
      (∀ z, Minimal F z → w u z = true ∧ w v z = true) →
      (∀ z, Maximal (fun x => ¬ F x) z → (w u z && w v z) = false) →
      (∀ b : Bool, ∃ z, Maximal (fun x => ¬ F x) z ∧ w u z = b ∧ w v z = !b) → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x4 x10 x11 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  classical
  let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  -- The four cyclic differences are exactly the roots of t^4 = t modulo thirteen.
  have cyclic (t : Fin 13) : t^4 = t ↔ t ∈ ({0,1,3,9} : Finset (Fin 13)) :=
    (show ∀ d : Fin 13, d^4 = d ↔ d ∈ ({0,1,3,9} : Finset (Fin 13)) from by decide) t
  rintro ⟨C, hs, hgates, hf, dirty, chain⟩
  change ∀ x, C.eval (List.ofFn x) = true ↔ F x at hf
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have hgateFacts (g : PEqualNP.CircuitLowerBounds.Gate) (hm : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨hop, u, v, hargs, hne, _, _⟩ := hgates k g hk
    exact ⟨hop, by simp [hargs], by simp [hargs, hne]⟩
  have hshape : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hm => (hgateFacts g hm).1, ?_, fun g hm => (hgateFacts g hm).2.1⟩
    intro k hk w hw
    have hgate : C.gates[k]? = some C.gates[k] := by simp [hk]
    obtain ⟨_, u, v, hargs, _, hu, hv⟩ := hgates k C.gates[k] hgate
    change w ∈ (C.gates.getD k ⟨.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem _ _ hk, hargs] at hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  have hdistinct : ∀ g ∈ C.gates, g.inputs.Nodup := fun g hm => (hgateFacts g hm).2.2
  let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true
  -- Wire monotonicity follows the gate induction in LowMergeWires.
  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      op.eval (l.map f) = true → op.eval (l.map f') = true := by
    rcases hop with rfl | rfl
    · change (l.map f).all id = true → (l.map f').all id = true
      simp only [List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i (H (f i) ⟨i, hi, rfl⟩)
    · change (l.map f).any id = true → (l.map f').any id = true
      simp only [List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

  have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ a b : List Bool, a.length = b.length → LeL a b →
        LeL (gs.foldl wstep a) (gs.foldl wstep b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [wstep, hl]
      · intro i hi
        unfold wstep at hi ⊢
        by_cases hia : i < a.length
        · rw [List.getD_append _ _ _ _ hia] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega)]
          rw [← hl]
          by_cases he : i - a.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
          · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
            rw [hm] at hi; simp at hi
  have rise (i : ℕ) {x y : Fin 26 → Bool} (h : x ≤ y) :
      wireVal 26 C i x = true → wireVal 26 C i y = true := by
    apply fold_mono C.gates hshape.1 _ _ (by simp) _ i
    intro j hj
    by_cases hlt : j < 26
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hj ⊢
      simp only [List.getElem_ofFn] at hj ⊢
      exact Bool.le_iff_imp.mp (h ⟨j,hlt⟩) hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      contradiction
  -- The cone recurrence follows the parent reduction R_meta_2071_319. It places the inner
  -- marked gate strictly before the outer one, so deleting the last gate preserves it.
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g rest ih =>
      intro cs
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + rest.length = cs.length + (g :: rest).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (r : ℕ),
      r < cs.length → (gs.foldl (coneStep 26) cs).getD r [] = cs.getD r [] := by
    intro gs
    induction gs with
    | nil => intro cs r _; rfl
    | cons g rest ih =>
      intro cs r hr
      simp only [List.foldl_cons]
      have hr' : r < (coneStep 26 cs g).length := by
        change r < (cs ++ [_]).length
        simp only [List.length_append, List.length_singleton]; omega
      rw [ih (coneStep 26 cs g) r hr']
      change (cs ++ [_]).getD r [] = cs.getD r []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have inCone_iff : ∀ (D : Circuit) (i j : ℕ),
      InCone 26 D i j ↔ j < D.gates.length ∧
        ∃ w ∈ (gateAt D j).inputs, 26 ≤ w ∧ w < 26 + j ∧
          (i = w - 26 ∨ InCone 26 D i (w - 26)) := by
    intro D i j
    unfold InCone cones
    by_cases hj : j < D.gates.length
    · have hsplit : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j D.gates
        have h2 := List.cons_getElem_drop_succ (l := D.gates) (n := j) (h := hj)
        rw [h2]; exact h1.symm
      have hlen_pre : ((D.gates.take j).foldl (coneStep 26) []).length = j := by
        rw [cones_len, List.length_nil, Nat.zero_add, List.length_take]; omega
      have hpre_cone : ∀ m, m < j →
          (D.gates.foldl (coneStep 26) []).getD m [] =
            ((D.gates.take j).foldl (coneStep 26) []).getD m [] := by
        intro m hm
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, cones_getD_lt _ _ m (by omega)]
      have hgateAt : gateAt D j = D.gates[j] := by
        change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]
        rw [List.getD_eq_getElem _ _ hj]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      have hlen_mid : (coneStep 26 ((D.gates.take j).foldl (coneStep 26) []) D.gates[j]).length = j + 1 := by
        change (((D.gates.take j).foldl (coneStep 26) []) ++ [_]).length = j + 1
        simp only [List.length_append, List.length_singleton, hlen_pre]
      rw [cones_getD_lt _ _ j (by omega)]
      have hmid_val : (coneStep 26 ((D.gates.take j).foldl (coneStep 26) []) D.gates[j]).getD j [] =
          ((D.gates[j].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + j))).flatMap
            (fun w => (w - 26) :: ((D.gates.take j).foldl (coneStep 26) []).getD (w - 26) [])) := by
        generalize hpre_def : (D.gates.take j).foldl (coneStep 26) [] = pre at hlen_pre ⊢
        change (pre ++ [((D.gates[j].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + pre.length))).flatMap
          (fun w => (w - 26) :: pre.getD (w - 26) []))]).getD j [] = _
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [hlen_pre])]
        simp only [hlen_pre, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hmid_val]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq, hgateAt]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨hj, w, hw, h1, h2, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · right
          rw [hpre_cone (w - 26) (by omega)]
          exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · right
          rw [← hpre_cone (w - 26) (by omega)]
          exact h3
    · have hlen : (D.gates.foldl (coneStep 26) []).length = D.gates.length := by
        rw [cones_len]; simp
      have hnone : (D.gates.foldl (coneStep 26) []).getD j [] = [] :=
        List.getD_eq_default _ _ (by omega)
      rw [hnone]
      simp [hj]
  have coneLT (i j : ℕ) (h : InCone 26 C i j) : i < j := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      obtain ⟨_,w,_,low,high,dep⟩ := (inCone_iff C i j).mp h
      rcases dep with rfl | dep
      · omega
      · exact lt_trans (ih (w-26) (by omega) dep) (by omega)
  have copy := chain
  obtain ⟨inner,outer,rel,innerTag,_⟩ := copy
  have ltOuter := coneLT inner outer rel
  have outerBound := ((inCone_iff C inner outer).mp rel).1
  have innerBound := lt_trans ltOuter outerBound
  let Core (D : Circuit) := ∃ k < D.gates.length, (gateAt D k).op = .and ∧
    gateVal 26 D k (pairInput 0 13) = true ∧
    ∀ b : Fin 2, wireVal 26 D (opnd D k b) (pairInput 0 0) = false
  have core : Core C := ⟨inner,innerBound,innerTag.1,innerTag.2.2⟩
  have size : C.gates.length = 64 := by
    by_contra h
    have bound : C.size ≤ 63 := by change C.gates.length ≤ 64 at hs; change C.gates.length ≤ 63; omega
    obtain ⟨x,hx⟩ := small C hshape hdistinct bound core
    exact hx (hf x)
  have ne : C.gates ≠ [] := fun h => by simp [h] at size
  let gs := C.gates.dropLast
  let g := C.gates.getLast ne
  have splitList : C.gates = gs ++ [g] := (List.dropLast_append_getLast ne).symm
  have gl : gs.length = 63 := by rw [splitList] at size; simp at size; omega
  have runSplit (x : Fin 26 → Bool) :
      C.wires (List.ofFn x) = wstep (gs.foldl wstep (List.ofFn x)) g := by
    change C.gates.foldl wstep (List.ofFn x) = _
    rw [splitList, List.foldl_append]; rfl
  have len (x : Fin 26 → Bool) : (gs.foldl wstep (List.ofFn x)).length = 26 + gs.length := by
    rw [wfold_len]; simp
  have prefixMem (g' : Gate) (hg' : g' ∈ gs) : g' ∈ C.gates := by
    rw [splitList]; exact List.mem_append_left _ hg'
  have prefixShape (o : ℕ) : IsAO2 26 (⟨gs,o⟩ : Circuit) := by
    refine ⟨fun g' hg' => hshape.1 g' (prefixMem g' hg'),?_,
      fun g' hg' => hshape.2.2 g' (prefixMem g' hg')⟩
    intro k hk w hw
    apply hshape.2.1 k (by change k < gs.length at hk; omega) w
    change w ∈ (C.gates.getD k ⟨.or,[]⟩).inputs
    rw [splitList,List.getD_append _ _ _ _ hk]
    exact hw
  have old (i : ℕ) (hi : i < 26+gs.length) (x : Fin 26 → Bool) :
      wireVal 26 C i x = (⟨gs,i⟩ : Circuit).eval (List.ofFn x) := by
    unfold wireVal
    rw [runSplit]
    exact List.getD_append _ _ _ _ (by rw [len]; exact hi)
  have prefixCounter (o : ℕ) : ∃ z, ¬ ((⟨gs,o⟩ : Circuit).eval (List.ofFn z) = true ↔ F z) := by
    apply small ⟨gs,o⟩ (prefixShape o) (fun g' hg' => hdistinct g' (prefixMem _ hg'))
      (by change gs.length ≤ 63; omega)
    have inside : inner < gs.length := by omega
    have ge : gateAt (⟨gs,o⟩ : Circuit) inner = gateAt C inner := by
      change gs.getD inner ⟨.or,[]⟩ = C.gates.getD inner ⟨.or,[]⟩
      rw [splitList,List.getD_append _ _ _ _ inside]
    refine ⟨inner,inside,ge ▸ innerTag.1,?_,?_⟩
    · change (⟨gs,26+inner⟩ : Circuit).eval _ = true
      rw [← old _ (by omega)]
      exact innerTag.2.2.1
    · intro b
      have atGate : gateAt C inner = C.gates[inner] := List.getD_eq_getElem _ _ innerBound
      have blt : (b : ℕ) < (gateAt C inner).inputs.length := by
        rw [atGate,hshape.2.2 _ (List.getElem_mem _)]; exact b.isLt
      have earlier : opnd C inner b < 26+inner := by
        apply hshape.2.1 inner innerBound
        change (gateAt C inner).inputs.getD (b : ℕ) 0 ∈ (gateAt C inner).inputs
        rw [List.getD_eq_getElem _ _ blt]; exact List.getElem_mem _
      have same : opnd (⟨gs,o⟩ : Circuit) inner b = opnd C inner b :=
        congrArg (fun (q : Gate) => q.inputs.getD (b : ℕ) 0) ge
      change (⟨gs,opnd (⟨gs,o⟩ : Circuit) inner b⟩ : Circuit).eval _ = false
      rw [same,← old _ (by omega)]
      exact innerTag.2.2.2 b
  have root : C.output = 26+gs.length := by
    have under : C.output < 26+gs.length+1 := by
      by_contra! hu
      let z : Fin 26 → Bool := fun _ => true
      have hz : F z := ⟨0,0,by decide,rfl,rfl⟩
      have e := (hf z).mpr hz
      unfold Circuit.eval at e
      have totalLen : (C.wires (List.ofFn z)).length = 26+gs.length+1 := by
        rw [runSplit]; simp only [wstep,List.length_append,List.length_singleton,len]
      rw [List.getD_eq_default _ _ (totalLen ▸ hu)] at e
      contradiction
    by_contra ho
    have before : C.output < 26+gs.length := by omega
    obtain ⟨z,hz⟩ := prefixCounter C.output
    apply hz
    rw [← old _ before]
    exact hf z
  have lastGet : C.gates[gs.length]? = some g := by
    rw [splitList]; simp
  obtain ⟨hop,u,v,pins,uv,hu,hv⟩ := hgates _ _ lastGet
  let W := wireVal 26 C
  have pinNot (i : ℕ) (hi : i < 26+gs.length) : ∃ z, ¬ (W i z = true ↔ F z) := by
    obtain ⟨z,hz⟩ := prefixCounter i
    refine ⟨z,?_⟩
    change ¬ (wireVal 26 C i z = true ↔ F z)
    rw [old i hi]
    exact hz
  have pinEval (z : Fin 26 → Bool) :
      C.eval (List.ofFn z) = g.op.eval [W u z,W v z] := by
    unfold Circuit.eval
    rw [root,runSplit,show 26+gs.length = (gs.foldl wstep (List.ofFn z)).length from (len z).symm]
    unfold wstep
    rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,pins]
    change g.op.eval [((⟨gs,u⟩ : Circuit).eval (List.ofFn z)),((⟨gs,v⟩ : Circuit).eval (List.ofFn z))] = _
    rw [← old u hu, ← old v hv]
  have dmax : ∃ d < gs.length, (gateAt C d).op = .and ∧
      ∃ z, Maximal (fun x => ¬ F x) z ∧ W (26+d) z = true := by
    obtain ⟨d,hd,hop',x,hx,hout⟩ := dirty
    have dx : W (26+d) x = true := hx
    have dh : d < gs.length := by
      rw [splitList] at hd
      simp only [List.length_append,List.length_singleton] at hd
      by_contra! h
      have ed : d = gs.length := by omega
      have i : 26+d = C.output := by omega
      change wireVal 26 C (26+d) x = true at dx
      rw [i] at dx
      exact Bool.noConfusion (hout.symm.trans dx)
    have nx : ¬ F x := fun h => Bool.noConfusion (hout.symm.trans ((hf x).mpr h))
    obtain ⟨z,xz,hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬ F y) x nx
    exact ⟨d,dh,hop',z,hz,rise _ xz dx⟩
  let bad := fun (k : ℕ) (s : Fin 26) => (gateAt C k).op = .and ∧
    (k = gs.length ∨ InCone 26 C k gs.length) ∧ W (26+k) (pairInput 0 13) = true ∧
    ∀ b : Fin 2, W (opnd C k b) (pairInput s s) = false
  have tags : ∃ i j, InCone 26 C i j ∧ bad i 0 ∧ bad j 13 := by
    obtain ⟨i,j,ic,bp,bl⟩ := chain
    refine ⟨i,j,ic,⟨bp.1,?_,bp.2.2⟩,⟨bl.1,?_,bl.2.2⟩⟩
    · simpa [root] using bp.2.1
    · simpa [root] using bl.2.1
  have whole (op : GateOp) (ho : g.op = op) :
      C = ⟨gs ++ [⟨op,[u,v]⟩],26+gs.length⟩ := by
    have ge : g = ⟨op,[u,v]⟩ := congrArg₂ Gate.mk ho pins
    exact congrArg₂ Circuit.mk (splitList.trans (by rw [ge])) root
  rcases hop with isAnd | isOr
  · have correct (x : Fin 26 → Bool) : (W u x && W v x) = true ↔ F x := by
      have e := hf x
      rw [pinEval,isAnd,eval_and] at e
      exact e
    have exclusive (i j : ℕ) (hi : i < 26+gs.length)
        (joint : ∀ x, (W i x && W j x) = true ↔ F x) :
        ∃ z, Maximal (fun x => ¬ F x) z ∧ W i z = true ∧ W j z = false := by
      obtain ⟨x,hx⟩ := pinNot i hi
      have nx : ¬ F x := fun fx => hx ⟨fun _ => fx,fun _ => (Bool.and_eq_true_iff.mp ((joint x).mpr fx)).1⟩
      have ix : W i x = true := by
        cases e : W i x with
        | true => rfl
        | false => exact False.elim (hx ⟨fun h => by simp [e] at h,fun f => (nx f).elim⟩)
      obtain ⟨z,xz,hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬ F y) x nx
      have iz := rise i xz ix
      change W i z = true at iz
      refine ⟨z,hz,iz,?_⟩
      cases e : W j z with
      | false => rfl
      | true => exact False.elim (hz.prop ((joint z).mp (by simp [iz,e])))
    have h := upper gs u v
    dsimp only at h
    simp only [cyclic] at h
    rw [← whole .and isAnd] at h
    have lastEq : g = ⟨.and,[u,v]⟩ := congrArg₂ Gate.mk isAnd pins
    refine h gl hshape (by simpa only [splitList,lastEq] using hdistinct)
      dmax tags ?_ ?_ ?_
    · intro z hz
      exact Bool.and_eq_true_iff.mp ((correct z).mpr hz.prop)
    · intro z hz
      cases e : W u z && W v z with
      | false => rfl
      | true => exact False.elim (hz.prop ((correct z).mp e))
    · intro b
      cases b with
      | false =>
        obtain ⟨z,hz,hv',hu'⟩ := exclusive v u hv (fun x => by simpa only [Bool.and_comm] using correct x)
        exact ⟨z,hz,hu',hv'⟩
      | true => exact exclusive u v hu correct
  · have correct (x : Fin 26 → Bool) : (W u x || W v x) = true ↔ F x := by
      have e := hf x
      rw [pinEval,isOr,eval_or] at e
      exact e
    have exclusive (i j : ℕ) (hi : i < 26+gs.length)
        (joint : ∀ x, (W i x || W j x) = true ↔ F x) :
        ∃ z, Minimal F z ∧ W i z = false ∧ W j z = true := by
      obtain ⟨x,hx⟩ := pinNot i hi
      have fx : F x := by
        by_contra nx
        exact hx ⟨fun h => (joint x).mp (by simp [h]),fun f => (nx f).elim⟩
      have ni : W i x ≠ true := fun h => hx ⟨fun _ => fx,fun _ => h⟩
      obtain ⟨z,zx,hz⟩ := exists_minimal_le_of_wellFoundedLT F x fx
      have iz : W i z = false := by
        cases e : W i z with
        | false => rfl
        | true => exact False.elim (ni (rise i zx e))
      exact ⟨z,hz,iz,by simpa only [iz,Bool.false_or] using (joint z).mpr hz.prop⟩
    have h := lower gs u v
    dsimp only at h
    simp only [cyclic] at h
    rw [← whole .or isOr] at h
    have lastEq : g = ⟨.or,[u,v]⟩ := congrArg₂ Gate.mk isOr pins
    refine h gl hshape (by simpa only [splitList,lastEq] using hdistinct)
      dmax tags ?_ ?_ ?_
    · exact fun z hz => (correct z).mpr hz.prop
    · intro z hz
      have no : ¬ (W u z || W v z) = true := fun e => hz.prop ((correct z).mp e)
      change W u z = false ∧ W v z = false
      cases a : W u z <;> cases b : W v z <;> simp [a,b] at no ⊢
    · intro b
      cases b with
      | false => exact exclusive u v hu correct
      | true =>
        obtain ⟨z,hz,hv',hu'⟩ := exclusive v u hv (fun x => by simpa only [Bool.or_comm] using correct x)
        exact ⟨z,hz,hu',hv'⟩
