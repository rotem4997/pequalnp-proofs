import Mathlib.Data.List.Basic
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Two incomparable dirty ANDs below a clean AND have restricted behaviour
-- on negative inputs. If they both fire on the same negative row, one pin of
-- the clean gate is false. That pin contains neither dirty gate. It is a
-- nonempty disjunction of inputs, so some input vertex forces it high.
-- The other pin contains both dirty gates. On every negative row containing
-- that vertex, both dirty gates must be false.
theorem PEqualNP.Outside.R_meta_4065_271
    (distinguish :
      ∀ (n : ℕ) (N : List ℕ) (C : Circuit) (a b t : ℕ),
        IsAO2 n C → t < C.gates.length → (gateAt C t).op = GateOp.and →
        (∀ k, InCone n C k t → (gateAt C k).op = GateOp.and → k = a ∨ k = b) →
        ¬InCone n C a b → ¬InCone n C b a → InCone n C a t → InCone n C b t →
        (∀ r ∈ N, gateVal n C t (fun i => r.testBit i.val) = false) →
        let v (g r : ℕ) := gateVal n C g (fun i => r.testBit i.val)
        (∀ r ∈ N, v a r = true → v b r = false) ∨
          ∃ i : Fin n, ∀ r ∈ N, r.testBit i.val = true → v a r = false ∧ v b r = false)
    (restricted :
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      ∀ C : Circuit,
        let isAnd (g : ℕ) := (gateAt C g).op = GateOp.and
        let v (g r : ℕ) := gateVal 11 C g (fun i => r.testBit i.val)
        let clean (g : ℕ) := ∀ r ∈ N, v g r = false
        let below := InCone 11 C
        let out (r : ℕ) := circuitFun 11 C (fun i => r.testBit i.val)
        ∀ a b : ℕ, IsAO2 11 C → C.size ≤ 21 → a < b → b < C.size → isAnd a → isAnd b →
          (∀ j < C.size, isAnd j → (clean j ↔ j ≠ a ∧ j ≠ b)) →
          (∀ j < C.size, isAnd j → clean j → ∀ k < C.size, isAnd k → ¬below j k) →
          ¬below a b → ¬below b a →
          (∃ t < C.size, isAnd t ∧ clean t ∧ below a t ∧ below b t) →
          ((∀ r ∈ N, v a r = true → v b r = false) ∨
            ∃ i : Fin 11, ∀ r ∈ N, r.testBit i.val = true → v a r = false ∧ v b r = false) →
          (∀ r ∈ P, out r = true) → (∀ r ∈ N, out r = false) → False) :
    have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → x6.size ≤ (21 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x15 < x6.size, x3 x6 x15 → (x4 x6 x15 ↔ x15 ≠ x7 ∧ x15 ≠ x8)) → (∀ x16 < x6.size, x3 x6 x16 → x4 x6 x16 → ∀ x20 < x6.size, x3 x6 x20 → ¬x5 x6 x16 x20) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x19 < x6.size, x3 x6 x19 ∧ x4 x6 x19 ∧ x5 x6 x7 x19 ∧ x5 x6 x8 x19) → (∀ x20 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x22 : Fin (11 : ℕ)) => x20.testBit ↑x22) = Bool.true) → (∀ x21 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.false) → False := by
  classical
  dsimp only
  intro C a b ao hsize hab hbs and_a and_b split clean_last ab ba common positives negatives
  obtain ⟨t, ht, and_t, clean_t, at_t, bt_t⟩ := common
  have ancestors (k : ℕ) (hkt : InCone 11 C k t) (hand : (gateAt C k).op = GateOp.and) :
      k = a ∨ k = b := by
    by_contra! other
    have hk : k < C.size := by
      by_contra! h
      have empty : gateAt C k = ⟨GateOp.or, []⟩ := by
        change C.gates.getD k ⟨GateOp.or, []⟩ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show C.gates.length ≤ k from h)]
        rfl
      rw [empty] at hand
      contradiction
    exact clean_last k hk hand ((split k hk hand).mpr other) t ht and_t hkt
  have signatures := distinguish 11 [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] C a b t ao ht and_t ancestors ab ba at_t bt_t clean_t
  exact restricted C a b ao hsize hab hbs and_a and_b split clean_last ab ba
    ⟨t, ht, and_t, clean_t, at_t, bt_t⟩ signatures positives negatives

-- Standalone proof of child one. Copy the declarations below into a fresh
-- file with the same dependencies, inside a namespace of your choice.
-- The wire and cone lemmas come from L_meta_1490 and L_meta_3756
-- through public upstream commits by willakone. The subsequent
-- declarations, from touches through distinguish, prove this new cut.
-- open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
-- -- Wire evaluation and the cone recursion below come from the project files
-- -- L_meta_1490 and L_meta_3756, distributed under the repository Apache 2.0 license.
-- def stepWire (w : List Bool) (g : Gate) : List Bool :=
--   w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--
-- lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
--     C.wires x = C.gates.foldl stepWire x := rfl
--
-- lemma foldl_length (gs : List Gate) (w : List Bool) :
--     (gs.foldl stepWire w).length = w.length + gs.length := by
--   induction gs generalizing w with
--   | nil => simp
--   | cons g gs ih =>
--     rw [List.foldl_cons, ih]
--     simp [stepWire]
--     omega
--
-- lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
--     (gs.foldl stepWire w).getD i false = w.getD i false := by
--   induction gs generalizing w with
--   | nil => rfl
--   | cons g gs ih =>
--     simp only [List.foldl_cons]
--     have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
--     rw [ih (stepWire w g) hlt]
--     simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--
-- lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
--   simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
--
-- lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
--     (gs.foldl stepWire w).getD (w.length + j) false =
--       (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
--         if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
--   induction gs generalizing w j with
--   | nil => simp at hj
--   | cons g gs ih =>
--     rw [List.foldl_cons]
--     cases j with
--     | zero =>
--       have h1 : w.length < (stepWire w g).length := by simp [stepWire]
--       rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
--       simp only [List.getElem_cons_zero]
--       have h2 : (stepWire w g).getD w.length false =
--           g.op.eval (g.inputs.map fun i => w.getD i false) := by
--         simp [stepWire, List.getD_eq_getElem?_getD]
--       rw [h2]
--       congr 1
--       apply List.map_congr_left
--       intro i _
--       by_cases hi : i < w.length
--       · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
--         simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--       · rw [if_neg hi]; exact getD_ge w i (by omega)
--     | succ j =>
--       have hj' : j < gs.length := by simpa using hj
--       have key := ih (stepWire w g) j hj'
--       have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
--       rw [hl] at key
--       have e : w.length + (j + 1) = w.length + 1 + j := by omega
--       simp only [List.getElem_cons_succ]
--       rw [e]
--       exact key
--
-- def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
--
-- lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
--
-- lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
--   simp [gateAt, List.getD_eq_getElem?_getD, hj]
--
-- lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
--   rw [gateAt_eq hj]; exact List.getElem_mem hj
--
-- lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
--     val C x u = x.getD u false := by
--   unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
--
-- lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
--     (hu : n + C.gates.length ≤ u) : val C x u = false := by
--   unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
--
-- lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
--     (hj : j < C.gates.length) :
--     val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
--       if i < n + j then val C x i else false) := by
--   subst hx
--   rw [gateAt_eq hj]
--   exact foldl_getD_gate C.gates x j hj
--
--
-- lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
--     (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
--     val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
--   rw [val_gate hx hr, hop]
--   simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
--   constructor
--   · rintro ⟨i, hi, h⟩
--     by_cases hlt : i < n + r
--     · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
--     · rw [if_neg hlt] at h; cases h
--   · rintro ⟨i, hi, hlt, h⟩
--     exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
--
-- lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
--     (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
--     val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
--   rw [val_gate hx hr, hop]
--   simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
--   constructor
--   · intro h i hi
--     have h' := h i hi
--     by_cases hlt : i < n + r
--     · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
--     · rw [if_neg hlt] at h'; cases h'
--   · intro h i hi
--     rw [if_pos (h i hi).1]; exact (h i hi).2
--
--
-- lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
--     val C (List.ofFn x) u.val = x u := by
--   rw [val_input (n := n) (by simp) u.isLt]
--   simp [List.getD_eq_getElem?_getD]
--
-- lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
--     PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
--
--
-- lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
--     (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
--   induction gs generalizing cs with
--   | nil => simp
--   | cons g gs ih =>
--     rw [List.foldl_cons, ih]
--     simp [coneStep]
--     omega
--
-- lemma cones_char (n : ℕ) (gs : List Gate) :
--     ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
--       j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
--         (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
--   induction gs using List.reverseRecOn with
--   | nil => intro i j; simp
--   | append_singleton gs g ih =>
--     intro i j
--     rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
--     have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
--       rw [cones_len]; simp
--     have key : ∀ k, k < gs.length →
--         (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
--           (gs.foldl (coneStep n) []).getD k [] := by
--       intro k hk
--       simp only [coneStep, List.getD_eq_getElem?_getD]
--       rw [List.getElem?_append_left (by omega)]
--     rcases Nat.lt_trichotomy j gs.length with h | h | h
--     · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
--         simp only [List.getD_eq_getElem?_getD]
--         rw [List.getElem?_append_left h]
--       rw [key j h, ih i j, e1]
--       constructor
--       · rintro ⟨_, w, hw, h1, h2, h3⟩
--         refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
--         rw [key (w - n) (by omega)]
--         exact h3
--       · rintro ⟨_, w, hw, h1, h2, h3⟩
--         refine ⟨h, w, hw, h1, h2, ?_⟩
--         rw [key (w - n) (by omega)] at h3
--         exact h3
--     · subst h
--       have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
--         simp [List.getD_eq_getElem?_getD]
--       have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
--           (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
--             (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
--         simp only [coneStep, List.getD_eq_getElem?_getD]
--         rw [List.getElem?_append_right (by omega)]
--         simp [hlen]
--       rw [e2, e1]
--       simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
--       constructor
--       · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
--         refine ⟨by simp, w, hw, h1, h2, ?_⟩
--         rw [key (w - n) (by omega)]
--         exact h3
--       · rintro ⟨_, w, hw, h1, h2, h3⟩
--         rw [key (w - n) (by omega)] at h3
--         exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
--     · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
--         simp only [coneStep, List.getD_eq_getElem?_getD]
--         rw [List.getElem?_eq_none (by simp; omega)]
--         rfl
--       rw [e0]
--       constructor
--       · intro h0; simp at h0
--       · rintro ⟨h0, _⟩
--         simp at h0
--         omega
--
-- lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
--     InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
--       (i = k ∨ InCone n C i k) := by
--   have h := cones_char n C.gates i j
--   unfold InCone cones gateAt
--   rw [h]
--   constructor
--   · rintro ⟨h0, w, hw, h1, h2, h3⟩
--     refine ⟨h0, w - n, by omega, ?_, h3⟩
--     have : n + (w - n) = w := by omega
--     rw [this]
--     exact hw
--   · rintro ⟨h0, k, hk, hw, h3⟩
--     refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
--     have : n + k - n = k := by omega
--     rw [this]
--     exact h3
--
--
-- private lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
--     ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
--   intro j
--   induction j using Nat.strong_induction_on with
--   | _ j ih =>
--     intro h
--     rw [inCone_iff] at h
--     obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
--     · exact ⟨by omega, h0⟩
--     · have := (ih k hk h3).1
--       exact ⟨by omega, h0⟩
--
--
-- private lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
--     ∀ j, InCone n C k j → InCone n C a j := by
--   intro j
--   induction j using Nat.strong_induction_on with
--   | _ j ih =>
--     intro h
--     rw [inCone_iff] at h
--     obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
--     · subst h3
--       rw [inCone_iff]
--       exact ⟨h0, k, hk2, hin, Or.inr hak⟩
--     · rw [inCone_iff]
--       exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩
--
-- def touches (n : ℕ) (C : Circuit) (g w : ℕ) : Prop :=
--   ∃ k, w = n + k ∧ (g = k ∨ InCone n C g k)
--
-- lemma ascends {n : ℕ} {C : Circuit} {g k w : ℕ} (hk : k < C.gates.length)
--     (hw : w ∈ (gateAt C k).inputs) (hlt : w < n + k) (h : touches n C g w) :
--     touches n C g (n + k) := by
--   obtain ⟨b, rfl, hb⟩ := h
--   exact ⟨k, rfl, Or.inr ((inCone_iff n C g k).mpr ⟨hk, b, by omega, hw, hb⟩)⟩
--
-- lemma select_operand {n : ℕ} {C : Circuit} {g t : ℕ} (hc : InCone n C g t) :
--     ∃ w ∈ (gateAt C t).inputs, touches n C g w := by
--   obtain ⟨_, b, _, hwin, hprev⟩ := (inCone_iff n C g t).mp hc
--   exact ⟨n+b, hwin, b, rfl, hprev⟩
--
-- lemma below_operand {n : ℕ} {C : Circuit} {k t p : ℕ} (ht : t < C.gates.length)
--     (hi : n+p ∈ (gateAt C k).inputs) (hp : n+p < n+k) (hk : k = t ∨ InCone n C k t) :
--     InCone n C p t := by
--   rcases hk with rfl | hk
--   · exact (inCone_iff n C p k).mpr ⟨ht, p, by omega, hi, Or.inl rfl⟩
--   · have hpk : InCone n C p k :=
--       (inCone_iff n C p k).mpr ⟨by have := (inCone_lt n C k t hk).1; omega, p, by omega, hi, Or.inl rfl⟩
--     exact inCone_trans n C p k hpk t hk
--
-- lemma propagates {n : ℕ} {C : Circuit} {d o t : ℕ}
--     (ao : IsAO2 n C) (ht : t < C.gates.length)
--     (only : ∀ k, InCone n C k t → (gateAt C k).op = GateOp.and → k = d ∨ k = o)
--     (free : ¬ InCone n C d o) (x : Fin n → Bool) (hd : gateVal n C d x = true) :
--     ∀ k, InCone n C k t → touches n C d (n+k) → val C (List.ofFn x) (n+k) = true := by
--   intro k
--   induction k using Nat.strong_induction_on with
--   | _ k ih =>
--     rintro hkt ⟨k', hwire, touch⟩
--     have eq : k' = k := by omega
--     subst k'
--     rcases touch with rfl | hdk
--     · exact hd
--     · have hk : k < C.gates.length := (inCone_lt n C k t hkt).1.trans ht
--       have hOR : (gateAt C k).op = GateOp.or := by
--         rcases ao.1 _ (gateAt_mem hk) with hand | hor
--         · rcases only k hkt hand with e | e
--           · subst k
--             exact False.elim ((Nat.lt_irrefl d) (inCone_lt n C d d hdk).1)
--           · subst k
--             exact False.elim (free hdk)
--         · exact hor
--       obtain ⟨_, j, hjk, harg, ancestor⟩ := (inCone_iff n C d k).mp hdk
--       have hjt := below_operand ht harg (by omega) (Or.inr hkt)
--       apply (val_or (n := n) (by simp) hk hOR).mpr
--       exact ⟨n+j, harg, by omega, ih j hjk hjt ⟨j, rfl, ancestor⟩⟩
--
-- lemma propagated_pin {n : ℕ} {C : Circuit} {d o t w : ℕ}
--     (ao : IsAO2 n C) (ht : t < C.gates.length)
--     (only : ∀ k, InCone n C k t → (gateAt C k).op = GateOp.and → k = d ∨ k = o)
--     (free : ¬ InCone n C d o) (hw : w ∈ (gateAt C t).inputs)
--     (reach : touches n C d w) (x : Fin n → Bool) (hon : gateVal n C d x = true) :
--     val C (List.ofFn x) w = true := by
--   obtain ⟨k, rfl, hr⟩ := reach
--   have hlt := ao.2.1 t ht (n+k) hw
--   have hkt := below_operand ht hw hlt (Or.inl rfl)
--   exact propagates ao ht only free x hon k hkt ⟨k, rfl, hr⟩
--
-- lemma pure_pin {n : ℕ} {C : Circuit} {d o t : ℕ}
--     (ao : IsAO2 n C) (ht : t < C.gates.length)
--     (only : ∀ k, InCone n C k t → (gateAt C k).op = GateOp.and → k = d ∨ k = o) :
--     ∀ w, (∀ k, w = n+k → InCone n C k t) →
--       ¬touches n C d w → ¬touches n C o w →
--       ∃ v : Fin n, ∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true := by
--   intro w
--   induction w using Nat.strong_induction_on with
--   | _ w ih =>
--     intro below nd no
--     by_cases hinput : w < n
--     · exact ⟨⟨w,hinput⟩, fun x hx => (val_ofFn C x ⟨w,hinput⟩).trans hx⟩
--     · let k := w - n
--       have ew : w = n+k := by dsimp [k]; omega
--       have hkt := below k ew
--       have hk : k < C.gates.length := (inCone_lt n C k t hkt).1.trans ht
--       have hOR : (gateAt C k).op = GateOp.or := by
--         rcases ao.1 _ (gateAt_mem hk) with hand | hor
--         · rcases only k hkt hand with he | he
--           · exact False.elim (nd ⟨k, ew, Or.inl he.symm⟩)
--           · exact False.elim (no ⟨k, ew, Or.inl he.symm⟩)
--         · exact hor
--       have hlen := ao.2.2 _ (gateAt_mem hk)
--       have hn : (gateAt C k).inputs ≠ [] := by intro e; rw [e] at hlen; contradiction
--       obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hn
--       have hqk := ao.2.1 k hk q hq
--       have hbefore : ∀ b, q = n+b → InCone n C b t := by
--         rintro b rfl
--         exact below_operand ht hq hqk (Or.inr hkt)
--       have child (g : ℕ) (h : ¬touches n C g w) : ¬touches n C g q :=
--         fun hqg => h (ew ▸ ascends hk hq hqk hqg)
--       obtain ⟨v, hv⟩ := ih q (by omega) hbefore (child d nd) (child o no)
--       refine ⟨v, fun x hx => ?_⟩
--       rw [ew]
--       exact (val_or (n := n) (by simp) hk hOR).mpr ⟨q, hq, hqk, hv x hx⟩
--
-- theorem distinguish (n : ℕ) (N : List ℕ) (C : Circuit) (a b t : ℕ)
--     (ao : IsAO2 n C) (ht : t < C.gates.length) (hand : (gateAt C t).op = GateOp.and)
--     (only : ∀ k, InCone n C k t → (gateAt C k).op = GateOp.and → k = a ∨ k = b)
--     (ab : ¬InCone n C a b) (ba : ¬InCone n C b a)
--     (atop : InCone n C a t) (btop : InCone n C b t)
--     (clean : ∀ r ∈ N, gateVal n C t (fun i => r.testBit i.val) = false) :
--     let v (g r : ℕ) := gateVal n C g (fun i => r.testBit i.val)
--     (∀ r ∈ N, v a r = true → v b r = false) ∨
--       ∃ i : Fin n, ∀ r ∈ N, r.testBit i.val = true → v a r = false ∧ v b r = false := by
--   classical
--   let x := fun (r : ℕ) (i : Fin n) => r.testBit i.val
--   let test (g r : ℕ) := gateVal n C g (x r)
--   change (∀ r ∈ N, test a r = true → test b r = false) ∨
--     ∃ i : Fin n, ∀ r ∈ N, x r i = true → test a r = false ∧ test b r = false
--   by_cases overlap : ∃ r ∈ N, test a r = true ∧ test b r = true
--   · right
--     obtain ⟨r, hr, ha, hb⟩ := overlap
--     obtain ⟨p, q, pins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem ht))
--     have mem_pins (w : ℕ) : w ∈ (gateAt C t).inputs ↔ w = p ∨ w = q := by
--       simp [pins]
--     have project_a (w : ℕ) (hw : w ∈ (gateAt C t).inputs) (h : touches n C a w)
--         (z : ℕ) (hza : test a z = true) : val C (List.ofFn (x z)) w = true :=
--       propagated_pin ao ht only ab hw h (x z) hza
--     have project_b (w : ℕ) (hw : w ∈ (gateAt C t).inputs) (h : touches n C b w)
--         (z : ℕ) (hzb : test b z = true) : val C (List.ofFn (x z)) w = true :=
--       propagated_pin ao ht (fun k hk hk' => (only k hk hk').symm) ba hw h (x z) hzb
--     have blocked (z : ℕ) (hz : z ∈ N)
--         (all_high : ∀ w ∈ (gateAt C t).inputs, val C (List.ofFn (x z)) w = true) : False := by
--       have yes := (val_and (n := n) (C := C) (x := List.ofFn (x z)) (by simp) ht hand).mpr
--         (fun w hw => ⟨ao.2.1 t ht w hw, all_high w hw⟩)
--       have no := clean z hz
--       change val C (List.ofFn (x z)) (n+t) = false at no
--       exact Bool.noConfusion (yes.symm.trans no)
--     have one_pin (u v : ℕ) (hu : u ∈ (gateAt C t).inputs) (hv : v ∈ (gateAt C t).inputs)
--         (cases_of : ∀ w ∈ (gateAt C t).inputs, w = u ∨ w = v)
--         (off : val C (List.ofFn (x r)) u = false) :
--         ∃ i : Fin n, ∀ z ∈ N, x z i = true → test a z = false ∧ test b z = false := by
--       have na : ¬touches n C a u := fun h => Bool.noConfusion ((project_a u hu h r ha).symm.trans off)
--       have nb : ¬touches n C b u := fun h => Bool.noConfusion ((project_b u hu h r hb).symm.trans off)
--       have move (g : ℕ) (h : InCone n C g t) (hno : ¬touches n C g u) : touches n C g v := by
--         obtain ⟨w, hw, hreach⟩ := select_operand h
--         rcases cases_of w hw with rfl | rfl
--         · exact False.elim (hno hreach)
--         · exact hreach
--       have target_a := move a atop na
--       have target_b := move b btop nb
--       have smaller : ∀ k, u = n+k → InCone n C k t := by
--         rintro k rfl
--         exact below_operand ht hu (ao.2.1 t ht (n+k) hu) (Or.inl rfl)
--       obtain ⟨i, hi⟩ := pure_pin ao ht only u smaller na nb
--       refine ⟨i, ?_⟩
--       intro z hz zi
--       have voff : val C (List.ofFn (x z)) v ≠ true := by
--         intro vv
--         apply blocked z hz
--         intro w hw
--         rcases cases_of w hw with rfl | rfl
--         · exact hi (x z) zi
--         · exact vv
--       exact ⟨Bool.eq_false_iff.mpr (fun h => voff (project_a v hv target_a z h)),
--              Bool.eq_false_iff.mpr (fun h => voff (project_b v hv target_b z h))⟩
--     have hp := (mem_pins p).mpr (Or.inl rfl)
--     have hq := (mem_pins q).mpr (Or.inr rfl)
--     cases pv : val C (List.ofFn (x r)) p with
--     | false => exact one_pin p q hp hq (fun w => (mem_pins w).mp) pv
--     | true =>
--       apply one_pin q p hq hp (fun w hw => ((mem_pins w).mp hw).symm)
--       apply Bool.eq_false_iff.mpr
--       intro qv
--       apply blocked r hr
--       intro w hw
--       rcases (mem_pins w).mp hw with rfl | rfl
--       · exact pv
--       · exact qv
--   · exact Or.inl (fun r hr ha => Bool.eq_false_iff.mpr (fun hb => overlap ⟨r, hr, ha, hb⟩))
