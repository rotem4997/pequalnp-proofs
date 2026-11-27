import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Reduce L-meta-2071 via PG(2,3) flag transitivity to incidence (0, 0), eliminate the
-- linearized propagation maps v and w by extracting live double-read AND gates k1 and k2,
-- and split into three structural cases: k1 = k2, oriented chain InCone k1 k2 (using
-- PG(2,3) point-line self-duality), and incomparable k1, k2.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2071_319
    (hSame : ¬ ∃ C : Circuit,
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let A := GateOp.and
      let gv := gateVal 26 C
      let wv := wireVal 26 C
      let isA := fun k => (gateAt C k).op = A
      let p0 := pairInput (0 : Fin 26) 0
      let p13 := pairInput (13 : Fin 26) 13
      let p013 := pairInput (0 : Fin 26) 13
      C.size ≤ 64 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = A ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < C.gates.length, isA d ∧
        ∃ x : Fin 26 → Bool, gv d x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ k : ℕ, isA k ∧
        (26 + k = C.output ∨ InCone 26 C k (C.output - 26)) ∧
        gv k p013 = true ∧
        ∀ b : Fin 2, wv (opnd C k b) p0 = false ∧ wv (opnd C k b) p13 = false)
    (hChain : ¬ ∃ C : Circuit,
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let A := GateOp.and
      let ic := InCone 26 C
      let gv := gateVal 26 C
      let p0 := pairInput (0 : Fin 26) 0
      let p13 := pairInput (13 : Fin 26) 13
      let p013 := pairInput (0 : Fin 26) 13
      let ok := fun k z => (gateAt C k).op = A ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧
        gv k p013 = true ∧ ∀ b : Fin 2, wireVal 26 C (opnd C k b) z = false
      C.size ≤ 64 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = A ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < C.gates.length, (gateAt C d).op = A ∧
        ∃ x : Fin 26 → Bool, gv d x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ k1 k2 : ℕ, ic k1 k2 ∧ ok k1 p0 ∧ ok k2 p13)
    (hPar : ¬ ∃ C : Circuit,
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let A := GateOp.and
      let ic := InCone 26 C
      let gv := gateVal 26 C
      let p0 := pairInput (0 : Fin 26) 0
      let p13 := pairInput (13 : Fin 26) 13
      let p013 := pairInput (0 : Fin 26) 13
      let ok := fun k z => (gateAt C k).op = A ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧
        gv k p013 = true ∧ ∀ b : Fin 2, wireVal 26 C (opnd C k b) z = false
      C.size ≤ 64 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = A ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ D ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < C.gates.length, (gateAt C d).op = A ∧
        ∃ x : Fin 26 → Bool, gv d x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ k1 k2 : ℕ, k1 ≠ k2 ∧ ¬ ic k1 k2 ∧ ¬ ic k2 k1 ∧ ok k1 p0 ∧ ok k2 p13) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  classical
  dsimp only
  intro C p l v w hSize hGates hEval _ hDirty hInc hV hW
  by_contra hBoth
  have hvOut : v C.output = false := by
    cases h : v C.output
    · rfl
    · exact absurd (Or.inl h) hBoth
  have hwOut : w C.output = false := by
    cases h : w C.output
    · rfl
    · exact absurd (Or.inr h) hBoth
  -- Wire evaluation helpers
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
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have wireVal_input : ∀ (D : Circuit) (x : Fin 26 → Bool) (r : ℕ) (hr : r < 26),
      wireVal 26 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlt : r < (List.ofFn x).length := by simp [hr]
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_gate : ∀ (D : Circuit) (x : Fin 26 → Bool) (k : ℕ) (g : Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 26 + k) →
      wireVal 26 D (26 + k) x = g.op.eval (g.inputs.map fun i => wireVal 26 D i x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 := List.cons_getElem_drop_succ (l := D.gates) (n := k) (h := hk)
      have hg_eq : D.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hgk)
      rw [hg_eq] at h2
      rw [h2]; exact h1.symm
    have hlen_pre : ((D.gates.take k).foldl wstep (List.ofFn x)).length = 26 + k := by
      rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hpre_val : ∀ i, i < 26 + k →
        wireVal 26 D i x = ((D.gates.take k).foldl wstep (List.ofFn x)).getD i false := by
      intro i hi
      change (D.gates.foldl wstep (List.ofFn x)).getD i false = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, wfold_getD_lt _ _ i (by omega)]
    change (D.gates.foldl wstep (List.ofFn x)).getD (26 + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlen_mid : (wstep ((D.gates.take k).foldl wstep (List.ofFn x)) g).length = 26 + k + 1 := by
      simp only [wstep, List.length_append, List.length_singleton, hlen_pre]
    rw [wfold_getD_lt _ _ (26 + k) (by omega)]
    have hmid_val : (wstep ((D.gates.take k).foldl wstep (List.ofFn x)) g).getD (26 + k) false =
        g.op.eval (g.inputs.map fun i => ((D.gates.take k).foldl wstep (List.ofFn x)).getD i false) := by
      generalize hpre_def : (D.gates.take k).foldl wstep (List.ofFn x) = pre at hlen_pre ⊢
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hlen_pre])]
      simp only [hlen_pre, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hmid_val]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (hpre_val i (hlt i hi)).symm
  -- Cone characterization
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
  have inCone_trans : ∀ (D : Circuit) (a b c : ℕ),
      InCone 26 D a b → InCone 26 D b c → InCone 26 D a c := by
    intro D a b c hab hbc
    induction c using Nat.strong_induction_on with
    | ind c ih =>
      rw [inCone_iff] at hbc
      obtain ⟨hc, w, hw, h1, h2, h3⟩ := hbc
      rw [inCone_iff]
      refine ⟨hc, w, hw, h1, h2, Or.inr ?_⟩
      rcases h3 with rfl | h3
      · exact hab
      · exact ih (w - 26) (by omega) h3
  -- General input-permutation relabeling for any bijection pi : Fin 26 → Fin 26
  have relabel_wires : ∀ (π : Fin 26 → Fin 26) (D : Circuit) (e : Fin 26 → Bool) (a : ℕ),
      let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
      let D' : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ D.output⟩
      wireVal 26 D' (ρ a) e = wireVal 26 D a (fun i => e (π i)) := by
    intro π D e a
    let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
    have hρ_lt : ∀ i, i < 26 → ρ i < 26 := by
      intro i hi; dsimp only [ρ]; rw [dif_pos hi]; exact (π ⟨i, hi⟩).isLt
    have hρ_ge : ∀ i, 26 ≤ i → ρ i = i := by
      intro i hi; dsimp only [ρ]; rw [dif_neg (by omega)]
    have getD_rel : ∀ (T : List Bool) (i : ℕ),
        (List.ofFn e ++ T).getD (ρ i) false =
          (List.ofFn (fun j : Fin 26 => e (π j)) ++ T).getD i false := by
      intro T i
      by_cases hi : i < 26
      · have h1 := hρ_lt i hi
        rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact h1),
          List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi),
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h1),
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi),
          List.getElem_ofFn, List.getElem_ofFn]
        congr 1; apply Fin.ext; dsimp only [ρ]; rw [dif_pos hi]
      · rw [hρ_ge i (by omega),
          List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega),
          List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega),
          List.length_ofFn, List.length_ofFn]
    have fold_rel : ∀ (gs : List Gate) (T : List Bool), ∃ T' : List Bool,
        (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl wstep (List.ofFn e ++ T) =
          List.ofFn e ++ T' ∧
        gs.foldl wstep (List.ofFn (fun j : Fin 26 => e (π j)) ++ T) =
          List.ofFn (fun j : Fin 26 => e (π j)) ++ T' := by
      intro gs
      induction gs with
      | nil => intro T; exact ⟨T, by simp, by simp⟩
      | cons g rest ih =>
        intro T
        have hval : g.op.eval ((g.inputs.map ρ).map fun i => (List.ofFn e ++ T).getD i false) =
            g.op.eval (g.inputs.map fun i =>
              (List.ofFn (fun j : Fin 26 => e (π j)) ++ T).getD i false) := by
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact getD_rel T i
        obtain ⟨T', h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i =>
          (List.ofFn (fun j : Fin 26 => e (π j)) ++ T).getD i false)])
        refine ⟨T', ?_, ?_⟩
        · rw [List.map_cons, List.foldl_cons]
          change ((rest.map fun g => Gate.mk g.op (g.inputs.map ρ)).foldl wstep
            ((List.ofFn e ++ T) ++ [g.op.eval ((g.inputs.map ρ).map fun i =>
              (List.ofFn e ++ T).getD i false)])) = _
          rw [hval, List.append_assoc]; exact h1
        · rw [List.foldl_cons]
          change (rest.foldl wstep ((List.ofFn (fun j : Fin 26 => e (π j)) ++ T) ++
            [g.op.eval (g.inputs.map fun i =>
              (List.ofFn (fun j : Fin 26 => e (π j)) ++ T).getD i false)])) = _
          rw [List.append_assoc]; exact h2
    obtain ⟨T', h1, h2⟩ := fold_rel D.gates []
    simp only [List.append_nil] at h1 h2
    change ((D.gates.map fun g => Gate.mk g.op (g.inputs.map ρ)).foldl wstep (List.ofFn e)).getD (ρ a) false =
      (D.gates.foldl wstep (List.ofFn fun j => e (π j))).getD a false
    rw [h1, h2]
    exact getD_rel T' a
  have relabel_cones : ∀ (π : Fin 26 → Fin 26) (D : Circuit),
      let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
      let D' : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ D.output⟩
      cones 26 D' = cones 26 D := by
    intro π D
    let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
    have hρ_lt : ∀ i, i < 26 → ρ i < 26 := by
      intro i hi; dsimp only [ρ]; rw [dif_pos hi]; exact (π ⟨i, hi⟩).isLt
    have hρ_ge : ∀ i, 26 ≤ i → ρ i = i := by
      intro i hi; dsimp only [ρ]; rw [dif_neg (by omega)]
    have hfold : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl (coneStep 26) cs =
          gs.foldl (coneStep 26) cs := by
      intro gs
      induction gs with
      | nil => intro cs; rfl
      | cons g rest ih =>
        intro cs
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hstep : coneStep 26 cs ⟨g.op, g.inputs.map ρ⟩ = coneStep 26 cs g := by
          change cs ++ [(((g.inputs.map ρ).filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
            (fun w => (w - 26) :: cs.getD (w - 26) []))] =
            cs ++ [((g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
              (fun w => (w - 26) :: cs.getD (w - 26) []))]
          congr 2
          rw [List.filter_map, List.flatMap_map]
          have hcomp : ∀ (l : List ℕ) (f1 f2 : ℕ → List ℕ),
              (∀ w ∈ l, f1 w = f2 w) → l.flatMap f1 = l.flatMap f2 := by
            intro l f1 f2 h; induction l with
            | nil => rfl
            | cons x xs ihxs => simp [h x (by simp), ihxs (fun w hw => h w (by simp [hw]))]
          have hflt_eq : g.inputs.filter ((fun w => decide (26 ≤ w ∧ w < 26 + cs.length)) ∘ ρ) =
              g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length)) := by
            apply List.filter_congr
            intro x _
            simp only [Function.comp_apply]
            by_cases hx : x < 26
            · have := hρ_lt x hx
              simp [show ¬ (26 ≤ ρ x ∧ ρ x < 26 + cs.length) by omega,
                    show ¬ (26 ≤ x ∧ x < 26 + cs.length) by omega]
            · simp [hρ_ge x (by omega)]
          rw [hflt_eq]
          apply hcomp
          intro w hw
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          simp [hρ_ge w hw.2.1]
        rw [hstep]
        exact ih _
    exact hfold D.gates []
  -- Relabeling preserves size, well-formedness, incidence, dirty AND, and maps v, w
  have relabel_all : ∀ (π : Fin 26 → Fin 26) (hbij : Function.Bijective π)
      (hPres : ∀ e : Fin 26 → Bool,
        (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          e (π (Fin.castAdd 13 u)) = true ∧ e (π (Fin.natAdd 13 t)) = true) ↔
        (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          e (Fin.castAdd 13 u) = true ∧ e (Fin.natAdd 13 t) = true))
      (D : Circuit),
      let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
      let D' : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ D.output⟩
      D.size ≤ 64 →
      (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
      (∃ d < D.gates.length, (gateAt D d).op = GateOp.and ∧
        ∃ x : Fin 26 → Bool, gateVal 26 D d x = true ∧ D.eval (List.ofFn x) = false) →
      D'.size ≤ 64 ∧
      (∀ (j : ℕ) (g : Gate), D'.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, D'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      (∃ d < D'.gates.length, (gateAt D' d).op = GateOp.and ∧
        ∃ x : Fin 26 → Bool, gateVal 26 D' d x = true ∧ D'.eval (List.ofFn x) = false) := by
    intro π hbij hPres D ρ D' hDsz hDg hDe hDd
    have hρ_lt : ∀ i, i < 26 → ρ i < 26 := by
      intro i hi; dsimp only [ρ]; rw [dif_pos hi]; exact (π ⟨i, hi⟩).isLt
    have hρ_ge : ∀ i, 26 ≤ i → ρ i = i := by
      intro i hi; dsimp only [ρ]; rw [dif_neg (by omega)]
    have hρ_inj : Function.Injective ρ := by
      intro a b hab
      by_cases ha : a < 26 <;> by_cases hb : b < 26
      · dsimp only [ρ] at hab
        rw [dif_pos ha, dif_pos hb] at hab
        have := hbij.1 (Fin.ext hab)
        exact congrArg Fin.val this
      · have := hρ_lt a ha; rw [hρ_ge b (by omega)] at hab; omega
      · have := hρ_lt b hb; rw [hρ_ge a (by omega)] at hab; omega
      · rw [hρ_ge a (by omega), hρ_ge b (by omega)] at hab; exact hab
    have hEval' : ∀ x : Fin 26 → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn (fun i => x (π i))) := by
      intro x
      exact relabel_wires π D x D.output
    refine ⟨by change (D.gates.map _).length ≤ 64; rw [List.length_map]; exact hDsz, ?_, ?_, ?_⟩
    · intro j g hg
      simp only [D', List.getElem?_map] at hg
      cases h0 : D.gates[j]? with
      | none => rw [h0] at hg; simp at hg
      | some g0 =>
        rw [h0] at hg; simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        obtain ⟨hop, a, b, hin, hne, ha, hb⟩ := hDg j g0 h0
        refine ⟨hop, ρ a, ρ b, by simp [hin], fun heq => hne (hρ_inj heq), ?_, ?_⟩
        · by_cases h : a < 26
          · have := hρ_lt a h; omega
          · rw [hρ_ge a (by omega)]; exact ha
        · by_cases h : b < 26
          · have := hρ_lt b h; omega
          · rw [hρ_ge b (by omega)]; exact hb
    · intro x
      rw [hEval' x, hDe (fun i => x (π i)), hPres x]
    · obtain ⟨d, hd, hdop, x, hdx, hfx⟩ := hDd
      obtain ⟨πinv, hlinv, hrinv⟩ := Function.bijective_iff_has_inverse.mp hbij
      refine ⟨d, by simpa [D'] using hd, ?_, fun i => x (πinv i), ?_, ?_⟩
      · have h1 : gateAt D d = D.gates[d] := by
          change D.gates.getD d ⟨GateOp.or, []⟩ = D.gates[d]
          rw [List.getD_eq_getElem _ _ hd]
        have h2 : gateAt D' d = D'.gates[d]'(by simpa [D'] using hd) := by
          change D'.gates.getD d ⟨GateOp.or, []⟩ = _
          rw [List.getD_eq_getElem _ _ (by simpa [D'] using hd)]
        rw [h2]; simp only [D', List.getElem_map]; rw [← h1]; exact hdop
      · have hgv : gateVal 26 D' d (fun i => x (πinv i)) =
            gateVal 26 D d (fun i => x (πinv (π i))) := by
          have hrw := relabel_wires π D (fun i => x (πinv i)) (26 + d)
          dsimp only at hrw
          rw [show (if h : 26 + d < 26 then (π ⟨26 + d, h⟩).val else 26 + d) = 26 + d from
            dif_neg (by omega)] at hrw
          exact hrw
        rw [hgv]
        have hfun : (fun i => x (πinv (π i))) = x := by funext i; rw [hlinv i]
        rw [hfun]; exact hdx
      · rw [hEval']
        have hfun : (fun i => x (πinv (π i))) = x := by funext i; rw [hlinv i]
        rw [hfun]; exact hfx
  -- Step 1: Flag transitivity of PG(2,3) sends (p, l) to (0, 0)
  have hFlag : ∃ π : Fin 26 → Fin 26, Function.Bijective π ∧
      π (Fin.castAdd 13 p) = Fin.castAdd 13 (0 : Fin 13) ∧
      π (Fin.natAdd 13 l) = Fin.natAdd 13 (0 : Fin 13) ∧
      ∀ e : Fin 26 → Bool,
        (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          e (π (Fin.castAdd 13 u)) = true ∧ e (π (Fin.natAdd 13 t)) = true) ↔
        (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          e (Fin.castAdd 13 u) = true ∧ e (Fin.natAdd 13 t) = true) := by
    have make_col : ∀ (σ τ : Fin 13 → Fin 13), Function.Bijective σ → Function.Bijective τ →
        (∀ u t : Fin 13, σ u - τ t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
          u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) →
        σ p = 0 → τ l = 0 →
        ∃ π : Fin 26 → Fin 26, Function.Bijective π ∧
          π (Fin.castAdd 13 p) = Fin.castAdd 13 (0 : Fin 13) ∧
          π (Fin.natAdd 13 l) = Fin.natAdd 13 (0 : Fin 13) ∧
          ∀ e : Fin 26 → Bool,
            (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
              e (π (Fin.castAdd 13 u)) = true ∧ e (π (Fin.natAdd 13 t)) = true) ↔
            (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
              e (Fin.castAdd 13 u) = true ∧ e (Fin.natAdd 13 t) = true) := by
      intro σ τ hσ hτ hcol hσp hτl
      let π : Fin 26 → Fin 26 := fun i =>
        if h : i.val < 13 then Fin.castAdd 13 (σ ⟨i.val, h⟩)
        else Fin.natAdd 13 (τ ⟨i.val - 13, by omega⟩)
      have hπ_cast : ∀ u : Fin 13, π (Fin.castAdd 13 u) = Fin.castAdd 13 (σ u) := by
        intro u; dsimp only [π]; simp only [Fin.val_castAdd, dif_pos u.isLt]
      have hπ_nat : ∀ t : Fin 13, π (Fin.natAdd 13 t) = Fin.natAdd 13 (τ t) := by
        intro t; dsimp only [π]; rw [dif_neg (by simp)]
        congr 2; apply Fin.ext; simp
      refine ⟨π, ?_, by rw [hπ_cast, hσp], by rw [hπ_nat, hτl], ?_⟩
      · constructor
        · intro a b hab
          dsimp only [π] at hab
          split_ifs at hab with ha hb hb
          · have h1 : σ ⟨a.val, ha⟩ = σ ⟨b.val, hb⟩ := Fin.ext (by
              have := congrArg Fin.val hab; simpa using this)
            have := congrArg Fin.val (hσ.1 h1)
            exact Fin.ext this
          · have := congrArg Fin.val hab
            simp only [Fin.val_castAdd, Fin.val_natAdd] at this
            have := (σ ⟨a.val, ha⟩).isLt; omega
          · have := congrArg Fin.val hab
            simp only [Fin.val_castAdd, Fin.val_natAdd] at this
            have := (σ ⟨b.val, hb⟩).isLt; omega
          · have h1 : τ ⟨a.val - 13, by omega⟩ = τ ⟨b.val - 13, by omega⟩ := Fin.ext (by
              have := congrArg Fin.val hab; simp only [Fin.val_natAdd] at this; omega)
            have := congrArg Fin.val (hτ.1 h1)
            exact Fin.ext (by dsimp at this; omega)
        · intro y
          by_cases hy : y.val < 13
          · obtain ⟨u, hu⟩ := hσ.2 ⟨y.val, hy⟩
            refine ⟨Fin.castAdd 13 u, ?_⟩
            rw [hπ_cast, hu]; apply Fin.ext; simp
          · obtain ⟨t, ht⟩ := hτ.2 ⟨y.val - 13, by omega⟩
            refine ⟨Fin.natAdd 13 t, ?_⟩
            rw [hπ_nat, ht]; apply Fin.ext; simp; omega
      · intro e
        constructor
        · rintro ⟨u, t, hut, he1, he2⟩
          rw [hπ_cast] at he1; rw [hπ_nat] at he2
          exact ⟨σ u, τ t, (hcol u t).mpr hut, he1, he2⟩
        · rintro ⟨u', t', hut', he1, he2⟩
          obtain ⟨u, rfl⟩ := hσ.2 u'
          obtain ⟨t, rfl⟩ := hτ.2 t'
          refine ⟨u, t, (hcol u t).mp hut', ?_, ?_⟩
          · rw [hπ_cast]; exact he1
          · rw [hπ_nat]; exact he2
    have hdiff_cases : ∀ a b : Fin 13, a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
        b - a = 0 ∨ b - a = 4 ∨ b - a = 10 ∨ b - a = 12 := by decide
    have h_col0 : (∀ u t : Fin 13, (u - p) - (t - p) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
        u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by
      intro u t; simp [sub_sub_sub_cancel_right]
    rcases hdiff_cases p l hInc with hd | hd | hd | hd
    · exact make_col (fun u => u - p) (fun t => t - p)
        (Equiv.subRight p).bijective (Equiv.subRight p).bijective h_col0 (sub_self p) hd
    · let σ2 : Fin 13 → Fin 13 := ![0, 2, 4, 8, 1, 9, 6, 3, 7, 12, 10, 11, 5]
      let τ2 : Fin 13 → Fin 13 := ![12, 1, 8, 5, 0, 6, 3, 7, 11, 9, 10, 2, 4]
      have hσ2 : Function.Bijective σ2 := by decide
      have hτ2 : Function.Bijective τ2 := by decide
      have hc2 : ∀ u t : Fin 13, σ2 u - τ2 t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
          u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
      have h02 : σ2 0 = 0 := by decide
      have hd2 : τ2 4 = 0 := by decide
      exact make_col (fun u => σ2 (u - p)) (fun t => τ2 (t - p))
        (hσ2.comp (Equiv.subRight p).bijective) (hτ2.comp (Equiv.subRight p).bijective)
        (fun u t => (hc2 _ _).trans (h_col0 u t))
        (by rw [sub_self, h02]) (by rw [hd, hd2])
    · let σ2 : Fin 13 → Fin 13 := ![0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7]
      let τ2 : Fin 13 → Fin 13 := ![12, 1, 8, 7, 10, 2, 3, 5, 9, 11, 0, 6, 4]
      have hσ2 : Function.Bijective σ2 := by decide
      have hτ2 : Function.Bijective τ2 := by decide
      have hc2 : ∀ u t : Fin 13, σ2 u - τ2 t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
          u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
      have h02 : σ2 0 = 0 := by decide
      have hd2 : τ2 10 = 0 := by decide
      exact make_col (fun u => σ2 (u - p)) (fun t => τ2 (t - p))
        (hσ2.comp (Equiv.subRight p).bijective) (hτ2.comp (Equiv.subRight p).bijective)
        (fun u t => (hc2 _ _).trans (h_col0 u t))
        (by rw [sub_self, h02]) (by rw [hd, hd2])
    · let σ2 : Fin 13 → Fin 13 := ![0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9]
      let τ2 : Fin 13 → Fin 13 := ![12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0]
      have hσ2 : Function.Bijective σ2 := by decide
      have hτ2 : Function.Bijective τ2 := by decide
      have hc2 : ∀ u t : Fin 13, σ2 u - τ2 t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
          u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
      have h02 : σ2 0 = 0 := by decide
      have hd2 : τ2 12 = 0 := by decide
      exact make_col (fun u => σ2 (u - p)) (fun t => τ2 (t - p))
        (hσ2.comp (Equiv.subRight p).bijective) (hτ2.comp (Equiv.subRight p).bijective)
        (fun u t => (hc2 _ _).trans (h_col0 u t))
        (by rw [sub_self, h02]) (by rw [hd, hd2])
  obtain ⟨π, hπ_bij, hπ_p, hπ_l, hπ_pres⟩ := hFlag
  let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
  let C' : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩
  obtain ⟨hSize', hGates', hEval', hDirty'⟩ :=
    relabel_all π hπ_bij hπ_pres C hSize hGates hEval hDirty
  -- Transport v and w along π to C'
  obtain ⟨πinv, hπ_linv, hπ_rinv⟩ := Function.bijective_iff_has_inverse.mp hπ_bij
  let ρinv : ℕ → ℕ := fun i => if h : i < 26 then (πinv ⟨i, h⟩).val else i
  have hρ_inv : ∀ a, ρinv (ρ a) = a := by
    intro a
    by_cases ha : a < 26
    · dsimp only [ρ, ρinv]
      rw [dif_pos ha, dif_pos (π ⟨a, ha⟩).isLt]
      simp only [Fin.eta]; rw [hπ_linv]
    · dsimp only [ρ, ρinv]
      rw [dif_neg ha, dif_neg ha]
  have hρ_rinv : ∀ a, ρ (ρinv a) = a := by
    intro a
    by_cases ha : a < 26
    · dsimp only [ρ, ρinv]
      rw [dif_pos ha, dif_pos (πinv ⟨a, ha⟩).isLt]
      simp only [Fin.eta]; rw [hπ_rinv]
    · dsimp only [ρ, ρinv]
      rw [dif_neg ha, dif_neg ha]
  let v' : ℕ → Bool := fun a => v (ρinv a)
  let w' : ℕ → Bool := fun a => w (ρinv a)
  have hv'_out : v' C'.output = false := by
    dsimp only [v', C']; rw [hρ_inv]; exact hvOut
  have hw'_out : w' C'.output = false := by
    dsimp only [w', C']; rw [hρ_inv]; exact hwOut
  have hv'_base : ∀ r < 26, v' r = decide (r = 13) := by
    intro r hr
    dsimp only [v', ρinv]; rw [dif_pos hr]
    rw [hV.1 _ (πinv ⟨r, hr⟩).isLt]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have hfin : πinv ⟨r, hr⟩ = Fin.natAdd 13 l := Fin.ext h
      have := congrArg π hfin
      rw [hπ_rinv, hπ_l] at this
      exact congrArg Fin.val this
    · intro h
      have hfin : (⟨r, hr⟩ : Fin 26) = Fin.natAdd 13 (0 : Fin 13) := Fin.ext h
      rw [hfin, ← hπ_l, hπ_linv]; rfl
  have hw'_base : ∀ r < 26, w' r = decide (r = 0) := by
    intro r hr
    dsimp only [w', ρinv]; rw [dif_pos hr]
    rw [hW.1 _ (πinv ⟨r, hr⟩).isLt]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have hfin : πinv ⟨r, hr⟩ = Fin.castAdd 13 p := Fin.ext h
      have := congrArg π hfin
      rw [hπ_rinv, hπ_p] at this
      exact congrArg Fin.val this
    · intro h
      have hfin : (⟨r, hr⟩ : Fin 26) = Fin.castAdd 13 (0 : Fin 13) := Fin.ext h
      rw [hfin, ← hπ_p, hπ_linv]; rfl
  have h1p_eq : (fun i : Fin 26 => pairInput (0 : Fin 26) 0 (π i)) =
      (fun i : Fin 26 => decide (i = Fin.castAdd 13 p)) := by
    funext i; unfold pairInput; apply Bool.eq_iff_iff.mpr
    simp only [or_self, decide_eq_true_eq]
    have h0 : (0 : Fin 26) = Fin.castAdd 13 (0 : Fin 13) := by decide
    rw [h0, ← hπ_p]
    exact ⟨fun h => hπ_bij.1 h, fun h => congrArg π h⟩
  have h1l_eq : (fun i : Fin 26 => pairInput (13 : Fin 26) 13 (π i)) =
      (fun i : Fin 26 => decide (i = Fin.natAdd 13 l)) := by
    funext i; unfold pairInput; apply Bool.eq_iff_iff.mpr
    simp only [or_self, decide_eq_true_eq]
    have h13 : (13 : Fin 26) = Fin.natAdd 13 (0 : Fin 13) := by decide
    rw [h13, ← hπ_l]
    exact ⟨fun h => hπ_bij.1 h, fun h => congrArg π h⟩
  have hv'_rec : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C'.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → v' (26 + k) =
        ((wireVal 26 C' a (pairInput (0 : Fin 26) 0) && v' b) ||
         (v' a && wireVal 26 C' b (pairInput (0 : Fin 26) 0)))) ∧
      (g.op = GateOp.or → v' (26 + k) = (v' a || v' b)) := by
    intro k g a b hgk hin
    simp only [C', List.getElem?_map] at hgk
    cases h0 : C.gates[k]? with
    | none => rw [h0] at hgk; simp at hgk
    | some g0 =>
      rw [h0] at hgk; simp only [Option.map_some, Option.some.injEq] at hgk
      subst hgk
      obtain ⟨_, c0, d0, hin0, _⟩ := hGates k g0 h0
      rw [hin0] at hin
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hin
      obtain ⟨rfl, rfl⟩ := hin
      have hrec0 := hV.2 k g0 c0 d0 h0 hin0
      have hv_k : v' (26 + k) = v (26 + k) := by
        dsimp only [v', ρinv]; rw [dif_neg (by omega)]
      have hv_c : v' (ρ c0) = v c0 := by dsimp only [v']; rw [hρ_inv]
      have hv_d : v' (ρ d0) = v d0 := by dsimp only [v']; rw [hρ_inv]
      have hw_c : wireVal 26 C' (ρ c0) (pairInput (0 : Fin 26) 0) =
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 p))).getD c0 false := by
        rw [relabel_wires π C (pairInput (0 : Fin 26) 0) c0, h1p_eq]; rfl
      have hw_d : wireVal 26 C' (ρ d0) (pairInput (0 : Fin 26) 0) =
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 p))).getD d0 false := by
        rw [relabel_wires π C (pairInput (0 : Fin 26) 0) d0, h1p_eq]; rfl
      rw [hv_k, hv_c, hv_d, hw_c, hw_d]
      exact hrec0
  have hw'_rec : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C'.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → w' (26 + k) =
        ((wireVal 26 C' a (pairInput (13 : Fin 26) 13) && w' b) ||
         (w' a && wireVal 26 C' b (pairInput (13 : Fin 26) 13)))) ∧
      (g.op = GateOp.or → w' (26 + k) = (w' a || w' b)) := by
    intro k g a b hgk hin
    simp only [C', List.getElem?_map] at hgk
    cases h0 : C.gates[k]? with
    | none => rw [h0] at hgk; simp at hgk
    | some g0 =>
      rw [h0] at hgk; simp only [Option.map_some, Option.some.injEq] at hgk
      subst hgk
      obtain ⟨_, c0, d0, hin0, _⟩ := hGates k g0 h0
      rw [hin0] at hin
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hin
      obtain ⟨rfl, rfl⟩ := hin
      have hrec0 := hW.2 k g0 c0 d0 h0 hin0
      have hw_k : w' (26 + k) = w (26 + k) := by
        dsimp only [w', ρinv]; rw [dif_neg (by omega)]
      have hw_c : w' (ρ c0) = w c0 := by dsimp only [w']; rw [hρ_inv]
      have hw_d : w' (ρ d0) = w d0 := by dsimp only [w']; rw [hρ_inv]
      have hwc : wireVal 26 C' (ρ c0) (pairInput (13 : Fin 26) 13) =
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = Fin.natAdd 13 l))).getD c0 false := by
        rw [relabel_wires π C (pairInput (13 : Fin 26) 13) c0, h1l_eq]; rfl
      have hwd : wireVal 26 C' (ρ d0) (pairInput (13 : Fin 26) 13) =
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = Fin.natAdd 13 l))).getD d0 false := by
        rw [relabel_wires π C (pairInput (13 : Fin 26) 13) d0, h1l_eq]; rfl
      rw [hw_k, hw_c, hw_d, hwc, hwd]
      exact hrec0
  -- Step 2: Evaluate C' at 1_{0,13}, 1_0, 1_{13}
  have hOut013 : wireVal 26 C' C'.output (pairInput (0 : Fin 26) 13) = true := by
    change C'.eval (List.ofFn (pairInput (0 : Fin 26) 13)) = true
    rw [hEval']
    exact ⟨0, 0, by decide, by decide, by decide⟩
  have hOut00 : wireVal 26 C' C'.output (pairInput (0 : Fin 26) 0) = false := by
    cases h : wireVal 26 C' C'.output (pairInput (0 : Fin 26) 0)
    · rfl
    · exfalso
      obtain ⟨u, t, _, _, ht⟩ := (hEval' _).mp h
      unfold pairInput at ht
      simp only [or_self, decide_eq_true_eq] at ht
      have := congrArg Fin.val ht
      simp only [Fin.val_natAdd, Fin.val_zero] at this
      omega
  have hOut1313 : wireVal 26 C' C'.output (pairInput (13 : Fin 26) 13) = false := by
    cases h : wireVal 26 C' C'.output (pairInput (13 : Fin 26) 13)
    · rfl
    · exfalso
      obtain ⟨u, t, _, hu, _⟩ := (hEval' _).mp h
      unfold pairInput at hu
      simp only [or_self, decide_eq_true_eq] at hu
      have := congrArg Fin.val hu
      have h13v : (13 : Fin 26).val = 13 := rfl
      simp only [Fin.val_castAdd, h13v] at this
      have := u.isLt
      omega
  have hOut_lt : C'.output < 26 + C'.gates.length := by
    by_contra hge
    have hlen : (C'.wires (List.ofFn (pairInput (0 : Fin 26) 13))).length = 26 + C'.gates.length := by
      change (C'.gates.foldl wstep (List.ofFn (pairInput (0 : Fin 26) 13))).length = _
      rw [wfold_len, List.length_ofFn]
    have hdef : wireVal 26 C' C'.output (pairInput (0 : Fin 26) 13) = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdef] at hOut013; cases hOut013
  have hOut_ge : 26 ≤ C'.output := by
    by_contra hlt
    have h1 := wireVal_input C' (pairInput (0 : Fin 26) 13) C'.output (by omega)
    have h2 := wireVal_input C' (pairInput (0 : Fin 26) 0) C'.output (by omega)
    have h3 := wireVal_input C' (pairInput (13 : Fin 26) 13) C'.output (by omega)
    rw [hOut013] at h1; rw [hOut00] at h2; rw [hOut1313] at h3
    unfold pairInput at h1 h2 h3
    have h1' : (⟨C'.output, by omega⟩ : Fin 26) = 0 ∨ (⟨C'.output, by omega⟩ : Fin 26) = 13 := by
      have := h1.symm
      simpa only [decide_eq_true_eq] using this
    rcases h1' with h | h
    · rw [h] at h2; simp at h2
    · rw [h] at h3; simp at h3
  have hLiveStep : ∀ (k : ℕ) (g : Gate) (c : ℕ),
      (26 + k = C'.output ∨ InCone 26 C' k (C'.output - 26)) →
      C'.gates[k]? = some g → c ∈ g.inputs → 26 ≤ c → c < 26 + k →
      26 + (c - 26) = C'.output ∨ InCone 26 C' (c - 26) (C'.output - 26) := by
    intro k g c hlive hgk hc hge hlt
    have hk : k < C'.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hgk; cases hgk
    have hgateAt : gateAt C' k = g := by
      change C'.gates.getD k ⟨GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem?_getD, hgk]; rfl
    have hck : InCone 26 C' (c - 26) k :=
      (inCone_iff C' (c - 26) k).mpr ⟨hk, c, by rw [hgateAt]; exact hc, hge, hlt, Or.inl rfl⟩
    right
    rcases hlive with heq | hcone
    · have : C'.output - 26 = k := by omega
      rw [this]; exact hck
    · exact inCone_trans C' (c - 26) k (C'.output - 26) hck hcone
  -- Step 3: Extract live double-read AND gate k1 (for line 0) and k2 (for point 0)
  have extract : ∀ (z0 : Fin 26) (u : ℕ → Bool),
      (∀ r < 26, wireVal 26 C' r (pairInput (0 : Fin 26) 13) = true →
        wireVal 26 C' r (pairInput z0 z0) = true ∨ u r = true) →
      (∀ (k : ℕ) (g : Gate) (a b : ℕ), C'.gates[k]? = some g → g.inputs = [a, b] →
        (g.op = GateOp.and → u (26 + k) =
          ((wireVal 26 C' a (pairInput z0 z0) && u b) ||
           (u a && wireVal 26 C' b (pairInput z0 z0)))) ∧
        (g.op = GateOp.or → u (26 + k) = (u a || u b))) →
      wireVal 26 C' C'.output (pairInput z0 z0) = false →
      u C'.output = false →
      ∃ k : ℕ, (gateAt C' k).op = GateOp.and ∧
        (26 + k = C'.output ∨ InCone 26 C' k (C'.output - 26)) ∧
        gateVal 26 C' k (pairInput (0 : Fin 26) 13) = true ∧
        ∀ b : Fin 2, wireVal 26 C' (opnd C' k b) (pairInput z0 z0) = false := by
    intro z0 u hu_base hu_rec hz_out hu_out
    by_contra hno
    have hInv : ∀ r : ℕ, r < 26 + C'.gates.length →
        (r < 26 ∨ (26 + (r - 26) = C'.output ∨ InCone 26 C' (r - 26) (C'.output - 26))) →
        wireVal 26 C' r (pairInput (0 : Fin 26) 13) = true →
        wireVal 26 C' r (pairInput z0 z0) = true ∨ u r = true := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hlive h013
        by_cases hr26 : r < 26
        · exact hu_base r hr26 h013
        · rcases hlive with hbad | hliveG
          · omega
          · let k := r - 26
            have hk : k < C'.gates.length := by omega
            have hrk : r = 26 + k := by omega
            rw [hrk] at h013 ⊢
            have hgk : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk
            obtain ⟨hop, c, d, hinp, _, hc, hd⟩ := hGates' k C'.gates[k] hgk
            have hlt : ∀ i ∈ C'.gates[k].inputs, i < 26 + k := by
              intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
            have hgateAt : gateAt C' k = C'.gates[k] := by
              change C'.gates.getD k ⟨GateOp.or, []⟩ = C'.gates[k]
              rw [List.getD_eq_getElem _ _ hk]
            have hopnd0 : opnd C' k 0 = c := by
              change (gateAt C' k).inputs.getD 0 0 = c; rw [hgateAt, hinp]; rfl
            have hopnd1 : opnd C' k 1 = d := by
              change (gateAt C' k).inputs.getD 1 0 = d; rw [hgateAt, hinp]; rfl
            have hlive_c : c < 26 ∨ (26 + (c - 26) = C'.output ∨ InCone 26 C' (c - 26) (C'.output - 26)) := by
              by_cases hc26 : c < 26
              · exact Or.inl hc26
              · exact Or.inr (hLiveStep k C'.gates[k] c hliveG hgk (by simp [hinp]) (by omega) hc)
            have hlive_d : d < 26 ∨ (26 + (d - 26) = C'.output ∨ InCone 26 C' (d - 26) (C'.output - 26)) := by
              by_cases hd26 : d < 26
              · exact Or.inl hd26
              · exact Or.inr (hLiveStep k C'.gates[k] d hliveG hgk (by simp [hinp]) (by omega) hd)
            have hrec := hu_rec k C'.gates[k] c d hgk hinp
            rw [wireVal_gate C' _ k _ hgk hlt] at h013
            rw [wireVal_gate C' _ k _ hgk hlt]
            rcases hop with hand | hor
            · rw [hand, hinp] at h013 ⊢
              simp only [List.map_cons, List.map_nil] at h013 ⊢
              rw [eval_and, Bool.and_eq_true] at h013 ⊢
              have hu_eq := hrec.1 hand
              cases hcz : wireVal 26 C' c (pairInput z0 z0) <;>
              cases hdz : wireVal 26 C' d (pairInput z0 z0)
              · exfalso
                apply hno
                refine ⟨k, by rw [hgateAt]; exact hand, hliveG, ?_, ?_⟩
                · change wireVal 26 C' (26 + k) (pairInput (0 : Fin 26) 13) = true
                  rw [wireVal_gate C' _ k _ hgk hlt, hand, hinp]
                  simp only [List.map_cons, List.map_nil]
                  rw [eval_and, h013.1, h013.2]; rfl
                · intro b; fin_cases b
                  · dsimp only; rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, hopnd0]; exact hcz
                  · dsimp only; rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, hopnd1]; exact hdz
              · have ihc := ih c (by omega) (by omega) hlive_c h013.1
                rw [hcz] at ihc
                have huc : u c = true := ihc.resolve_left Bool.false_ne_true
                right; rw [hu_eq, huc, hdz]; simp
              · have ihd := ih d (by omega) (by omega) hlive_d h013.2
                rw [hdz] at ihd
                have hud : u d = true := ihd.resolve_left Bool.false_ne_true
                right; rw [hu_eq, hud, hcz]; simp
              · exact Or.inl ⟨rfl, rfl⟩
            · rw [hor, hinp] at h013 ⊢
              simp only [List.map_cons, List.map_nil] at h013 ⊢
              rw [eval_or, Bool.or_eq_true] at h013 ⊢
              have hu_eq := hrec.2 hor
              rcases h013 with hc013 | hd013
              · rcases ih c (by omega) (by omega) hlive_c hc013 with h1 | h2
                · exact Or.inl (Or.inl h1)
                · right; rw [hu_eq, h2]; simp
              · rcases ih d (by omega) (by omega) hlive_d hd013 with h1 | h2
                · exact Or.inl (Or.inr h1)
                · right; rw [hu_eq, h2]; simp
    have hcontra := hInv C'.output hOut_lt (Or.inr (Or.inl (by omega))) hOut013
    rw [hz_out, hu_out] at hcontra
    exact hcontra.elim Bool.false_ne_true Bool.false_ne_true
  have hk1 : ∃ k1 : ℕ, (gateAt C' k1).op = GateOp.and ∧
      (26 + k1 = C'.output ∨ InCone 26 C' k1 (C'.output - 26)) ∧
      gateVal 26 C' k1 (pairInput (0 : Fin 26) 13) = true ∧
      ∀ b : Fin 2, wireVal 26 C' (opnd C' k1 b) (pairInput (0 : Fin 26) 0) = false := by
    apply extract (0 : Fin 26) v' ?_ hv'_rec hOut00 hv'_out
    intro r hr h013
    rw [wireVal_input C' _ r hr] at h013
    rw [wireVal_input C' _ r hr, hv'_base r hr]
    unfold pairInput at h013 ⊢
    simp only [or_self, decide_eq_true_eq] at h013 ⊢
    rcases h013 with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg Fin.val h)
  have hk2 : ∃ k2 : ℕ, (gateAt C' k2).op = GateOp.and ∧
      (26 + k2 = C'.output ∨ InCone 26 C' k2 (C'.output - 26)) ∧
      gateVal 26 C' k2 (pairInput (0 : Fin 26) 13) = true ∧
      ∀ b : Fin 2, wireVal 26 C' (opnd C' k2 b) (pairInput (13 : Fin 26) 13) = false := by
    apply extract (13 : Fin 26) w' ?_ hw'_rec hOut1313 hw'_out
    intro r hr h013
    rw [wireVal_input C' _ r hr] at h013
    rw [wireVal_input C' _ r hr, hw'_base r hr]
    unfold pairInput at h013 ⊢
    simp only [or_self, decide_eq_true_eq] at h013 ⊢
    rcases h013 with h | h
    · exact Or.inr (congrArg Fin.val h)
    · exact Or.inl h
  obtain ⟨k1, hk1_op, hk1_live, hk1_013, hk1_00⟩ := hk1
  obtain ⟨k2, hk2_op, hk2_live, hk2_013, hk2_1313⟩ := hk2
  -- Step 4: Split by relative position of k1 and k2; orient InCone k2 k1 via PG(2,3) self-duality
  by_cases hEq : k1 = k2
  · subst hEq
    exact hSame ⟨C', hSize', hGates', hEval', hDirty', k1, hk1_op, hk1_live, hk1_013,
      fun b => ⟨hk1_00 b, hk2_1313 b⟩⟩
  · by_cases h12 : InCone 26 C' k1 k2
    · exact hChain ⟨C', hSize', hGates', hEval', hDirty', k1, k2, h12,
        ⟨hk1_op, hk1_live, hk1_013, hk1_00⟩,
        ⟨hk2_op, hk2_live, hk2_013, hk2_1313⟩⟩
    · by_cases h21 : InCone 26 C' k2 k1
      · -- Apply PG(2,3) point-line self-duality (u, t) ↦ (-t, -u) to swap 0 and 13
        let δ : Fin 26 → Fin 26 := fun i => Fin.addCases (motive := fun _ => Fin 26)
          (fun u : Fin 13 => Fin.natAdd 13 (-u)) (fun t : Fin 13 => Fin.castAdd 13 (-t)) i
        have hδ_bij : Function.Bijective δ := by decide
        have hδ_cast : ∀ u : Fin 13, δ (Fin.castAdd 13 u) = Fin.natAdd 13 (-u) := by decide
        have hδ_nat : ∀ t : Fin 13, δ (Fin.natAdd 13 t) = Fin.castAdd 13 (-t) := by decide
        have hδ_pres : ∀ e : Fin 26 → Bool,
            (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
              e (δ (Fin.castAdd 13 u)) = true ∧ e (δ (Fin.natAdd 13 t)) = true) ↔
            (∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
              e (Fin.castAdd 13 u) = true ∧ e (Fin.natAdd 13 t) = true) := by
          intro e
          constructor
          · rintro ⟨u, t, hut, h1, h2⟩
            rw [hδ_cast] at h1; rw [hδ_nat] at h2
            refine ⟨-t, -u, ?_, h2, h1⟩
            simpa [sub_neg_eq_add, neg_add_eq_sub] using hut
          · rintro ⟨u, t, hut, h1, h2⟩
            refine ⟨-t, -u, ?_, ?_, ?_⟩
            · simpa [sub_neg_eq_add, neg_add_eq_sub] using hut
            · rw [hδ_cast, neg_neg]; exact h2
            · rw [hδ_nat, neg_neg]; exact h1
        let ρd : ℕ → ℕ := fun i => if h : i < 26 then (δ ⟨i, h⟩).val else i
        let C'' : Circuit := ⟨C'.gates.map (fun g => ⟨g.op, g.inputs.map ρd⟩), ρd C'.output⟩
        obtain ⟨hSize'', hGates'', hEval'', hDirty''⟩ :=
          relabel_all δ hδ_bij hδ_pres C' hSize' hGates' hEval' hDirty'
        have hCones'' : cones 26 C'' = cones 26 C' := relabel_cones δ C'
        have hInCone'' : ∀ a b, InCone 26 C'' a b ↔ InCone 26 C' a b := by
          intro a b; unfold InCone; rw [hCones'']
        have hOut'' : C''.output = C'.output := by
          dsimp only [C'', ρd]; rw [dif_neg (by omega)]
        have hGateOp'' : ∀ k, (gateAt C' k).op = GateOp.and → (gateAt C'' k).op = GateOp.and := by
          intro k hkop
          have hk : k < C'.gates.length := by
            by_contra h
            have : gateAt C' k = ⟨GateOp.or, []⟩ := List.getD_eq_default _ _ (by omega)
            rw [this] at hkop; cases hkop
          have h1 : gateAt C' k = C'.gates[k] := by
            change C'.gates.getD k ⟨GateOp.or, []⟩ = C'.gates[k]
            rw [List.getD_eq_getElem _ _ hk]
          have h2 : gateAt C'' k = C''.gates[k]'(by simpa [C''] using hk) := by
            change C''.gates.getD k ⟨GateOp.or, []⟩ = _
            rw [List.getD_eq_getElem _ _ (by simpa [C''] using hk)]
          rw [h2]; simp only [C'', List.getElem_map]; rw [← h1]; exact hkop
        have hOpnd'' : ∀ k b, (gateAt C' k).op = GateOp.and → opnd C'' k b = ρd (opnd C' k b) := by
          intro k b hkop
          have hk : k < C'.gates.length := by
            by_contra h
            have : gateAt C' k = ⟨GateOp.or, []⟩ := List.getD_eq_default _ _ (by omega)
            rw [this] at hkop; cases hkop
          have hgk : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk
          obtain ⟨_, a, c, hin, _⟩ := hGates' k C'.gates[k] hgk
          have h1 : gateAt C' k = C'.gates[k] := by
            change C'.gates.getD k ⟨GateOp.or, []⟩ = C'.gates[k]
            rw [List.getD_eq_getElem _ _ hk]
          have h2 : gateAt C'' k = C''.gates[k]'(by simpa [C''] using hk) := by
            change C''.gates.getD k ⟨GateOp.or, []⟩ = _
            rw [List.getD_eq_getElem _ _ (by simpa [C''] using hk)]
          unfold opnd
          rw [h1, h2]
          simp only [C'', List.getElem_map, hin, List.map_cons, List.map_nil]
          fin_cases b <;> rfl
        have hδ_013 : (fun i : Fin 26 => pairInput (0 : Fin 26) 13 (δ i)) =
            pairInput (0 : Fin 26) 13 := by funext i; revert i; decide
        have hδ_00 : (fun i : Fin 26 => pairInput (0 : Fin 26) 0 (δ i)) =
            pairInput (13 : Fin 26) 13 := by funext i; revert i; decide
        have hδ_1313 : (fun i : Fin 26 => pairInput (13 : Fin 26) 13 (δ i)) =
            pairInput (0 : Fin 26) 0 := by funext i; revert i; decide
        have hgv'' : ∀ k, gateVal 26 C'' k (pairInput (0 : Fin 26) 13) =
            gateVal 26 C' k (pairInput (0 : Fin 26) 13) := by
          intro k
          have := relabel_wires δ C' (pairInput (0 : Fin 26) 13) (26 + k)
          dsimp only at this
          rw [show (if h : 26 + k < 26 then (δ ⟨26 + k, h⟩).val else 26 + k) = 26 + k from
            dif_neg (by omega), hδ_013] at this
          exact this
        refine hChain ⟨C'', hSize'', hGates'', hEval'', hDirty'', k2, k1,
          (hInCone'' k2 k1).mpr h21,
          ⟨hGateOp'' k2 hk2_op,
            by rw [hOut'']; rcases hk2_live with h | h; exact Or.inl h; exact Or.inr ((hInCone'' _ _).mpr h),
            by rw [hgv'']; exact hk2_013, ?_⟩,
          ⟨hGateOp'' k1 hk1_op,
            by rw [hOut'']; rcases hk1_live with h | h; exact Or.inl h; exact Or.inr ((hInCone'' _ _).mpr h),
            by rw [hgv'']; exact hk1_013, ?_⟩⟩
        · intro b
          rw [hOpnd'' k2 b hk2_op]
          have := relabel_wires δ C' (pairInput (0 : Fin 26) 0) (opnd C' k2 b)
          dsimp only at this
          rw [this, hδ_00]
          exact hk2_1313 b
        · intro b
          rw [hOpnd'' k1 b hk1_op]
          have := relabel_wires δ C' (pairInput (13 : Fin 26) 13) (opnd C' k1 b)
          dsimp only at this
          rw [this, hδ_1313]
          exact hk1_00 b
      · exact hPar ⟨C', hSize', hGates', hEval', hDirty', k1, k2, hEq, h12, h21,
          ⟨hk1_op, hk1_live, hk1_013, hk1_00⟩,
          ⟨hk2_op, hk2_live, hk2_013, hk2_1313⟩⟩
