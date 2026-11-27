import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Reduce the Fano plane double re-read bound via flag transitivity to the fixed incidence
-- (0, 0), extract live double-read AND gates k1 (for line 0) and k2 (for point 0) from the
-- witness maps v and w, and split into three structural cases: k1 = k2, chained (one in the
-- cone of the other), or incomparable (neither in the cone of the other).
theorem PEqualNP.Outside.R_meta_1480_1 :
    (¬ (∃ C : Circuit, C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k : ℕ, (gateAt C k).op = GateOp.and ∧
        (14 + k = C.output ∨ InCone 14 C k (C.output - 14)) ∧
        gateVal 14 C k (pairInput (0 : Fin 14) 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C k b) (pairInput (0 : Fin 14) 0) = false ∧
          wireVal 14 C (opnd C k b) (pairInput (7 : Fin 14) 7) = false)) →
    (¬ (∃ C : Circuit, C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k1 k2 : ℕ, (InCone 14 C k1 k2 ∨ InCone 14 C k2 k1) ∧
        (gateAt C k1).op = GateOp.and ∧
        (14 + k1 = C.output ∨ InCone 14 C k1 (C.output - 14)) ∧
        gateVal 14 C k1 (pairInput (0 : Fin 14) 7) = true ∧
        (∀ b : Fin 2, wireVal 14 C (opnd C k1 b) (pairInput (0 : Fin 14) 0) = false) ∧
        (gateAt C k2).op = GateOp.and ∧
        (14 + k2 = C.output ∨ InCone 14 C k2 (C.output - 14)) ∧
        gateVal 14 C k2 (pairInput (0 : Fin 14) 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C k2 b) (pairInput (7 : Fin 14) 7) = false)) →
    (¬ (∃ C : Circuit, C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧
      ∃ k1 k2 : ℕ, k1 ≠ k2 ∧ ¬ InCone 14 C k1 k2 ∧ ¬ InCone 14 C k2 k1 ∧
        (gateAt C k1).op = GateOp.and ∧
        (14 + k1 = C.output ∨ InCone 14 C k1 (C.output - 14)) ∧
        gateVal 14 C k1 (pairInput (0 : Fin 14) 7) = true ∧
        (∀ b : Fin 2, wireVal 14 C (opnd C k1 b) (pairInput (0 : Fin 14) 0) = false) ∧
        (gateAt C k2).op = GateOp.and ∧
        (14 + k2 = C.output ∨ InCone 14 C k2 (C.output - 14)) ∧
        gateVal 14 C k2 (pairInput (0 : Fin 14) 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C k2 b) (pairInput (7 : Fin 14) 7) = false)) →
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  intro hSame hChain hPar
  rintro ⟨C, hSize, hGates, hFano, p, l, hInc, ⟨v, hvBase, hvRec, hvOut⟩, ⟨w, hwBase, hwRec, hwOut⟩⟩
  -- Step 1: General foldl wire lemmas for Circuit.wires and cones
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
  have wireVal_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      wireVal 14 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hlt : r < (List.ofFn x).length := by omega
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_gate : ∀ (D : Circuit) (x : Fin 14 → Bool) (k : ℕ) (g : Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
      wireVal 14 D (14 + k) x = g.op.eval (g.inputs.map fun i => wireVal 14 D i x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hg_eq : D.gates[k] = g := by
      rw [List.getElem?_eq_getElem hk] at hgk
      exact Option.some.inj hgk
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (D.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + k := by
      dsimp only [pref]
      rw [wfold_len, List.length_ofFn, List.length_take]
      omega
    have hwires_eq : D.wires (List.ofFn x) =
        (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + k, pref.getD i false = wireVal 14 D i x := by
      intro i hi
      change pref.getD i false = (D.wires (List.ofFn x)).getD i false
      rw [hwires_eq]
      have hi1 : i < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ i hi1]
      have hi0 : i < pref.length := by omega
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    change (D.wires (List.ofFn x)).getD (14 + k) false = _
    rw [hwires_eq]
    have hidx : 14 + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref g).getD (14 + k) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
  -- Step 2: General cone lemmas for InCone 14
  let cstep : List (List ℕ) → Gate → List (List ℕ) := fun cs g =>
    cs ++ [(g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
      (fun w => (w - 14) :: cs.getD (w - 14) [])]
  have cfold_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl cstep cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g rest ih =>
      intro cs
      simp only [List.foldl_cons, ih, cstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have cfold_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (r : ℕ),
      r < cs.length → (gs.foldl cstep cs).getD r [] = cs.getD r [] := by
    intro gs
    induction gs with
    | nil => intro cs r _; rfl
    | cons g rest ih =>
      intro cs r hr
      simp only [List.foldl_cons]
      have hr' : r < (cstep cs g).length := by
        simp only [cstep, List.length_append, List.length_singleton]; omega
      rw [ih (cstep cs g) r hr']
      simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have inCone_child : ∀ (D : Circuit) (j : ℕ) (g : Gate) (u : ℕ),
      D.gates[j]? = some g → u ∈ g.inputs → 14 ≤ u → u < 14 + j →
      InCone 14 D (u - 14) j ∧ ∀ i, InCone 14 D i (u - 14) → InCone 14 D i j := by
    intro D j g u hgj hu hu14 huj
    have hj : j < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgj
      cases hgj
    have hg_eq : D.gates[j] = g := by
      rw [List.getElem?_eq_getElem hj] at hgj
      exact Option.some.inj hgj
    have hsplit : D.gates = D.gates.take j ++ g :: D.gates.drop (j + 1) := by
      rw [← hg_eq, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
    let pref := (D.gates.take j).foldl cstep []
    have hpref_len : pref.length = j := by
      dsimp only [pref]
      rw [cfold_len, List.length_nil, List.length_take]
      omega
    have hcones_eq : cones 14 D = (D.gates.drop (j + 1)).foldl cstep (cstep pref g) := by
      change D.gates.foldl cstep [] = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < j, pref.getD i [] = (cones 14 D).getD i [] := by
      intro i hi
      rw [hcones_eq]
      have hi1 : i < (cstep pref g).length := by
        simp only [cstep, List.length_append, List.length_singleton]; omega
      rw [cfold_getD_lt _ _ i hi1]
      have hi0 : i < pref.length := by omega
      simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    have hj_at : (cones 14 D).getD j [] =
        (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j))).flatMap
          (fun w => (w - 14) :: pref.getD (w - 14) []) := by
      rw [hcones_eq]
      have hj1 : j < (cstep pref g).length := by
        simp only [cstep, List.length_append, List.length_singleton]; omega
      rw [cfold_getD_lt _ _ j hj1]
      simp only [cstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    have hu_filt : u ∈ g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j)) :=
      List.mem_filter.mpr ⟨hu, decide_eq_true ⟨hu14, huj⟩⟩
    constructor
    · change u - 14 ∈ (cones 14 D).getD j []
      rw [hj_at]
      exact List.mem_flatMap.mpr ⟨u, hu_filt, List.mem_cons_self⟩
    · intro i hi
      change i ∈ (cones 14 D).getD (u - 14) [] at hi
      change i ∈ (cones 14 D).getD j []
      rw [hj_at]
      refine List.mem_flatMap.mpr ⟨u, hu_filt, List.mem_cons_of_mem _ ?_⟩
      rw [hpref_get (u - 14) (by omega)]
      exact hi
  -- Step 3: Fano plane flag transitivity mapping (0, 0) to (p, l)
  have hAut : ∃ (fP fL gP gL : Fin 7 → Fin 7),
      (∀ u, gP (fP u) = u ∧ fP (gP u) = u) ∧
      (∀ t, gL (fL t) = t ∧ fL (gL t) = t) ∧
      fP 0 = p ∧ fL 0 = l ∧
      (∀ u t : Fin 7,
        (fP u = fL t ∨ fP u = fL t + 1 ∨ fP u = fL t + 3) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3)) := by
    have hdiff : ∀ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ↔
        (u - t = 0 ∨ u - t = 1 ∨ u - t = 3) := by
      intro u t; simp [sub_eq_iff_eq_add, add_comm]
    have hadd : ∀ u l0 : Fin 7, (u + l0) - l0 = u ∧ (u - l0) + l0 = u := by decide
    have hm2_inv : ∀ u l0 : Fin 7,
        4 * (2 * u + 1 + l0 - l0 - 1) = u ∧ 2 * (4 * (u - l0 - 1)) + 1 + l0 = u := by decide
    have hm2_inv0 : ∀ t l0 : Fin 7,
        4 * (2 * t + l0 - l0) = t ∧ 2 * (4 * (t - l0)) + l0 = t := by decide
    have hm4_inv : ∀ u l0 : Fin 7,
        2 * (4 * u + 3 + l0 - l0 - 3) = u ∧ 4 * (2 * (u - l0 - 3)) + 3 + l0 = u := by decide
    have hm4_inv0 : ∀ t l0 : Fin 7,
        2 * (4 * t + l0 - l0) = t ∧ 4 * (2 * (t - l0)) + l0 = t := by decide
    have h0_eval : ∀ l0 : Fin 7,
        0 + l0 = l0 ∧ 2 * 0 + 1 + l0 = l0 + 1 ∧ 2 * 0 + l0 = l0 ∧
        4 * 0 + 3 + l0 = l0 + 3 ∧ 4 * 0 + l0 = l0 := by decide
    have hsub_mul2 : ∀ u t : Fin 7, (2 * u + 1) - 2 * t = 2 * (u - t) + 1 := by decide
    have hsub_mul4 : ∀ u t : Fin 7, (4 * u + 3) - 4 * t = 4 * (u - t) + 3 := by decide
    have hm2 : ∀ d : Fin 7, (2 * d + 1 = 0 ∨ 2 * d + 1 = 1 ∨ 2 * d + 1 = 3) ↔
        (d = 0 ∨ d = 1 ∨ d = 3) := by decide
    have hm4 : ∀ d : Fin 7, (4 * d + 3 = 0 ∨ 4 * d + 3 = 1 ∨ 4 * d + 3 = 3) ↔
        (d = 0 ∨ d = 1 ∨ d = 3) := by decide
    rcases hInc with hpl | hpl | hpl
    · subst p
      refine ⟨fun u => u + l, fun t => t + l, fun u => u - l, fun t => t - l,
        fun u => hadd u l, fun t => hadd t l, (h0_eval l).1, (h0_eval l).1, ?_⟩
      intro u t; rw [hdiff, hdiff, add_sub_add_right_eq_sub]
    · subst p
      refine ⟨fun u => 2 * u + 1 + l, fun t => 2 * t + l,
        fun u => 4 * (u - l - 1), fun t => 4 * (t - l),
        fun u => hm2_inv u l, fun t => hm2_inv0 t l, (h0_eval l).2.1, (h0_eval l).2.2.1, ?_⟩
      intro u t; rw [hdiff, hdiff, add_sub_add_right_eq_sub, hsub_mul2]; exact hm2 (u - t)
    · subst p
      refine ⟨fun u => 4 * u + 3 + l, fun t => 4 * t + l,
        fun u => 2 * (u - l - 3), fun t => 2 * (t - l),
        fun u => hm4_inv u l, fun t => hm4_inv0 t l, (h0_eval l).2.2.2.1, (h0_eval l).2.2.2.2, ?_⟩
      intro u t; rw [hdiff, hdiff, add_sub_add_right_eq_sub, hsub_mul4]; exact hm4 (u - t)
  obtain ⟨fP, fL, gP, gL, hPG, hLG, hfP0, hfL0, hPres⟩ := hAut
  let pi : Fin 14 → Fin 14 := fun i =>
    if h : i.val < 7 then Fin.castAdd 7 (fP ⟨i.val, h⟩)
    else Fin.natAdd 7 (fL ⟨i.val - 7, by omega⟩)
  let piInv : Fin 14 → Fin 14 := fun i =>
    if h : i.val < 7 then Fin.castAdd 7 (gP ⟨i.val, h⟩)
    else Fin.natAdd 7 (gL ⟨i.val - 7, by omega⟩)
  have hpi_cast : ∀ u : Fin 7, pi (Fin.castAdd 7 u) = Fin.castAdd 7 (fP u) := by
    intro u; simp [pi, u.isLt]
  have hpi_nat : ∀ t : Fin 7, pi (Fin.natAdd 7 t) = Fin.natAdd 7 (fL t) := by
    intro t; simp [pi]
  have hpiInv_cast : ∀ u : Fin 7, piInv (Fin.castAdd 7 u) = Fin.castAdd 7 (gP u) := by
    intro u; simp [piInv, u.isLt]
  have hpiInv_nat : ∀ t : Fin 7, piInv (Fin.natAdd 7 t) = Fin.natAdd 7 (gL t) := by
    intro t; simp [piInv]
  have hpi_inv : ∀ i : Fin 14, piInv (pi i) = i := by
    intro i
    by_cases h : i.val < 7
    · have hi : i = Fin.castAdd 7 ⟨i.val, h⟩ := by ext; rfl
      rw [hi, hpi_cast, hpiInv_cast, (hPG _).1]
    · have hi : i = Fin.natAdd 7 (⟨i.val - 7, by omega⟩ : Fin 7) :=
        Fin.ext (by show i.val = 7 + (i.val - 7); omega)
      rw [hi, hpi_nat, hpiInv_nat, (hLG _).1]
  have hinv_pi : ∀ i : Fin 14, pi (piInv i) = i := by
    intro i
    by_cases h : i.val < 7
    · have hi : i = Fin.castAdd 7 ⟨i.val, h⟩ := by ext; rfl
      rw [hi, hpiInv_cast, hpi_cast, (hPG _).2]
    · have hi : i = Fin.natAdd 7 (⟨i.val - 7, by omega⟩ : Fin 7) :=
        Fin.ext (by show i.val = 7 + (i.val - 7); omega)
      rw [hi, hpiInv_nat, hpi_nat, (hLG _).2]
  -- Relabeled circuit C' moving (p, l) to (0, 0)
  let mapW : ℕ → ℕ := fun r => if h : r < 14 then (piInv ⟨r, h⟩).val else r
  have hmapW_inj : ∀ a b : ℕ, mapW a = mapW b → a = b := by
    intro a b hab
    by_cases ha : a < 14 <;> by_cases hb : b < 14
    · simp only [mapW, ha, hb, ↓reduceDIte] at hab
      have heq : piInv ⟨a, ha⟩ = piInv ⟨b, hb⟩ := Fin.ext hab
      have h2 := congrArg pi heq
      rw [hinv_pi, hinv_pi] at h2
      exact congrArg Fin.val h2
    · simp only [mapW, ha, hb, ↓reduceDIte] at hab
      have := (piInv ⟨a, ha⟩).isLt; omega
    · simp only [mapW, ha, hb, ↓reduceDIte] at hab
      have := (piInv ⟨b, hb⟩).isLt; omega
    · simp only [mapW, ha, hb, ↓reduceDIte] at hab; exact hab
  have hmapW_lt : ∀ a j : ℕ, a < 14 + j → mapW a < 14 + j := by
    intro a j haj
    by_cases ha : a < 14
    · simp only [mapW, ha, ↓reduceDIte]
      have := (piInv ⟨a, ha⟩).isLt; omega
    · simp only [mapW, ha, ↓reduceDIte]; exact haj
  let C' : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩, mapW C.output⟩
  have hSize' : C'.size ≤ 27 := by
    change (C.gates.map fun g => (⟨g.op, g.inputs.map mapW⟩ : Gate)).length ≤ 27
    rw [List.length_map]; exact hSize
  have hGates' : ∀ (j : ℕ) (g : Gate), C'.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
    intro j g hgj
    simp only [C', List.getElem?_map] at hgj
    rcases hCgj : C.gates[j]? with _ | g0
    · rw [hCgj] at hgj; simp at hgj
    · rw [hCgj] at hgj
      have hge := Option.some.inj hgj
      subst hge
      obtain ⟨hop, a, b, hinp, hne, ha, hb⟩ := hGates j g0 hCgj
      refine ⟨hop, mapW a, mapW b, by simp [hinp], fun heq => hne (hmapW_inj a b heq),
        hmapW_lt a j ha, hmapW_lt b j hb⟩
  have hWireMap : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.gates.length →
      wireVal 14 C' (mapW r) x = wireVal 14 C r (fun i => x (piInv i)) := by
    intro x r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr
      by_cases hr14 : r < 14
      · simp only [mapW, hr14, ↓reduceDIte]
        rw [wireVal_input C' x _ (piInv ⟨r, hr14⟩).isLt, wireVal_input C _ r hr14]
      · have hmap_eq : mapW r = r := by simp [mapW, hr14]
        rw [hmap_eq]
        let k := r - 14
        have hk : k < C.gates.length := by omega
        have hrk : r = 14 + k := by omega
        rw [hrk]
        have hCgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
        have hC'gk : C'.gates[k]? = some ⟨C.gates[k].op, C.gates[k].inputs.map mapW⟩ := by
          simp [C', List.getElem?_map, hCgk]
        obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates k C.gates[k] hCgk
        have hltC : ∀ i ∈ C.gates[k].inputs, i < 14 + k := by
          intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
        have hltC' : ∀ i ∈ (C.gates[k].inputs.map mapW), i < 14 + k := by
          intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          exact hmapW_lt i0 k (hltC i0 hi0)
        rw [wireVal_gate C' x k _ hC'gk hltC', wireVal_gate C _ k _ hCgk hltC]
        simp only [List.map_map]
        congr 1
        exact List.map_congr_left fun i hi => ih i (by have := hltC i hi; omega) (by have := hltC i hi; omega)
  have hEvalMap : ∀ x : Fin 14 → Bool,
      C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (piInv i))) := by
    intro x
    by_cases ho : C.output < 14 + C.gates.length
    · exact hWireMap x C.output ho
    · have hlenC : (C.wires (List.ofFn (fun i => x (piInv i)))).length = 14 + C.gates.length := by
        change (C.gates.foldl wstep (List.ofFn (fun i => x (piInv i)))).length = _
        rw [wfold_len, List.length_ofFn]
      have hlenC' : (C'.wires (List.ofFn x)).length = 14 + C.gates.length := by
        change (C'.gates.foldl wstep (List.ofFn x)).length = _
        rw [wfold_len, List.length_ofFn]; simp [C']
      have ho' : ¬ C'.output < 14 + C.gates.length := by
        have h14 : ¬ C.output < 14 := by omega
        simp [C', mapW, h14]; omega
      change (C'.wires (List.ofFn x)).getD C'.output false =
        (C.wires (List.ofFn (fun i => x (piInv i)))).getD C.output false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hFano' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    intro x
    rw [hEvalMap x, hFano (fun i => x (piInv i))]
    constructor
    · rintro ⟨u, t, hinc, hu, ht⟩
      refine ⟨gP u, gL t, ?_, ?_, ?_⟩
      · rw [← hPres (gP u) (gL t), (hPG u).2, (hLG t).2]; exact hinc
      · rw [hpiInv_cast] at hu; exact hu
      · rw [hpiInv_nat] at ht; exact ht
    · rintro ⟨u, t, hinc, hu, ht⟩
      refine ⟨fP u, fL t, (hPres u t).mpr hinc, ?_, ?_⟩
      · rw [hpiInv_cast, (hPG u).1]; exact hu
      · rw [hpiInv_nat, (hLG t).1]; exact ht
  -- Step 4: Transfer v and w to v' and w' on C' at (0, 0)
  let v' : ℕ → Bool := fun r => if h : r < 14 then v (pi ⟨r, h⟩).val else v r
  let w' : ℕ → Bool := fun r => if h : r < 14 then w (pi ⟨r, h⟩).val else w r
  have hv'_map : ∀ a : ℕ, v' (mapW a) = v a := by
    intro a
    by_cases ha : a < 14
    · simp only [mapW, ha, ↓reduceDIte, v', (piInv ⟨a, ha⟩).isLt, hinv_pi]
    · simp only [mapW, ha, ↓reduceDIte, v']
  have hw'_map : ∀ a : ℕ, w' (mapW a) = w a := by
    intro a
    by_cases ha : a < 14
    · simp only [mapW, ha, ↓reduceDIte, w', (piInv ⟨a, ha⟩).isLt, hinv_pi]
    · simp only [mapW, ha, ↓reduceDIte, w']
  have hpi_0 : pi (0 : Fin 14) = Fin.castAdd 7 p := by
    have h0 : (0 : Fin 14) = Fin.castAdd 7 (0 : Fin 7) := by ext; rfl
    rw [h0, hpi_cast, hfP0]
  have hpi_7 : pi (7 : Fin 14) = Fin.natAdd 7 l := by
    have h7 : (7 : Fin 14) = Fin.natAdd 7 (0 : Fin 7) := by ext; rfl
    rw [h7, hpi_nat, hfL0]
  have hpair00_eq : (fun i : Fin 14 => pairInput (0 : Fin 14) 0 (piInv i)) =
      (fun i : Fin 14 => decide (i = Fin.castAdd 7 p)) := by
    funext i
    change decide (piInv i = (0 : Fin 14) ∨ piInv i = 0) = decide (i = Fin.castAdd 7 p)
    simp only [or_self]
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := congrArg pi h; rw [hinv_pi, hpi_0] at h2; exact h2
    · rw [h, ← hpi_0, hpi_inv]
  have hpair77_eq : (fun i : Fin 14 => pairInput (7 : Fin 14) 7 (piInv i)) =
      (fun i : Fin 14 => decide (i = Fin.natAdd 7 l)) := by
    funext i
    change decide (piInv i = (7 : Fin 14) ∨ piInv i = 7) = decide (i = Fin.natAdd 7 l)
    simp only [or_self]
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := congrArg pi h; rw [hinv_pi, hpi_7] at h2; exact h2
    · rw [h, ← hpi_7, hpi_inv]
  have hv'_out : v' C'.output = false := by
    change v' (mapW C.output) = false; rw [hv'_map, hvOut]
  have hw'_out : w' C'.output = false := by
    change w' (mapW C.output) = false; rw [hw'_map, hwOut]
  have hv'_base : ∀ r < 14,
      wireVal 14 C' r (pairInput (0 : Fin 14) 7) = true →
      wireVal 14 C' r (pairInput (0 : Fin 14) 0) = true ∨ v' r = true := by
    intro r hr h07
    rw [wireVal_input C' _ r hr] at h07
    rw [wireVal_input C' _ r hr]
    change decide ((⟨r, hr⟩ : Fin 14) = 0 ∨ (⟨r, hr⟩ : Fin 14) = 7) = true at h07
    change decide ((⟨r, hr⟩ : Fin 14) = 0 ∨ (⟨r, hr⟩ : Fin 14) = 0) = true ∨ v' r = true
    simp only [decide_eq_true_eq] at h07 ⊢
    rcases h07 with h0 | h7
    · exact Or.inl (Or.inl h0)
    · right
      have hr7 : r = 7 := congrArg Fin.val h7
      subst hr7
      simp only [v', hr, ↓reduceDIte]
      have heq : pi ⟨7, hr⟩ = Fin.natAdd 7 l := hpi_7
      rw [heq]
      exact (hvBase l).2.trans (decide_eq_true rfl)
  have hw'_base : ∀ r < 14,
      wireVal 14 C' r (pairInput (0 : Fin 14) 7) = true →
      wireVal 14 C' r (pairInput (7 : Fin 14) 7) = true ∨ w' r = true := by
    intro r hr h07
    rw [wireVal_input C' _ r hr] at h07
    rw [wireVal_input C' _ r hr]
    change decide ((⟨r, hr⟩ : Fin 14) = 0 ∨ (⟨r, hr⟩ : Fin 14) = 7) = true at h07
    change decide ((⟨r, hr⟩ : Fin 14) = 7 ∨ (⟨r, hr⟩ : Fin 14) = 7) = true ∨ w' r = true
    simp only [decide_eq_true_eq] at h07 ⊢
    rcases h07 with h0 | h7
    · right
      have hr0 : r = 0 := congrArg Fin.val h0
      subst hr0
      simp only [w', hr, ↓reduceDIte]
      have heq : pi ⟨0, hr⟩ = Fin.castAdd 7 p := hpi_0
      rw [heq]
      exact (hwBase p).1.trans (decide_eq_true rfl)
    · exact Or.inl (Or.inl h7)
  have hv'_rec : ∀ (k : ℕ) (g : Gate) (c d : ℕ), C'.gates[k]? = some g → g.inputs = [c, d] →
      (g.op = GateOp.and → v' (14 + k) =
        ((wireVal 14 C' c (pairInput (0 : Fin 14) 0) && v' d) ||
         (v' c && wireVal 14 C' d (pairInput (0 : Fin 14) 0)))) ∧
      (g.op = GateOp.or → v' (14 + k) = (v' c || v' d)) := by
    intro k g c d hgk hinp
    simp only [C', List.getElem?_map] at hgk
    rcases hCgk : C.gates[k]? with _ | g0
    · rw [hCgk] at hgk; simp at hgk
    · rw [hCgk] at hgk
      have hge := Option.some.inj hgk
      subst hge
      obtain ⟨_, a, b, hinp0, _, ha, hb⟩ := hGates k g0 hCgk
      have hcd : [mapW a, mapW b] = [c, d] := by simpa [hinp0] using hinp
      have hc : c = mapW a := (List.cons.inj hcd).1.symm
      have hd : d = mapW b := (List.cons.inj (List.cons.inj hcd).2).1.symm
      subst hc; subst hd
      have hk_len : k < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hCgk; cases hCgk
      have h14k : ¬ (14 + k < 14) := by omega
      have hvk : v' (14 + k) = v (14 + k) := by simp [v', h14k]
      have hwa : wireVal 14 C' (mapW a) (pairInput (0 : Fin 14) 0) =
          (C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD a false := by
        rw [hWireMap _ a (by omega), hpair00_eq]; rfl
      have hwb : wireVal 14 C' (mapW b) (pairInput (0 : Fin 14) 0) =
          (C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD b false := by
        rw [hWireMap _ b (by omega), hpair00_eq]; rfl
      have hr := hvRec k g0 a b hCgk hinp0
      rw [hvk, hv'_map a, hv'_map b, hwa, hwb]
      exact hr
  have hw'_rec : ∀ (k : ℕ) (g : Gate) (c d : ℕ), C'.gates[k]? = some g → g.inputs = [c, d] →
      (g.op = GateOp.and → w' (14 + k) =
        ((wireVal 14 C' c (pairInput (7 : Fin 14) 7) && w' d) ||
         (w' c && wireVal 14 C' d (pairInput (7 : Fin 14) 7)))) ∧
      (g.op = GateOp.or → w' (14 + k) = (w' c || w' d)) := by
    intro k g c d hgk hinp
    simp only [C', List.getElem?_map] at hgk
    rcases hCgk : C.gates[k]? with _ | g0
    · rw [hCgk] at hgk; simp at hgk
    · rw [hCgk] at hgk
      have hge := Option.some.inj hgk
      subst hge
      obtain ⟨_, a, b, hinp0, _, ha, hb⟩ := hGates k g0 hCgk
      have hcd : [mapW a, mapW b] = [c, d] := by simpa [hinp0] using hinp
      have hc : c = mapW a := (List.cons.inj hcd).1.symm
      have hd : d = mapW b := (List.cons.inj (List.cons.inj hcd).2).1.symm
      subst hc; subst hd
      have hk_len : k < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hCgk; cases hCgk
      have h14k : ¬ (14 + k < 14) := by omega
      have hwk : w' (14 + k) = w (14 + k) := by simp [w', h14k]
      have hwa : wireVal 14 C' (mapW a) (pairInput (7 : Fin 14) 7) =
          (C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD a false := by
        rw [hWireMap _ a (by omega), hpair77_eq]; rfl
      have hwb : wireVal 14 C' (mapW b) (pairInput (7 : Fin 14) 7) =
          (C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD b false := by
        rw [hWireMap _ b (by omega), hpair77_eq]; rfl
      have hr := hwRec k g0 a b hCgk hinp0
      rw [hwk, hw'_map a, hw'_map b, hwa, hwb]
      exact hr
  -- Step 5: Locate C'.output as a real gate 14 + outG and extract live k1 and k2
  have hOut07 : wireVal 14 C' C'.output (pairInput (0 : Fin 14) 7) = true := by
    change C'.eval (List.ofFn (pairInput (0 : Fin 14) 7)) = true
    exact (hFano' _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
  have hOut00 : wireVal 14 C' C'.output (pairInput (0 : Fin 14) 0) = false := by
    change C'.eval (List.ofFn (pairInput (0 : Fin 14) 0)) = false
    cases h : C'.eval (List.ofFn (pairInput (0 : Fin 14) 0))
    · rfl
    · exfalso
      obtain ⟨u, t, _, _, ht⟩ := (hFano' _).mp h
      change decide (Fin.natAdd 7 t = (0 : Fin 14) ∨ Fin.natAdd 7 t = 0) = true at ht
      simp only [or_self, decide_eq_true_eq] at ht
      have h7 : (Fin.natAdd 7 t).val = 0 := congrArg Fin.val ht
      simp at h7
  have hOut77 : wireVal 14 C' C'.output (pairInput (7 : Fin 14) 7) = false := by
    change C'.eval (List.ofFn (pairInput (7 : Fin 14) 7)) = false
    cases h : C'.eval (List.ofFn (pairInput (7 : Fin 14) 7))
    · rfl
    · exfalso
      obtain ⟨u, t, _, hu, _⟩ := (hFano' _).mp h
      change decide (Fin.castAdd 7 u = (7 : Fin 14) ∨ Fin.castAdd 7 u = 7) = true at hu
      simp only [or_self, decide_eq_true_eq] at hu
      have h7 : (Fin.castAdd 7 u).val = 7 := congrArg Fin.val hu
      simp at h7
      omega
  have hOut_lt : C'.output < 14 + C'.gates.length := by
    by_contra hge
    have hlen : (C'.wires (List.ofFn (pairInput (0 : Fin 14) 7))).length = 14 + C'.gates.length := by
      change (C'.gates.foldl wstep (List.ofFn (pairInput (0 : Fin 14) 7))).length = _
      rw [wfold_len, List.length_ofFn]
    have hf : wireVal 14 C' C'.output (pairInput (0 : Fin 14) 7) = false := by
      change (C'.wires (List.ofFn (pairInput (0 : Fin 14) 7))).getD C'.output false = false
      exact List.getD_eq_default _ _ (by omega)
    rw [hOut07] at hf; exact Bool.noConfusion hf
  have hOut_ge14 : 14 ≤ C'.output := by
    by_contra hlt
    have hlt14 : C'.output < 14 := by omega
    have h1 := wireVal_input C' (pairInput ⟨C'.output, hlt14⟩ ⟨C'.output, hlt14⟩) C'.output hlt14
    have htrue : C'.eval (List.ofFn (pairInput ⟨C'.output, hlt14⟩ ⟨C'.output, hlt14⟩)) = true := by
      change wireVal 14 C' C'.output _ = true
      rw [h1]
      change decide (⟨C'.output, hlt14⟩ = (⟨C'.output, hlt14⟩ : Fin 14) ∨
        ⟨C'.output, hlt14⟩ = (⟨C'.output, hlt14⟩ : Fin 14)) = true
      exact decide_eq_true (Or.inl rfl)
    obtain ⟨u, t, _, hu, ht⟩ := (hFano' _).mp htrue
    change decide (Fin.castAdd 7 u = ⟨C'.output, hlt14⟩ ∨ Fin.castAdd 7 u = ⟨C'.output, hlt14⟩) = true at hu
    change decide (Fin.natAdd 7 t = ⟨C'.output, hlt14⟩ ∨ Fin.natAdd 7 t = ⟨C'.output, hlt14⟩) = true at ht
    simp only [or_self, decide_eq_true_eq] at hu ht
    have hu' := congrArg Fin.val hu
    have ht' := congrArg Fin.val ht
    simp at hu' ht'
    omega
  -- Prove InCone transitivity via strong induction on j
  have inCone_trans : ∀ (j : ℕ), j < C'.gates.length →
      ∀ (a b : ℕ), InCone 14 C' a b → InCone 14 C' b j → InCone 14 C' a j := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj a b hab hbj
      let gj := C'.gates[j]
      have hgj : C'.gates[j]? = some gj := List.getElem?_eq_getElem hj
      let pref := (C'.gates.take j).foldl cstep []
      have hsplit : C'.gates = C'.gates.take j ++ gj :: C'.gates.drop (j + 1) := by
        dsimp only [gj]
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      have hpref_len : pref.length = j := by
        dsimp only [pref]; rw [cfold_len, List.length_nil, List.length_take]; omega
      have hcones_eq : cones 14 C' =
          (C'.gates.drop (j + 1)).foldl cstep (cstep pref gj) := by
        change C'.gates.foldl cstep [] = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hpref_get : ∀ i < j, pref.getD i [] = (cones 14 C').getD i [] := by
        intro i hi
        rw [hcones_eq]
        have hi1 : i < (cstep pref gj).length := by
          simp only [cstep, List.length_append, List.length_singleton]; omega
        rw [cfold_getD_lt _ _ i hi1]
        simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.length)]
      have hj_at : (cones 14 C').getD j [] =
          (gj.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j))).flatMap
            (fun w => (w - 14) :: pref.getD (w - 14) []) := by
        rw [hcones_eq]
        have hj1 : j < (cstep pref gj).length := by
          simp only [cstep, List.length_append, List.length_singleton]; omega
        rw [cfold_getD_lt _ _ j hj1]
        simp only [cstep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), hpref_len]; simp
      change b ∈ (cones 14 C').getD j [] at hbj
      rw [hj_at] at hbj
      obtain ⟨u, hu_filt, hb_mem⟩ := List.mem_flatMap.mp hbj
      obtain ⟨hu_in, hu_dec⟩ := List.mem_filter.mp hu_filt
      obtain ⟨hu14, huj⟩ := of_decide_eq_true hu_dec
      obtain ⟨_, hc2⟩ := inCone_child C' j gj u hgj hu_in hu14 huj
      rcases List.mem_cons.mp hb_mem with rfl | hb_tail
      · exact hc2 a hab
      · rw [hpref_get (u - 14) (by omega)] at hb_tail
        exact hc2 a (ih (u - 14) (by omega) (by omega) a b hab hb_tail)
  have hLiveStep : ∀ (k : ℕ) (g : Gate) (u : ℕ),
      (14 + k = C'.output ∨ InCone 14 C' k (C'.output - 14)) →
      C'.gates[k]? = some g → u ∈ g.inputs → 14 ≤ u → u < 14 + k →
      14 + (u - 14) = C'.output ∨ InCone 14 C' (u - 14) (C'.output - 14) := by
    intro k g u hlive hgk hu hu14 huk
    obtain ⟨hc1, _⟩ := inCone_child C' k g u hgk hu hu14 huk
    rcases hlive with hEq | hIn
    · right
      have hko : k = C'.output - 14 := by omega
      rw [← hko]; exact hc1
    · right
      exact inCone_trans (C'.output - 14) (by omega) (u - 14) k hc1 hIn
  -- Extract k1 (live double-read of line 0)
  have hk1 : ∃ k1 : ℕ, k1 < C'.gates.length ∧ (gateAt C' k1).op = GateOp.and ∧
      (14 + k1 = C'.output ∨ InCone 14 C' k1 (C'.output - 14)) ∧
      gateVal 14 C' k1 (pairInput (0 : Fin 14) 7) = true ∧
      wireVal 14 C' (opnd C' k1 0) (pairInput (0 : Fin 14) 0) = false ∧
      wireVal 14 C' (opnd C' k1 1) (pairInput (0 : Fin 14) 0) = false := by
    by_contra hno
    have hInv : ∀ r : ℕ, r < 14 + C'.gates.length →
        (r < 14 ∨ (14 + (r - 14) = C'.output ∨ InCone 14 C' (r - 14) (C'.output - 14))) →
        wireVal 14 C' r (pairInput (0 : Fin 14) 7) = true →
        wireVal 14 C' r (pairInput (0 : Fin 14) 0) = true ∨ v' r = true := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hlive h07
        by_cases hr14 : r < 14
        · exact hv'_base r hr14 h07
        · rcases hlive with hbad | hliveG
          · omega
          · let k := r - 14
            have hk : k < C'.gates.length := by omega
            have hrk : r = 14 + k := by omega
            rw [hrk] at h07 ⊢
            have hgk : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk
            obtain ⟨hop, c, d, hinp, _, hc, hd⟩ := hGates' k C'.gates[k] hgk
            have hlt : ∀ i ∈ C'.gates[k].inputs, i < 14 + k := by
              intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
            have hgateAt : gateAt C' k = C'.gates[k] := by
              change C'.gates.getD k ⟨GateOp.or, []⟩ = C'.gates[k]
              rw [List.getD_eq_getElem _ _ hk]
            have hopnd0 : opnd C' k 0 = c := by
              change (gateAt C' k).inputs.getD 0 0 = c; rw [hgateAt, hinp]; rfl
            have hopnd1 : opnd C' k 1 = d := by
              change (gateAt C' k).inputs.getD 1 0 = d; rw [hgateAt, hinp]; rfl
            have hlive_c : c < 14 ∨ (14 + (c - 14) = C'.output ∨ InCone 14 C' (c - 14) (C'.output - 14)) := by
              by_cases hc14 : c < 14
              · exact Or.inl hc14
              · exact Or.inr (hLiveStep k C'.gates[k] c hliveG hgk (by simp [hinp]) (by omega) hc)
            have hlive_d : d < 14 ∨ (14 + (d - 14) = C'.output ∨ InCone 14 C' (d - 14) (C'.output - 14)) := by
              by_cases hd14 : d < 14
              · exact Or.inl hd14
              · exact Or.inr (hLiveStep k C'.gates[k] d hliveG hgk (by simp [hinp]) (by omega) hd)
            have hrec := hv'_rec k C'.gates[k] c d hgk hinp
            rw [wireVal_gate C' _ k _ hgk hlt] at h07
            rw [wireVal_gate C' _ k _ hgk hlt]
            rcases hop with hand | hor
            · rw [hand, hinp] at h07 ⊢
              simp only [List.map_cons, List.map_nil] at h07 ⊢
              rw [eval_and, Bool.and_eq_true] at h07 ⊢
              have hv_eq := hrec.1 hand
              cases hc0 : wireVal 14 C' c (pairInput (0 : Fin 14) 0) <;>
              cases hd0 : wireVal 14 C' d (pairInput (0 : Fin 14) 0)
              · exfalso
                apply hno
                refine ⟨k, hk, by rw [hgateAt]; exact hand, hliveG, ?_, by rw [hopnd0]; exact hc0, by rw [hopnd1]; exact hd0⟩
                change wireVal 14 C' (14 + k) (pairInput (0 : Fin 14) 7) = true
                rw [wireVal_gate C' _ k _ hgk hlt, hand, hinp]
                simp only [List.map_cons, List.map_nil]
                rw [eval_and, h07.1, h07.2]; rfl
              · have ihc := ih c (by omega) (by omega) hlive_c h07.1
                rw [hc0] at ihc
                have hvc : v' c = true := ihc.resolve_left Bool.false_ne_true
                right; rw [hv_eq, hvc, hd0]; simp
              · have ihd := ih d (by omega) (by omega) hlive_d h07.2
                rw [hd0] at ihd
                have hvd : v' d = true := ihd.resolve_left Bool.false_ne_true
                right; rw [hv_eq, hvd, hc0]; simp
              · exact Or.inl ⟨rfl, rfl⟩
            · rw [hor, hinp] at h07 ⊢
              simp only [List.map_cons, List.map_nil] at h07 ⊢
              rw [eval_or, Bool.or_eq_true] at h07 ⊢
              have hv_eq := hrec.2 hor
              rcases h07 with hc07 | hd07
              · rcases ih c (by omega) (by omega) hlive_c hc07 with h1 | h2
                · exact Or.inl (Or.inl h1)
                · right; rw [hv_eq, h2]; simp
              · rcases ih d (by omega) (by omega) hlive_d hd07 with h1 | h2
                · exact Or.inl (Or.inr h1)
                · right; rw [hv_eq, h2]; simp
    have hcontra := hInv C'.output hOut_lt (Or.inr (Or.inl (by omega))) hOut07
    rw [hOut00, hv'_out] at hcontra
    exact hcontra.elim Bool.false_ne_true Bool.false_ne_true
  -- Extract k2 (live double-read of point 0)
  have hk2 : ∃ k2 : ℕ, k2 < C'.gates.length ∧ (gateAt C' k2).op = GateOp.and ∧
      (14 + k2 = C'.output ∨ InCone 14 C' k2 (C'.output - 14)) ∧
      gateVal 14 C' k2 (pairInput (0 : Fin 14) 7) = true ∧
      wireVal 14 C' (opnd C' k2 0) (pairInput (7 : Fin 14) 7) = false ∧
      wireVal 14 C' (opnd C' k2 1) (pairInput (7 : Fin 14) 7) = false := by
    by_contra hno
    have hInv : ∀ r : ℕ, r < 14 + C'.gates.length →
        (r < 14 ∨ (14 + (r - 14) = C'.output ∨ InCone 14 C' (r - 14) (C'.output - 14))) →
        wireVal 14 C' r (pairInput (0 : Fin 14) 7) = true →
        wireVal 14 C' r (pairInput (7 : Fin 14) 7) = true ∨ w' r = true := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hlive h07
        by_cases hr14 : r < 14
        · exact hw'_base r hr14 h07
        · rcases hlive with hbad | hliveG
          · omega
          · let k := r - 14
            have hk : k < C'.gates.length := by omega
            have hrk : r = 14 + k := by omega
            rw [hrk] at h07 ⊢
            have hgk : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk
            obtain ⟨hop, c, d, hinp, _, hc, hd⟩ := hGates' k C'.gates[k] hgk
            have hlt : ∀ i ∈ C'.gates[k].inputs, i < 14 + k := by
              intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
            have hgateAt : gateAt C' k = C'.gates[k] := by
              change C'.gates.getD k ⟨GateOp.or, []⟩ = C'.gates[k]
              rw [List.getD_eq_getElem _ _ hk]
            have hopnd0 : opnd C' k 0 = c := by
              change (gateAt C' k).inputs.getD 0 0 = c; rw [hgateAt, hinp]; rfl
            have hopnd1 : opnd C' k 1 = d := by
              change (gateAt C' k).inputs.getD 1 0 = d; rw [hgateAt, hinp]; rfl
            have hlive_c : c < 14 ∨ (14 + (c - 14) = C'.output ∨ InCone 14 C' (c - 14) (C'.output - 14)) := by
              by_cases hc14 : c < 14
              · exact Or.inl hc14
              · exact Or.inr (hLiveStep k C'.gates[k] c hliveG hgk (by simp [hinp]) (by omega) hc)
            have hlive_d : d < 14 ∨ (14 + (d - 14) = C'.output ∨ InCone 14 C' (d - 14) (C'.output - 14)) := by
              by_cases hd14 : d < 14
              · exact Or.inl hd14
              · exact Or.inr (hLiveStep k C'.gates[k] d hliveG hgk (by simp [hinp]) (by omega) hd)
            have hrec := hw'_rec k C'.gates[k] c d hgk hinp
            rw [wireVal_gate C' _ k _ hgk hlt] at h07
            rw [wireVal_gate C' _ k _ hgk hlt]
            rcases hop with hand | hor
            · rw [hand, hinp] at h07 ⊢
              simp only [List.map_cons, List.map_nil] at h07 ⊢
              rw [eval_and, Bool.and_eq_true] at h07 ⊢
              have hw_eq := hrec.1 hand
              cases hc7 : wireVal 14 C' c (pairInput (7 : Fin 14) 7) <;>
              cases hd7 : wireVal 14 C' d (pairInput (7 : Fin 14) 7)
              · exfalso
                apply hno
                refine ⟨k, hk, by rw [hgateAt]; exact hand, hliveG, ?_, by rw [hopnd0]; exact hc7, by rw [hopnd1]; exact hd7⟩
                change wireVal 14 C' (14 + k) (pairInput (0 : Fin 14) 7) = true
                rw [wireVal_gate C' _ k _ hgk hlt, hand, hinp]
                simp only [List.map_cons, List.map_nil]
                rw [eval_and, h07.1, h07.2]; rfl
              · have ihc := ih c (by omega) (by omega) hlive_c h07.1
                rw [hc7] at ihc
                have hwc : w' c = true := ihc.resolve_left Bool.false_ne_true
                right; rw [hw_eq, hwc, hd7]; simp
              · have ihd := ih d (by omega) (by omega) hlive_d h07.2
                rw [hd7] at ihd
                have hwd : w' d = true := ihd.resolve_left Bool.false_ne_true
                right; rw [hw_eq, hwd, hc7]; simp
              · exact Or.inl ⟨rfl, rfl⟩
            · rw [hor, hinp] at h07 ⊢
              simp only [List.map_cons, List.map_nil] at h07 ⊢
              rw [eval_or, Bool.or_eq_true] at h07 ⊢
              have hw_eq := hrec.2 hor
              rcases h07 with hc07 | hd07
              · rcases ih c (by omega) (by omega) hlive_c hc07 with h1 | h2
                · exact Or.inl (Or.inl h1)
                · right; rw [hw_eq, h2]; simp
              · rcases ih d (by omega) (by omega) hlive_d hd07 with h1 | h2
                · exact Or.inl (Or.inr h1)
                · right; rw [hw_eq, h2]; simp
    have hcontra := hInv C'.output hOut_lt (Or.inr (Or.inl (by omega))) hOut07
    rw [hOut77, hw'_out] at hcontra
    exact hcontra.elim Bool.false_ne_true Bool.false_ne_true
  -- Step 6: Split into the three children by the relative position of k1 and k2
  obtain ⟨k1, _, hk1_op, hk1_live, hk1_07, hk1_00a, hk1_00b⟩ := hk1
  obtain ⟨k2, _, hk2_op, hk2_live, hk2_07, hk2_77a, hk2_77b⟩ := hk2
  have hk1_00 : ∀ b : Fin 2, wireVal 14 C' (opnd C' k1 b) (pairInput (0 : Fin 14) 0) = false := by
    intro b; fin_cases b; exact hk1_00a; exact hk1_00b
  have hk2_77 : ∀ b : Fin 2, wireVal 14 C' (opnd C' k2 b) (pairInput (7 : Fin 14) 7) = false := by
    intro b; fin_cases b; exact hk2_77a; exact hk2_77b
  by_cases hEq : k1 = k2
  · subst hEq
    exact hSame ⟨C', hSize', hGates', hFano', k1, hk1_op, hk1_live, hk1_07,
      fun b => ⟨hk1_00 b, hk2_77 b⟩⟩
  · by_cases hCone : InCone 14 C' k1 k2 ∨ InCone 14 C' k2 k1
    · exact hChain ⟨C', hSize', hGates', hFano', k1, k2, hCone,
        hk1_op, hk1_live, hk1_07, hk1_00,
        hk2_op, hk2_live, hk2_07, hk2_77⟩
    · have hnc12 : ¬ InCone 14 C' k1 k2 := fun h => hCone (Or.inl h)
      have hnc21 : ¬ InCone 14 C' k2 k1 := fun h => hCone (Or.inr h)
      exact hPar ⟨C', hSize', hGates', hFano', k1, k2, hEq, hnc12, hnc21,
        hk1_op, hk1_live, hk1_07, hk1_00,
        hk2_op, hk2_live, hk2_07, hk2_77⟩
