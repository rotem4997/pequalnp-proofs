import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

-- Unpack both lineSingle = false conditions via linearParts into live active-path
-- double-read AND gates k1 (line-double) and k2 (point-double), and partition the
-- double re-read edges into three witness-free structural classes: k1 = k2,
-- chained (InCone k1 k2 ∨ InCone k2 k1), and incomparable (neither in the other's cone).
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2974_319
    (hSame : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
      (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      let wv := wireVal (N + N) C
      let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) =>
        decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
      let act := fun (x : Fin (N + N) → Bool) => Relation.ReflTransGen (fun u v : ℕ =>
        ∃ j < C.size, v = N + N + j ∧ u ∈ (gateAt C j).inputs ∧ wv u x = true ∧ wv v x = true)
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        wv C.output z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ wv C.output (pair e) = true ∧
        ∃ k < C.size, (gateAt C k).op = GateOp.and ∧ act (pair e) (N + N + k) C.output ∧
          ∀ b : Fin 2, wv (opnd C k b) (fun i => decide (i = Fin.castAdd N e.1)) = false ∧
            wv (opnd C k b) (fun i => decide (i = Fin.natAdd N e.2)) = false) → E.card ≤ 8 * C.size)
    (hChain : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
      (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      let wv := wireVal (N + N) C
      let ic := InCone (N + N) C
      let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) =>
        decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
      let ok := fun (e : Fin N × Fin N) (v : Fin (N + N)) (k : ℕ) =>
        k < C.size ∧ (gateAt C k).op = GateOp.and ∧
          Relation.ReflTransGen (fun u w : ℕ =>
            ∃ j < C.size, w = N + N + j ∧ u ∈ (gateAt C j).inputs ∧
              wv u (pair e) = true ∧ wv w (pair e) = true) (N + N + k) C.output ∧
          ∀ b : Fin 2, wv (opnd C k b) (fun i => decide (i = v)) = false
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        wv C.output z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ wv C.output (pair e) = true ∧
        ∃ k1 k2, (ic k1 k2 ∨ ic k2 k1) ∧
          ok e (Fin.castAdd N e.1) k1 ∧ ok e (Fin.natAdd N e.2) k2) → E.card ≤ 8 * C.size)
    (hPar : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
      (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N + N) C →
      let wv := wireVal (N + N) C
      let ic := InCone (N + N) C
      let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) =>
        decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
      let ok := fun (e : Fin N × Fin N) (v : Fin (N + N)) (k : ℕ) =>
        k < C.size ∧ (gateAt C k).op = GateOp.and ∧
          Relation.ReflTransGen (fun u w : ℕ =>
            ∃ j < C.size, w = N + N + j ∧ u ∈ (gateAt C j).inputs ∧
              wv u (pair e) = true ∧ wv w (pair e) = true) (N + N + k) C.output ∧
          ∀ b : Fin 2, wv (opnd C k b) (fun i => decide (i = v)) = false
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        wv C.output z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ wv C.output (pair e) = true ∧
        ∃ k1 k2, k1 ≠ k2 ∧ ¬ ic k1 k2 ∧ ¬ ic k2 k1 ∧
          ok e (Fin.castAdd N e.1) k1 ∧ ok e (Fin.natAdd N e.2) k2) → E.card ≤ 8 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I instI C hq hN hcol huniq hAO hSound
  let wv := wireVal (N + N) C
  let ic := InCone (N + N) C
  let single := fun (v i : Fin (N + N)) => decide (i = v)
  let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) =>
    decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
  let act := fun (x : Fin (N + N) → Bool) => Relation.ReflTransGen (fun u v : ℕ =>
    ∃ j < C.size, v = N + N + j ∧ u ∈ (gateAt C j).inputs ∧ wv u x = true ∧ wv v x = true)
  let ok := fun (e : Fin N × Fin N) (v : Fin (N + N)) (k : ℕ) =>
    k < C.size ∧ (gateAt C k).op = GateOp.and ∧ act (pair e) (N + N + k) C.output ∧
      ∀ b : Fin 2, wv (opnd C k b) (single v) = false
  -- Generic scan lemmas for both Circuit.wires and linearParts
  let scan : ∀ {α : Type}, (List α → Gate → α) → List Gate → List α → List α :=
    fun step gs init => gs.foldl (fun w g => w ++ [step w g]) init
  have scan_len : ∀ {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α),
      (scan step gs init).length = init.length + gs.length := by
    intro α step gs
    induction gs with
    | nil => intro init; simp [scan]
    | cons g rest ih =>
      intro init
      change (scan step rest (init ++ [step init g])).length = _
      rw [ih]; simp; omega
  have scan_prefix : ∀ {α : Type} (step : List α → Gate → α) (d : α) (gs : List Gate)
      (init : List α) (r : ℕ), r < init.length → (scan step gs init).getD r d = init.getD r d := by
    intro α step d gs
    induction gs with
    | nil => intro init r _; rfl
    | cons g rest ih =>
      intro init r hr
      change (scan step rest (init ++ [step init g])).getD r d = _
      rw [ih _ r (by simp; omega), List.getD_append _ _ _ _ hr]
  have scan_gate : ∀ {α : Type} (step : List α → Gate → α) (d : α) (gs : List Gate)
      (init : List α) (k : ℕ) (hk : k < gs.length)
      (hdep : ∀ w1 w2 : List α, (∀ i < init.length + k, w1.getD i d = w2.getD i d) →
        step w1 gs[k] = step w2 gs[k]),
      (scan step gs init).getD (init.length + k) d = step (scan step gs init) gs[k] := by
    intro α step d gs init k hk hdep
    let pre := scan step (gs.take k) init
    have hpre_len : pre.length = init.length + k := by
      rw [scan_len, List.length_take, Nat.min_eq_left hk.le]
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h1 := List.take_append_drop k gs
      have h2 := List.cons_getElem_drop_succ (l := gs) (n := k) (h := hk)
      rw [h2]; exact h1.symm
    have hscan_split : scan step gs init = scan step (gs[k] :: gs.drop (k + 1)) pre := by
      conv_lhs => rw [hsplit]
      change (gs.take k ++ gs[k] :: gs.drop (k + 1)).foldl _ init = _
      rw [List.foldl_append]
    have hpre_eq : ∀ i < init.length + k, (scan step gs init).getD i d = pre.getD i d := by
      intro i hi
      rw [hscan_split]
      exact scan_prefix step d _ pre i (by omega)
    have hres : (scan step gs init).getD (init.length + k) d = step pre gs[k] := by
      rw [hscan_split]
      change (scan step (gs.drop (k + 1)) (pre ++ [step pre gs[k]])).getD (init.length + k) d = _
      rw [scan_prefix step d _ _ (init.length + k) (by simp [hpre_len])]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hsub : init.length + k - pre.length = 0 := by omega
      rw [hsub]; rfl
    rw [hres]
    exact hdep pre (scan step gs init) (fun i hi => (hpre_eq i hi).symm)
  -- Wire evaluation and linearParts recurrence under IsAO2
  let bstep : List Bool → Gate → Bool :=
    fun ws g => g.op.eval (g.inputs.map fun i => ws.getD i false)
  have gate_info : ∀ j < C.size,
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
      opnd C j 0 < N + N + j ∧ opnd C j 1 < N + N + j := by
    intro j hj
    have hj' : j < C.gates.length := hj
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj'
    have hg : gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
      rw [List.getD_eq_getElem _ _ hj']
    have hop := hAO.1 C.gates[j] hmem
    have hlen := hAO.2.2 C.gates[j] hmem
    have hlt := hAO.2.1 j hj'
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have ha0 : opnd C j 0 = a := by change (gateAt C j).inputs.getD 0 0 = a; rw [hg, hab]; rfl
    have hb1 : opnd C j 1 = b := by change (gateAt C j).inputs.getD 1 0 = b; rw [hg, hab]; rfl
    refine ⟨by rw [hg]; exact hop, by rw [hg, hab, ha0, hb1], ?_, ?_⟩
    · rw [ha0]; exact hlt a (by rw [hg, hab]; simp)
    · rw [hb1]; exact hlt b (by rw [hg, hab]; simp)
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have wv_input : ∀ (x : Fin (N + N) → Bool) (r : ℕ) (hr : r < N + N),
      wv r x = x ⟨r, hr⟩ := by
    intro x r hr
    change (scan bstep C.gates (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [scan_prefix bstep false C.gates (List.ofFn x) r (by simp [hr]),
      List.getD_eq_getElem _ _ (by simp [hr]), List.getElem_ofFn]
  have wv_ge : ∀ (x : Fin (N + N) → Bool) (r : ℕ), N + N + C.size ≤ r → wv r x = false := by
    intro x r hr
    change (scan bstep C.gates (List.ofFn x)).getD r false = false
    exact List.getD_eq_default _ _ (by rw [scan_len, List.length_ofFn]; exact hr)
  have wv_gate : ∀ (x : Fin (N + N) → Bool) (k : ℕ) (hk : k < C.size),
      wv (N + N + k) x =
        if (gateAt C k).op = GateOp.and then wv (opnd C k 0) x && wv (opnd C k 1) x
        else wv (opnd C k 0) x || wv (opnd C k 1) x := by
    intro x k hk
    obtain ⟨hop, hinp, ha, hb⟩ := gate_info k hk
    have hgk : gateAt C k = C.gates[k]'hk := by
      change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]'hk
      rw [List.getD_eq_getElem _ _ hk]
    have hstep : (scan bstep C.gates (List.ofFn x)).getD (N + N + k) false =
        bstep (scan bstep C.gates (List.ofFn x)) (C.gates[k]'hk) := by
      have := scan_gate bstep false C.gates (List.ofFn x) k hk (fun w1 w2 heq => by
        dsimp only [bstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [← hgk, hinp] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact heq _ (by rw [List.length_ofFn]; exact ha)
        · exact heq _ (by rw [List.length_ofFn]; exact hb))
      simpa only [List.length_ofFn] using this
    change (scan bstep C.gates (List.ofFn x)).getD (N + N + k) false = _
    rw [hstep]
    dsimp only [bstep]
    rw [← hgk, hinp]
    simp only [List.map_cons, List.map_nil]
    rcases hop with hand | hor
    · rw [hand, if_pos rfl, eval_and]; rfl
    · rw [hor, if_neg (by intro h; cases h), eval_or]; rfl
  -- Soundness on singletons
  have separate : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.isLt; omega
  have single_off : ∀ v : Fin (N + N), wv C.output (single v) = false := by
    intro v
    change circuitFun (N + N) C (single v) = false
    apply hSound
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, decide_eq_true_eq] at ha hb
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha.trans hb.symm)))
    · rintro ⟨p, l, _, hp, hl⟩
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  -- Unified active-path double-read AND gate extraction from lineSingle = false
  have extract : ∀ (e : Fin N × Fin N) (isLine : ℕ → Bool) (z0 z1 : Fin (N + N)),
      (e.1.val = z0.val ∧ N + e.2.val = z1.val ∨ e.1.val = z1.val ∧ N + e.2.val = z0.val) →
      isLine z0.val = false → isLine z1.val = true →
      circuitFun (N + N) C (pair e) = true →
      lineSingle C (N + N) isLine e.1.val (N + e.2.val) = false →
      ∃ k, ok e z0 k := by
    intro e isLine z0 z1 hpair h0 h1 hacc hls
    let xList : List Bool := (List.range (N + N)).map fun i => i == e.1.val || i == N + e.2.val
    let lp : ℕ → Bool × Bool := fun r => (linearParts C isLine xList).getD r (false, false)
    have hlen_x : xList.length = N + N := by simp [xList]
    have hlp_in : ∀ r (hr : r < N + N),
        lp r = if isLine r then (false, decide (r = e.1.val ∨ r = N + e.2.val))
               else (decide (r = e.1.val ∨ r = N + e.2.val), false) := by
      intro r hr
      dsimp only [lp]
      have hmap_eq : ((xList.zipIdx).map fun bi => if isLine bi.2 then (false, bi.1) else (bi.1, false)) =
          ((xList.zipIdx).map fun bi => Prod.casesOn (motive := fun _ => Bool × Bool) bi
            (fun b i => if isLine i then (false, b) else (b, false))) := by
        apply List.map_congr_left; intro bi _; cases bi; rfl
      have hlp_scan : ∃ step : List (Bool × Bool) → Gate → Bool × Bool,
          linearParts C isLine xList = scan step C.gates
            ((xList.zipIdx).map fun bi => Prod.casesOn (motive := fun _ => Bool × Bool) bi
              (fun b i => if isLine i then (false, b) else (b, false))) := ⟨_, rfl⟩
      obtain ⟨step, hscan_eq⟩ := hlp_scan
      rw [hscan_eq, ← hmap_eq]
      rw [scan_prefix step (false, false) C.gates _ r (by simp [hlen_x, hr])]
      rw [List.getD_eq_getElem _ _ (by simp [hlen_x, hr])]
      dsimp only [xList]
      simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add]
      have heqb : (r == e.1.val || r == N + e.2.val) = decide (r = e.1.val ∨ r = N + e.2.val) := by
        apply Bool.eq_iff_iff.mpr; simp
      rw [heqb]
    have hlp_gate : ∀ k (hk : k < C.size),
        lp (N + N + k) =
          if (gateAt C k).op = GateOp.and then
            ((lp (opnd C k 0)).1 && (lp (opnd C k 1)).1,
             ((lp (opnd C k 0)).1 && (lp (opnd C k 1)).2) ||
             ((lp (opnd C k 0)).2 && (lp (opnd C k 1)).1))
          else
            ((lp (opnd C k 0)).1 || (lp (opnd C k 1)).1,
             (lp (opnd C k 0)).2 || (lp (opnd C k 1)).2) := by
      intro k hk
      obtain ⟨hop, hinp, ha, hb⟩ := gate_info k hk
      have hgk : gateAt C k = C.gates[k]'hk := by
        change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]'hk
        rw [List.getD_eq_getElem _ _ hk]
      have hlp_scan : ∃ (step : List (Bool × Bool) → Gate → Bool × Bool) (init : List (Bool × Bool)),
          init.length = N + N ∧
          linearParts C isLine xList = scan step C.gates init ∧
          (∀ w g, g.op = GateOp.and → g.inputs = [opnd C k 0, opnd C k 1] →
            step w g = ((w.getD (opnd C k 0) (false, false)).1 && (w.getD (opnd C k 1) (false, false)).1,
              ((w.getD (opnd C k 0) (false, false)).1 && (w.getD (opnd C k 1) (false, false)).2) ||
              ((w.getD (opnd C k 0) (false, false)).2 && (w.getD (opnd C k 1) (false, false)).1))) ∧
          (∀ w g, g.op = GateOp.or → g.inputs = [opnd C k 0, opnd C k 1] →
            step w g = ((w.getD (opnd C k 0) (false, false)).1 || (w.getD (opnd C k 1) (false, false)).1,
              (w.getD (opnd C k 0) (false, false)).2 || (w.getD (opnd C k 1) (false, false)).2)) := by
        refine ⟨_, _, by simp [hlen_x], rfl, ?_, ?_⟩
        · intro w g hg_op hg_in
          rcases g with ⟨op, ins⟩
          dsimp only at hg_op hg_in
          subst hg_op; subst hg_in
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
            Bool.true_and, Bool.false_and, Bool.or_false]
        · intro w g hg_op hg_in
          rcases g with ⟨op, ins⟩
          dsimp only at hg_op hg_in
          subst hg_op; subst hg_in
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
      obtain ⟨step, init, hinit_len, hscan_eq, hstep_and, hstep_or⟩ := hlp_scan
      have hst : (scan step C.gates init).getD (N + N + k) (false, false) =
          step (scan step C.gates init) (C.gates[k]'hk) := by
        have := scan_gate step (false, false) C.gates init k hk (fun w1 w2 heq => by
          rcases hop with hand | hor
          · rw [hstep_and w1 _ (by rw [← hgk]; exact hand) (by rw [← hgk]; exact hinp),
                hstep_and w2 _ (by rw [← hgk]; exact hand) (by rw [← hgk]; exact hinp),
                heq _ (by omega), heq _ (by omega)]
          · rw [hstep_or w1 _ (by rw [← hgk]; exact hor) (by rw [← hgk]; exact hinp),
                hstep_or w2 _ (by rw [← hgk]; exact hor) (by rw [← hgk]; exact hinp),
                heq _ (by omega), heq _ (by omega)])
        simpa only [hinit_len] using this
      dsimp only [lp]
      rw [hscan_eq, hst]
      rcases hop with hand | hor
      · rw [hand, if_pos rfl,
            hstep_and _ _ (by rw [← hgk]; exact hand) (by rw [← hgk]; exact hinp)]
      · rw [hor, if_neg (by intro h; cases h),
            hstep_or _ _ (by rw [← hgk]; exact hor) (by rw [← hgk]; exact hinp)]
    -- Show (lp r).1 = wv r (single z0) for all r
    have hlp1 : ∀ r < N + N + C.size, (lp r).1 = wv r (single z0) := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr
        by_cases hrN : r < N + N
        · rw [hlp_in r hrN, wv_input (single z0) r hrN]
          by_cases hreq : r = z0.val
          · subst hreq
            rw [show isLine z0.val = false from by assumption]
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hmem : z0.val = e.1.val ∨ z0.val = N + e.2.val := by
              rcases ‹e.1.val = z0.val ∧ N + e.2.val = z1.val ∨
                e.1.val = z1.val ∧ N + e.2.val = z0.val› with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact Or.inl h1.symm
              · exact Or.inr h2.symm
            simp [single, hmem]
          · have hne_fin : (⟨r, hrN⟩ : Fin (N + N)) ≠ z0 := fun h => hreq (congrArg Fin.val h)
            have hsf : single z0 ⟨r, hrN⟩ = false := by simp [single, hne_fin]
            rw [hsf]
            by_cases hl : isLine r = true
            · rw [hl]; rfl
            · simp only [hl, ↓reduceIte]
              by_cases h1 : r = e.1.val ∨ r = N + e.2.val
              · exfalso
                have hrz1 : r = z1.val := by
                  rcases ‹e.1.val = z0.val ∧ N + e.2.val = z1.val ∨
                    e.1.val = z1.val ∧ N + e.2.val = z0.val› with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
                  rcases h1 with h1 | h1 <;> omega
                rw [hrz1] at hl; exact hl (by assumption)
              · simp [h1]
        · let k := r - (N + N)
          have hk : k < C.size := by omega
          have hrk : r = N + N + k := by omega
          rw [hrk, hlp_gate k hk, wv_gate (single z0) k hk]
          obtain ⟨_, _, ha, hb⟩ := gate_info k hk
          have iha := ih (opnd C k 0) (by omega) (by omega)
          have ihb := ih (opnd C k 1) (by omega) (by omega)
          split_ifs <;> simp [iha, ihb]
    -- Extract live active-path AND gate k with both operands false at single z0
    by_contra hno
    have hOut_true : wv C.output (pair e) = true := ‹circuitFun (N + N) C (pair e) = true›
    have hOut_lt : C.output < N + N + C.size := by
      by_contra hge
      have := wv_ge (pair e) C.output (by omega)
      rw [this] at hOut_true; cases hOut_true
    have hInv : ∀ r < N + N + C.size, act (pair e) r C.output → wv r (pair e) = true →
        wv r (single z0) = true ∨ (lp r).2 = true := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hact hpair
        by_cases hrN : r < N + N
        · rw [wv_input (pair e) r hrN] at hpair
          rw [wv_input (single z0) r hrN, hlp_in r hrN]
          have hpair' : r = e.1.val ∨ r = N + e.2.val := by
            dsimp only [pair] at hpair
            have := of_decide_eq_true hpair
            rcases this with h | h
            · exact Or.inl (congrArg Fin.val h)
            · exact Or.inr (congrArg Fin.val h)
          have hrz : r = z0.val ∨ r = z1.val := by
            rcases ‹e.1.val = z0.val ∧ N + e.2.val = z1.val ∨
              e.1.val = z1.val ∧ N + e.2.val = z0.val› with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            rcases hpair' with h | h <;> omega
          rcases hrz with rfl | rfl
          · left; simp [single]
          · right; rw [‹isLine z1.val = true›]; simp [hpair']
        · let k := r - (N + N)
          have hk : k < C.size := by omega
          have hrk : r = N + N + k := by omega
          rw [hrk] at hact hpair ⊢
          obtain ⟨hop, hinp, ha, hb⟩ := gate_info k hk
          have hact_c : ∀ b : Fin 2, wv (opnd C k b) (pair e) = true →
              act (pair e) (opnd C k b) C.output := by
            intro b hbv
            apply Relation.ReflTransGen.head _ hact
            refine ⟨k, hk, rfl, ?_, hbv, hpair⟩
            rw [hinp]; fin_cases b <;> simp
          rw [wv_gate (pair e) k hk] at hpair
          rw [wv_gate (single z0) k hk, hlp_gate k hk]
          rcases hop with hand | hor
          · rw [hand, if_pos rfl] at hpair ⊢
            rw [Bool.and_eq_true] at hpair
            cases hc : wv (opnd C k 0) (single z0) <;>
            cases hd : wv (opnd C k 1) (single z0)
            · exfalso
              apply hno
              refine ⟨k, hk, hand, hact, ?_⟩
              intro b; fin_cases b
              · exact hc
              · exact hd
            · have ihc := ih (opnd C k 0) (by omega) (by omega) (hact_c 0 hpair.1) hpair.1
              rw [hc] at ihc
              have hlc : (lp (opnd C k 0)).2 = true := ihc.resolve_left Bool.false_ne_true
              right
              have hd1 : (lp (opnd C k 1)).1 = true := (hlp1 _ (by omega)).trans hd
              simp [hlc, hd1]
            · have ihd := ih (opnd C k 1) (by omega) (by omega) (hact_c 1 hpair.2) hpair.2
              rw [hd] at ihd
              have hld : (lp (opnd C k 1)).2 = true := ihd.resolve_left Bool.false_ne_true
              right
              have hc1 : (lp (opnd C k 0)).1 = true := (hlp1 _ (by omega)).trans hc
              simp [hld, hc1]
            · exact Or.inl rfl
          · rw [hor, if_neg (by intro h; cases h)] at hpair ⊢
            rw [Bool.or_eq_true] at hpair
            rcases hpair with hc | hd
            · rcases ih (opnd C k 0) (by omega) (by omega) (hact_c 0 hc) hc with h1 | h2
              · exact Or.inl (by simp [h1])
              · exact Or.inr (by simp [h2])
            · rcases ih (opnd C k 1) (by omega) (by omega) (hact_c 1 hd) hd with h1 | h2
              · exact Or.inl (by simp [h1])
              · exact Or.inr (by simp [h2])
    have hres := hInv C.output hOut_lt Relation.ReflTransGen.refl hOut_true
    have hlp_out : (lp C.output).2 = false := hls
    rw [single_off z0, hlp_out] at hres
    exact hres.elim Bool.false_ne_true Bool.false_ne_true
  -- Partition the double re-read edges into E_same, E_chain, E_par
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ circuitFun (N + N) C (pair e) = true ∧
    lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false
  let Esame : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ circuitFun (N + N) C (pair e) = true ∧
    ∃ k < C.size, (gateAt C k).op = GateOp.and ∧ act (pair e) (N + N + k) C.output ∧
      ∀ b : Fin 2, wv (opnd C k b) (single (Fin.castAdd N e.1)) = false ∧
        wv (opnd C k b) (single (Fin.natAdd N e.2)) = false
  let Echain : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ circuitFun (N + N) C (pair e) = true ∧
    ∃ k1 k2, (ic k1 k2 ∨ ic k2 k1) ∧
      ok e (Fin.castAdd N e.1) k1 ∧ ok e (Fin.natAdd N e.2) k2
  let Epar : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ circuitFun (N + N) C (pair e) = true ∧
    ∃ k1 k2, k1 ≠ k2 ∧ ¬ ic k1 k2 ∧ ¬ ic k2 k1 ∧
      ok e (Fin.castAdd N e.1) k1 ∧ ok e (Fin.natAdd N e.2) k2
  have hSub : E ⊆ Esame ∪ (Echain ∪ Epar) := by
    intro e he
    obtain ⟨hI, hAcc, hlsL, hlsP⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨k1, hk1⟩ := extract e (fun i => decide (N ≤ i)) (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      (Or.inl ⟨rfl, rfl⟩)
      (by simp only [Fin.val_castAdd, decide_eq_false_iff_not]; have := e.1.isLt; omega)
      (by simp only [Fin.val_natAdd, decide_eq_true_eq]; omega)
      hAcc hlsL
    obtain ⟨k2, hk2⟩ := extract e (fun i => decide (i < N)) (Fin.natAdd N e.2) (Fin.castAdd N e.1)
      (Or.inr ⟨rfl, rfl⟩)
      (by simp only [Fin.val_natAdd, decide_eq_false_iff_not]; omega)
      (by simp only [Fin.val_castAdd, decide_eq_true_eq]; exact e.1.isLt)
      hAcc hlsP
    by_cases hEq : k1 = k2
    · apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hAcc, k1, hk1.1, hk1.2.1, hk1.2.2.1, ?_⟩
      intro b
      exact ⟨hk1.2.2.2 b, hEq ▸ hk2.2.2.2 b⟩
    · by_cases hC : ic k1 k2 ∨ ic k2 k1
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hAcc, k1, k2, hC, hk1, hk2⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hAcc, k1, k2, hEq,
          fun h => hC (Or.inl h), fun h => hC (Or.inr h), hk1, hk2⟩
  have h1 : Esame.card ≤ 8 * C.size :=
    hSame q N I C Esame hq hN hcol huniq hAO hSound (fun e he => (Finset.mem_filter.mp he).2)
  have h2 : Echain.card ≤ 8 * C.size :=
    hChain q N I C Echain hq hN hcol huniq hAO hSound (fun e he => (Finset.mem_filter.mp he).2)
  have h3 : Epar.card ≤ 8 * C.size :=
    hPar q N I C Epar hq hN hcol huniq hAO hSound (fun e he => (Finset.mem_filter.mp he).2)
  have hUnion : E.card ≤ Esame.card + (Echain.card + Epar.card) :=
    le_trans (Finset.card_le_card hSub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  rw [Fintype.card_subtype]
  change E.card ≤ 24 * C.size
  omega
