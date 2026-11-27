import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2970

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def pairList (N : ℕ) (p l : Fin N) : List Bool :=
  (List.range (N + N)).map fun i => i == p.val || i == N + l.val

def lpInit (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  ((pairList N p l).zipIdx).map fun (b, i) => if decide (N ≤ i) then (false, b) else (b, false)

def lpList (C : Circuit) (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  linearParts C (fun k => decide (N ≤ k)) (pairList N p l)

def lpAt (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (lpList C N p l).getD w (false, false)

lemma lineSingle_eq_lpAt (C : Circuit) (N : ℕ) (p l : Fin N) :
    lineSingle C (N + N) (fun k => decide (N ≤ k)) p.val (N + l.val) = (lpAt C N p l C.output).2 := rfl

lemma lpInit_length (N : ℕ) (p l : Fin N) : (lpInit N p l).length = N + N := by
  simp [lpInit, pairList]

lemma lpInit_getD (N : ℕ) (p l : Fin N) (i : ℕ) (hi : i < N + N) :
    (lpInit N p l).getD i (false, false) =
      if i < N then (decide (i = p.val), false) else (false, decide (i = N + l.val)) := by
  have hl1 : (pairList N p l).length = N + N := by simp [pairList]
  have hl2 : ((pairList N p l).zipIdx).length = N + N := by simp [hl1]
  rw [lpInit, List.getD_eq_getElem _ _ (by simp [hl2, hi]), List.getElem_map]
  have hz : ((pairList N p l).zipIdx)[i]'(by omega) = ((pairList N p l)[i]'(by omega), i) := by
    simp [List.getElem_zipIdx]
  rw [hz]
  dsimp only
  unfold pairList
  rw [List.getElem_map, List.getElem_range]
  by_cases hlt : i < N
  · have hni : ¬ (N ≤ i) := by omega
    have hne : (i == N + l.val) = false := by
      simp
      omega
    simp only [hlt, hni, hne, Bool.or_false, decide_false, ite_true]
    by_cases hep : i = p.val <;> simp [hep]
  · have hle : N ≤ i := by omega
    have hne : (i == p.val) = false := by
      simp
      omega
    simp only [hlt, hle, hne, Bool.false_or, decide_true, ite_true, ite_false]
    by_cases hel : i = N + l.val <;> simp [hel]

def pointInput (N : ℕ) (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i.val = p.val)

def zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then decide (¬ I ⟨i.val, h⟩ l) else decide (i.val = N + l.val)

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma getD_map_fst (ws : List (Bool × Bool)) (i : ℕ) :
    (ws.map (·.1)).getD i false = (ws.getD i (false, false)).1 := by
  by_cases hi : i < ws.length
  · simp [hi]
  · have hle : ws.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hle)]

lemma boolStep_fst_linStep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (linStep ws g).1 = boolStep (ws.map (·.1)) g := by
  rcases hg with hop | hop
  · simp only [linStep, boolStep, hop, GateOp.eval]
    have hfold : ∀ (l : List (Bool × Bool)) (b c : Bool),
        (l.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (b, c)).1 =
        (b && l.all (·.1)) := by
      intro l
      induction l with
      | nil => intro b c; simp
      | cons x xs ih =>
        intro b c
        simp only [List.foldl_cons, List.all_cons]
        rw [ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi; rw [getD_map_fst]; exact h i hi
    · intro h i hi; rw [← getD_map_fst]; exact h i hi
  · simp only [linStep, boolStep, hop, GateOp.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [getD_map_fst]; exact hit⟩
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [← getD_map_fst]; exact hit⟩

lemma scan_lin_fst (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (scan linStep gs ws).map (·.1) = scan boolStep gs (ws.map (·.1)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]

lemma lpInit_map_fst (N : ℕ) (p l : Fin N) :
    (lpInit N p l).map (·.1) = List.ofFn (pointInput N p) := by
  apply List.ext_getElem
  · simp [lpInit_length]
  · intro i h1 h2
    have hi : i < N + N := by simpa [lpInit_length] using h1
    rw [List.getElem_map, List.getElem_ofFn]
    have hg := lpInit_getD N p l i hi
    rw [List.getD_eq_getElem _ _ (by simp [lpInit_length, hi])] at hg
    rw [hg]
    by_cases hlt : i < N
    · simp [hlt, pointInput]
    · simp [hlt, pointInput]
      omega

lemma lpAt_fst (C : Circuit) (hAO : AndOrOnly C) (N : ℕ) (p l : Fin N) (w : ℕ) :
    (lpAt C N p l w).1 = wireVal (N + N) C w (pointInput N p) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  change ((scan linStep C.gates (lpInit N p l)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn (pointInput N p))).getD w false
  rw [← getD_map_fst, scan_lin_fst C.gates hAO, lpInit_map_fst]

lemma lpList_length (C : Circuit) (N : ℕ) (p l : Fin N) :
    (lpList C N p l).length = N + N + C.gates.length := by
  rw [lpList, linearParts_eq_scan, scan_length]
  change (lpInit N p l).length + C.gates.length = N + N + C.gates.length
  rw [lpInit_length]

lemma lpAt_ge (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    lpAt C N p l w = (false, false) := by
  rw [lpAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lpList_length]; exact hw)]
  rfl

lemma lpAt_lt_len (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N + N) :
    lpAt C N p l w = (lpInit N p l).getD w (false, false) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  exact scan_prefix linStep C.gates (lpInit N p l) (false, false) w (by rw [lpInit_length]; exact hw)

lemma lpAt_snd_lt_N (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N) :
    (lpAt C N p l w).2 = false := by
  rw [lpAt_lt_len C N p l w (by omega), lpInit_getD N p l w (by omega)]
  simp [hw]

lemma lpAt_snd_line (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    (lpAt C N p l w).2 = decide (w = N + l.val) := by
  rw [lpAt_lt_len C N p l w h2, lpInit_getD N p l w h2]
  have hnot : ¬ (w < N) := by omega
  simp [hnot]

lemma lpAt_gate {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) :
    lpAt C N p l (N + N + j) = linStep (lpList C N p l) C.gates[j] := by
  rw [lpAt, lpList, linearParts_eq_scan]
  have hlen : (lpInit N p l).length = N + N := lpInit_length N p l
  conv_lhs => rw [← hlen]
  apply scan_gate linStep C.gates (lpInit N p l) (false, false) j hj
  intro q1 q2 hq
  simp only [linStep]
  have hrb := hAO2.2.1 j hj
  have hcongr : C.gates[j].inputs.map (fun i => q1.getD i (false, false)) =
      C.gates[j].inputs.map (fun i => q2.getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    apply hq
    rw [hlen]
    exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
  rw [hcongr]

lemma lpAt_snd_or {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    (lpAt C N p l (N + N + j)).2 =
      ((lpAt C N p l (opnd C j 0)).2 || (lpAt C N p l (opnd C j 1)).2) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [linStep, hop, hin, lpAt]

lemma lpAt_snd_and {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    (lpAt C N p l (N + N + j)).2 =
      ((wireVal (N + N) C (opnd C j 0) (pointInput N p) && (lpAt C N p l (opnd C j 1)).2) ||
       ((lpAt C N p l (opnd C j 0)).2 && wireVal (N + N) C (opnd C j 1) (pointInput N p))) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp only [linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.or_false]
  rw [← lpAt_fst C hAO2.1 N p l (opnd C j 0), ← lpAt_fst C hAO2.1 N p l (opnd C j 1)]
  rfl

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  exact (scan_bool_mono C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) hle).2 w

lemma eval_zInput_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hSound : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    (l : Fin N) :
    wireVal (N + N) C C.output (zInput I l) = false := by
  have hcard : Fintype.card { l' : Fin N // zInput I l (Fin.natAdd N l') = true } ≤ 1 := by
    have hsub : Subsingleton { l' : Fin N // zInput I l (Fin.natAdd N l') = true } := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : a.1 = l := by
        have h1 : (Fin.natAdd N a.1).val = N + a.1.val := Fin.val_natAdd N a.1
        have h2 := a.2
        dsimp only [zInput] at h2
        split_ifs at h2 with hlt
        · omega
        · simp only [h1, decide_eq_true_eq] at h2
          exact Fin.ext (by omega)
      have hb : b.1 = l := by
        have h1 : (Fin.natAdd N b.1).val = N + b.1.val := Fin.val_natAdd N b.1
        have h2 := b.2
        dsimp only [zInput] at h2
        split_ifs at h2 with hlt
        · omega
        · simp only [h1, decide_eq_true_eq] at h2
          exact Fin.ext (by omega)
      exact ha.trans hb.symm
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hno : ¬ ∃ p l' : Fin N, I p l' ∧ zInput I l (Fin.castAdd N p) = true ∧
      zInput I l (Fin.natAdd N l') = true := by
    rintro ⟨p, l', hI, hp, hl'⟩
    have hl'' : l' = l := by
      have h1 : (Fin.natAdd N l').val = N + l'.val := Fin.val_natAdd N l'
      dsimp only [zInput] at hl'
      split_ifs at hl' with hlt
      · omega
      · simp only [h1, decide_eq_true_eq] at hl'
        exact Fin.ext (by omega)
    subst hl''
    have hp' : ¬ I p l' := by
      have h1 : (Fin.castAdd N p).val = p.val := Fin.val_castAdd N p
      have h2 : (Fin.castAdd N p).val < N := p.isLt
      have hpe : (⟨(Fin.castAdd N p).val, h2⟩ : Fin N) = p := Fin.ext h1
      simp only [zInput, h2, dite_true, hpe, decide_eq_true_eq] at hp
      exact hp
    exact hp' hI
  exact hSound (zInput I l) hcard hno

lemma pointInput_le_zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {p l' : Fin N} (hnot : ¬ I p l') :
    ∀ i : Fin (N + N), pointInput N p i = true → zInput I l' i = true := by
  intro i hi
  simp only [pointInput, decide_eq_true_eq] at hi
  have hlt : i.val < N := by omega
  have hpi : (⟨i.val, hlt⟩ : Fin N) = p := Fin.ext hi
  simp [zInput, hlt, hpi, hnot]

def aSet (C : Circuit) (N w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => wireVal (N + N) C w (pointInput N p) = true

def zLineSet {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (w : ℕ) :
    Finset (Fin N) :=
  Finset.univ.filter fun l => wireVal (N + N) C w (zInput I l) = true

lemma mem_aSet {C : Circuit} {N w : ℕ} {p : Fin N} :
    p ∈ aSet C N w ↔ wireVal (N + N) C w (pointInput N p) = true := by
  simp [aSet]

lemma mem_zLineSet {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit} {w : ℕ} {l : Fin N} :
    l ∈ zLineSet I C w ↔ wireVal (N + N) C w (zInput I l) = true := by
  simp [zLineSet]

lemma aSet_lt_N (C : Circuit) (N : ℕ) {w : ℕ} (hw : w < N) :
    aSet C N w = {⟨w, hw⟩} := by
  ext p
  rw [mem_aSet, wireVal_input (N + N) C (pointInput N p) w (by omega)]
  simp [pointInput, Fin.ext_iff, eq_comm]

lemma aSet_line (C : Circuit) (N : ℕ) {w : ℕ} (h1 : N ≤ w) (h2 : w < N + N) :
    aSet C N w = ∅ := by
  ext p
  rw [mem_aSet, wireVal_input (N + N) C (pointInput N p) w h2]
  simp [pointInput]
  omega

lemma aSet_ge (C : Circuit) (N : ℕ) {w : ℕ} (hw : N + N + C.gates.length ≤ w) :
    aSet C N w = ∅ := by
  ext p
  rw [mem_aSet, wireVal_ge (N + N) C (pointInput N p) w hw]
  simp

lemma zLineSet_line {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    {w : ℕ} (h1 : N ≤ w) (h2 : w < N + N) :
    zLineSet I C w = {⟨w - N, by omega⟩} := by
  ext l
  rw [mem_zLineSet, wireVal_input (N + N) C (zInput I l) w h2]
  have hnot : ¬ (w < N) := by omega
  simp [zInput, hnot, Fin.ext_iff]
  omega

lemma zLineSet_and {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    zLineSet I C (N + N + j) = zLineSet I C (opnd C j 0) ∩ zLineSet I C (opnd C j 1) := by
  ext l
  simp [mem_zLineSet, wireVal_and hAO2 (zInput I l) hj hop]

lemma aSet_subset_of_zInput_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {C : Circuit} (hAO : AndOrOnly C) {w : ℕ} {l : Fin N}
    (hz : wireVal (N + N) C w (zInput I l) = false) :
    ∀ p' ∈ aSet C N w, I p' l := by
  intro p' hp'
  rw [mem_aSet] at hp'
  by_contra hnot
  have ht := wireVal_mono hAO (pointInput_le_zInput I hnot) w hp'
  rw [hz] at ht
  exact Bool.noConfusion ht

def bStep (C : Circuit) (N : ℕ) (p : Fin N) (w w' : ℕ) : Prop :=
  ∃ j < C.gates.length, w = (N + N) + j ∧
    (((gateAt C j).op = GateOp.or ∧ (w' = opnd C j 0 ∨ w' = opnd C j 1)) ∨
     ((gateAt C j).op = GateOp.and ∧
       ((w' = opnd C j 0 ∧ wireVal (N + N) C (opnd C j 1) (pointInput N p) = true) ∨
        (w' = opnd C j 1 ∧ wireVal (N + N) C (opnd C j 0) (pointInput N p) = true))))

def reachesOut (C : Circuit) (N : ℕ) (p : Fin N) (w : ℕ) : Prop :=
  Relation.ReflTransGen (bStep C N p) C.output w

lemma bStep_zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {p l' : Fin N} (hnot : ¬ I p l') {w w' : ℕ}
    (hs : bStep C N p w w') (hw' : wireVal (N + N) C w' (zInput I l') = true) :
    wireVal (N + N) C w (zInput I l') = true := by
  rcases hs with ⟨j, hj, rfl, ⟨hop, rfl | rfl⟩ | ⟨hop, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩⟩
  · rw [wireVal_or hAO2 _ hj hop, hw', Bool.true_or]
  · rw [wireVal_or hAO2 _ hj hop, hw', Bool.or_true]
  · have ha' := wireVal_mono hAO2.1 (pointInput_le_zInput I hnot) (opnd C j 1) ha
    rw [wireVal_and hAO2 _ hj hop, hw', ha', Bool.true_and]
  · have ha' := wireVal_mono hAO2.1 (pointInput_le_zInput I hnot) (opnd C j 0) ha
    rw [wireVal_and hAO2 _ hj hop, ha', hw', Bool.true_and]

lemma reachesOut_zInput_gen {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {p l' : Fin N} (hnot : ¬ I p l') {u v : ℕ}
    (hr : Relation.ReflTransGen (bStep C N p) u v)
    (hv : wireVal (N + N) C v (zInput I l') = true) :
    wireVal (N + N) C u (zInput I l') = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hs _ ih => exact bStep_zInput I hAO2 hnot hs ih

lemma reachesOut_zLineSet {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    {p : Fin N} {w : ℕ} (hr : reachesOut C N p w) :
    ∀ l' ∈ zLineSet I C w, I p l' := by
  intro l' hl'
  rw [mem_zLineSet] at hl'
  by_contra hnot
  have hout := reachesOut_zInput_gen I hAO2 hnot hr hl'
  have hf := eval_zInput_false I C hEval l'
  rw [hf] at hout
  exact Bool.noConfusion hout

def R1 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (kb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  I pl.1 pl.2 ∧ 2 ≤ (aSet C N (N + N + kb.1.val)).card ∧
    (∀ p' ∈ aSet C N (N + N + kb.1.val), I p' pl.2) ∧
    aSet C N (opnd C kb.1.val kb.2) = {pl.1}

def R2a {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (jb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  (gateAt C jb.1.val).op = GateOp.and ∧
    aSet C N (opnd C jb.1.val jb.2) = {pl.1} ∧
    zLineSet I C (opnd C jb.1.val (1 - jb.2)) = {pl.2}

def R2b {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (mb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  I pl.1 pl.2 ∧ (gateAt C mb.1.val).op = GateOp.or ∧
    2 ≤ (zLineSet I C (N + N + mb.1.val)).card ∧
    (∀ l' ∈ zLineSet I C (N + N + mb.1.val), I pl.1 l') ∧
    zLineSet I C (opnd C mb.1.val mb.2) = {pl.2}

lemma R1_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC4 : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (C : Circuit) (kb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R1 I C kb pl1) (h2 : R1 I C kb pl2) : pl1 = pl2 := by
  have hp : pl1.1 = pl2.1 := Finset.singleton_injective (h1.2.2.2.symm.trans h2.2.2.2)
  have hl : pl1.2 = pl2.2 := by
    by_contra hneL
    have hlt : 1 < (aSet C N (N + N + kb.1.val)).card := Nat.lt_of_lt_of_le (by decide) h1.2.1
    obtain ⟨pa, hpa, pb, hpb, hne⟩ := Finset.one_lt_card.mp hlt
    exact hC4 pa pb pl1.2 pl2.2 hne hneL ⟨h1.2.2.1 pa hpa, h1.2.2.1 pb hpb, h2.2.2.1 pa hpa, h2.2.2.1 pb hpb⟩
  exact Prod.ext hp hl

lemma R2a_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (jb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R2a I C jb pl1) (h2 : R2a I C jb pl2) : pl1 = pl2 := by
  have hp : pl1.1 = pl2.1 := Finset.singleton_injective (h1.2.1.symm.trans h2.2.1)
  have hl : pl1.2 = pl2.2 := Finset.singleton_injective (h1.2.2.symm.trans h2.2.2)
  exact Prod.ext hp hl

lemma R2b_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC4 : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (C : Circuit) (mb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R2b I C mb pl1) (h2 : R2b I C mb pl2) : pl1 = pl2 := by
  have hl : pl1.2 = pl2.2 := Finset.singleton_injective (h1.2.2.2.2.symm.trans h2.2.2.2.2)
  have hp : pl1.1 = pl2.1 := by
    by_contra hne
    have hlt : 1 < (zLineSet I C (N + N + mb.1.val)).card := Nat.lt_of_lt_of_le (by decide) h1.2.2.1
    obtain ⟨la, hla, lb, hlb, hneL⟩ := Finset.one_lt_card.mp hlt
    have h1a := h1.2.2.2.1 la hla
    have h1b := h1.2.2.2.1 lb hlb
    have h2a := h2.2.2.2.1 la hla
    have h2b := h2.2.2.2.1 lb hlb
    exact hC4 pl1.1 pl2.1 la lb hne hneL ⟨h1a, h2a, h1b, h2b⟩
  exact Prod.ext hp hl

lemma card_le_of_rel {α β : Type} [Fintype α] [DecidableEq β]
    (S : Finset β) (R : α → β → Prop)
    (hEx : ∀ y ∈ S, ∃ x : α, R x y)
    (hUniq : ∀ x : α, ∀ y1 y2 : β, R x y1 → R x y2 → y1 = y2) :
    S.card ≤ Fintype.card α := by
  classical
  let f : { y : β // y ∈ S } → α := fun y => Classical.choose (hEx y.1 y.2)
  have hf : Function.Injective f := by
    intro y1 y2 heq
    have h1 : R (f y1) y1.1 := Classical.choose_spec (hEx y1.1 y1.2)
    have h2 : R (f y2) y2.1 := Classical.choose_spec (hEx y2.1 y2.2)
    rw [heq] at h1
    exact Subtype.ext (hUniq (f y2) y1.1 y2.1 h1 h2)
  simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma classify_pair {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    (p l : Fin N) (hI : I p l) (hls : (lpAt C N p l C.output).2 = true) :
    (∃ kb, R1 I C kb (p, l)) ∨ (∃ jb, R2a I C jb (p, l)) ∨ (∃ mb, R2b I C mb (p, l)) := by
  classical
  let goodG : ℕ → Prop := fun w =>
    reachesOut C N p w ∧ (lpAt C N p l w).2 = true ∧ wireVal (N + N) C w (zInput I l) = false
  have hOut : goodG C.output :=
    ⟨Relation.ReflTransGen.refl, hls, eval_zInput_false I C hEval l⟩
  let gStar := Nat.find ⟨C.output, hOut⟩
  have hgStar : goodG gStar := Nat.find_spec ⟨C.output, hOut⟩
  have hgMin : ∀ w < gStar, ¬ goodG w := fun w hw => Nat.find_min ⟨C.output, hOut⟩ hw
  have hgLtLen : gStar < N + N + C.gates.length := by
    by_contra hge
    have hge' : N + N + C.gates.length ≤ gStar := by omega
    have hlp := lpAt_ge C N p l gStar hge'
    have hgs2 := hgStar.2.1
    rw [hlp] at hgs2
    exact Bool.noConfusion hgs2
  have hgGeN : N ≤ gStar := by
    by_contra hlt
    have hlp := lpAt_snd_lt_N C N p l gStar (by omega)
    have hgs2 := hgStar.2.1
    rw [hlp] at hgs2
    exact Bool.noConfusion hgs2
  have hgGeNN : N + N ≤ gStar := by
    by_contra hlt
    have hlp := lpAt_snd_line C N p l gStar hgGeN (by omega)
    have hgs2 := hgStar.2.1
    rw [hlp, decide_eq_true_eq] at hgs2
    have hzv : wireVal (N + N) C gStar (zInput I l) = true := by
      rw [wireVal_input (N + N) C (zInput I l) gStar (by omega)]
      have hnot : ¬ (gStar < N) := by omega
      simp [zInput, hgs2]
    have hgs3 := hgStar.2.2
    rw [hzv] at hgs3
    exact Bool.noConfusion hgs3
  let j := gStar - (N + N)
  have hj : j < C.gates.length := by omega
  have hgEq : gStar = N + N + j := by omega
  have ⟨hop, _, h0lt, h1lt⟩ := ao2_gate_props hAO2 hj
  have hNotOr : (gateAt C j).op ≠ GateOp.or := by
    intro hor
    have hlp := lpAt_snd_or hAO2 p l hj hor
    rw [← hgEq, hgStar.2.1] at hlp
    have hz := wireVal_or hAO2 (zInput I l) hj hor
    rw [← hgEq, hgStar.2.2] at hz
    obtain ⟨hz0, hz1⟩ := Bool.or_eq_false_iff.mp hz.symm
    rcases Bool.or_eq_true_iff.mp hlp.symm with h0 | h1
    · have hs : bStep C N p gStar (opnd C j 0) :=
        ⟨j, hj, hgEq, Or.inl ⟨hor, Or.inl rfl⟩⟩
      exact hgMin (opnd C j 0) (by omega)
        ⟨Relation.ReflTransGen.tail hgStar.1 hs, h0, hz0⟩
    · have hs : bStep C N p gStar (opnd C j 1) :=
        ⟨j, hj, hgEq, Or.inl ⟨hor, Or.inr rfl⟩⟩
      exact hgMin (opnd C j 1) (by omega)
        ⟨Relation.ReflTransGen.tail hgStar.1 hs, h1, hz1⟩
  have hAnd : (gateAt C j).op = GateOp.and := hop.resolve_right hNotOr
  have hlpAnd := lpAt_snd_and hAO2 p l hj hAnd
  rw [← hgEq, hgStar.2.1] at hlpAnd
  have hChoice : ∃ b : Fin 2,
      wireVal (N + N) C (opnd C j b) (pointInput N p) = true ∧
      (lpAt C N p l (opnd C j (1 - b))).2 = true := by
    rcases Bool.or_eq_true_iff.mp hlpAnd.symm with h01 | h10
    · rcases Bool.and_eq_true_iff.mp h01 with ⟨ha, hb⟩
      exact ⟨0, ha, by simpa using hb⟩
    · rcases Bool.and_eq_true_iff.mp h10 with ⟨hb, ha⟩
      exact ⟨1, ha, by simpa using hb⟩
  rcases hChoice with ⟨b, hua, hvb⟩
  let uStar := opnd C j b
  let vStar := opnd C j (1 - b)
  have hb01 : b = 0 ∨ b = 1 := by
    rcases b with ⟨_ | _ | _, hb⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  have huLt : uStar < gStar := by
    rcases hb01 with rfl | rfl <;> dsimp [uStar] <;> omega
  have hvLt : vStar < gStar := by
    rcases hb01 with rfl | rfl <;> dsimp [vStar] <;> omega
  have hStepV : bStep C N p gStar vStar := by
    rcases hb01 with rfl | rfl
    · exact ⟨j, hj, hgEq, Or.inr ⟨hAnd, Or.inr ⟨rfl, hua⟩⟩⟩
    · exact ⟨j, hj, hgEq, Or.inr ⟨hAnd, Or.inl ⟨rfl, hua⟩⟩⟩
  have hvReach : reachesOut C N p vStar := Relation.ReflTransGen.tail hgStar.1 hStepV
  have hvZ : wireVal (N + N) C vStar (zInput I l) = true := by
    have hng := hgMin vStar hvLt
    by_contra hne
    have hzf : wireVal (N + N) C vStar (zInput I l) = false := Bool.eq_false_iff.mpr hne
    exact hng ⟨hvReach, hvb, hzf⟩
  have huZ : wireVal (N + N) C uStar (zInput I l) = false := by
    have hz := wireVal_and hAO2 (zInput I l) hj hAnd
    rw [← hgEq, hgStar.2.2] at hz
    rcases hb01 with rfl | rfl
    · dsimp only [uStar]
      dsimp only [vStar] at hvZ
      rw [show (1 : Fin 2) - 0 = 1 from rfl] at hvZ
      rw [hvZ, Bool.and_true] at hz
      exact hz.symm
    · dsimp only [uStar]
      dsimp only [vStar] at hvZ
      rw [show (1 : Fin 2) - 1 = 0 from rfl] at hvZ
      rw [hvZ, Bool.true_and] at hz
      exact hz.symm
  have hpMemU : p ∈ aSet C N uStar := mem_aSet.mpr hua
  have hlMemV : l ∈ zLineSet I C vStar := mem_zLineSet.mpr hvZ
  by_cases hA2 : 2 ≤ (aSet C N uStar).card
  · left
    let hasA : ℕ → Prop := fun w =>
      wireVal (N + N) C w (pointInput N p) = true ∧ wireVal (N + N) C w (zInput I l) = false
    have hExA : ∃ w, hasA w ∧ 2 ≤ (aSet C N w).card := ⟨uStar, ⟨hua, huZ⟩, hA2⟩
    let wA := Nat.find hExA
    have hwA : hasA wA ∧ 2 ≤ (aSet C N wA).card := Nat.find_spec hExA
    have hwAMin : ∀ w < wA, ¬ (hasA w ∧ 2 ≤ (aSet C N w).card) := fun w hw => Nat.find_min hExA hw
    have hwALt : wA < N + N + C.gates.length := by
      by_contra hge
      have h0 : aSet C N wA = ∅ := aSet_ge C N (by omega)
      have hwAc := hwA.2
      rw [h0] at hwAc
      simp at hwAc
    have hwAGe : N + N ≤ wA := by
      by_contra hlt
      by_cases hltN : wA < N
      · have h1 := aSet_lt_N C N hltN
        have hwAc := hwA.2
        rw [h1] at hwAc
        simp at hwAc
      · have h0 := aSet_line C N (w := wA) (by omega) (by omega)
        have hwAc := hwA.2
        rw [h0] at hwAc
        simp at hwAc
    let k := wA - (N + N)
    have hk : k < C.gates.length := by omega
    have hwAEq : wA = N + N + k := by omega
    have ⟨hopk, _, hk0, hk1⟩ := ao2_gate_props hAO2 hk
    have hChildA : ∃ bA : Fin 2, hasA (opnd C k bA) := by
      rcases hopk with hand | hor
      · have ha := wireVal_and hAO2 (pointInput N p) hk hand
        have hz := wireVal_and hAO2 (zInput I l) hk hand
        rw [← hwAEq, hwA.1.1] at ha
        rw [← hwAEq, hwA.1.2] at hz
        obtain ⟨ha0, ha1⟩ := Bool.and_eq_true_iff.mp ha.symm
        rcases Bool.and_eq_false_iff.mp hz.symm with hz0 | hz1
        · exact ⟨0, ha0, hz0⟩
        · exact ⟨1, ha1, hz1⟩
      · have ha := wireVal_or hAO2 (pointInput N p) hk hor
        have hz := wireVal_or hAO2 (zInput I l) hk hor
        rw [← hwAEq, hwA.1.1] at ha
        rw [← hwAEq, hwA.1.2] at hz
        obtain ⟨hz0, hz1⟩ := Bool.or_eq_false_iff.mp hz.symm
        rcases Bool.or_eq_true_iff.mp ha.symm with ha0 | ha1
        · exact ⟨0, ha0, hz0⟩
        · exact ⟨1, ha1, hz1⟩
    rcases hChildA with ⟨bA, hbA⟩
    have hbA01 : bA = 0 ∨ bA = 1 := by
      rcases bA with ⟨_ | _ | _, hb⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    have hcLt : opnd C k bA < wA := by
      rcases hbA01 with rfl | rfl <;> omega
    have hcCard : (aSet C N (opnd C k bA)).card < 2 := by
      by_contra hge2
      exact hwAMin (opnd C k bA) hcLt ⟨hbA, by omega⟩
    have hcMem : p ∈ aSet C N (opnd C k bA) := mem_aSet.mpr hbA.1
    have hcSing : aSet C N (opnd C k bA) = {p} := by
      have hpos : 0 < (aSet C N (opnd C k bA)).card := Finset.card_pos.mpr ⟨p, hcMem⟩
      have hcard1 : (aSet C N (opnd C k bA)).card = 1 := by omega
      obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hcard1
      rw [hp'] at hcMem ⊢
      simp at hcMem
      simp [hcMem]
    refine ⟨(⟨k, hk⟩, bA), hI, ?_, ?_, hcSing⟩
    · simpa [← hwAEq] using hwA.2
    · simpa [← hwAEq] using aSet_subset_of_zInput_false I hAO2.1 hwA.1.2
  · right
    have huMem : p ∈ aSet C N uStar := hpMemU
    have huSing : aSet C N uStar = {p} := by
      have hpos : 0 < (aSet C N uStar).card := Finset.card_pos.mpr ⟨p, huMem⟩
      have hcard1 : (aSet C N uStar).card = 1 := by omega
      obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hcard1
      rw [hp'] at huMem ⊢
      simp at huMem
      simp [huMem]
    by_cases hB2 : 2 ≤ (zLineSet I C vStar).card
    · right
      let hasB : ℕ → Prop := fun w =>
        reachesOut C N p w ∧ (lpAt C N p l w).2 = true ∧ l ∈ zLineSet I C w
      have hExB : ∃ w, hasB w ∧ 2 ≤ (zLineSet I C w).card :=
        ⟨vStar, ⟨hvReach, hvb, hlMemV⟩, hB2⟩
      let wB := Nat.find hExB
      have hwB : hasB wB ∧ 2 ≤ (zLineSet I C wB).card := Nat.find_spec hExB
      have hwBMin : ∀ w < wB, ¬ (hasB w ∧ 2 ≤ (zLineSet I C w).card) := fun w hw => Nat.find_min hExB hw
      have hwBLeV : wB ≤ vStar := Nat.find_min' hExB ⟨⟨hvReach, hvb, hlMemV⟩, hB2⟩
      have hwBLtG : wB < gStar := lt_of_le_of_lt hwBLeV hvLt
      have hwBLtLen : wB < N + N + C.gates.length := by
        by_contra hge
        have hlp := lpAt_ge C N p l wB (by omega)
        have hwb2 := hwB.1.2.1
        rw [hlp] at hwb2
        exact Bool.noConfusion hwb2
      have hwBGeN : N ≤ wB := by
        by_contra hlt
        have hlp := lpAt_snd_lt_N C N p l wB (by omega)
        have hwb2 := hwB.1.2.1
        rw [hlp] at hwb2
        exact Bool.noConfusion hwb2
      have hwBGeNN : N + N ≤ wB := by
        by_contra hlt
        have hzl := zLineSet_line I C hwBGeN (by omega)
        have hwBc := hwB.2
        rw [hzl] at hwBc
        simp at hwBc
      let m := wB - (N + N)
      have hm : m < C.gates.length := by omega
      have hwBEq : wB = N + N + m := by omega
      have ⟨hopm, _, hm0, hm1⟩ := ao2_gate_props hAO2 hm
      have hNotAnd : (gateAt C m).op ≠ GateOp.and := by
        intro hand
        have hlp := lpAt_snd_and hAO2 p l hm hand
        rw [← hwBEq, hwB.1.2.1] at hlp
        have hz := zLineSet_and I hAO2 hm hand
        rw [← hwBEq] at hz
        have hlZ := hwB.1.2.2
        rw [hz, Finset.mem_inter] at hlZ
        rcases Bool.or_eq_true_iff.mp hlp.symm with h01 | h10
        · rcases Bool.and_eq_true_iff.mp h01 with ⟨ha0, hb1⟩
          have hs : bStep C N p wB (opnd C m 1) :=
            ⟨m, hm, hwBEq, Or.inr ⟨hand, Or.inr ⟨rfl, ha0⟩⟩⟩
          have hsub : zLineSet I C wB ⊆ zLineSet I C (opnd C m 1) := by
            rw [hz]
            exact Finset.inter_subset_right
          have hcard : 2 ≤ (zLineSet I C (opnd C m 1)).card :=
            le_trans hwB.2 (Finset.card_le_card hsub)
          exact hwBMin (opnd C m 1) (by omega)
            ⟨⟨Relation.ReflTransGen.tail hwB.1.1 hs, hb1, hlZ.2⟩, hcard⟩
        · rcases Bool.and_eq_true_iff.mp h10 with ⟨hb0, ha1⟩
          have hs : bStep C N p wB (opnd C m 0) :=
            ⟨m, hm, hwBEq, Or.inr ⟨hand, Or.inl ⟨rfl, ha1⟩⟩⟩
          have hsub : zLineSet I C wB ⊆ zLineSet I C (opnd C m 0) := by
            rw [hz]
            exact Finset.inter_subset_left
          have hcard : 2 ≤ (zLineSet I C (opnd C m 0)).card :=
            le_trans hwB.2 (Finset.card_le_card hsub)
          exact hwBMin (opnd C m 0) (by omega)
            ⟨⟨Relation.ReflTransGen.tail hwB.1.1 hs, hb0, hlZ.1⟩, hcard⟩
      have hOr : (gateAt C m).op = GateOp.or := hopm.resolve_left hNotAnd
      have hlpOr := lpAt_snd_or hAO2 p l hm hOr
      rw [← hwBEq, hwB.1.2.1] at hlpOr
      have hChildB : ∃ bB : Fin 2, (lpAt C N p l (opnd C m bB)).2 = true := by
        rcases Bool.or_eq_true_iff.mp hlpOr.symm with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      rcases hChildB with ⟨bB, hbB⟩
      have hbB01 : bB = 0 ∨ bB = 1 := by
        rcases bB with ⟨_ | _ | _, hb⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      have hcLt : opnd C m bB < wB := by
        rcases hbB01 with rfl | rfl <;> omega
      have hStepB : bStep C N p wB (opnd C m bB) := by
        rcases hbB01 with rfl | rfl
        · exact ⟨m, hm, hwBEq, Or.inl ⟨hOr, Or.inl rfl⟩⟩
        · exact ⟨m, hm, hwBEq, Or.inl ⟨hOr, Or.inr rfl⟩⟩
      have hcReach : reachesOut C N p (opnd C m bB) :=
        Relation.ReflTransGen.tail hwB.1.1 hStepB
      have hcZ : l ∈ zLineSet I C (opnd C m bB) := by
        rw [mem_zLineSet]
        have hng := hgMin (opnd C m bB) (lt_trans hcLt hwBLtG)
        by_contra hne
        have hzf : wireVal (N + N) C (opnd C m bB) (zInput I l) = false :=
          Bool.eq_false_iff.mpr hne
        exact hng ⟨hcReach, hbB, hzf⟩
      have hcCard : (zLineSet I C (opnd C m bB)).card < 2 := by
        by_contra hge2
        exact hwBMin (opnd C m bB) hcLt ⟨⟨hcReach, hbB, hcZ⟩, by omega⟩
      have hcSing : zLineSet I C (opnd C m bB) = {l} := by
        have hpos : 0 < (zLineSet I C (opnd C m bB)).card := Finset.card_pos.mpr ⟨l, hcZ⟩
        have hcard1 : (zLineSet I C (opnd C m bB)).card = 1 := by omega
        obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hcard1
        rw [hl'] at hcZ ⊢
        simp at hcZ
        simp [hcZ]
      refine ⟨(⟨m, hm⟩, bB), hI, hOr, ?_, ?_, hcSing⟩
      · simpa [← hwBEq] using hwB.2
      · simpa [← hwBEq] using reachesOut_zLineSet I hAO2 hEval hwB.1.1
    · left
      have hvSing : zLineSet I C vStar = {l} := by
        have hpos : 0 < (zLineSet I C vStar).card := Finset.card_pos.mpr ⟨l, hlMemV⟩
        have hcard1 : (zLineSet I C vStar).card = 1 := by omega
        obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hcard1
        rw [hl'] at hlMemV ⊢
        simp at hlMemV
        simp [hlMemV]
      exact ⟨(⟨j, hj⟩, b), hAnd, huSing, hvSing⟩

lemma main (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hUnique : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true } ≤ 10 * C.size := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun pl =>
    I pl.1 pl.2 ∧ lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true
  have hCardE : Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true } = E.card := by
    rw [Fintype.card_subtype]
  rw [hCardE]
  let E1 := E.filter fun pl => ∃ kb, R1 I C kb pl
  let E2a := E.filter fun pl => ∃ jb, R2a I C jb pl
  let E2b := E.filter fun pl => ∃ mb, R2b I C mb pl
  have hSub : E ⊆ E1 ∪ (E2a ∪ E2b) := by
    intro pl hpl
    have hmem := Finset.mem_filter.mp hpl
    rcases hmem.2 with ⟨hI, hls⟩
    rw [lineSingle_eq_lpAt] at hls
    rcases classify_pair I hAO2 hEval pl.1 pl.2 hI hls with h1 | h2a | h2b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpl, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpl, h2a⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpl, h2b⟩))
  have hc1 : E1.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E1 (R1 I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R1_uniq I hUnique C)
  have hc2a : E2a.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E2a (R2a I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R2a_uniq I C)
  have hc2b : E2b.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E2b (R2b I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R2b_uniq I hUnique C)
  have hFcard : Fintype.card (Fin C.size × Fin 2) = 2 * C.size := by
    simp [Fintype.card_prod, mul_comm]
  have hUnion : E.card ≤ E1.card + (E2a.card + E2b.card) :=
    le_trans (Finset.card_le_card hSub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  omega

end PEqualNP.Outside.L_meta_2970

theorem PEqualNP.Outside.L_meta_2970 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size := by
  intro x1 x2 _ x4 hC4 hAO2 hSound
  exact PEqualNP.Outside.L_meta_2970.main x1 x2 x4 hC4 hAO2 hSound
