import Mathlib
import PEqualNP.Defs

-- Helpers adapted from the merged files Outside/L_meta_2970.lean (scan, wireVal and linear-part
-- lemmas) and Outside/L_meta_1942.lean (supports, essential_bound, plane_support).

namespace PEqualNP.Outside.L_meta_7021

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
  ((pairList N p l).zipIdx).map fun (b, i) => if decide (i < N) then (false, b) else (b, false)

def lpList (C : Circuit) (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  linearParts C (fun k => decide (k < N)) (pairList N p l)

def lpAt (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (lpList C N p l).getD w (false, false)

lemma lineSingle_eq_lpAt (C : Circuit) (N : ℕ) (p l : Fin N) :
    lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = (lpAt C N p l C.output).2 := rfl

lemma lpInit_length (N : ℕ) (p l : Fin N) : (lpInit N p l).length = N + N := by
  simp [lpInit, pairList]

lemma lpInit_getD (N : ℕ) (p l : Fin N) (i : ℕ) (hi : i < N + N) :
    (lpInit N p l).getD i (false, false) =
      if i < N then (false, decide (i = p.val)) else (decide (i = N + l.val), false) := by
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
  · have hne : (i == N + l.val) = false := by
      simp
      omega
    simp only [hlt, hne, Bool.or_false, decide_true, ite_true]
    by_cases hep : i = p.val <;> simp [hep]
  · have hne : (i == p.val) = false := by
      simp
      omega
    simp only [hlt, hne, Bool.false_or, decide_false, Bool.false_eq_true, ite_false]
    by_cases hel : i = N + l.val <;> simp [hel]

def lineInput (N : ℕ) (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i.val = N + l.val)

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
    (lpInit N p l).map (·.1) = List.ofFn (lineInput N l) := by
  apply List.ext_getElem
  · simp [lpInit_length]
  · intro i h1 h2
    have hi : i < N + N := by simpa [lpInit_length] using h1
    rw [List.getElem_map, List.getElem_ofFn]
    have hg := lpInit_getD N p l i hi
    rw [List.getD_eq_getElem _ _ (by simp [lpInit_length, hi])] at hg
    rw [hg]
    by_cases hlt : i < N
    · simp [hlt, lineInput]
      omega
    · simp [hlt, lineInput]

lemma lpAt_fst (C : Circuit) (hAO : AndOrOnly C) (N : ℕ) (p l : Fin N) (w : ℕ) :
    (lpAt C N p l w).1 = wireVal (N + N) C w (lineInput N l) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  change ((scan linStep C.gates (lpInit N p l)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn (lineInput N l))).getD w false
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

lemma lpAt_snd_point (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N) :
    (lpAt C N p l w).2 = decide (w = p.val) := by
  rw [lpAt_lt_len C N p l w (by omega), lpInit_getD N p l w (by omega)]
  simp [hw]

lemma lpAt_snd_line (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    (lpAt C N p l w).2 = false := by
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
      ((wireVal (N + N) C (opnd C j 0) (lineInput N l) && (lpAt C N p l (opnd C j 1)).2) ||
       ((lpAt C N p l (opnd C j 0)).2 && wireVal (N + N) C (opnd C j 1) (lineInput N l))) := by
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

noncomputable section Cnt

open Finset Classical

def Le {n : ℕ} (x y : Fin n → Bool) : Prop := ∀ v, x v = true → y v = true

def Mono {n : ℕ} (g : (Fin n → Bool) → Bool) : Prop := ∀ x y, Le x y → g x = true → g y = true

def single {n : ℕ} (a : Fin n) : Fin n → Bool := fun v => decide (v = a)

def Tset {n : ℕ} (g : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  univ.filter fun a => g (single a) = true

lemma mem_Tset {n : ℕ} {g : (Fin n → Bool) → Bool} {a : Fin n} :
    a ∈ Tset g ↔ g (single a) = true := by
  simp [Tset]

def ind {n : ℕ} (Z : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ Z)

lemma ind_single {n : ℕ} (a : Fin n) : ind ({a} : Finset (Fin n)) = single a := by
  funext v; simp [ind, single]

lemma ind_le {n : ℕ} {Z Z' : Finset (Fin n)} (h : Z ⊆ Z') : Le (ind Z) (ind Z') := by
  intro v hv
  simp only [ind, decide_eq_true_eq] at hv ⊢
  exact h hv

def Dirt {n : ℕ} (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) (m : ℕ) : Prop :=
  ∃ Z : Finset (Fin n), Disjoint Z S ∧ Z.card ≤ m ∧ g (ind Z) = true

lemma dirt_mono {n : ℕ} {S : Finset (Fin n)} {g : (Fin n → Bool) → Bool} {m m' : ℕ}
    (h : Dirt S g m) (hm : m ≤ m') : Dirt S g m' := by
  obtain ⟨Z, h1, h2, h3⟩ := h
  exact ⟨Z, h1, h2.trans hm, h3⟩

lemma T_sub_of_not_dirt {n : ℕ} {S : Finset (Fin n)} {g : (Fin n → Bool) → Bool}
    (h : ¬ Dirt S g 1) : Tset g ⊆ S := by
  intro a ha
  by_contra hn
  exact h ⟨{a}, by simpa using hn, by simp, by rw [ind_single]; exact mem_Tset.mp ha⟩

lemma wv_cases (n : ℕ) (C : Circuit) (w : ℕ) :
    (∃ h : w < n, ∀ x : Fin n → Bool, wireVal n C w x = x ⟨w, h⟩) ∨
    (∃ j, j < C.gates.length ∧ w = n + j) ∨
    (∀ x : Fin n → Bool, wireVal n C w x = false) := by
  by_cases h : w < n
  · exact Or.inl ⟨h, fun x => wireVal_input n C x w h⟩
  by_cases h2 : w < n + C.gates.length
  · exact Or.inr (Or.inl ⟨w - n, by omega, by omega⟩)
  · exact Or.inr (Or.inr fun x => wireVal_ge n C x w (by omega))

lemma f_and {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∧ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_and hC x hj hop, Bool.and_eq_true]

lemma f_or {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∨ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_or hC x hj hop, Bool.or_eq_true]

lemma mono_wire {n : ℕ} {C : Circuit} (hC : IsAO2 n C) : ∀ w, Mono (wireVal n C w) := by
  intro w
  induction' w using Nat.strong_induction_on with w ih
  intro x y hxy hx
  rcases wv_cases n C w with ⟨h, hv⟩ | ⟨j, hj, rfl⟩ | hv
  · rw [hv] at hx
    rw [hv]
    exact hxy _ hx
  · obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hC hj
    rcases hop with hop | hop
    · rw [f_and hC hj hop] at hx
      rw [f_and hC hj hop]
      exact ⟨ih _ h0 x y hxy hx.1, ih _ h1 x y hxy hx.2⟩
    · rw [f_or hC hj hop] at hx
      rw [f_or hC hj hop]
      exact hx.imp (ih _ h0 x y hxy) (ih _ h1 x y hxy)
  · rw [hv] at hx
    exact absurd hx (by decide)

lemma T_or {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    Tset (wireVal n C (n + j)) ⊆
      Tset (wireVal n C (opnd C j 0)) ∪ Tset (wireVal n C (opnd C j 1)) := by
  intro a ha
  rw [mem_union, mem_Tset, mem_Tset]
  exact (f_or hC hj hop _).mp (mem_Tset.mp ha)

lemma T_and_left {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 0)) :=
  fun _ ha => mem_Tset.mpr ((f_and hC hj hop _).mp (mem_Tset.mp ha)).1

lemma T_and_right {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 1)) :=
  fun _ ha => mem_Tset.mpr ((f_and hC hj hop _).mp (mem_Tset.mp ha)).2

def mid (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (range C.gates.length).filter fun j =>
    2 ≤ (Tset (wireVal n C (n + j)) ∩ S).card ∧ ¬ Dirt S (wireVal n C (n + j)) 1

lemma mem_mid {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {j : ℕ} :
    j ∈ mid n C S ↔ j < C.gates.length ∧
      2 ≤ (Tset (wireVal n C (n + j)) ∩ S).card ∧ ¬ Dirt S (wireVal n C (n + j)) 1 := by
  simp [mid]

def smA (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  if (Tset (wireVal n C w) ∩ S).card ≤ 1 then Tset (wireVal n C w) ∩ S else ∅

def smB (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  if h : Dirt S (wireVal n C w) 1 then h.choose else ∅

lemma smA_card (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : (smA n C S w).card ≤ 1 := by
  unfold smA
  split_ifs with h
  · exact h
  · simp

lemma smB_card (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : (smB n C S w).card ≤ 1 := by
  unfold smB
  split_ifs with h
  · exact h.choose_spec.2.1
  · simp

lemma smB_disj (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Disjoint (smB n C S w) S := by
  unfold smB
  split_ifs with h
  · exact h.choose_spec.1
  · simp

def LA (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset (Fin n) :=
  (mid n C S).biUnion fun j => smA n C S (opnd C j 0) ∪ smA n C S (opnd C j 1)

def LB (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset (Fin n) :=
  (mid n C S).biUnion fun j => smB n C S (opnd C j 0) ∪ smB n C S (opnd C j 1)

lemma LA_card (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    (LA n C S).card ≤ 2 * (mid n C S).card := by
  unfold LA
  calc _ ≤ ∑ j ∈ mid n C S, (smA n C S (opnd C j 0) ∪ smA n C S (opnd C j 1)).card :=
        card_biUnion_le
    _ ≤ ∑ _j ∈ mid n C S, 2 := sum_le_sum fun j _ => by
        have h0 := card_union_le (smA n C S (opnd C j 0)) (smA n C S (opnd C j 1))
        have h1 := smA_card n C S (opnd C j 0)
        have h2 := smA_card n C S (opnd C j 1)
        omega
    _ = 2 * (mid n C S).card := by simp [mul_comm]

lemma LB_card (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    (LB n C S).card ≤ 2 * (mid n C S).card := by
  unfold LB
  calc _ ≤ ∑ j ∈ mid n C S, (smB n C S (opnd C j 0) ∪ smB n C S (opnd C j 1)).card :=
        card_biUnion_le
    _ ≤ ∑ _j ∈ mid n C S, 2 := sum_le_sum fun j _ => by
        have h0 := card_union_le (smB n C S (opnd C j 0)) (smB n C S (opnd C j 1))
        have h1 := smB_card n C S (opnd C j 0)
        have h2 := smB_card n C S (opnd C j 1)
        omega
    _ = 2 * (mid n C S).card := by simp [mul_comm]

lemma LB_disj (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Disjoint (LB n C S) S := by
  unfold LB
  rw [disjoint_biUnion_left]
  intro i _
  rw [disjoint_union_left]
  exact ⟨smB_disj n C S _, smB_disj n C S _⟩

lemma opd_cases {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) :
    (Tset (wireVal n C w) ∩ S).card ≤ 1 ∨ Dirt S (wireVal n C w) 1 ∨
      ∃ j, w = n + j ∧ j ∈ mid n C S := by
  by_cases h1 : (Tset (wireVal n C w) ∩ S).card ≤ 1
  · exact Or.inl h1
  by_cases h2 : Dirt S (wireVal n C w) 1
  · exact Or.inr (Or.inl h2)
  right; right
  rcases wv_cases n C w with ⟨h, hv⟩ | ⟨j, hj, rfl⟩ | hv
  · exfalso; apply h1
    have hsub : Tset (wireVal n C w) ∩ S ⊆ {⟨w, h⟩} := by
      intro a ha
      have h3 := mem_Tset.mp (mem_inter.mp ha).1
      rw [hv] at h3
      simp only [single, decide_eq_true_eq] at h3
      exact mem_singleton.mpr h3.symm
    exact (card_le_card hsub).trans (by simp)
  · exact ⟨j, rfl, mem_mid.mpr ⟨hj, by omega, h2⟩⟩
  · exfalso; apply h1
    have h3 : Tset (wireVal n C w) = ∅ := by
      ext a; simp [mem_Tset, hv]
    simp [h3]

lemma mid_claim {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (S : Finset (Fin n)) :
    ∀ j, j ∈ mid n C S →
      Tset (wireVal n C (n + j)) ∩ S ⊆ LA n C S ∨ wireVal n C (n + j) (ind (LB n C S)) = true := by
  intro j
  induction' j using Nat.strong_induction_on with j ih
  intro hi
  have hj := (mem_mid.mp hi).1
  obtain ⟨hop, _, hb0, hb1⟩ := ao2_gate_props hC hj
  have child : ∀ b : Fin 2, (b = 0 ∨ b = 1) →
      Tset (wireVal n C (opnd C j b)) ∩ S ⊆ LA n C S ∨
        wireVal n C (opnd C j b) (ind (LB n C S)) = true := by
    intro b hb
    have hlt : opnd C j b < n + j := by
      rcases hb with rfl | rfl
      · exact hb0
      · exact hb1
    rcases opd_cases C S (opnd C j b) with h1 | h2 | ⟨j', hoj, hj'⟩
    · left
      have hsm : smA n C S (opnd C j b) = Tset (wireVal n C (opnd C j b)) ∩ S := by
        simp [smA, h1]
      rw [← hsm]
      intro a ha
      refine mem_biUnion.mpr ⟨j, hi, ?_⟩
      rcases hb with rfl | rfl
      · exact mem_union_left _ ha
      · exact mem_union_right _ ha
    · right
      have hsub : smB n C S (opnd C j b) ⊆ LB n C S := by
        intro a ha
        refine mem_biUnion.mpr ⟨j, hi, ?_⟩
        rcases hb with rfl | rfl
        · exact mem_union_left _ ha
        · exact mem_union_right _ ha
      have hsm : smB n C S (opnd C j b) = h2.choose := by unfold smB; exact dif_pos h2
      have htrue : wireVal n C (opnd C j b) (ind (smB n C S (opnd C j b))) = true := by
        rw [hsm]; exact h2.choose_spec.2.2
      exact mono_wire hC _ _ _ (ind_le hsub) htrue
    · have hlt' : j' < j := by omega
      rw [hoj]
      exact ih j' hlt' hj'
  have hL := child 0 (Or.inl rfl)
  have hR := child 1 (Or.inr rfl)
  rcases hop with ha | ha
  · rcases hL with hL | hL
    · exact Or.inl ((inter_subset_inter (T_and_left hC hj ha) (subset_refl S)).trans hL)
    rcases hR with hR | hR
    · exact Or.inl ((inter_subset_inter (T_and_right hC hj ha) (subset_refl S)).trans hR)
    · exact Or.inr ((f_and hC hj ha _).mpr ⟨hL, hR⟩)
  · rcases hL with hL | hL
    · rcases hR with hR | hR
      · left
        intro a hm
        obtain ⟨h1, h2⟩ := mem_inter.mp hm
        rcases mem_union.mp (T_or hC hj ha h1) with h3 | h3
        · exact hL (mem_inter.mpr ⟨h3, h2⟩)
        · exact hR (mem_inter.mpr ⟨h3, h2⟩)
      · exact Or.inr ((f_or hC hj ha _).mpr (Or.inr hR))
    · exact Or.inr ((f_or hC hj ha _).mpr (Or.inl hL))

lemma approx_one {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (S : Finset (Fin n)) (w : ℕ) :
    (Tset (wireVal n C w) ∩ S).card ≤ 2 * (mid n C S).card + 1 ∨
      Dirt S (wireVal n C w) (2 * (mid n C S).card + 1) := by
  rcases opd_cases C S w with h1 | h2 | ⟨j, hoj, hj⟩
  · left; omega
  · right; exact dirt_mono h2 (by omega)
  · subst hoj
    rcases mid_claim hC S j hj with h | h
    · left
      exact le_trans (card_le_card h) ((LA_card n C S).trans (by omega))
    · right
      exact ⟨LB n C S, LB_disj n C S, (LB_card n C S).trans (by omega), h⟩

theorem sum_min_le {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {κ : Type} [Fintype κ]
    (Nb : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) (σ : ℕ)
    (h : κ → ℕ)
    (hsound : ∀ c, ∀ Z : Finset (Fin n), Disjoint Z (Nb c) → Z.card < σ →
      wireVal n C (h c) (ind Z) = false) :
    ∑ c, min (Tset (wireVal n C (h c)) ∩ Nb c).card σ ≤
      2 * C.gates.length + Fintype.card κ := by
  have hterm : ∀ c, min (Tset (wireVal n C (h c)) ∩ Nb c).card σ ≤
      2 * (mid n C (Nb c)).card + 1 := by
    intro c
    rcases approx_one hC (Nb c) (h c) with h1 | ⟨Z, hd, hc, ht⟩
    · exact (Nat.min_le_left _ _).trans h1
    · have hσ : σ ≤ Z.card := by
        by_contra hlt
        have hf := hsound c Z hd (by omega)
        rw [hf] at ht
        exact Bool.false_ne_true ht
      exact (Nat.min_le_right _ _).trans (by omega)
  have hpair : ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (mid n C (Nb c)) (mid n C (Nb c')) := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨_, h2, _⟩ := mem_mid.mp hi
    obtain ⟨_, _, hn'⟩ := mem_mid.mp hi'
    have hsub : Tset (wireVal n C (n + i)) ∩ Nb c ⊆ Nb c ∩ Nb c' := fun a ha =>
      mem_inter.mpr ⟨(mem_inter.mp ha).2, T_sub_of_not_dirt hn' (mem_inter.mp ha).1⟩
    have h3 := card_le_card hsub
    have h4 := hdisj c c' hne
    omega
  have hsum : ∑ c, (mid n C (Nb c)).card ≤ C.gates.length := by
    rw [← card_biUnion hpair]
    have hsub : (univ.biUnion fun c => mid n C (Nb c)) ⊆ range C.gates.length := by
      intro j hj
      obtain ⟨c, _, hc⟩ := mem_biUnion.mp hj
      exact mem_range.mpr (mem_mid.mp hc).1
    exact (card_le_card hsub).trans (by simp)
  calc ∑ c, min (Tset (wireVal n C (h c)) ∩ Nb c).card σ
      ≤ ∑ c, (2 * (mid n C (Nb c)).card + 1) := sum_le_sum fun c _ => hterm c
    _ = 2 * ∑ c, (mid n C (Nb c)).card + Fintype.card κ := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ 2 * C.gates.length + Fintype.card κ := by omega

def lift0 {N : ℕ} (x : Fin N → Bool) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then false else x ⟨i.val - N, by omega⟩

def val0 (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → Bool) : Bool :=
  wireVal (N + N) C w (lift0 x)

def opdAt (C : Circuit) (k : ℕ) : ℕ := if k % 2 = 0 then opnd C (k / 2) 0 else opnd C (k / 2) 1

def othAt (C : Circuit) (k : ℕ) : ℕ := if k % 2 = 0 then opnd C (k / 2) 1 else opnd C (k / 2) 0

lemma opdAt_even (C : Circuit) (j : ℕ) : opdAt C (2 * j) = opnd C j 0 := by
  have h1 : (2 * j) % 2 = 0 := by omega
  have h2 : (2 * j) / 2 = j := by omega
  unfold opdAt
  rw [if_pos h1, h2]

lemma opdAt_odd (C : Circuit) (j : ℕ) : opdAt C (2 * j + 1) = opnd C j 1 := by
  have h1 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  unfold opdAt
  rw [if_neg h1, h2]

lemma othAt_even (C : Circuit) (j : ℕ) : othAt C (2 * j) = opnd C j 1 := by
  have h1 : (2 * j) % 2 = 0 := by omega
  have h2 : (2 * j) / 2 = j := by omega
  unfold othAt
  rw [if_pos h1, h2]

lemma othAt_odd (C : Circuit) (j : ℕ) : othAt C (2 * j + 1) = opnd C j 0 := by
  have h1 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  unfold othAt
  rw [if_neg h1, h2]

lemma opdAt_lt {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {k : ℕ} (hk : k < 2 * C.gates.length) :
    opdAt C k < n + k / 2 := by
  have hj : k / 2 < C.gates.length := by omega
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_props hC hj
  unfold opdAt
  split_ifs
  · exact h0
  · exact h1

lemma othAt_lt {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {k : ℕ} (hk : k < 2 * C.gates.length) :
    othAt C k < n + k / 2 := by
  have hj : k / 2 < C.gates.length := by omega
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_props hC hj
  unfold othAt
  split_ifs
  · exact h1
  · exact h0

def Side (N : ℕ) (C : Circuit) (x : Fin N → Bool) (k : ℕ) : Prop :=
  (gateAt C (k / 2)).op = GateOp.and → val0 N C (othAt C k) x = true

def AdjStep (N : ℕ) (C : Circuit) (x : Fin N → Bool) (w' w : ℕ) : Prop :=
  ∃ k, k < 2 * C.gates.length ∧ N + N + k / 2 = w' ∧ opdAt C k = w ∧ Side N C x k

def Reach (N : ℕ) (C : Circuit) (x : Fin N → Bool) (w' w : ℕ) : Prop :=
  Relation.ReflTransGen (AdjStep N C x) w' w

def Cp (N : ℕ) (C : Circuit) (x : Fin N → Bool) (k : ℕ) : Prop :=
  Reach N C x C.output (N + N + k / 2) ∧ Side N C x k

def EpFrom (N : ℕ) (C : Circuit) (x : Fin N → Bool) (k0 w : ℕ) : Prop :=
  ∃ k', k0 ≤ k' ∧ k' < 2 * C.gates.length ∧ opdAt C k' = w ∧ Cp N C x k'

lemma reach_iff (N : ℕ) (C : Circuit) (x : Fin N → Bool) {w : ℕ} (hw : w ≠ C.output) :
    Reach N C x C.output w ↔ EpFrom N C x 0 w := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h0 | ⟨b, hb, k, hk, rfl, ho, hs⟩
    · exact absurd h0 hw
    · exact ⟨k, Nat.zero_le _, hk, ho, hb, hs⟩
  · rintro ⟨k, _, hk, ho, hp, hs⟩
    exact Relation.ReflTransGen.tail hp ⟨k, hk, rfl, ho, hs⟩

lemma gate_true {N : ℕ} {C : Circuit} (hC : IsAO2 (N + N) C) {k : ℕ}
    (hk : k < 2 * C.gates.length) (z : Fin (N + N) → Bool)
    (h1 : wireVal (N + N) C (opdAt C k) z = true)
    (h2 : (gateAt C (k / 2)).op = GateOp.and → wireVal (N + N) C (othAt C k) z = true) :
    wireVal (N + N) C (N + N + k / 2) z = true := by
  have hj : k / 2 < C.gates.length := by omega
  obtain ⟨hop, _, _, _⟩ := ao2_gate_props hC hj
  unfold opdAt at h1
  unfold othAt at h2
  rcases hop with hop | hop
  · rw [f_and hC hj hop]
    have h2' := h2 hop
    split_ifs at h1 h2'
    · exact ⟨h1, h2'⟩
    · exact ⟨h2', h1⟩
  · rw [f_or hC hj hop]
    split_ifs at h1
    · exact Or.inl h1
    · exact Or.inr h1

lemma reach_sound {N : ℕ} {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) {w' w : ℕ}
    (h : Reach N C x w' w) :
    ∀ z, Le (lift0 x) z → wireVal (N + N) C w z = true → wireVal (N + N) C w' z = true := by
  unfold Reach at h
  induction h with
  | refl => exact fun _ _ h => h
  | tail _ hstep ih =>
    obtain ⟨k, hk, rfl, rfl, hs⟩ := hstep
    intro z hz hw
    apply ih z hz
    exact gate_true hC hk z hw (fun hop => mono_wire hC _ _ _ hz (hs hop))

def ONE (N : ℕ) : ℕ := 2 * N - 1

def ZERO (N : ℕ) : ℕ := 3 * N - 1

def tr (N : ℕ) (w : ℕ) : ℕ := if w < N then ZERO N else if w < 2 * N then w - N else N + w

def cW (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  3 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k)

def eW (N : ℕ) (C : Circuit) (k : ℕ) : ℕ := cW N C k + 1

def lnk (N : ℕ) (C : Circuit) (k0 w : ℕ) : ℕ :=
  if h : ∃ k', k0 ≤ k' ∧ k' < 2 * C.gates.length ∧ opdAt C k' = w then eW N C (Nat.find h)
  else ZERO N

def adjW (N : ℕ) (C : Circuit) (w : ℕ) : ℕ := if w = C.output then ONE N else lnk N C 0 w

def uGate (N j : ℕ) : Gate := ⟨GateOp.or, [if j = 0 then 0 else N + (j - 1), j]⟩

def zGate (N i : ℕ) : Gate := ⟨GateOp.and, [if i = 0 then 0 else 2 * N + (i - 1), i]⟩

def dGate (N : ℕ) (C : Circuit) (i : ℕ) : Gate :=
  ⟨(gateAt C i).op, [tr N (opnd C i 0), tr N (opnd C i 1)]⟩

def cGate (N : ℕ) (C : Circuit) (k : ℕ) : Gate :=
  ⟨GateOp.and, [adjW N C (N + N + k / 2),
    if (gateAt C (k / 2)).op = GateOp.and then tr N (othAt C k) else ONE N]⟩

def eGate (N : ℕ) (C : Circuit) (k : ℕ) : Gate :=
  ⟨GateOp.or, [cW N C k, lnk N C (k + 1) (opdAt C k)]⟩

def adjGate (N : ℕ) (C : Circuit) (j : ℕ) : Gate :=
  if j < N then uGate N j
  else if j < 2 * N then zGate N (j - N)
  else if j < 2 * N + C.gates.length then dGate N C (j - 2 * N)
  else if (j - (2 * N + C.gates.length)) % 2 = 0 then
    cGate N C (2 * C.gates.length - 1 - (j - (2 * N + C.gates.length)) / 2)
  else eGate N C (2 * C.gates.length - 1 - (j - (2 * N + C.gates.length)) / 2)

def adjC (N : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range (2 * N + 5 * C.gates.length)).map (adjGate N C), 0⟩

lemma adj_len (N : ℕ) (C : Circuit) :
    (adjC N C).gates.length = 2 * N + 5 * C.gates.length := by
  simp [adjC]

lemma gateAt_adj (N : ℕ) (C : Circuit) {j : ℕ} (hj : j < 2 * N + 5 * C.gates.length) :
    gateAt (adjC N C) j = adjGate N C j := by
  unfold gateAt adjC
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

lemma tr_lt {N : ℕ} (hN : 0 < N) {w i : ℕ} (hw : w < N + N + i) : tr N w < 3 * N + i := by
  unfold tr ZERO
  split_ifs <;> omega

lemma lnk_lt {N : ℕ} (hN : 0 < N) (C : Circuit) (k0 w kmin : ℕ)
    (hk : ∀ k', k0 ≤ k' → k' < 2 * C.gates.length → opdAt C k' = w → kmin ≤ k') :
    lnk N C k0 w < 3 * N + C.gates.length + 2 * (2 * C.gates.length - kmin) := by
  unfold lnk
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    have h4 := hk _ h1 h2 h3
    unfold eW cW
    omega
  · unfold ZERO
    omega

lemma adjGate_shape {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) {j : ℕ}
    (hj : j < 2 * N + 5 * C.gates.length) :
    ((adjGate N C j).op = GateOp.and ∨ (adjGate N C j).op = GateOp.or) ∧
      ∃ a b, (adjGate N C j).inputs = [a, b] ∧ a < N + j ∧ b < N + j := by
  unfold adjGate
  split_ifs with h1 h2 h3 h4
  · refine ⟨Or.inr rfl, _, _, rfl, ?_, ?_⟩
    · split_ifs <;> omega
    · omega
  · refine ⟨Or.inl rfl, _, _, rfl, ?_, ?_⟩
    · split_ifs <;> omega
    · omega
  · have hi : j - 2 * N < C.gates.length := by omega
    obtain ⟨hop, _, hb0, hb1⟩ := ao2_gate_props hC hi
    refine ⟨hop, _, _, rfl, ?_, ?_⟩
    · have := tr_lt hN hb0
      omega
    · have := tr_lt hN hb1
      omega
  · obtain ⟨k, hkd⟩ : ∃ k, k = 2 * C.gates.length - 1 - (j - (2 * N + C.gates.length)) / 2 :=
      ⟨_, rfl⟩
    rw [← hkd]
    have hk : k < 2 * C.gates.length := by omega
    refine ⟨Or.inl rfl, _, _, rfl, ?_, ?_⟩
    · unfold adjW
      split_ifs
      · unfold ONE
        omega
      · have := lnk_lt hN C 0 (N + N + k / 2) (k + 1) (by
          intro k' _ hk' ho
          have := opdAt_lt hC hk'
          omega)
        omega
    · split_ifs
      · have := tr_lt hN (othAt_lt hC hk)
        omega
      · unfold ONE
        omega
  · obtain ⟨k, hkd⟩ : ∃ k, k = 2 * C.gates.length - 1 - (j - (2 * N + C.gates.length)) / 2 :=
      ⟨_, rfl⟩
    rw [← hkd]
    have hk : k < 2 * C.gates.length := by omega
    refine ⟨Or.inr rfl, _, _, rfl, ?_, ?_⟩
    · unfold cW
      omega
    · have := lnk_lt hN C (k + 1) (opdAt C k) (k + 1) (fun k' h _ _ => h)
      omega

lemma adj_AO2 {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) :
    IsAO2 N (adjC N C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (List.range (2 * N + 5 * C.gates.length)).map (adjGate N C) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact (adjGate_shape hN hC (List.mem_range.mp hj)).1
  · intro j hj i hi
    rw [adj_len] at hj
    rw [gateAt_adj N C hj] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := adjGate_shape hN hC hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    have hg' : g ∈ (List.range (2 * N + 5 * C.gates.length)).map (adjGate N C) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    obtain ⟨_, a, b, hab, _⟩ := adjGate_shape hN hC (List.mem_range.mp hj)
    rw [hab]
    rfl

lemma gate_and2 {n : ℕ} {G : Circuit} (hG : IsAO2 n G) (x : Fin n → Bool) {j : ℕ}
    (hj : j < G.gates.length) {a b : ℕ} (hg : gateAt G j = ⟨GateOp.and, [a, b]⟩) :
    wireVal n G (n + j) x = (wireVal n G a x && wireVal n G b x) := by
  have hop : (gateAt G j).op = GateOp.and := by rw [hg]
  have e0 : opnd G j 0 = a := by simp [opnd, hg]
  have e1 : opnd G j 1 = b := by simp [opnd, hg]
  rw [wireVal_and hG x hj hop, e0, e1]

lemma gate_or2 {n : ℕ} {G : Circuit} (hG : IsAO2 n G) (x : Fin n → Bool) {j : ℕ}
    (hj : j < G.gates.length) {a b : ℕ} (hg : gateAt G j = ⟨GateOp.or, [a, b]⟩) :
    wireVal n G (n + j) x = (wireVal n G a x || wireVal n G b x) := by
  have hop : (gateAt G j).op = GateOp.or := by rw [hg]
  have e0 : opnd G j 0 = a := by simp [opnd, hg]
  have e1 : opnd G j 1 = b := by simp [opnd, hg]
  rw [wireVal_or hG x hj hop, e0, e1]

def Full {N : ℕ} (x : Fin N → Bool) : Prop := ∀ i, x i = true

def Ne {N : ℕ} (x : Fin N → Bool) : Prop := ∃ i, x i = true

def Ap {N : ℕ} (x : Fin N → Bool) (v : Bool) (P : Prop) : Prop :=
  (¬ Full x → v = true → P) ∧ (Ne x → P → v = true)

lemma Ap_and {N : ℕ} {x : Fin N → Bool} {v1 v2 : Bool} {P1 P2 : Prop}
    (h1 : Ap x v1 P1) (h2 : Ap x v2 P2) : Ap x (v1 && v2) (P1 ∧ P2) := by
  constructor
  · intro hf hv
    rw [Bool.and_eq_true] at hv
    exact ⟨h1.1 hf hv.1, h2.1 hf hv.2⟩
  · intro hn hp
    rw [Bool.and_eq_true]
    exact ⟨h1.2 hn hp.1, h2.2 hn hp.2⟩

lemma Ap_or {N : ℕ} {x : Fin N → Bool} {v1 v2 : Bool} {P1 P2 : Prop}
    (h1 : Ap x v1 P1) (h2 : Ap x v2 P2) : Ap x (v1 || v2) (P1 ∨ P2) := by
  constructor
  · intro hf hv
    rw [Bool.or_eq_true] at hv
    exact hv.imp (h1.1 hf) (h2.1 hf)
  · intro hn hp
    rw [Bool.or_eq_true]
    exact hp.imp (h1.2 hn) (h2.2 hn)

lemma Ap_congr {N : ℕ} {x : Fin N → Bool} {v : Bool} {P Q : Prop}
    (h : Ap x v P) (hpq : P ↔ Q) : Ap x v Q :=
  ⟨fun hf hv => hpq.mp (h.1 hf hv), fun hn hq => h.2 hn (hpq.mpr hq)⟩

lemma Ap_exact {N : ℕ} {x : Fin N → Bool} {v : Bool} {P : Prop}
    (h : v = true ↔ P) : Ap x v P :=
  ⟨fun _ hv => h.mp hv, fun _ hp => h.mpr hp⟩

lemma u_val {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    ∀ i, i < N → (wireVal N (adjC N C) (N + i) x = true ↔
      ∃ i' : Fin N, i'.val ≤ i ∧ x i' = true) := by
  have hG := adj_AO2 hN hC
  intro i
  induction i with
  | zero =>
    intro hi
    have hg : gateAt (adjC N C) 0 = ⟨GateOp.or, [0, 0]⟩ := by
      rw [gateAt_adj N C (by omega), adjGate, if_pos hi]
      rfl
    rw [gate_or2 hG x (by rw [adj_len]; omega) hg, wireVal_input N (adjC N C) x 0 hN,
      Bool.or_self]
    constructor
    · intro h
      exact ⟨⟨0, hN⟩, le_refl _, h⟩
    · rintro ⟨i', hi', h⟩
      have e : i' = ⟨0, hN⟩ := Fin.ext (by simpa using hi')
      rw [← e]
      exact h
  | succ i ih =>
    intro hi
    have hg : gateAt (adjC N C) (i + 1) = ⟨GateOp.or, [N + i, i + 1]⟩ := by
      rw [gateAt_adj N C (by omega), adjGate, if_pos hi]
      simp [uGate]
    rw [gate_or2 hG x (by rw [adj_len]; omega) hg, wireVal_input N (adjC N C) x (i + 1) hi,
      Bool.or_eq_true, ih (by omega)]
    constructor
    · rintro (⟨i', hi', h⟩ | h)
      · exact ⟨i', by omega, h⟩
      · exact ⟨⟨i + 1, hi⟩, le_refl _, h⟩
    · rintro ⟨i', hi', h⟩
      by_cases hle : i'.val ≤ i
      · exact Or.inl ⟨i', hle, h⟩
      · right
        have e : i' = ⟨i + 1, hi⟩ := Fin.ext (by simp; omega)
        rw [← e]
        exact h

lemma z_val {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    ∀ i, i < N → (wireVal N (adjC N C) (N + (N + i)) x = true ↔
      ∀ i' : Fin N, i'.val ≤ i → x i' = true) := by
  have hG := adj_AO2 hN hC
  intro i
  induction i with
  | zero =>
    intro hi
    have hg : gateAt (adjC N C) (N + 0) = ⟨GateOp.and, [0, 0]⟩ := by
      rw [gateAt_adj N C (by omega), adjGate, if_neg (by omega), if_pos (by omega)]
      simp [zGate]
    rw [gate_and2 hG x (by rw [adj_len]; omega) hg, wireVal_input N (adjC N C) x 0 hN,
      Bool.and_self]
    constructor
    · intro h i' hi'
      have e : i' = ⟨0, hN⟩ := Fin.ext (by simpa using hi')
      rw [e]
      exact h
    · intro h
      exact h ⟨0, hN⟩ (le_refl _)
  | succ i ih =>
    intro hi
    have hg : gateAt (adjC N C) (N + (i + 1)) = ⟨GateOp.and, [N + (N + i), i + 1]⟩ := by
      rw [gateAt_adj N C (by omega), adjGate, if_neg (by omega), if_pos (by omega)]
      have e : N + (i + 1) - N = i + 1 := by omega
      rw [e]
      simp [zGate]
      omega
    rw [gate_and2 hG x (by rw [adj_len]; omega) hg, wireVal_input N (adjC N C) x (i + 1) hi,
      Bool.and_eq_true, ih (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ i' hi'
      by_cases hle : i'.val ≤ i
      · exact h1 i' hle
      · have e : i' = ⟨i + 1, hi⟩ := Fin.ext (by simp; omega)
        rw [e]
        exact h2
    · intro h
      exact ⟨fun i' hi' => h i' (by omega), h ⟨i + 1, hi⟩ (le_refl _)⟩

lemma ONE_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    Ap x (wireVal N (adjC N C) (ONE N) x) True := by
  have e : ONE N = N + (N - 1) := by unfold ONE; omega
  rw [e]
  refine ⟨fun _ _ => trivial, fun hn _ => ?_⟩
  obtain ⟨i, hi⟩ := hn
  exact (u_val hN hC x (N - 1) (by omega)).mpr ⟨i, by have := i.isLt; omega, hi⟩

lemma ZERO_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    Ap x (wireVal N (adjC N C) (ZERO N) x) False := by
  have e : ZERO N = N + (N + (N - 1)) := by unfold ZERO; omega
  rw [e]
  refine ⟨fun hf hv => ?_, fun _ h => h.elim⟩
  apply hf
  intro i
  exact (z_val hN hC x (N - 1) (by omega)).mp hv i (by have := i.isLt; omega)

lemma tr_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    ∀ w, w < N + N + C.gates.length →
      Ap x (wireVal N (adjC N C) (tr N w) x) (val0 N C w x = true) := by
  have hG := adj_AO2 hN hC
  intro w
  induction' w using Nat.strong_induction_on with w ih
  intro hw
  by_cases h1 : w < N
  · have e : tr N w = ZERO N := by unfold tr; rw [if_pos h1]
    have e2 : val0 N C w x = false := by
      unfold val0
      rw [wireVal_input _ _ _ _ (by omega)]
      simp [lift0, h1]
    rw [e, e2]
    exact Ap_congr (ZERO_ap hN hC x) (by simp)
  by_cases h2 : w < N + N
  · have e : tr N w = w - N := by unfold tr; rw [if_neg h1, if_pos (by omega)]
    have e2 : val0 N C w x = x ⟨w - N, by omega⟩ := by
      unfold val0
      rw [wireVal_input _ _ _ _ h2]
      simp [lift0, h1]
    rw [e]
    apply Ap_exact
    rw [e2, wireVal_input N (adjC N C) x (w - N) (by omega)]
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨hop, _, hb0, hb1⟩ := ao2_gate_props hC hj
    have e : tr N (N + N + j) = N + (2 * N + j) := by
      unfold tr
      rw [if_neg (by omega), if_neg (by omega)]
      omega
    have hjG : 2 * N + j < (adjC N C).gates.length := by rw [adj_len]; omega
    have hg0 : gateAt (adjC N C) (2 * N + j) = dGate N C j := by
      rw [gateAt_adj N C (by omega), adjGate, if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
      have e3 : 2 * N + j - 2 * N = j := by omega
      rw [e3]
    have a0 := ih _ hb0 (by omega)
    have a1 := ih _ hb1 (by omega)
    rw [e]
    rcases hop with hop | hop
    · have hg : gateAt (adjC N C) (2 * N + j) =
          ⟨GateOp.and, [tr N (opnd C j 0), tr N (opnd C j 1)]⟩ := by
        rw [hg0, dGate, hop]
      rw [gate_and2 hG x hjG hg]
      refine Ap_congr (Ap_and a0 a1) ?_
      unfold val0
      exact (f_and hC hj hop _).symm
    · have hg : gateAt (adjC N C) (2 * N + j) =
          ⟨GateOp.or, [tr N (opnd C j 0), tr N (opnd C j 1)]⟩ := by
        rw [hg0, dGate, hop]
      rw [gate_or2 hG x hjG hg]
      refine Ap_congr (Ap_or a0 a1) ?_
      unfold val0
      exact (f_or hC hj hop _).symm

lemma lnk_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool)
    (k0 w : ℕ)
    (hE : ∀ k', k0 ≤ k' → k' < 2 * C.gates.length → opdAt C k' = w →
      Ap x (wireVal N (adjC N C) (eW N C k') x) (EpFrom N C x k' w)) :
    Ap x (wireVal N (adjC N C) (lnk N C k0 w) x) (EpFrom N C x k0 w) := by
  unfold lnk
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine Ap_congr (hE _ h1 h2 h3) ?_
    constructor
    · rintro ⟨k', a, b, c, d⟩
      exact ⟨k', by omega, b, c, d⟩
    · rintro ⟨k', a, b, c, d⟩
      exact ⟨k', Nat.find_min' h ⟨a, b, c⟩, b, c, d⟩
  · refine Ap_congr (ZERO_ap hN hC x) ?_
    constructor
    · exact False.elim
    · rintro ⟨k', a, b, c, _⟩
      exact h ⟨k', a, b, c⟩

lemma adjW_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool)
    (w : ℕ)
    (hE : ∀ k', k' < 2 * C.gates.length → opdAt C k' = w →
      Ap x (wireVal N (adjC N C) (eW N C k') x) (EpFrom N C x k' w)) :
    Ap x (wireVal N (adjC N C) (adjW N C w) x) (Reach N C x C.output w) := by
  unfold adjW
  split_ifs with h
  · refine Ap_congr (ONE_ap hN hC x) ?_
    rw [h]
    exact ⟨fun _ => Relation.ReflTransGen.refl, fun _ => trivial⟩
  · exact Ap_congr (lnk_ap hN hC x 0 w (fun k' _ => hE k')) (reach_iff N C x h).symm

lemma main_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool) :
    ∀ k, k < 2 * C.gates.length →
      Ap x (wireVal N (adjC N C) (cW N C k) x) (Cp N C x k) ∧
      Ap x (wireVal N (adjC N C) (eW N C k) x) (EpFrom N C x k (opdAt C k)) := by
  have hG := adj_AO2 hN hC
  intro k
  induction' hm : 2 * C.gates.length - k using Nat.strong_induction_on with m ih generalizing k
  intro hk
  have IH : ∀ k', k < k' → k' < 2 * C.gates.length →
      Ap x (wireVal N (adjC N C) (eW N C k') x) (EpFrom N C x k' (opdAt C k')) :=
    fun k' h1 h2 => (ih _ (by omega) k' rfl h2).2
  have hc : Ap x (wireVal N (adjC N C) (cW N C k) x) (Cp N C x k) := by
    have ew : cW N C k = N + (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k)) := by
      unfold cW; omega
    have hjG : 2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) <
        (adjC N C).gates.length := by rw [adj_len]; omega
    have hg : gateAt (adjC N C) (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k)) =
        ⟨GateOp.and, [adjW N C (N + N + k / 2),
          if (gateAt C (k / 2)).op = GateOp.and then tr N (othAt C k) else ONE N]⟩ := by
      rw [gateAt_adj N C (by omega), adjGate, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega)]
      have e3 : 2 * C.gates.length - 1 -
          (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) -
            (2 * N + C.gates.length)) / 2 = k := by omega
      rw [e3]
      rfl
    rw [ew, gate_and2 hG x hjG hg]
    have hadj : Ap x (wireVal N (adjC N C) (adjW N C (N + N + k / 2)) x)
        (Reach N C x C.output (N + N + k / 2)) := by
      apply adjW_ap hN hC x
      intro k' h1 h2
      have h3 := opdAt_lt hC h1
      have h4 := IH k' (by omega) h1
      rw [h2] at h4
      exact h4
    have hside : Ap x (wireVal N (adjC N C)
        (if (gateAt C (k / 2)).op = GateOp.and then tr N (othAt C k) else ONE N) x)
        (Side N C x k) := by
      by_cases hop : (gateAt C (k / 2)).op = GateOp.and
      · rw [if_pos hop]
        have h3 := othAt_lt hC hk
        exact Ap_congr (tr_ap hN hC x (othAt C k) (by omega)) ⟨fun h _ => h, fun h => h hop⟩
      · rw [if_neg hop]
        exact Ap_congr (ONE_ap hN hC x) ⟨fun _ h => absurd h hop, fun _ => trivial⟩
    exact Ap_and hadj hside
  refine ⟨hc, ?_⟩
  have ew : eW N C k = N + (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) + 1) := by
    unfold eW cW; omega
  have hjG : 2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) + 1 <
      (adjC N C).gates.length := by rw [adj_len]; omega
  have hg : gateAt (adjC N C) (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) + 1) =
      ⟨GateOp.or, [cW N C k, lnk N C (k + 1) (opdAt C k)]⟩ := by
    rw [gateAt_adj N C (by omega), adjGate, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    have e3 : 2 * C.gates.length - 1 -
        (2 * N + C.gates.length + 2 * (2 * C.gates.length - 1 - k) + 1 -
          (2 * N + C.gates.length)) / 2 = k := by omega
    rw [e3]
    rfl
  rw [ew, gate_or2 hG x hjG hg]
  have hl := lnk_ap hN hC x (k + 1) (opdAt C k) (fun k' h1 h2 h3 => by
    have h4 := IH k' (by omega) h2
    rw [h3] at h4
    exact h4)
  refine Ap_congr (Ap_or hc hl) ?_
  constructor
  · rintro (h | ⟨k', a, b, c, d⟩)
    · exact ⟨k, le_refl _, hk, rfl, h⟩
    · exact ⟨k', by omega, b, c, d⟩
  · rintro ⟨k', a, b, c, d⟩
    by_cases hkk : k' = k
    · subst hkk
      exact Or.inl d
    · exact Or.inr ⟨k', by omega, b, c, d⟩

lemma adj_ap {N : ℕ} (hN : 0 < N) {C : Circuit} (hC : IsAO2 (N + N) C) (x : Fin N → Bool)
    (w : ℕ) :
    Ap x (wireVal N (adjC N C) (adjW N C w) x) (Reach N C x C.output w) := by
  apply adjW_ap hN hC x
  intro k' h1 h2
  have h4 := (main_ap hN hC x k' h1).2
  rw [h2] at h4
  exact h4

lemma lift0_single (N : ℕ) (l : Fin N) : lift0 (single l) = lineInput N l := by
  funext i
  unfold lift0 lineInput
  split_ifs with h
  · symm
    apply decide_eq_false
    omega
  · simp only [single]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro e
      have h3 : i.val - N = l.val := congrArg Fin.val e
      omega
    · intro e
      exact Fin.ext (by simp; omega)

lemma side_or {N : ℕ} {C : Circuit} (x : Fin N → Bool) {k : ℕ}
    (hop : (gateAt C (k / 2)).op = GateOp.or) : Side N C x k := by
  intro h
  rw [hop] at h
  cases h

lemma lp_reach {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w : ℕ, (lpAt C N p l w).2 = true → Reach N C (single l) w p.val := by
  intro w
  induction' w using Nat.strong_induction_on with w ih
  intro hw
  by_cases h1 : w < N
  · rw [lpAt_snd_point C N p l w h1] at hw
    rw [of_decide_eq_true hw]
    exact Relation.ReflTransGen.refl
  by_cases h2 : w < N + N
  · rw [lpAt_snd_line C N p l w (by omega) h2] at hw
    exact absurd hw (by decide)
  by_cases h3 : w < N + N + C.gates.length
  swap
  · rw [lpAt_ge C N p l w (by omega)] at hw
    exact absurd hw (by decide)
  obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
  have hj : j < C.gates.length := by omega
  obtain ⟨hop, _, hb0, hb1⟩ := ao2_gate_props hAO2 hj
  have stepdown : ∀ k, k / 2 = j → k < 2 * C.gates.length →
      (lpAt C N p l (opdAt C k)).2 = true → Side N C (single l) k →
      Reach N C (single l) (N + N + j) p.val := by
    intro k hkj hk hb hside
    have hlt : opdAt C k < N + N + j := by
      have := opdAt_lt hAO2 hk
      omega
    exact Relation.ReflTransGen.head ⟨k, hk, by rw [hkj], rfl, hside⟩ (ih _ hlt hb)
  have e0 : (2 * j) / 2 = j := by omega
  have e1 : (2 * j + 1) / 2 = j := by omega
  rcases hop with hop | hop
  · rw [lpAt_snd_and hAO2 p l hj hop] at hw
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hw
    rcases hw with ⟨hv, hb⟩ | ⟨hb, hv⟩
    · apply stepdown (2 * j + 1) e1 (by omega)
      · rw [opdAt_odd]
        exact hb
      · intro _
        unfold val0
        rw [othAt_odd, lift0_single]
        exact hv
    · apply stepdown (2 * j) e0 (by omega)
      · rw [opdAt_even]
        exact hb
      · intro _
        unfold val0
        rw [othAt_even, lift0_single]
        exact hv
  · rw [lpAt_snd_or hAO2 p l hj hop] at hw
    simp only [Bool.or_eq_true] at hw
    rcases hw with hb | hb
    · apply stepdown (2 * j) e0 (by omega)
      · rw [opdAt_even]
        exact hb
      · exact side_or _ (by rw [e0]; exact hop)
    · apply stepdown (2 * j + 1) e1 (by omega)
      · rw [opdAt_odd]
        exact hb
      · exact side_or _ (by rw [e1]; exact hop)

def onePt {N : ℕ} (Z : Finset (Fin N)) (p : Fin N) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then decide (i.val = p.val)
    else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ Z)

lemma lift0_le_onePt {N : ℕ} (Z : Finset (Fin N)) (p : Fin N) :
    Le (lift0 (ind Z)) (onePt Z p) := by
  intro v hv
  unfold lift0 at hv
  unfold onePt
  split_ifs at hv ⊢ with h
  exact hv

lemma onePt_natAdd {N : ℕ} (Z : Finset (Fin N)) (p l : Fin N) :
    onePt Z p (Fin.natAdd N l) = decide (l ∈ Z) := by
  have h : ¬ ((Fin.natAdd N l).val < N) := by simp
  unfold onePt
  rw [dif_neg h]
  have e : (⟨(Fin.natAdd N l).val - N, by have := l.isLt; simp⟩ : Fin N) = l := Fin.ext (by simp)
  rw [e]

lemma onePt_castAdd {N : ℕ} (Z : Finset (Fin N)) (p p' : Fin N) :
    onePt Z p (Fin.castAdd N p') = decide (p' = p) := by
  have h : (Fin.castAdd N p').val < N := p'.isLt
  unfold onePt
  rw [dif_pos h]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩

theorem graded_pointSingle (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (σ : ℕ) (hN : 0 < N) (hσ : σ ≤ N)
    (hC4 : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l')
    (hAO2 : IsAO2 (N + N) C)
    (hSound : ∀ (Z : Finset (Fin N)) (p : Fin N), Z.card < σ →
      circuitFun (N + N) C (onePt Z p) = true → ∃ l ∈ Z, I p l) :
    ∑ p : Fin N, min ((Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card) σ
      ≤ 10 * C.size + 5 * N := by
  have hG := adj_AO2 hN hAO2
  have hdisj : ∀ p p' : Fin N, p ≠ p' →
      ((Finset.univ.filter fun l : Fin N => I p l) ∩
        (Finset.univ.filter fun l : Fin N => I p' l)).card ≤ 1 := by
    intro p p' hne
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_inter, mem_filter, mem_univ, true_and] at ha hb
    exact hC4 p p' hne a b ha.1 ha.2 hb.1 hb.2
  have hs : ∀ p : Fin N, ∀ Z : Finset (Fin N),
      Disjoint Z (Finset.univ.filter fun l : Fin N => I p l) → Z.card < σ →
      wireVal N (adjC N C) (adjW N C p.val) (ind Z) = false := by
    intro p Z hd hZ
    rw [Bool.eq_false_iff]
    intro hx
    have hnf : ¬ Full (ind Z) := by
      intro hf
      have hu : Z = Finset.univ := by
        ext a
        have := hf a
        simp only [ind, decide_eq_true_eq] at this
        simp [this]
      rw [hu, Finset.card_univ, Fintype.card_fin] at hZ
      omega
    have hr := (adj_ap hN hAO2 (ind Z) p.val).1 hnf hx
    have hp : wireVal (N + N) C p.val (onePt Z p) = true := by
      rw [wireVal_input _ _ _ _ (by have := p.isLt; omega)]
      simp [onePt]
    have ht := reach_sound hAO2 (ind Z) hr _ (lift0_le_onePt Z p) hp
    obtain ⟨l, hl, hI⟩ := hSound Z p hZ ht
    exact Finset.disjoint_left.mp hd hl (by simp [hI])
  have key := sum_min_le hG (fun p : Fin N => Finset.univ.filter fun l : Fin N => I p l)
    hdisj σ (fun p => adjW N C p.val) hs
  rw [adj_len, Fintype.card_fin] at key
  have hfin : ∑ p : Fin N, min ((Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card) σ ≤
      ∑ p : Fin N, min (Tset (wireVal N (adjC N C) (adjW N C p.val)) ∩
        (Finset.univ.filter fun l : Fin N => I p l)).card σ := by
    refine Finset.sum_le_sum fun p _ => ?_
    apply min_le_min _ le_rfl
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [mem_inter, mem_Tset]
    refine ⟨?_, by simp [hl.1]⟩
    have hls := hl.2
    rw [lineSingle_eq_lpAt] at hls
    exact (adj_ap hN hAO2 (single l) p.val).2 ⟨l, by simp [single]⟩ (lp_reach hAO2 p l _ hls)
  have hsz : C.size = C.gates.length := rfl
  omega

end Cnt

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (scan boolStep gs x).getD i false = (scan boolStep gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (scan boolStep gs x).length = j := by simp [scan_length, hx, j]
    have ey : (scan boolStep gs y).length = j := by simp [scan_length, hy, j]
    rw [scan_snoc, scan_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  show (scan boolStep C.gates (List.ofFn x)).getD C.output false =
    (scan boolStep C.gates (List.ofFn y)).getD C.output false
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

lemma size_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1) (hq2 : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hpair : ∀ p l : Fin N, I p l → circuitFun (N + N) C (pair p l) = true)
    (hpoint : ∀ p : Fin N, circuitFun (N + N) C (point p) = false)
    (hline : ∀ l : Fin N, circuitFun (N + N) C (line l) = false) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]

lemma point_deg_le (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l')
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  classical
  have hdisj : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ l' ∈ Finset.univ.filter (fun l => I p l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p' => I p' l)).erase p)
        ((Finset.univ.filter (fun p' => I p' l')).erase p) := by
    intro l hl1 l' hl2 hne
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hne (hu p a (Ne.symm ha.1) l l' (Finset.mem_filter.mp hl1).2 ha.2
      (Finset.mem_filter.mp hl2).2 ha'.2)
  have hcard : ((Finset.univ.filter (fun l => I p l)).biUnion
      fun l => (Finset.univ.filter (fun p' => I p' l)).erase p).card =
      (Finset.univ.filter (fun l => I p l)).card * q := by
    rw [Finset.card_biUnion hdisj]
    have hc : ∀ l ∈ Finset.univ.filter (fun l => I p l),
        ((Finset.univ.filter (fun p' => I p' l)).erase p).card = q := by
      intro l hl1
      have hpm : p ∈ Finset.univ.filter (fun p' => I p' l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hl1).2⟩
      rw [Finset.card_erase_of_mem hpm, hl]
      simp
    rw [Finset.sum_congr rfl hc]
    simp
  have hsub : ((Finset.univ.filter (fun l => I p l)).biUnion
      fun l => (Finset.univ.filter (fun p' => I p' l)).erase p) ⊆ Finset.univ.erase p := by
    intro a ha
    obtain ⟨l, _, hal⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hal).1, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have hN' : N - 1 = q ^ 2 + q := by rw [hN]; rfl
  rw [hN'] at h1
  by_contra hcon
  push_neg at hcon
  have h2 := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hcon)
  nlinarith

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO2 : IsAO2 (N + N) C)
    (hT : ∀ p l : Fin N, I p l → circuitFun (N + N) C
      (fun i : Fin (N + N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (hF : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (k < N)) pl.1.val (N + pl.2.val) = true } ≤ 38 * C.size := by
  have hl' : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    rw [← hl l, Fintype.card_subtype]
  have hu : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l' := by
    intro p p' hne l l' h1 h2 h3 h4
    obtain ⟨m, _, hm⟩ := hp p p' hne
    rw [hm l ⟨h1, h2⟩, hm l' ⟨h3, h4⟩]
  have hSound : ∀ (Z : Finset (Fin N)) (p : Fin N), Z.card < q + 1 →
      circuitFun (N + N) C (onePt Z p) = true → ∃ l ∈ Z, I p l := by
    intro Z p hZ ht
    by_contra hno
    have hc : Fintype.card { l : Fin N // onePt Z p (Fin.natAdd N l) = true } ≤ Z.card := by
      rw [Fintype.card_subtype]
      apply Finset.card_le_card
      intro l hl
      have h := (Finset.mem_filter.mp hl).2
      rw [onePt_natAdd] at h
      exact of_decide_eq_true h
    have hf := hF (onePt Z p) (by omega) (by
      rintro ⟨p', l, hI, h1, h2⟩
      rw [onePt_castAdd] at h1
      rw [onePt_natAdd] at h2
      have e : p' = p := of_decide_eq_true h1
      subst e
      exact hno ⟨l, of_decide_eq_true h2, hI⟩)
    rw [hf] at ht
    exact Bool.false_ne_true ht
  have hNpos : 0 < N := by rw [hN]; omega
  have hσ : q + 1 ≤ N := by rw [hN]; linarith [Nat.zero_le (q ^ 2)]
  have key := graded_pointSingle N I C (q + 1) hNpos hσ hu hAO2 hSound
  have hpoint : ∀ p : Fin N, circuitFun (N + N) C (point p) = false := by
    intro p
    apply hF
    · have h0 : Fintype.card { l : Fin N // point p (Fin.natAdd N l) = true } = 0 := by
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun x => cast_ne_nat p x.1 (of_decide_eq_true x.2).symm⟩
      omega
    · rintro ⟨_, l, _, _, h⟩
      exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline : ∀ l : Fin N, circuitFun (N + N) C (line l) = false := by
    intro l
    apply hF
    · rw [Fintype.card_subtype]
      have hsub : (Finset.univ.filter fun l' : Fin N => line l (Fin.natAdd N l') = true) ⊆ {l} := by
        intro l' h'
        have h2 := of_decide_eq_true (Finset.mem_filter.mp h').2
        have h3 : N + l'.val = N + l.val := congrArg Fin.val h2
        exact Finset.mem_singleton.mpr (Fin.ext (by omega))
      have h4 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h4
      omega
    · rintro ⟨p, _, _, h, _⟩
      exact cast_ne_nat p l (of_decide_eq_true h)
  have hsize := size_bound q N I C hN (by omega) hl' hp hAO2 (fun p l h => hT p l h) hpoint hline
  have hcount : Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (k < N)) pl.1.val (N + pl.2.val) = true } =
      ∑ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_filter]
  have hmin : ∀ p : Fin N, min ((Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card) (q + 1) =
      (Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card := by
    intro p
    apply min_eq_left
    refine le_trans (Finset.card_le_card ?_) (point_deg_le q N I (by omega) hN hl' hu p)
    intro l hl1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl1).2.1⟩
  rw [Finset.sum_congr rfl (fun p _ => hmin p)] at key
  rw [hcount]
  have htwo : 2 ≤ N := by nlinarith
  omega

end PEqualNP.Outside.L_meta_7021

theorem PEqualNP.Outside.L_meta_7021 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (38 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 h1 h2 h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L_meta_7021.main x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7
