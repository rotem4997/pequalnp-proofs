import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18930_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def isNotOp (op : GateOp) : Bool := op.eval [false]

def effInputs (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma op_cases {g : Gate} (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

lemma isNotOp_and : isNotOp GateOp.and = false := rfl
lemma isNotOp_or : isNotOp GateOp.or = false := rfl
lemma isNotOp_not : isNotOp GateOp.not = true := rfl

lemma effInputs_eval_eq (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effInputs g).map f) := by
  cases g with
  | mk op ins =>
    dsimp only at hop hlen
    rcases hop with rfl | rfl | rfl
    · have ht : effInputs ⟨GateOp.and, ins⟩ = ins := by
        unfold effInputs; exact List.take_of_length_le hlen
      rw [ht]
    · have ht : effInputs ⟨GateOp.or, ins⟩ = ins := by
        unfold effInputs; exact List.take_of_length_le hlen
      rw [ht]
    · unfold effInputs
      change GateOp.not.eval (ins.map f) = GateOp.not.eval ((ins.take 1).map f)
      cases ins with
      | nil => rfl
      | cons a tl => rfl

lemma effInputs_len_add_not (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    (effInputs g).length + (if isNotOp g.op = true then 1 else 0) ≤ 2 := by
  cases g with
  | mk op ins =>
    dsimp only at hop hlen
    rcases hop with rfl | rfl | rfl
    · change (ins.take 2).length + 0 ≤ 2
      simp only [List.length_take]; omega
    · change (ins.take 2).length + 0 ≤ 2
      simp only [List.length_take]; omega
    · change (ins.take 1).length + 1 ≤ 2
      simp only [List.length_take]; omega

lemma foldl_len : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl stepWire w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) i hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
    gs[j]? = some g →
    (gs.foldl stepWire w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  intro gs
  induction gs with
  | nil => intro w j g h; simp at h
  | cons hd tl ih =>
    intro w j g hj
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero]
      have hlt : w.length < (stepWire w hd).length := by simp [stepWire]
      rw [foldl_getD_lt tl (stepWire w hd) w.length hlt]
      have hstep : (stepWire w hd).getD w.length false =
          hd.op.eval (hd.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · simp only [hi, ↓reduceIte]
        rw [foldl_getD_lt tl (stepWire w hd) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [hi, ↓reduceIte]
        exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)
    | succ k =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (stepWire w hd).length = w.length + 1 := by simp [stepWire]
      have hidx : w.length + (k + 1) = (stepWire w hd).length + k := by omega
      rw [hidx, ih (stepWire w hd) k g hj]

lemma wire_lt_n (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  change (C.gates.foldl stepWire (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [foldl_getD_lt C.gates (List.ofFn x) i (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]

lemma wire_at_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := foldl_getD_gate C.gates (List.ofFn x) j g hj
  rw [hlen] at h
  exact h

def remapAfter (cut repl : ℕ) (w : ℕ) : ℕ :=
  if w < cut then w else if w = cut then repl else w - 1

def remapBefore (cut big : ℕ) (w : ℕ) : ℕ :=
  if w < cut then w else if w = cut then big else w - 1

def mapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

def eraseGateAt (n : ℕ) (C : Circuit) (j repl : ℕ) : Circuit :=
  let cut := n + j
  let big := n + C.gates.length
  let pre := (C.gates.take j).map (mapGate (remapBefore cut big))
  let post := (C.gates.drop (j + 1)).map (mapGate (remapAfter cut repl))
  ⟨pre ++ post, remapAfter cut repl C.output⟩

lemma eraseGateAt_size (n : ℕ) (C : Circuit) (j repl : ℕ) (hj : j < C.gates.length) :
    (eraseGateAt n C j repl).gates.length = C.gates.length - 1 := by
  change ((C.gates.take j).map _ ++ (C.gates.drop (j + 1)).map _).length = C.gates.length - 1
  rw [List.length_append, List.length_map, List.length_map, List.length_take, List.length_drop]
  omega

lemma eraseGateAt_fanInTwo (n : ℕ) (C : Circuit) (j repl : ℕ) (hfan : FanInTwo C) :
    FanInTwo (eraseGateAt n C j repl) := by
  intro g hg
  change g ∈ (C.gates.take j).map (mapGate (remapBefore (n + j) (n + C.gates.length))) ++
      (C.gates.drop (j + 1)).map (mapGate (remapAfter (n + j) repl)) at hg
  rcases List.mem_append.mp hg with h1 | h2
  · rcases List.mem_map.mp h1 with ⟨g0, hg0, rfl⟩
    have h0 := hfan g0 (List.mem_of_mem_take hg0)
    exact ⟨h0.1, by simp [mapGate, h0.2]⟩
  · rcases List.mem_map.mp h2 with ⟨g0, hg0, rfl⟩
    have h0 := hfan g0 (List.mem_of_mem_drop hg0)
    exact ⟨h0.1, by simp [mapGate, h0.2]⟩

lemma eraseGateAt_getElem? (n : ℕ) (C : Circuit) (j repl k : ℕ) (hj : j < C.gates.length) :
    (eraseGateAt n C j repl).gates[k]? =
      if k < j then (C.gates[k]?).map (mapGate (remapBefore (n + j) (n + C.gates.length)))
      else (C.gates[k + 1]?).map (mapGate (remapAfter (n + j) repl)) := by
  unfold eraseGateAt
  dsimp only
  have hprelen : ((C.gates.take j).map (mapGate (remapBefore (n + j) (n + C.gates.length)))).length = j := by
    rw [List.length_map, List.length_take_of_le (Nat.le_of_lt hj)]
  by_cases hk : k < j
  · simp only [hk, ↓reduceIte]
    rw [List.getElem?_append_left (by omega), List.getElem?_map, List.getElem?_take_of_lt hk]
  · simp only [hk, ↓reduceIte]
    rw [List.getElem?_append_right (by omega), hprelen, List.getElem?_map, List.getElem?_drop]
    have hidx : j + 1 + (k - j) = k + 1 := by omega
    rw [hidx]

lemma eraseGateAt_wires_eq (n : ℕ) (C : Circuit) (j repl : ℕ) (hfan : FanInTwo C)
    (hj : j < C.gates.length)
    (hrepl_bound : repl < n + j ∨ n + C.gates.length ≤ repl)
    (x : Fin n → Bool)
    (heq_or_dead :
      ((C.wires (List.ofFn x)).getD (n + j) false = (C.wires (List.ofFn x)).getD repl false) ∨
      (C.output ≠ n + j ∧ ∀ k, j < k → ∀ g, C.gates[k]? = some g → n + j ∉ effInputs g)) :
    let D := eraseGateAt n C j repl
    ∀ w < n + C.gates.length, w ≠ n + j →
      (D.wires (List.ofFn x)).getD (remapAfter (n + j) repl w) false =
        (C.wires (List.ofFn x)).getD w false := by
  intro D
  have hDlen : D.gates.length = C.gates.length - 1 := eraseGateAt_size n C j repl hj
  have hDwires_len : (D.wires (List.ofFn x)).length = n + (C.gates.length - 1) := by
    change (D.gates.foldl stepWire (List.ofFn x)).length = _
    rw [foldl_len, List.length_ofFn, hDlen]
  have hCwires_len : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    change (C.gates.foldl stepWire (List.ofFn x)).length = _
    rw [foldl_len, List.length_ofFn]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwne
    by_cases hlt_n : w < n
    · have hmap : remapAfter (n + j) repl w = w := by
        unfold remapAfter; simp only [show w < n + j by omega, ↓reduceIte]
      rw [hmap, wire_lt_n n D x w hlt_n, wire_lt_n n C x w hlt_n]
    · let k : ℕ := w - n
      have hk_lt : k < C.gates.length := by omega
      have hw_eq : w = n + k := by omega
      let g : Gate := C.gates[k]
      have hgk : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
      have hgk_fan := hfan g (List.mem_of_getElem? hgk)
      have hgk_op := op_cases hgk_fan.1
      by_cases hkj : k < j
      · have hmap : remapAfter (n + j) repl w = n + k := by
          unfold remapAfter; simp only [show w < n + j by omega, ↓reduceIte]; exact hw_eq
        rw [hmap, hw_eq]
        have hDk : D.gates[k]? = some (mapGate (remapBefore (n + j) (n + C.gates.length)) g) := by
          rw [eraseGateAt_getElem? n C j repl k hj]
          simp only [hkj, ↓reduceIte, hgk, Option.map_some]
        rw [wire_at_gate n D x k _ hDk, wire_at_gate n C x k g hgk]
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        dsimp only [Function.comp_apply]
        by_cases hik : i < n + k
        · have hrb : remapBefore (n + j) (n + C.gates.length) i = i := by
            unfold remapBefore; simp only [show i < n + j by omega, ↓reduceIte]
          have hra : remapAfter (n + j) repl i = i := by
            unfold remapAfter; simp only [show i < n + j by omega, ↓reduceIte]
          rw [hrb]
          simp only [hik, ↓reduceIte]
          have hih := ih i (by omega) (by omega) (by omega)
          rw [hra] at hih
          exact hih
        · have hrb_ge : n + k ≤ remapBefore (n + j) (n + C.gates.length) i := by
            unfold remapBefore; split_ifs <;> omega
          simp only [show ¬ remapBefore (n + j) (n + C.gates.length) i < n + k by omega, hik, ↓reduceIte]
      · have hkj_gt : j < k := by omega
        let k' : ℕ := k - 1
        have hk_eq : k = k' + 1 := by omega
        have hmap : remapAfter (n + j) repl w = n + k' := by
          unfold remapAfter
          simp only [show ¬ w < n + j by omega, show ¬ w = n + j by omega, ↓reduceIte]
          omega
        rw [hmap, hw_eq]
        have hDk' : D.gates[k']? = some (mapGate (remapAfter (n + j) repl) g) := by
          rw [eraseGateAt_getElem? n C j repl k' hj]
          simp only [show ¬ k' < j by omega, ↓reduceIte, ← hk_eq, hgk, Option.map_some]
        rw [wire_at_gate n D x k' _ hDk', wire_at_gate n C x k g hgk]
        have hD_eff := effInputs_eval_eq (mapGate (remapAfter (n + j) repl) g) hgk_op
          (by simp [mapGate, hgk_fan.2])
          (fun i => if i < n + k' then (D.wires (List.ofFn x)).getD i false else false)
        have hC_eff := effInputs_eval_eq g hgk_op hgk_fan.2
          (fun i => if i < n + k then (C.wires (List.ofFn x)).getD i false else false)
        rw [hD_eff, hC_eff]
        have heff_map : effInputs (mapGate (remapAfter (n + j) repl) g) =
            (effInputs g).map (remapAfter (n + j) repl) := by
          unfold effInputs mapGate
          exact List.map_take.symm
        rw [heff_map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        dsimp only [Function.comp_apply]
        by_cases hij_eq : i = n + j
        · subst hij_eq
          rcases heq_or_dead with heq_val | ⟨_, hdead⟩
          · simp only [show n + j < n + k by omega, ↓reduceIte]
            have hrm : remapAfter (n + j) repl (n + j) = repl := by
              unfold remapAfter; simp only [show ¬ n + j < n + j by omega, ↓reduceIte]
            rw [hrm, heq_val]
            rcases hrepl_bound with hrl | hrg
            · simp only [show repl < n + k' by omega, ↓reduceIte]
              have hrmr : remapAfter (n + j) repl repl = repl := by
                unfold remapAfter; simp only [hrl, ↓reduceIte]
              have hih := ih repl (by omega) (by omega) (by omega)
              rw [hrmr] at hih
              exact hih
            · simp only [show ¬ repl < n + k' by omega, ↓reduceIte]
              exact (List.getD_eq_default _ _ (by omega)).symm
          · exact (hdead k hkj_gt g hgk hi).elim
        · by_cases hik : i < n + k
          · have hrm_lt : remapAfter (n + j) repl i < n + k' := by
              unfold remapAfter; split_ifs <;> omega
            simp only [hrm_lt, hik, ↓reduceIte]
            exact ih i (by omega) (by omega) hij_eq
          · have hrm_ge : n + k' ≤ remapAfter (n + j) repl i := by
              unfold remapAfter; split_ifs <;> omega
            simp only [show ¬ remapAfter (n + j) repl i < n + k' by omega, hik, ↓reduceIte]

lemma no_erasable_gate (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit n C)
    (j repl : ℕ) (hj : j < C.gates.length)
    (hrepl_bound : repl < n + j ∨ n + C.gates.length ≤ repl)
    (hcond :
      (∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = (C.wires (List.ofFn x)).getD repl false) ∨
      (C.output ≠ n + j ∧ ∀ k, j < k → ∀ g, C.gates[k]? = some g → n + j ∉ effInputs g)) :
    False := by
  let D := eraseGateAt n C j repl
  have hDfan : FanInTwo D := eraseGateAt_fanInTwo n C j repl hmin.1
  have hDlen : D.gates.length = C.gates.length - 1 := eraseGateAt_size n C j repl hj
  have hDeq : circuitFun n D = circuitFun n C := by
    funext x
    change (D.wires (List.ofFn x)).getD D.output false = (C.wires (List.ofFn x)).getD C.output false
    have hDout : D.output = remapAfter (n + j) repl C.output := rfl
    rw [hDout]
    have hCw_len : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      change (C.gates.foldl stepWire (List.ofFn x)).length = _
      rw [foldl_len, List.length_ofFn]
    have hDw_len : (D.wires (List.ofFn x)).length = n + (C.gates.length - 1) := by
      change (D.gates.foldl stepWire (List.ofFn x)).length = _
      rw [foldl_len, List.length_ofFn, hDlen]
    have hxcond :
        ((C.wires (List.ofFn x)).getD (n + j) false = (C.wires (List.ofFn x)).getD repl false) ∨
        (C.output ≠ n + j ∧ ∀ k, j < k → ∀ g, C.gates[k]? = some g → n + j ∉ effInputs g) := by
      rcases hcond with h1 | h2
      · exact Or.inl (h1 x)
      · exact Or.inr h2
    by_cases hout_eq : C.output = n + j
    · rcases hxcond with heq_val | ⟨hne, _⟩
      · rw [hout_eq]
        have hrm : remapAfter (n + j) repl (n + j) = repl := by
          unfold remapAfter; simp only [show ¬ n + j < n + j by omega, ↓reduceIte]
        rw [hrm, heq_val]
        rcases hrepl_bound with hrl | hrg
        · have hrmr : remapAfter (n + j) repl repl = repl := by
            unfold remapAfter; simp only [hrl, ↓reduceIte]
          have hweq := eraseGateAt_wires_eq n C j repl hmin.1 hj (Or.inl hrl) x (Or.inl heq_val)
            repl (by omega) (by omega)
          rw [hrmr] at hweq
          exact hweq
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · exact (hne hout_eq).elim
    · by_cases hout_lt : C.output < n + C.gates.length
      · exact eraseGateAt_wires_eq n C j repl hmin.1 hj hrepl_bound x hxcond C.output hout_lt hout_eq
      · have hrm_ge : n + (C.gates.length - 1) ≤ remapAfter (n + j) repl C.output := by
          unfold remapAfter; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hle : C.size ≤ D.size := hmin.2 D hDfan hDeq
  have hCsz : C.size = C.gates.length := rfl
  have hDsz : D.size = D.gates.length := rfl
  omega

lemma graphFun_empty_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
    decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
  have h0 : decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) = false := by
    rw [decide_eq_false_iff_not]
    rintro ⟨a, ha, _⟩
    exact Finset.notMem_empty a ha
  rw [h0, Bool.false_or, decide_eq_true_eq]

lemma wires_agree_if_avoid (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (v : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (hgate_eq : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → v.val ∈ effInputs g →
      (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn y)).getD (n + k) false) :
    ∀ w < n + C.gates.length, w ≠ v.val →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwne
    by_cases hlt : w < n
    · rw [wire_lt_n n C x w hlt, wire_lt_n n C y w hlt]
      exact hxy ⟨w, hlt⟩ (fun h => hwne (congrArg Fin.val h))
    · let k : ℕ := w - n
      have hk : k < C.gates.length := by omega
      have hw_eq : w = n + k := by omega
      rw [hw_eq]
      let g : Gate := C.gates[k]
      have hgk : C.gates[k]? = some g := List.getElem?_eq_getElem hk
      by_cases hmem : v.val ∈ effInputs g
      · exact hgate_eq k g hgk hmem
      · have hgf := hfan g (List.mem_of_getElem? hgk)
        have hgop := op_cases hgf.1
        rw [wire_at_gate n C x k g hgk, wire_at_gate n C y k g hgk]
        rw [effInputs_eval_eq g hgop hgf.2, effInputs_eval_eq g hgop hgf.2]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hik : i < n + k
        · simp only [hik, ↓reduceIte]
          have hine : i ≠ v.val := fun heq => hmem (heq ▸ hi)
          exact ih i (by omega) (by omega) hine
        · simp only [hik, ↓reduceIte]

lemma list_filter_eq_singleton {α : Type} (p : α → Bool) :
    ∀ (l : List α) (idx : ℕ) (a : α),
      l[idx]? = some a → p a = true →
      (∀ j < l.length, j ≠ idx → ∀ b, l[j]? = some b → p b = false) →
      l.filter p = [a] := by
  intro l
  induction l with
  | nil => intro idx a h; simp at h
  | cons hd tl ih =>
    intro idx a hidx hp hall
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
      subst hidx
      rw [List.filter_cons]
      simp only [hp, ↓reduceIte]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro b hb
      rcases List.mem_iff_getElem?.mp hb with ⟨k, hk⟩
      have hlt : k < tl.length := (List.getElem?_eq_some_iff.mp hk).1
      have hfalse := hall (k + 1) (by simp; omega) (by omega) b (by simpa using hk)
      rw [hfalse]
      exact Bool.false_ne_true
    | succ k =>
      simp only [List.getElem?_cons_succ] at hidx
      have hhd : p hd = false := hall 0 (by simp) (by omega) hd (by simp)
      rw [List.filter_cons]
      simp only [hhd, Bool.false_eq_true, ↓reduceIte]
      exact ih k a hidx hp (fun j hj hne b hb =>
        hall (j + 1) (by simp; omega) (by omega) b (by simpa using hb))

lemma sum_count_le_countP_lt (n : ℕ) (S : Finset (Fin n)) :
    ∀ (l : List ℕ), (∑ v ∈ S, l.count v.val) ≤ l.countP (fun w => decide (w < n)) := by
  intro l
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.count_cons, List.countP_cons]
    rw [Finset.sum_add_distrib]
    have hhead : (∑ v ∈ S, if a == v.val then 1 else 0) ≤ if decide (a < n) then 1 else 0 := by
      by_cases ha : a < n
      · simp only [decide_eq_true ha, ↓reduceIte]
        let v0 : Fin n := ⟨a, ha⟩
        have h1 : (∑ v ∈ S, if a == v.val then 1 else 0) =
            (S.filter (fun v : Fin n => v = v0)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : v = v0
          · subst hv; simp [v0]
          · have hne : a ≠ v.val := fun heq => hv (Fin.ext heq.symm)
            simp [hv, hne]
        rw [h1]
        have hsub : S.filter (fun v : Fin n => v = v0) ⊆ {v0} := by
          intro v hv; exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hv).2
        exact (Finset.card_le_card hsub).trans (by simp)
      · simp only [decide_eq_false ha, Bool.false_eq_true, ↓reduceIte]
        have hzero : ∀ v ∈ S, (if a == v.val then 1 else 0) = 0 := by
          intro v _
          have hne : a ≠ v.val := by have := v.isLt; omega
          simp [hne]
        rw [Finset.sum_eq_zero hzero]
    omega

lemma countP_lt_add_ge (n : ℕ) :
    ∀ (l : List ℕ), l.countP (fun w => decide (w < n)) + l.countP (fun w => decide (n ≤ w)) = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases ha : a < n
    · have hge : ¬ n ≤ a := by omega
      simp [ha, hge]
      omega
    · have hge : n ≤ a := by omega
      simp [ha, hge]
      omega

lemma sum_ge_card_distinct (n : ℕ) (C : Circuit) (K : Finset ℕ)
    (hK : ∀ k ∈ K, ∃ j < C.gates.length, ∃ g, C.gates[j]? = some g ∧ (n + k) ∈ effInputs g) :
    K.card ≤ ∑ j ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).countP (fun w => decide (n ≤ w)) := by
  have h1 : ∀ k ∈ K, 1 ≤ ∑ j ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count (n + k) := by
    intro k hk
    rcases hK k hk with ⟨j, hj, g, hgj, hmem⟩
    have hget : C.gates.getD j ⟨GateOp.or, []⟩ = g := by
      simp [List.getD_eq_getElem?_getD, hgj]
    have hpos : 1 ≤ (effInputs g).count (n + k) := List.count_pos_iff.mpr hmem
    calc 1 ≤ (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count (n + k) := by rw [hget]; exact hpos
      _ ≤ ∑ j' ∈ Finset.range C.gates.length,
            (effInputs (C.gates.getD j' ⟨GateOp.or, []⟩)).count (n + k) :=
          Finset.single_le_sum
            (f := fun j' => (effInputs (C.gates.getD j' ⟨GateOp.or, []⟩)).count (n + k))
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  have hsum1 : K.card ≤ ∑ k ∈ K, ∑ j ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count (n + k) := by
    calc K.card = ∑ _k ∈ K, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum h1
  rw [Finset.sum_comm] at hsum1
  refine hsum1.trans (Finset.sum_le_sum ?_)
  intro j _
  have hlist : ∀ (l : List ℕ), (∑ k ∈ K, l.count (n + k)) ≤ l.countP (fun w => decide (n ≤ w)) := by
    intro l
    induction l with
    | nil => simp
    | cons a tl ih =>
      simp only [List.count_cons, List.countP_cons]
      rw [Finset.sum_add_distrib]
      have hhead : (∑ k ∈ K, if a == n + k then 1 else 0) ≤ if decide (n ≤ a) then 1 else 0 := by
        by_cases ha : n ≤ a
        · simp only [decide_eq_true ha, ↓reduceIte]
          have hcard : (∑ k ∈ K, if a == n + k then 1 else 0) =
              (K.filter (fun k => k = a - n)).card := by
            rw [Finset.card_filter]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : k = a - n
            · subst hk
              have heq : (a == n + (a - n)) = true := by
                rw [beq_iff_eq]; omega
              simp [heq]
            · have hne : (a == n + k) = false := by
                rw [beq_eq_false_iff_ne]; omega
              simp [hk, hne]
          rw [hcard]
          have hsub : K.filter (fun k => k = a - n) ⊆ {a - n} := by
            intro k hk; exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hk).2
          exact (Finset.card_le_card hsub).trans (by simp)
        · simp only [decide_eq_false ha, Bool.false_eq_true, ↓reduceIte]
          have hzero : ∀ k ∈ K, (if a == n + k then 1 else 0) = 0 := by
            intro k _
            have hne : (a == n + k) = false := by
              rw [beq_eq_false_iff_ne]; omega
            simp [hne]
          rw [Finset.sum_eq_zero hzero]
      omega
  exact hlist _

lemma no_triangle_of_egirth5 {n : ℕ} {G : SimpleGraph (Fin n)} (hg : (5 : ℕ∞) ≤ G.egirth)
    {a b c : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  have h1 : a ≠ b := G.ne_of_adj hab
  have h2 : b ≠ c := G.ne_of_adj hbc
  have h3 : c ≠ a := G.ne_of_adj hca
  let p : G.Walk a a := SimpleGraph.Walk.cons hab
    (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, by simp [p], ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [p, h1, h2, h3, h1.symm, h3.symm]
    · simp [p, h2, h3, h1.symm]
  have h5 := (SimpleGraph.le_egirth.mp hg) a p hcyc
  have hlen : p.length = 3 := rfl
  rw [hlen] at h5
  exact absurd h5 (by decide)

lemma no_four_cycle_of_egirth5 {n : ℕ} {G : SimpleGraph (Fin n)} (hg : (5 : ℕ∞) ≤ G.egirth)
    {a b c d : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have h1 : a ≠ b := G.ne_of_adj hab
  have h2 : b ≠ c := G.ne_of_adj hbc
  have h3 : c ≠ d := G.ne_of_adj hcd
  have h4 : d ≠ a := G.ne_of_adj hda
  let p : G.Walk a a := SimpleGraph.Walk.cons hab
    (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, by simp [p], ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [p, h1, h2, h3, h4, hac, hbd, h1.symm, h4.symm, hac.symm]
    · simp [p, h2, h3, h4, hbd, h1.symm, hac.symm]
  have h5 := (SimpleGraph.le_egirth.mp hg) a p hcyc
  have hlen : p.length = 4 := rfl
  rw [hlen] at h5
  exact absurd h5 (by decide)

lemma main_proof :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x6 ∉ x4, (2 : ℕ) ≤ x2.degree x6) → (5 : ℕ∞) ≤ x2.egirth → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ x12 ∉ x4, ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ), x5.gates[x13]? = Option.some x14 ∧ List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x12) x5.gates = [x14] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x1 ≤ x15 ∧ x15 < x1 + x13 ∧ (x14.inputs = [↑x12, x15] ∨ x14.inputs = [x15, ↑x12])) := by
  classical
  intro n G _ I C hdeg hgirth hedge hmin heval hsize
  have hC_eval : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    have hx := congrFun heval x
    change C.eval (List.ofFn x) = graphFun G ∅ x at hx
    rw [hx, graphFun_empty_iff]
  have hout_ge : n ≤ C.output := by
    by_contra hlt
    have hk : C.output < n := Nat.lt_of_not_ge hlt
    let k : Fin n := ⟨C.output, hk⟩
    let x : Fin n → Bool := fun i => decide (i = k)
    have ht : C.eval (List.ofFn x) = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      rw [wire_lt_n n C x C.output hk]
      simp [x, k]
    rcases (hC_eval x).mp ht with ⟨u, v, huv, hu, hv⟩
    simp only [x, decide_eq_true_eq] at hu hv
    rw [hu, hv] at huv
    exact G.loopless.irrefl k huv
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    rcases hedge with ⟨u, v, huv⟩
    let x : Fin n → Bool := fun i => decide (i = u ∨ i = v)
    have ht : C.eval (List.ofFn x) = true :=
      (hC_eval x).mpr ⟨u, v, huv, by simp [x], by simp [x]⟩
    have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      change (C.gates.foldl stepWire (List.ofFn x)).length = _
      rw [foldl_len, List.length_ofFn]
    have hf : C.eval (List.ofFn x) = false := by
      change (C.wires (List.ofFn x)).getD C.output false = false
      exact List.getD_eq_default _ _ (by omega)
    rw [hf] at ht
    cases ht
  have hCpos : 1 ≤ C.gates.length := by omega
  let S : Finset (Fin n) := Finset.univ \ I
  have hScard : S.card = n - I.card := by
    simp only [S, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  let outIdx : ℕ := C.output - n
  have houtIdx_mem : outIdx ∈ Finset.range C.gates.length := by
    rw [Finset.mem_range]; omega
  let K : Finset ℕ := (Finset.range C.gates.length).erase outIdx
  have hKcard : K.card = C.gates.length - 1 := by
    rw [Finset.card_erase_of_mem houtIdx_mem, Finset.card_range]
  have hK_used : ∀ k ∈ K, ∃ j < C.gates.length, ∃ g, C.gates[j]? = some g ∧ (n + k) ∈ effInputs g := by
    intro k hk
    have hk_ne : k ≠ outIdx := (Finset.mem_erase.mp hk).1
    have hk_lt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    by_contra hnone
    push Not at hnone
    apply no_erasable_gate n C hmin k (n + C.gates.length) hk_lt (Or.inr le_rfl)
    right
    refine ⟨by omega, ?_⟩
    intro j _ g hgj
    exact hnone j (List.getElem?_eq_some_iff.mp hgj).1 g hgj
  have hge_bound : C.gates.length - 1 ≤ ∑ j ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).countP (fun w => decide (n ≤ w)) := by
    rw [← hKcard]
    exact sum_ge_card_distinct n C K hK_used
  let cnt : Fin n → ℕ := fun v =>
    ∑ j ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val
  let notCnt : Fin n → ℕ := fun v =>
    ∑ j ∈ Finset.range C.gates.length,
      if isNotOp (C.gates.getD j ⟨GateOp.or, []⟩).op = true ∧
        v.val ∈ effInputs (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 0
  have htotal : (∑ v ∈ S, (cnt v + notCnt v)) +
      (∑ j ∈ Finset.range C.gates.length,
        (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).countP (fun w => decide (n ≤ w))) ≤
      2 * C.gates.length := by
    rw [Finset.sum_add_distrib]
    have hswap1 : ∑ v ∈ S, cnt v = ∑ j ∈ Finset.range C.gates.length,
        ∑ v ∈ S, (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val := Finset.sum_comm
    have hswap2 : ∑ v ∈ S, notCnt v = ∑ j ∈ Finset.range C.gates.length,
        ∑ v ∈ S, if isNotOp (C.gates.getD j ⟨GateOp.or, []⟩).op = true ∧
          v.val ∈ effInputs (C.gates.getD j ⟨GateOp.or, []⟩) then 1 else 0 := Finset.sum_comm
    rw [hswap1, hswap2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ _j ∈ Finset.range C.gates.length, (2 : ℕ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjlt : j < C.gates.length := Finset.mem_range.mp hj
          let g : Gate := C.gates[j]
          have hgj : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
          have hget : C.gates.getD j ⟨GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD, hgj]
          rw [hget]
          have hgf := hmin.1 g (List.mem_of_getElem? hgj)
          have hgop := op_cases hgf.1
          have hlt_le := sum_count_le_countP_lt n S (effInputs g)
          have hpart := countP_lt_add_ge n (effInputs g)
          have hnot_le : (∑ v ∈ S, if isNotOp g.op = true ∧ v.val ∈ effInputs g then 1 else 0) ≤
              if isNotOp g.op = true then 1 else 0 := by
            by_cases hnot : isNotOp g.op = true
            · simp only [hnot, true_and, ↓reduceIte]
              have hlen1 : (effInputs g).length ≤ 1 := by
                unfold effInputs
                have hbg : g.op.eval [false] = true := hnot
                rw [hbg]
                change (g.inputs.take 1).length ≤ 1
                simp only [List.length_take]; omega
              cases heff : effInputs g with
              | nil => simp
              | cons a tl =>
                have htl : tl = [] := by
                  rw [heff, List.length_cons] at hlen1
                  exact List.eq_nil_of_length_eq_zero (by omega)
                subst htl
                have hcard : (∑ v ∈ S, if v.val ∈ ([a] : List ℕ) then 1 else 0) =
                    (S.filter (fun v : Fin n => v.val = a)).card := by
                  rw [Finset.card_filter]
                  apply Finset.sum_congr rfl
                  intro v _; simp
                rw [hcard]
                by_cases ha : a < n
                · have hsub : S.filter (fun v : Fin n => v.val = a) ⊆ {⟨a, ha⟩} := by
                    intro v hv; exact Finset.mem_singleton.mpr (Fin.ext (Finset.mem_filter.mp hv).2)
                  exact (Finset.card_le_card hsub).trans (by simp)
                · have hemp : S.filter (fun v : Fin n => v.val = a) = ∅ := by
                    ext v; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
                    intro _; have := v.isLt; omega
                  rw [hemp]; simp
            · simp [hnot]
          have hlen_bound := effInputs_len_add_not g hgop hgf.2
          omega
      _ = 2 * C.gates.length := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  have hsum_lt : ∑ v ∈ S, (cnt v + notCnt v) < 2 * S.card := by
    have hCsz : C.size = C.gates.length := rfl
    omega
  have hex_v : ∃ v ∈ S, cnt v + notCnt v < 2 := by
    by_contra hall
    push Not at hall
    have hge2 : 2 * S.card ≤ ∑ v ∈ S, (cnt v + notCnt v) := by
      calc 2 * S.card = ∑ _v ∈ S, (2 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum hall
    omega
  rcases hex_v with ⟨v, hvS, hv_lt2⟩
  have hvI : v ∉ I := (Finset.mem_sdiff.mp hvS).2
  have hv_deg : 2 ≤ G.degree v := hdeg v hvI
  have hv_nbrs : ∃ w1 w2 : Fin n, w1 ≠ w2 ∧ G.Adj v w1 ∧ G.Adj v w2 := by
    have hcard : 1 < (G.neighborFinset v).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
    rcases Finset.one_lt_card.mp hcard with ⟨w1, hw1, w2, hw2, hne⟩
    exact ⟨w1, w2, hne, (SimpleGraph.mem_neighborFinset G v w1).mp hw1,
      (SimpleGraph.mem_neighborFinset G v w2).mp hw2⟩
  have hv_cnt_pos : 1 ≤ cnt v := by
    by_contra h0
    have hcz : cnt v = 0 := by omega
    rcases hv_nbrs with ⟨w1, _, _, hvw1, _⟩
    let x : Fin n → Bool := fun i => decide (i = w1)
    let y : Fin n → Bool := fun i => decide (i = v ∨ i = w1)
    have hxy : ∀ i : Fin n, i ≠ v → x i = y i := by
      intro i hi; simp [x, y, hi]
    have hno_read : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → v.val ∉ effInputs g := by
      intro k g hgk hmem
      have hlt : k < C.gates.length := (List.getElem?_eq_some_iff.mp hgk).1
      have hget : C.gates.getD k ⟨GateOp.or, []⟩ = g := by simp [List.getD_eq_getElem?_getD, hgk]
      have hpos : 1 ≤ (effInputs g).count v.val := List.count_pos_iff.mpr hmem
      have hle : (effInputs g).count v.val ≤ cnt v := by
        rw [← hget]
        exact Finset.single_le_sum
          (f := fun j' => (effInputs (C.gates.getD j' ⟨GateOp.or, []⟩)).count v.val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hlt)
      omega
    have heq_out : C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
      wires_agree_if_avoid n C hmin.1 v x y hxy
        (fun k g hgk hmem => (hno_read k g hgk hmem).elim)
        C.output hout_lt (by have := v.isLt; omega)
    have hyt : C.eval (List.ofFn y) = true := (hC_eval y).mpr ⟨v, w1, hvw1, by simp [y], by simp [y]⟩
    rw [← heq_out] at hyt
    rcases (hC_eval x).mp hyt with ⟨a, b, hab, ha, hb⟩
    simp only [x, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact G.loopless.irrefl w1 hab
  have hcnt1 : cnt v = 1 := by omega
  have hnot0 : notCnt v = 0 := by omega
  have hex_idx : ∃ idx ∈ Finset.range C.gates.length,
      (effInputs (C.gates.getD idx ⟨GateOp.or, []⟩)).count v.val = 1 := by
    by_contra hnone
    push Not at hnone
    have hall0 : ∀ j ∈ Finset.range C.gates.length,
        (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val = 0 := by
      intro j hj
      have hle : (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val ≤ cnt v :=
        Finset.single_le_sum
          (f := fun j' => (effInputs (C.gates.getD j' ⟨GateOp.or, []⟩)).count v.val)
          (fun _ _ => Nat.zero_le _) hj
      have hne1 := hnone j hj
      omega
    have hcz : cnt v = 0 := Finset.sum_eq_zero hall0
    omega
  rcases hex_idx with ⟨idx, hidx_mem, hidx_cnt1⟩
  have hidx_lt : idx < C.gates.length := Finset.mem_range.mp hidx_mem
  let g : Gate := C.gates[idx]
  have hidx_eq : C.gates[idx]? = some g := List.getElem?_eq_getElem hidx_lt
  have hget_idx : C.gates.getD idx ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD, hidx_eq]
  rw [hget_idx] at hidx_cnt1
  have hv_mem_g : v.val ∈ effInputs g := List.count_pos_iff.mp (by omega)
  have hother0 : ∀ j < C.gates.length, j ≠ idx →
      (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val = 0 := by
    intro j hj hne
    have hpair : (effInputs (C.gates.getD idx ⟨GateOp.or, []⟩)).count v.val +
        (effInputs (C.gates.getD j ⟨GateOp.or, []⟩)).count v.val ≤ cnt v := by
      have hsub : ({idx, j} : Finset ℕ) ⊆ Finset.range C.gates.length := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
      have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        (f := fun k => (effInputs (C.gates.getD k ⟨GateOp.or, []⟩)).count v.val)
      rw [Finset.sum_pair hne.symm] at hsum_le
      exact hsum_le
    rw [hget_idx, hidx_cnt1] at hpair
    omega
  have hfilter : List.filter (fun h : Gate => (effInputs h).contains v.val) C.gates = [g] := by
    apply list_filter_eq_singleton _ C.gates idx g hidx_eq
    · exact List.contains_iff_mem.mpr hv_mem_g
    · intro j hj hne b hb
      have hget_j : C.gates.getD j ⟨GateOp.or, []⟩ = b := by simp [List.getD_eq_getElem?_getD, hb]
      have hc0 := hother0 j hj hne
      rw [hget_j] at hc0
      have hnm : v.val ∉ effInputs b := fun hm => by
        have := List.count_pos_iff.mpr hm; omega
      cases hc : (effInputs b).contains v.val
      · rfl
      · exact (hnm (List.contains_iff_mem.mp hc)).elim
  have hnot_ne : g.op ≠ GateOp.not := by
    intro hnot
    have hle : (if isNotOp (C.gates.getD idx ⟨GateOp.or, []⟩).op = true ∧
        v.val ∈ effInputs (C.gates.getD idx ⟨GateOp.or, []⟩) then 1 else 0) ≤ notCnt v :=
      Finset.single_le_sum
        (f := fun j' => if isNotOp (C.gates.getD j' ⟨GateOp.or, []⟩).op = true ∧
          v.val ∈ effInputs (C.gates.getD j' ⟨GateOp.or, []⟩) then 1 else 0)
        (fun _ _ => Nat.zero_le _) hidx_mem
    rw [hget_idx] at hle
    have hcond_t : isNotOp g.op = true ∧ v.val ∈ effInputs g := ⟨by rw [hnot]; rfl, hv_mem_g⟩
    simp [hcond_t, hnot0] at hle
  have hgf := hmin.1 g (List.mem_of_getElem? hidx_eq)
  have hgop_ao : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases op_cases hgf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot_ne h).elim
  have heff_g_eq : effInputs g = g.inputs := by
    rcases hgop_ao with h | h
    · unfold effInputs; rw [h]; exact List.take_of_length_le hgf.2
    · unfold effInputs; rw [h]; exact List.take_of_length_le hgf.2
  rw [heff_g_eq] at hidx_cnt1 hv_mem_g
  have hinputs_pair : ∃ q : ℕ, q ≠ v.val ∧ (g.inputs = [v.val, q] ∨ g.inputs = [q, v.val]) := by
    cases hin : g.inputs with
    | nil => rw [hin] at hv_mem_g; simp at hv_mem_g
    | cons a tl =>
      cases tl with
      | nil =>
        exfalso
        rw [hin, List.mem_singleton] at hv_mem_g
        subst hv_mem_g
        apply no_erasable_gate n C hmin idx v.val hidx_lt (Or.inl (by have := v.isLt; omega))
        left
        intro x
        rw [wire_at_gate n C x idx g hidx_eq, hin]
        have hvlt : v.val < n + idx := by have := v.isLt; omega
        rcases hgop_ao with h | h <;> simp [h, GateOp.eval, hvlt]
      | cons b tl2 =>
        have htl2 : tl2 = [] := by
          rw [hin, List.length_cons, List.length_cons] at hgf
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst htl2
        rw [hin] at hidx_cnt1 hv_mem_g
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_mem_g
        rcases hv_mem_g with hv_a | hv_b
        · have hne : b ≠ v.val := by
            intro heq; rw [← hv_a, heq] at hidx_cnt1; simp at hidx_cnt1
          exact ⟨b, hne, Or.inl (by rw [hv_a])⟩
        · have hne : a ≠ v.val := by
            intro heq; rw [← hv_b, heq] at hidx_cnt1; simp at hidx_cnt1
          exact ⟨a, hne, Or.inr (by rw [hv_b])⟩
  rcases hinputs_pair with ⟨q, hq_ne, hq_in⟩
  have hq_lt : q < n + idx := by
    by_contra hge
    rcases hgop_ao with hand | hor
    · apply no_erasable_gate n C hmin idx (n + C.gates.length) hidx_lt (Or.inr le_rfl)
      left
      intro x
      have hCw_len : (C.wires (List.ofFn x)).length = n + C.gates.length := by
        change (C.gates.foldl stepWire (List.ofFn x)).length = _
        rw [foldl_len, List.length_ofFn]
      rw [List.getD_eq_default _ _ (le_of_eq hCw_len), wire_at_gate n C x idx g hidx_eq, hand]
      rcases hq_in with h | h
      · rw [h]; simp only [List.map_cons, List.map_nil, hge, ↓reduceIte, GateOp.eval, List.all_cons,
          List.all_nil, id_eq, Bool.and_false, Bool.and_true]
      · rw [h]; simp only [List.map_cons, List.map_nil, hge, ↓reduceIte, GateOp.eval, List.all_cons,
          List.all_nil, id_eq, Bool.false_and]
    · apply no_erasable_gate n C hmin idx v.val hidx_lt (Or.inl (by have := v.isLt; omega))
      left
      intro x
      have hvlt : v.val < n + idx := by have := v.isLt; omega
      rw [wire_at_gate n C x idx g hidx_eq, hor]
      rcases hq_in with h | h
      · rw [h]; simp only [List.map_cons, List.map_nil, hvlt, hge, ↓reduceIte, GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
      · rw [h]; simp only [List.map_cons, List.map_nil, hvlt, hge, ↓reduceIte, GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
  have hq_ge_n : n ≤ q := by
    by_contra hlt_n
    have hq_n : q < n := Nat.lt_of_not_ge hlt_n
    let u : Fin n := ⟨q, hq_n⟩
    have huv_ne : u ≠ v := fun h => hq_ne (congrArg Fin.val h)
    rcases hv_nbrs with ⟨w1, w2, hw12, hvw1, hvw2⟩
    have h_other_no_read : ∀ (k : ℕ) (h : Gate), C.gates[k]? = some h → v.val ∈ effInputs h → k = idx := by
      intro k h hkh hmem
      by_contra hne
      have hklt : k < C.gates.length := (List.getElem?_eq_some_iff.mp hkh).1
      have hget_k : C.gates.getD k ⟨GateOp.or, []⟩ = h := by simp [List.getD_eq_getElem?_getD, hkh]
      have hc0 := hother0 k hklt hne
      rw [hget_k] at hc0
      have hpos := List.count_pos_iff.mpr hmem
      omega
    rcases hgop_ao with hand | hor
    · have hex_w : ∃ w : Fin n, G.Adj v w ∧ w ≠ u := by
        by_cases h1 : w1 = u
        · exact ⟨w2, hvw2, fun h2 => hw12 (h1.trans h2.symm)⟩
        · exact ⟨w1, hvw1, h1⟩
      rcases hex_w with ⟨w, hvw, hwu⟩
      let x : Fin n → Bool := fun i => decide (i = w)
      let y : Fin n → Bool := fun i => decide (i = v ∨ i = w)
      have hxy : ∀ i : Fin n, i ≠ v → x i = y i := fun i hi => by simp [x, y, hi]
      have hxu : x u = false := by simp [x, hwu.symm]
      have hyu : y u = false := by simp [y, huv_ne, hwu.symm]
      have hidx_same : (C.wires (List.ofFn x)).getD (n + idx) false =
          (C.wires (List.ofFn y)).getD (n + idx) false := by
        rw [wire_at_gate n C x idx g hidx_eq, wire_at_gate n C y idx g hidx_eq, hand]
        have hwxq : (C.wires (List.ofFn x)).getD q false = false := by
          rw [wire_lt_n n C x q hq_n]; exact hxu
        have hwyq : (C.wires (List.ofFn y)).getD q false = false := by
          rw [wire_lt_n n C y q hq_n]; exact hyu
        rcases hq_in with h | h
        · rw [h]
          simp only [List.map_cons, List.map_nil, hq_lt, ↓reduceIte, hwxq, hwyq, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.and_false, Bool.and_true]
        · rw [h]
          simp only [List.map_cons, List.map_nil, hq_lt, ↓reduceIte, hwxq, hwyq, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.false_and]
      have heq_out : C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
        wires_agree_if_avoid n C hmin.1 v x y hxy
          (fun k h hkh hmem => by rw [h_other_no_read k h hkh hmem]; exact hidx_same)
          C.output hout_lt (by have := v.isLt; omega)
      have hyt : C.eval (List.ofFn y) = true := (hC_eval y).mpr ⟨v, w, hvw, by simp [y], by simp [y]⟩
      rw [← heq_out] at hyt
      rcases (hC_eval x).mp hyt with ⟨a, b, hab, ha, hb⟩
      simp only [x, decide_eq_true_eq] at ha hb
      rw [ha, hb] at hab
      exact G.loopless.irrefl w hab
    · have hex_w : ∃ w : Fin n, G.Adj v w ∧ w ≠ u ∧ ¬ G.Adj u w := by
        by_cases h1 : w1 = u
        · refine ⟨w2, hvw2, fun h2 => hw12 (h1.trans h2.symm), fun hadj => ?_⟩
          rw [← h1] at hadj
          exact no_triangle_of_egirth5 hgirth hvw1 hadj hvw2.symm
        · by_cases h2 : w2 = u
          · refine ⟨w1, hvw1, h1, fun hadj => ?_⟩
            rw [← h2] at hadj
            exact no_triangle_of_egirth5 hgirth hvw2 hadj hvw1.symm
          · by_cases ha1 : G.Adj u w1
            · refine ⟨w2, hvw2, h2, fun ha2 => ?_⟩
              exact no_four_cycle_of_egirth5 hgirth hvw1 ha1.symm ha2 hvw2.symm huv_ne.symm hw12
            · exact ⟨w1, hvw1, h1, ha1⟩
      rcases hex_w with ⟨w, hvw, _, hnuw⟩
      let x : Fin n → Bool := fun i => decide (i = u ∨ i = w)
      let y : Fin n → Bool := fun i => decide (i = v ∨ i = u ∨ i = w)
      have hxy : ∀ i : Fin n, i ≠ v → x i = y i := fun i hi => by simp [x, y, hi]
      have hxu : x u = true := by simp [x]
      have hyu : y u = true := by simp [y]
      have hidx_same : (C.wires (List.ofFn x)).getD (n + idx) false =
          (C.wires (List.ofFn y)).getD (n + idx) false := by
        rw [wire_at_gate n C x idx g hidx_eq, wire_at_gate n C y idx g hidx_eq, hor]
        have hwxq : (C.wires (List.ofFn x)).getD q false = true := by
          rw [wire_lt_n n C x q hq_n]; exact hxu
        have hwyq : (C.wires (List.ofFn y)).getD q false = true := by
          rw [wire_lt_n n C y q hq_n]; exact hyu
        rcases hq_in with h | h
        · rw [h]
          simp only [List.map_cons, List.map_nil, hq_lt, ↓reduceIte, hwxq, hwyq, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.true_or]
        · rw [h]
          simp only [List.map_cons, List.map_nil, hq_lt, ↓reduceIte, hwxq, hwyq, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.true_or]
      have heq_out : C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
        wires_agree_if_avoid n C hmin.1 v x y hxy
          (fun k h hkh hmem => by rw [h_other_no_read k h hkh hmem]; exact hidx_same)
          C.output hout_lt (by have := v.isLt; omega)
      have hyt : C.eval (List.ofFn y) = true := (hC_eval y).mpr ⟨v, w, hvw, by simp [y], by simp [y]⟩
      rw [← heq_out] at hyt
      rcases (hC_eval x).mp hyt with ⟨a, b, hab, ha, hb⟩
      simp only [x, decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.loopless.irrefl _ hab
      · exact hnuw hab
      · exact hnuw hab.symm
      · exact G.loopless.irrefl _ hab
  exact ⟨v, hvI, idx, g, q, hidx_eq, hfilter, hgop_ao, hq_ge_n, hq_lt, hq_in⟩

end PEqualNP.Outside.L_meta_18930_aux

theorem PEqualNP.Outside.L_meta_18930 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x6 ∉ x4, (2 : ℕ) ≤ x2.degree x6) → (5 : ℕ∞) ≤ x2.egirth → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ x12 ∉ x4, ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ), x5.gates[x13]? = Option.some x14 ∧ List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x12) x5.gates = [x14] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x1 ≤ x15 ∧ x15 < x1 + x13 ∧ (x14.inputs = [↑x12, x15] ∨ x14.inputs = [x15, ↑x12])) :=
  PEqualNP.Outside.L_meta_18930_aux.main_proof
