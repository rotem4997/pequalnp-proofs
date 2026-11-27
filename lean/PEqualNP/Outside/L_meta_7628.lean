import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7628

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma W_nil (w : List Bool) : W [] w = w := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) :
    W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_append_lt (l₁ l₂ : List Bool) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma W_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_append_lt w _ i hi

lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false :=
  getD_ge _ _ (by rw [W_length]; exact h)

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  have htlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hprelen : (W (gs.take j) w).length = w.length + j := by
    rw [W_length, htlen]
  conv_lhs => rw [hsplit, W_append, W_cons]
  rw [W_prefix (gs.drop (j + 1)) (step (W (gs.take j) w) gs[j]) (w.length + j)
    (by rw [step_len, hprelen]; omega)]
  have hlast : (step (W (gs.take j) w) gs[j]).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (W (gs.take j) w).getD i false) := by
    rw [← hprelen]
    exact getD_append_len _ _
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + j
  · simp only [hi, ↓reduceIte]
    have hpref : (W gs w).getD i false = (W (gs.take j) w).getD i false := by
      conv_lhs => rw [hsplit, W_append]
      exact W_prefix (gs[j] :: gs.drop (j + 1)) (W (gs.take j) w) i (by rw [hprelen]; exact hi)
    exact hpref.symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge (W (gs.take j) w) i (by rw [hprelen]; omega)

lemma val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false :=
  W_prefix C.gates x i hi

lemma val_ge (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    val C x i = false :=
  W_ge C.gates x i hi

lemma val_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (x.length + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then val C x i else false) :=
  W_gate C.gates x j hj

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false =
      if i < n then decide (i = u.val)
      else if i < n + m then decide (i - n = v.val)
      else false := by
  unfold oneEach
  by_cases h1 : i < n
  · simp only [h1, ↓reduceIte]
    rw [getD_append_lt _ _ i (by simp; exact h1)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact h1)]
    simp [Fin.ext_iff]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i < n + m
    · simp only [h2, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp [Fin.ext_iff]
    · simp only [h2, ↓reduceIte]
      exact getD_ge _ _ (by simp; omega)

def CleanCircuit (N : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧
  (∀ j : ℕ, (hj : j < C.gates.length) →
    ∃ a b : ℕ, C.gates[j].inputs = [a, b] ∧ a < N + j ∧ b < N + j ∧ a ≠ b) ∧
  (∀ j : ℕ, j < C.gates.length →
    C.output = N + j ∨ ∃ k : ℕ, ∃ hk : k < C.gates.length, j < k ∧ N + j ∈ C.gates[k].inputs)

def shiftDown (w : ℕ) (i : ℕ) : ℕ :=
  if w < i then i - 1 else i

def remapAlias (w a : ℕ) (i : ℕ) : ℕ :=
  if i = w then a else if w < i then i - 1 else i

def elimAlias (C : Circuit) (N j a : ℕ) : Circuit :=
  let w := N + j
  { gates := C.gates.take j ++
      (C.gates.drop (j + 1)).map (fun g => { g with inputs := g.inputs.map (remapAlias w a) })
    output := remapAlias w a C.output }

lemma elimAlias_size (C : Circuit) (N j a : ℕ) (hj : j < C.gates.length) :
    (elimAlias C N j a).size = C.size - 1 := by
  simp only [Circuit.size, elimAlias, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

lemma elimAlias_mono (C : Circuit) (N j a : ℕ) (hm : Monotone2 C) :
    Monotone2 (elimAlias C N j a) := by
  intro g hg
  simp only [elimAlias, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g', hg', rfl⟩
  · exact hm g (List.mem_of_mem_take h1)
  · have h := hm g' (List.mem_of_mem_drop hg')
    exact ⟨h.1, by simp [h.2]⟩

lemma elimAlias_val (C : Circuit) (N j a : ℕ) (hj : j < C.gates.length) (ha : a < N + j)
    (x : List Bool) (hx : x.length = N)
    (hval : val C x (N + j) = val C x a ∨
      (C.output ≠ N + j ∧ ∀ k (hk : k < C.gates.length), j < k → N + j ∉ C.gates[k].inputs)) :
    ∀ t < N + (C.gates.length - 1),
      val (elimAlias C N j a) x t = val C x (if t < N + j then t else t + 1) := by
  subst hx
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    have hlen : (elimAlias C x.length j a).gates.length = C.gates.length - 1 :=
      elimAlias_size C x.length j a hj
    by_cases hlt : t < x.length
    · rw [val_input _ x t hlt, val_input _ x (if t < x.length + j then t else t + 1) (by split_ifs <;> omega)]
      have h1 : t < x.length + j := by omega
      simp [h1]
    · set k := t - x.length with hk_def
      have ht_eq : t = x.length + k := by omega
      have hk : k < (elimAlias C x.length j a).gates.length := by omega
      rw [ht_eq, val_gate (elimAlias C x.length j a) x k hk]
      by_cases hkj : k < j
      · have hcond : x.length + k < x.length + j := by omega
        simp only [hcond, ↓reduceIte]
        rw [val_gate C x k (by omega)]
        have hgate : (elimAlias C x.length j a).gates[k] = C.gates[k] := by
          simp only [elimAlias]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [hgate]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, ↓reduceIte]
          have hih := ih i (by omega) (by omega)
          have hi2 : i < x.length + j := by omega
          simpa [hi2] using hih
        · simp only [hi, ↓reduceIte]
      · have hcond : ¬ (x.length + k < x.length + j) := by omega
        simp only [hcond, ↓reduceIte]
        have hk1 : k + 1 < C.gates.length := by omega
        have hidx : x.length + k + 1 = x.length + (k + 1) := by omega
        rw [hidx, val_gate C x (k + 1) hk1]
        have hgate : (elimAlias C x.length j a).gates[k] =
            { (C.gates[k + 1]) with inputs := (C.gates[k + 1]).inputs.map (remapAlias (x.length + j) a) } := by
          simp only [elimAlias]
          have htake : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
          rw [List.getElem_append_right (by rw [htake]; omega)]
          have hidx2 : j + 1 + (k - j) = k + 1 := by omega
          simp only [List.getElem_map, List.getElem_drop, htake, hidx2]
        rw [hgate]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi_mem
        simp only [Function.comp_apply, remapAlias]
        by_cases hi_eq : i = x.length + j
        · subst hi_eq
          have hi_lt : x.length + j < x.length + (k + 1) := by omega
          have ha_lt : a < x.length + k := by omega
          simp only [↓reduceIte, ha_lt, hi_lt]
          have hih := ih a (by omega) (by omega)
          simp only [ha, ↓reduceIte] at hih
          rw [hih]
          rcases hval with h1 | ⟨_, h2⟩
          · exact h1.symm
          · exact False.elim (h2 (k + 1) hk1 (by omega) hi_mem)
        · simp only [hi_eq, ↓reduceIte]
          by_cases hi_gt : x.length + j < i
          · simp only [hi_gt, ↓reduceIte]
            by_cases hi_lt : i < x.length + (k + 1)
            · have hi1_lt : i - 1 < x.length + k := by omega
              simp only [hi1_lt, hi_lt, ↓reduceIte]
              have hih := ih (i - 1) (by omega) (by omega)
              have hnot : ¬ (i - 1 < x.length + j) := by omega
              simp only [hnot, ↓reduceIte] at hih
              have hplus : i - 1 + 1 = i := by omega
              rw [hplus] at hih
              exact hih
            · have hi1_nlt : ¬ (i - 1 < x.length + k) := by omega
              simp only [hi1_nlt, hi_lt, ↓reduceIte]
          · simp only [hi_gt, ↓reduceIte]
            have hi_lt1 : i < x.length + k := by omega
            have hi_lt2 : i < x.length + (k + 1) := by omega
            simp only [hi_lt1, hi_lt2, ↓reduceIte]
            have hih := ih i (by omega) (by omega)
            have hi_ltj : i < x.length + j := by omega
            simp only [hi_ltj, ↓reduceIte] at hih
            exact hih

lemma elimAlias_eval (C : Circuit) (N j a : ℕ) (hj : j < C.gates.length) (ha : a < N + j)
    (x : List Bool) (hx : x.length = N)
    (hval : val C x (N + j) = val C x a ∨
      (C.output ≠ N + j ∧ ∀ k (hk : k < C.gates.length), j < k → N + j ∉ C.gates[k].inputs)) :
    (elimAlias C N j a).eval x = C.eval x := by
  have hout : (elimAlias C N j a).output = remapAlias (N + j) a C.output := rfl
  rw [eval_eq_val, eval_eq_val, hout]
  have hlen : (elimAlias C N j a).gates.length = C.gates.length - 1 := elimAlias_size C N j a hj
  unfold remapAlias
  by_cases ho_eq : C.output = N + j
  · simp only [ho_eq, ↓reduceIte]
    have h1 := elimAlias_val C N j a hj ha x hx hval a (by omega)
    simp only [ha, ↓reduceIte] at h1
    rw [h1]
    rcases hval with h | ⟨h, _⟩
    · exact h.symm
    · exact False.elim (h ho_eq)
  · simp only [ho_eq, ↓reduceIte]
    by_cases ho_gt : N + j < C.output
    · simp only [ho_gt, ↓reduceIte]
      by_cases ho_lt : C.output < N + C.gates.length
      · have h1 := elimAlias_val C N j a hj ha x hx hval (C.output - 1) (by omega)
        have hnot : ¬ (C.output - 1 < N + j) := by omega
        simp only [hnot, ↓reduceIte] at h1
        have hplus : C.output - 1 + 1 = C.output := by omega
        rw [hplus] at h1
        exact h1
      · rw [val_ge (elimAlias C N j a) x _ (by rw [hx, hlen]; omega),
          val_ge C x _ (by rw [hx]; omega)]
    · simp only [ho_gt, ↓reduceIte]
      have ho_ltj : C.output < N + j := by omega
      have h1 := elimAlias_val C N j a hj ha x hx hval C.output (by omega)
      simp only [ho_ltj, ↓reduceIte] at h1
      exact h1

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def elimConstGate (w : ℕ) (b : Bool) (g : Gate) : Gate :=
  if b then
    if isAndOp g.op then
      { op := GateOp.and, inputs := (g.inputs.filter (fun i => decide (i ≠ w))).map (shiftDown w) }
    else if w ∈ g.inputs then
      { op := GateOp.and, inputs := [] }
    else
      { op := g.op, inputs := g.inputs.map (shiftDown w) }
  else
    if !isAndOp g.op then
      { op := GateOp.or, inputs := (g.inputs.filter (fun i => decide (i ≠ w))).map (shiftDown w) }
    else if w ∈ g.inputs then
      { op := GateOp.or, inputs := [] }
    else
      { op := g.op, inputs := g.inputs.map (shiftDown w) }

def elimConst (C : Circuit) (N j : ℕ) (b : Bool) : Circuit :=
  let w := N + j
  { gates := C.gates.take j ++ (C.gates.drop (j + 1)).map (elimConstGate w b)
    output := if C.output = w then N + C.gates.length else shiftDown w C.output }

lemma elimConst_size (C : Circuit) (N j : ℕ) (b : Bool) (hj : j < C.gates.length) :
    (elimConst C N j b).size = C.size - 1 := by
  simp only [Circuit.size, elimConst, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

lemma elimConst_mono (C : Circuit) (N j : ℕ) (b : Bool) (hm : Monotone2 C) :
    Monotone2 (elimConst C N j b) := by
  intro g hg
  simp only [elimConst, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g', hg', rfl⟩
  · exact hm g (List.mem_of_mem_take h1)
  · have h := hm g' (List.mem_of_mem_drop hg')
    unfold elimConstGate
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · refine ⟨by simp, ?_⟩
        rw [List.length_map]
        exact (List.length_filter_le ..).trans h.2
      · exact ⟨by simp, by simp⟩
      · exact ⟨h.1, by simp [h.2]⟩
    · simp only [↓reduceIte]
      split_ifs
      · refine ⟨by simp, ?_⟩
        rw [List.length_map]
        exact (List.length_filter_le ..).trans h.2
      · exact ⟨by simp, by simp⟩
      · exact ⟨h.1, by simp [h.2]⟩

lemma elimConst_val (C : Circuit) (N j : ℕ) (b : Bool) (hm : Monotone2 C)
    (hj : j < C.gates.length) (x : List Bool) (hx : x.length = N)
    (hval : val C x (N + j) = b) :
    ∀ t < N + (C.gates.length - 1),
      val (elimConst C N j b) x t = val C x (if t < N + j then t else t + 1) := by
  subst hx
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    have hlen : (elimConst C x.length j b).gates.length = C.gates.length - 1 :=
      elimConst_size C x.length j b hj
    by_cases hlt : t < x.length
    · rw [val_input _ x t hlt, val_input _ x (if t < x.length + j then t else t + 1) (by split_ifs <;> omega)]
      have h1 : t < x.length + j := by omega
      simp [h1]
    · set k := t - x.length with hk_def
      have ht_eq : t = x.length + k := by omega
      have hk : k < (elimConst C x.length j b).gates.length := by omega
      rw [ht_eq, val_gate (elimConst C x.length j b) x k hk]
      by_cases hkj : k < j
      · have hcond : x.length + k < x.length + j := by omega
        simp only [hcond, ↓reduceIte]
        rw [val_gate C x k (by omega)]
        have hgate : (elimConst C x.length j b).gates[k] = C.gates[k] := by
          simp only [elimConst]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [hgate]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, ↓reduceIte]
          have hih := ih i (by omega) (by omega)
          have hi2 : i < x.length + j := by omega
          simpa [hi2] using hih
        · simp only [hi, ↓reduceIte]
      · have hcond : ¬ (x.length + k < x.length + j) := by omega
        simp only [hcond, ↓reduceIte]
        have hk1 : k + 1 < C.gates.length := by omega
        have hidx : x.length + k + 1 = x.length + (k + 1) := by omega
        rw [hidx, val_gate C x (k + 1) hk1]
        have hgate : (elimConst C x.length j b).gates[k] = elimConstGate (x.length + j) b C.gates[k + 1] := by
          simp only [elimConst]
          have htake : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
          rw [List.getElem_append_right (by rw [htake]; omega)]
          simp only [List.getElem_map, List.getElem_drop, htake]
          congr 2
          omega
        rw [hgate]
        have hread : ∀ i, i ≠ x.length + j →
            (if shiftDown (x.length + j) i < x.length + k then
                val (elimConst C x.length j b) x (shiftDown (x.length + j) i) else false) =
            (if i < x.length + (k + 1) then val C x i else false) := by
          intro i hne
          unfold shiftDown
          by_cases hgt : x.length + j < i
          · simp only [hgt, ↓reduceIte]
            by_cases hi_lt : i < x.length + (k + 1)
            · have hi1_lt : i - 1 < x.length + k := by omega
              simp only [hi1_lt, hi_lt, ↓reduceIte]
              have hih := ih (i - 1) (by omega) (by omega)
              have hnot : ¬ (i - 1 < x.length + j) := by omega
              simp only [hnot, ↓reduceIte] at hih
              have hplus : i - 1 + 1 = i := by omega
              rw [hplus] at hih
              exact hih
            · have hi1_nlt : ¬ (i - 1 < x.length + k) := by omega
              simp only [hi1_nlt, hi_lt, ↓reduceIte]
          · simp only [hgt, ↓reduceIte]
            have hi_lt1 : i < x.length + k := by omega
            have hi_lt2 : i < x.length + (k + 1) := by omega
            simp only [hi_lt1, hi_lt2, ↓reduceIte]
            have hih := ih i (by omega) (by omega)
            have hi_ltj : i < x.length + j := by omega
            simp only [hi_ltj, ↓reduceIte] at hih
            exact hih
        have hmem_op : C.gates[k + 1].op = GateOp.and ∨ C.gates[k + 1].op = GateOp.or := by
          have h := (hm _ (List.getElem_mem hk1)).1
          simpa using h
        cases b
        · rcases hmem_op with hop | hop
          · unfold elimConstGate
            simp only [hop, isAndOp, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
            by_cases hmem : x.length + j ∈ C.gates[k + 1].inputs
            · simp only [hmem, ↓reduceIte, List.map_nil, GateOp.eval, List.any_nil]
              symm
              rw [Bool.eq_false_iff]
              intro htrue
              rw [List.all_eq_true] at htrue
              have h1 := htrue _ (List.mem_map.mpr ⟨x.length + j, hmem, rfl⟩)
              simp only [id_eq] at h1
              have hltw : x.length + j < x.length + (k + 1) := by omega
              simp only [hltw, ↓reduceIte, hval] at h1
              exact Bool.false_ne_true h1
            · simp only [hmem, ↓reduceIte, List.map_map]
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hread i (fun heq => hmem (heq ▸ hi))
          · unfold elimConstGate
            simp only [hop, isAndOp, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
            apply Bool.eq_iff_iff.mpr
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, List.mem_filter,
              decide_eq_true_eq, id_eq]
            constructor
            · rintro ⟨_, ⟨w, ⟨i, ⟨hi, hne⟩, rfl⟩, htrue⟩, rfl⟩
              refine ⟨true, ⟨i, hi, ?_⟩, rfl⟩
              rw [← hread i hne]
              exact htrue
            · rintro ⟨_, ⟨i, hi, htrue⟩, rfl⟩
              have hne : i ≠ x.length + j := by
                intro heq
                subst heq
                have hltw : x.length + j < x.length + (k + 1) := by omega
                simp only [hltw, ↓reduceIte, hval] at htrue
                exact Bool.false_ne_true htrue
              refine ⟨true, ⟨shiftDown (x.length + j) i, ⟨i, ⟨hi, hne⟩, rfl⟩, ?_⟩, rfl⟩
              rw [hread i hne]
              exact htrue
        · rcases hmem_op with hop | hop
          · unfold elimConstGate
            simp only [hop, isAndOp, ↓reduceIte]
            apply Bool.eq_iff_iff.mpr
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, List.mem_filter,
              decide_eq_true_eq, id_eq]
            constructor
            · rintro h _ ⟨i, hi, rfl⟩
              by_cases hne : i = x.length + j
              · subst hne
                have hltw : x.length + j < x.length + (k + 1) := by omega
                simp only [hltw, ↓reduceIte, hval]
              · rw [← hread i hne]
                exact h _ ⟨shiftDown (x.length + j) i, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩
            · rintro h _ ⟨w, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩
              rw [hread i hne]
              exact h _ ⟨i, hi, rfl⟩
          · unfold elimConstGate
            simp only [hop, isAndOp, Bool.false_eq_true, ↓reduceIte]
            by_cases hmem : x.length + j ∈ C.gates[k + 1].inputs
            · simp only [hmem, ↓reduceIte, List.map_nil, GateOp.eval, List.all_nil]
              symm
              rw [List.any_eq_true]
              refine ⟨true, List.mem_map.mpr ⟨x.length + j, hmem, ?_⟩, rfl⟩
              have hltw : x.length + j < x.length + (k + 1) := by omega
              simp only [hltw, ↓reduceIte, hval]
            · simp only [hmem, ↓reduceIte, List.map_map]
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hread i (fun heq => hmem (heq ▸ hi))

lemma elimConst_eval (C : Circuit) (N j : ℕ) (b : Bool) (hm : Monotone2 C)
    (hj : j < C.gates.length) (x : List Bool) (hx : x.length = N)
    (hval : val C x (N + j) = b) (hout : b = true → C.output ≠ N + j) :
    (elimConst C N j b).eval x = C.eval x := by
  have hout_def : (elimConst C N j b).output =
      if C.output = N + j then N + C.gates.length else shiftDown (N + j) C.output := rfl
  rw [eval_eq_val, eval_eq_val, hout_def]
  have hlen : (elimConst C N j b).gates.length = C.gates.length - 1 := elimConst_size C N j b hj
  by_cases ho_eq : C.output = N + j
  · simp only [ho_eq, ↓reduceIte]
    rw [val_ge (elimConst C N j b) x _ (by rw [hx, hlen]; omega), hval]
    cases b with
    | false => rfl
    | true => exact False.elim (hout rfl ho_eq)
  · simp only [ho_eq, ↓reduceIte]
    unfold shiftDown
    by_cases ho_gt : N + j < C.output
    · simp only [ho_gt, ↓reduceIte]
      by_cases ho_lt : C.output < N + C.gates.length
      · have h1 := elimConst_val C N j b hm hj x hx hval (C.output - 1) (by omega)
        have hnot : ¬ (C.output - 1 < N + j) := by omega
        simp only [hnot, ↓reduceIte] at h1
        have hplus : C.output - 1 + 1 = C.output := by omega
        rw [hplus] at h1
        exact h1
      · rw [val_ge (elimConst C N j b) x _ (by rw [hx, hlen]; omega),
          val_ge C x _ (by rw [hx]; omega)]
    · simp only [ho_gt, ↓reduceIte]
      have ho_ltj : C.output < N + j := by omega
      have h1 := elimConst_val C N j b hm hj x hx hval C.output (by omega)
      simp only [ho_ltj, ↓reduceIte] at h1
      exact h1

lemma minimal_clean {n m : ℕ} {A : Fin n → Fin m → Bool} (hn : 0 < n + m)
    (u : Fin n) (v : Fin m) (hfalse : A u v = false)
    (C : Circuit) (hm : Monotone2 C) (hr : Represents A C)
    (hmin : ∀ C', Monotone2 C' → Represents A C' → C.size ≤ C'.size)
    (hout_ge : n + m ≤ C.output) (hout_lt : C.output < n + m + C.gates.length) :
    CleanCircuit (n + m) C ∧ C.output = n + m + (C.gates.length - 1) := by
  have hbin : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, C.gates[j].inputs = [a, b] ∧ a < (n + m) + j ∧ b < (n + m) + j ∧ a ≠ b := by
    intro j hj
    have hg := hm _ (List.getElem_mem hj)
    have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hg.1
    have hlen2 : C.gates[j].inputs.length ≤ 2 := hg.2
    match h_in : C.gates[j].inputs with
    | [] =>
      rcases hop with hop | hop
      · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = true := by
          intro x hx
          rw [← hx, val_gate C x j hj, hop, h_in]
          rfl
        have hne_out : C.output ≠ (n + m) + j := by
          intro heq
          have h := hr u v
          rw [eval_eq_val, heq, hv _ (by simp only [oneEach_length]), hfalse] at h
          exact Bool.false_ne_true h.symm
        have hrep' : Represents A (elimConst C (n + m) j true) := by
          intro u v
          rw [elimConst_eval C (n + m) j true hm hj _ (by simp only [oneEach_length])
            (hv _ (by simp only [oneEach_length])) (fun _ => hne_out)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (n + m) j true hm) hrep'
        rw [elimConst_size C (n + m) j true hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
      · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = false := by
          intro x hx
          rw [← hx, val_gate C x j hj, hop, h_in]
          rfl
        have hrep' : Represents A (elimConst C (n + m) j false) := by
          intro u v
          rw [elimConst_eval C (n + m) j false hm hj _ (by simp only [oneEach_length])
            (hv _ (by simp only [oneEach_length])) (by simp)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (n + m) j false hm) hrep'
        rw [elimConst_size C (n + m) j false hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
    | [a] =>
      by_cases ha : a < (n + m) + j
      · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = val C x a := by
          intro x hx
          rw [← hx, val_gate C x j hj, h_in]
          have ha' : a < x.length + j := by omega
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
        have hrep' : Represents A (elimAlias C (n + m) j a) := by
          intro u v
          rw [elimAlias_eval C (n + m) j a hj ha _ (by simp only [oneEach_length])
            (Or.inl (hv _ (by simp only [oneEach_length])))]
          exact hr u v
        have hle := hmin _ (elimAlias_mono C (n + m) j a hm) hrep'
        rw [elimAlias_size C (n + m) j a hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
      · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = false := by
          intro x hx
          rw [← hx, val_gate C x j hj, h_in]
          have ha' : ¬ (a < x.length + j) := by omega
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
        have hrep' : Represents A (elimConst C (n + m) j false) := by
          intro u v
          rw [elimConst_eval C (n + m) j false hm hj _ (by simp only [oneEach_length])
            (hv _ (by simp only [oneEach_length])) (by simp)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (n + m) j false hm) hrep'
        rw [elimConst_size C (n + m) j false hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
    | [a, b] =>
      by_cases ha : a < (n + m) + j
      · by_cases hb : b < (n + m) + j
        · by_cases hab : a = b
          · subst hab
            have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = val C x a := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in]
              have ha' : a < x.length + j := by omega
              rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
            have hrep' : Represents A (elimAlias C (n + m) j a) := by
              intro u v
              rw [elimAlias_eval C (n + m) j a hj ha _ (by simp only [oneEach_length])
                (Or.inl (hv _ (by simp only [oneEach_length])))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (n + m) j a hm) hrep'
            rw [elimAlias_size C (n + m) j a hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · exact ⟨a, b, rfl, ha, hb, hab⟩
        · rcases hop with hop | hop
          · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = false := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have hb' : ¬ (b < x.length + j) := by omega
              simp [GateOp.eval, hb']
            have hrep' : Represents A (elimConst C (n + m) j false) := by
              intro u v
              rw [elimConst_eval C (n + m) j false hm hj _ (by simp only [oneEach_length])
                (hv _ (by simp only [oneEach_length])) (by simp)]
              exact hr u v
            have hle := hmin _ (elimConst_mono C (n + m) j false hm) hrep'
            rw [elimConst_size C (n + m) j false hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = val C x a := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : a < x.length + j := by omega
              have hb' : ¬ (b < x.length + j) := by omega
              simp [GateOp.eval, ha', hb']
            have hrep' : Represents A (elimAlias C (n + m) j a) := by
              intro u v
              rw [elimAlias_eval C (n + m) j a hj ha _ (by simp only [oneEach_length])
                (Or.inl (hv _ (by simp only [oneEach_length])))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (n + m) j a hm) hrep'
            rw [elimAlias_size C (n + m) j a hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
      · by_cases hb : b < (n + m) + j
        · rcases hop with hop | hop
          · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = false := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : ¬ (a < x.length + j) := by omega
              simp [GateOp.eval, ha']
            have hrep' : Represents A (elimConst C (n + m) j false) := by
              intro u v
              rw [elimConst_eval C (n + m) j false hm hj _ (by simp only [oneEach_length])
                (hv _ (by simp only [oneEach_length])) (by simp)]
              exact hr u v
            have hle := hmin _ (elimConst_mono C (n + m) j false hm) hrep'
            rw [elimConst_size C (n + m) j false hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = val C x b := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : ¬ (a < x.length + j) := by omega
              have hb' : b < x.length + j := by omega
              simp [GateOp.eval, ha', hb']
            have hrep' : Represents A (elimAlias C (n + m) j b) := by
              intro u v
              rw [elimAlias_eval C (n + m) j b hj hb _ (by simp only [oneEach_length])
                (Or.inl (hv _ (by simp only [oneEach_length])))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (n + m) j b hm) hrep'
            rw [elimAlias_size C (n + m) j b hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
        · have hv : ∀ x : List Bool, x.length = (n + m) → val C x ((n + m) + j) = false := by
            intro x hx
            rw [← hx, val_gate C x j hj, h_in]
            have ha' : ¬ (a < x.length + j) := by omega
            have hb' : ¬ (b < x.length + j) := by omega
            rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha', hb']
          have hrep' : Represents A (elimConst C (n + m) j false) := by
            intro u v
            rw [elimConst_eval C (n + m) j false hm hj _ (by simp only [oneEach_length])
              (hv _ (by simp only [oneEach_length])) (by simp)]
            exact hr u v
          have hle := hmin _ (elimConst_mono C (n + m) j false hm) hrep'
          rw [elimConst_size C (n + m) j false hj] at hle
          change C.gates.length ≤ C.gates.length - 1 at hle
          omega
    | _ :: _ :: _ :: _ =>
      rw [h_in] at hlen2
      simp at hlen2
  have hused : ∀ j, j < C.gates.length →
      C.output = (n + m) + j ∨ ∃ k, ∃ hk : k < C.gates.length, j < k ∧ (n + m) + j ∈ C.gates[k].inputs := by
    intro j hj
    by_contra h
    push Not at h
    have hrep' : Represents A (elimAlias C (n + m) j 0) := by
      intro u v
      rw [elimAlias_eval C (n + m) j 0 hj (by omega) _ (by simp only [oneEach_length])
        (Or.inr ⟨h.1, fun k hk hjk => h.2 k hk hjk⟩)]
      exact hr u v
    have hle := hmin _ (elimAlias_mono C (n + m) j 0 hm) hrep'
    rw [elimAlias_size C (n + m) j 0 hj] at hle
    change C.gates.length ≤ C.gates.length - 1 at hle
    omega
  have hout_last : C.output = (n + m) + (C.gates.length - 1) := by
    rcases hused (C.gates.length - 1) (by omega) with h | ⟨k, hk, hlt, _⟩
    · exact h
    · omega
  exact ⟨⟨hm, hbin, hused⟩, hout_last⟩


def gateWires (C : Circuit) (N : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).image (N + ·)

def gateAt (C : Circuit) (N w : ℕ) : Gate :=
  C.gates.getD (w - N) { op := GateOp.or, inputs := [] }

def left (C : Circuit) (N w : ℕ) : ℕ := (gateAt C N w).inputs.getD 0 0
def right (C : Circuit) (N w : ℕ) : ℕ := (gateAt C N w).inputs.getD 1 0

def isOr (C : Circuit) (N w : ℕ) : Bool :=
  !(isAndOp (gateAt C N w).op)

lemma gateWires_iff {C : Circuit} {N w : ℕ} :
    w ∈ gateWires C N ↔ N ≤ w ∧ w < N + C.gates.length := by
  simp only [gateWires, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro h
    exact ⟨w - N, by omega, by omega⟩

lemma gateAt_eq {C : Circuit} {N j : ℕ} (hj : j < C.gates.length) :
    gateAt C N (N + j) = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gate_data {C : Circuit} {N w : ℕ} (hc : CleanCircuit N C)
    (hw : w ∈ gateWires C N) :
    (gateAt C N w).inputs = [left C N w, right C N w] ∧
      left C N w < w ∧ right C N w < w ∧ left C N w ≠ right C N w := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hj' := Finset.mem_range.mp hj
  obtain ⟨a, b, hab, ha, hb, hne⟩ := hc.2.1 j hj'
  simp [left, right, gateAt_eq hj', hab, ha, hb, hne]

def reads (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (gateWires C N).filter fun q => left C N q = w ∨ right C N q = w

lemma mem_reads {C : Circuit} {N w q : ℕ} :
    q ∈ reads C N w ↔ q ∈ gateWires C N ∧ (left C N q = w ∨ right C N q = w) :=
  Finset.mem_filter

lemma reads_increases {C : Circuit} {N w q : ℕ} (hc : CleanCircuit N C)
    (hq : q ∈ reads C N w) : w < q := by
  obtain ⟨hq, h⟩ := mem_reads.mp hq
  obtain ⟨_, hl, hr, _⟩ := gate_data hc hq
  rcases h with h | h <;> omega

def run (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool :=
  val C (List.ofFn fun i : Fin N => x i) w

lemma run_input {C : Circuit} {N w : ℕ} (x : ℕ → Bool) (hw : w < N) :
    run C N x w = x w := by
  unfold run
  rw [val_input C _ w (by simpa), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa)]
  simp

lemma run_gate {C : Circuit} {N w : ℕ} (hc : CleanCircuit N C)
    (x : ℕ → Bool) (hw : w ∈ gateWires C N) :
    run C N x w =
      if isOr C N w then run C N x (left C N w) || run C N x (right C N w)
      else run C N x (left C N w) && run C N x (right C N w) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hj' := Finset.mem_range.mp hj
  obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hj'
  have hopen : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
    simpa using (hc.1 _ (List.getElem_mem hj')).1
  simp only [left, right, isOr, gateAt_eq hj', hab]
  let xs := List.ofFn fun i : Fin N => x i
  have hlen : xs.length = N := by simp [xs]
  have hvg := val_gate C xs j hj'
  rw [hlen] at hvg
  rw [hab] at hvg
  unfold run
  change val C xs (N + j) = _
  rw [hvg]
  rcases hopen with h | h <;> simp [h, isAndOp, GateOp.eval, ha, hb, List.getD, xs]

-- Follow an input through OR gates as long as it has a unique reader.
def Forward (C : Circuit) (N p q : ℕ) : Prop :=
  reads C N p = {q} ∧ isOr C N q = true

lemma forward_mem {C : Circuit} {N p q : ℕ} (h : Forward C N p q) :
    q ∈ reads C N p := by simp [h.1]

noncomputable def stop (C : Circuit) (N : ℕ) (hc : CleanCircuit N C) (p : ℕ) : ℕ := by
  classical
  by_cases h : ∃ q, Forward C N p q
  · have hmem := forward_mem (Classical.choose_spec h)
    have hlt := reads_increases hc hmem
    have hb := gateWires_iff.mp (mem_reads.mp hmem).1
    exact stop C N hc (Classical.choose h)
  · exact p
termination_by N + C.gates.length - p
decreasing_by omega

lemma stop_step {C : Circuit} {N p q : ℕ} {hc : CleanCircuit N C}
    (h : Forward C N p q) : stop C N hc p = stop C N hc q := by
  rw [stop]
  split
  next h' =>
    have hq := forward_mem (Classical.choose_spec h')
    rw [h.1, Finset.mem_singleton] at hq
    simp only [hq]
  next h' => exact (h' ⟨q, h⟩).elim

lemma stop_fixed {C : Circuit} {N p : ℕ} {hc : CleanCircuit N C}
    (h : ¬ ∃ q, Forward C N p q) : stop C N hc p = p := by
  rw [stop]
  split
  next h' => exact (h h').elim
  next => rfl

lemma forward_of_ne_stop {C : Circuit} {N p : ℕ} {hc : CleanCircuit N C}
    (h : p ≠ stop C N hc p) : ∃ q, Forward C N p q := by
  by_contra hn
  exact h (stop_fixed hn).symm

lemma stop_bounded {C : Circuit} {N p : ℕ} {hc : CleanCircuit N C}
    (hp : p < N + C.gates.length) :
    p ≤ stop C N hc p ∧ stop C N hc p < N + C.gates.length := by
  suffices ∀ t p : ℕ, N + C.gates.length - p = t →
      p < N + C.gates.length →
      p ≤ stop C N hc p ∧ stop C N hc p < N + C.gates.length from this _ _ rfl hp
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro p he hp
    by_cases h : ∃ q, Forward C N p q
    · obtain ⟨q, hq⟩ := h
      have hm := forward_mem hq
      have hlt := reads_increases hc hm
      have hb := gateWires_iff.mp (mem_reads.mp hm).1
      have hi := ih (N + C.gates.length - q) (by omega) q rfl hb.2
      rw [stop_step hq]
      omega
    · rw [stop_fixed h]
      exact ⟨le_rfl, hp⟩

lemma stop_idem {C : Circuit} {N p : ℕ} {hc : CleanCircuit N C}
    (hp : p < N + C.gates.length) : stop C N hc (stop C N hc p) = stop C N hc p := by
  suffices ∀ t p : ℕ, N + C.gates.length - p = t →
      p < N + C.gates.length →
      stop C N hc (stop C N hc p) = stop C N hc p from this _ _ rfl hp
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro p he hp
    by_cases h : ∃ q, Forward C N p q
    · obtain ⟨q, hq⟩ := h
      have hm := forward_mem hq
      have hlt := reads_increases hc hm
      have hb := gateWires_iff.mp (mem_reads.mp hm).1
      rw [stop_step hq]
      exact ih (N + C.gates.length - q) (by omega) q rfl hb.2
    · exact congrArg (stop C N hc) (stop_fixed (hc := hc) h)

lemma run_stop {C : Circuit} {N p : ℕ} {hc : CleanCircuit N C}
    (x : ℕ → Bool) (hp : p < N + C.gates.length) (hx : run C N x p = true) :
    run C N x (stop C N hc p) = true := by
  suffices ∀ t p : ℕ, N + C.gates.length - p = t →
      p < N + C.gates.length → run C N x p = true →
      run C N x (stop C N hc p) = true from this _ _ rfl hp hx
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro p he hp hx
    by_cases h : ∃ q, Forward C N p q
    · obtain ⟨q, hq⟩ := h
      have hm := forward_mem hq
      have hlt := reads_increases hc hm
      obtain ⟨hg, heq⟩ := mem_reads.mp hm
      have hb := (gateWires_iff.mp hg).2
      rw [stop_step hq]
      apply ih (N + C.gates.length - q) (by omega) q rfl hb
      rw [run_gate hc x hg]
      simp only [hq.2, ↓reduceIte]
      rcases heq with heq | heq <;> simp [heq, hx]
    · rwa [stop_fixed h]

lemma end_of_reader {C : Circuit} {N p q z : ℕ} {hc : CleanCircuit N C}
    (hs : stop C N hc p = z) (hn : p ≠ z) (hq : q ∈ reads C N p) :
    stop C N hc q = z ∧ isOr C N q = true := by
  obtain ⟨v, hv⟩ := forward_of_ne_stop (hc := hc) (p := p) (hs ▸ hn)
  have he : q = v := by simpa [hv.1] using hq
  subst v
  exact ⟨(stop_step (hc := hc) hv).symm.trans hs, hv.2⟩

-- Two inputs with the same stopping wire are interchangeable when one is set.
lemma stop_diff {C : Circuit} {N i j : ℕ} {hc : CleanCircuit N C}
    (x y : ℕ → Bool) (hi : i < N) (hj : j < N)
    (hx : x i = true) (hy : y j = true)
    (he : ∀ w, x w ≠ y w → w = i ∨ w = j)
    (hs : stop C N hc i = stop C N hc j) :
    ∀ w < N + C.gates.length, run C N x w ≠ run C N y w →
      stop C N hc w = stop C N hc i ∧ w ≠ stop C N hc i := by
  have hz₁ := run_stop x (p := i) (hc := hc) (by omega) ((run_input x hi).trans hx)
  have hz₂ := run_stop y (p := j) (hc := hc) (by omega) ((run_input y hj).trans hy)
  rw [← hs] at hz₂
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hb hd
    have hn : w ≠ stop C N hc i := by
      intro h
      exact hd (h ▸ hz₁.trans hz₂.symm)
    refine ⟨?_, hn⟩
    by_cases hw : w < N
    · rw [run_input x hw, run_input y hw] at hd
      rcases he w hd with rfl | rfl
      · rfl
      · exact hs.symm
    · have hg := gateWires_iff.mpr ⟨by omega, hb⟩
      obtain ⟨_, hl, hr, _⟩ := gate_data hc hg
      have hd' : run C N x (left C N w) ≠ run C N y (left C N w) ∨
          run C N x (right C N w) ≠ run C N y (right C N w) := by
        by_contra! hh
        apply hd
        rw [run_gate hc x hg, run_gate hc y hg, hh.1, hh.2]
      rcases hd' with hd' | hd'
      · have h := ih _ hl (by omega) hd'
        exact (end_of_reader h.1 h.2 (mem_reads.mpr ⟨hg, Or.inl rfl⟩)).1
      · have h := ih _ hr (by omega) hd'
        exact (end_of_reader h.1 h.2 (mem_reads.mpr ⟨hg, Or.inr rfl⟩)).1


def single (i w : ℕ) : Bool := decide (w = i)
def pair (i j w : ℕ) : Bool := decide (w = i ∨ w = j)

lemma pair_input {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (hw : w < n + m) :
    (oneEach u v).getD w false = pair u (n + v.val) w := by
  rw [oneEach_getD]
  by_cases hn : w < n
  · have hh : w ≠ n + v.val := by omega
    simp [pair, hn, hh]
  · have hh : w ≠ u.val := by have := u.isLt; omega
    have he : w - n = v.val ↔ w = n + v.val := by omega
    simp [pair, hn, hw, hh, he]

lemma pair_rep {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hrep : Represents A C) (u : Fin n) (v : Fin m) :
    run C (n + m) (pair u (n + v.val)) C.output = A u v := by
  have he : (List.ofFn fun i : Fin (n + m) => pair u (n + v.val) i) = oneEach u v := by
    apply List.ext_getElem
    · simp [oneEach_length]
    · intro w h₁ h₂
      simp only [List.getElem_ofFn]
      have h := pair_input u v w (by simpa [oneEach_length] using h₂)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some, eq_comm] at h
  simpa only [run, he, ← eval_eq_val] using hrep u v

lemma run_mono {C : Circuit} {N : ℕ} (hc : CleanCircuit N C) (x y : ℕ → Bool)
    (hxy : ∀ w, x w = true → y w = true) :
    ∀ w < N + C.gates.length, run C N x w = true → run C N y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hb hx
    by_cases hw : w < N
    · rw [run_input x hw] at hx
      rw [run_input y hw]
      exact hxy _ hx
    · have hg := gateWires_iff.mpr ⟨by omega, hb⟩
      obtain ⟨_, hl, hr, _⟩ := gate_data hc hg
      rw [run_gate hc x hg] at hx
      rw [run_gate hc y hg]
      by_cases ho : isOr C N w = true
      · simp only [ite_eq_left ho, Bool.or_eq_true] at hx ⊢
        exact hx.imp (ih _ hl (by omega)) (ih _ hr (by omega))
      · simp only [ite_eq_right ho, Bool.and_eq_true] at hx ⊢
        exact ⟨ih _ hl (by omega) hx.1, ih _ hr (by omega) hx.2⟩

lemma run_eq_unread {C : Circuit} {N : ℕ} (hc : CleanCircuit N C) (x y : ℕ → Bool)
    (hxy : ∀ p, (reads C N p).Nonempty → x p = y p) :
    ∀ w ∈ gateWires C N, run C N x w = run C N y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    obtain ⟨_, hl, hr, _⟩ := gate_data hc hw
    have hb := (gateWires_iff.mp hw).2
    have aux : ∀ p < w, w ∈ reads C N p → run C N x p = run C N y p := by
      intro p hp hread
      by_cases hi : p < N
      · rw [run_input x hi, run_input y hi]
        exact hxy _ ⟨w, hread⟩
      · exact ih p hp (gateWires_iff.mpr ⟨by omega, by omega⟩)
    rw [run_gate hc x hw, run_gate hc y hw,
      aux _ hl (mem_reads.mpr ⟨hw, Or.inl rfl⟩),
      aux _ hr (mem_reads.mpr ⟨hw, Or.inr rfl⟩)]

lemma singleton_stop {C : Circuit} {N i z : ℕ} {hc : CleanCircuit N C}
    (hs : stop C N hc i = z) (hz : stop C N hc z = z) (hd : (reads C N z).card < 2) :
    ∀ w < N + C.gates.length, run C N (single i) w = true → stop C N hc w = z := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hb hv
    by_cases hw : w < N
    · rw [run_input _ hw, single, decide_eq_true_eq] at hv
      rwa [hv]
    · have hg := gateWires_iff.mpr ⟨by omega, hb⟩
      obtain ⟨_, hl, hr, hne⟩ := gate_data hc hg
      rw [run_gate hc (single i) hg] at hv
      have aux : ∀ p < w, w ∈ reads C N p → run C N (single i) p = true →
          (p = z ∨ isOr C N w = true) ∧
          (isOr C N w = true → stop C N hc w = z) := by
        intro p hp hread hval
        have hps := ih p hp (by omega) hval
        by_cases hpz : p = z
        · subst p
          refine ⟨Or.inl rfl, ?_⟩
          intro hor
          have hcard : (reads C N z).card = 1 := by
            have := Finset.card_pos.mpr ⟨w, hread⟩
            omega
          obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
          have hqw : w = q := by simpa [hq] using hread
          subst q
          exact (stop_step (hc := hc) ⟨hq, hor⟩).symm.trans hz
        · have he := end_of_reader hps hpz hread
          exact ⟨Or.inr he.2, fun _ => he.1⟩
      have hm₁ : w ∈ reads C N (left C N w) := mem_reads.mpr ⟨hg, Or.inl rfl⟩
      have hm₂ : w ∈ reads C N (right C N w) := mem_reads.mpr ⟨hg, Or.inr rfl⟩
      by_cases hor : isOr C N w = true
      · simp only [hor, ↓reduceIte, Bool.or_eq_true] at hv
        exact hv.elim (fun h => (aux _ hl hm₁ h).2 hor) (fun h => (aux _ hr hm₂ h).2 hor)
      · simp only [ite_eq_right hor, Bool.and_eq_true] at hv
        have h₁ := (aux _ hl hm₁ hv.1).1.resolve_right hor
        have h₂ := (aux _ hr hm₂ hv.2).1.resolve_right hor
        exact (hne (h₁.trans h₂.symm)).elim

lemma and_port {C : Circuit} {N i w p : ℕ} {hc : CleanCircuit N C}
    (hb : w < N + C.gates.length) (hm : w ∈ reads C N p) (hor : isOr C N w ≠ true)
    (hd : (reads C N (stop C N hc i)).card < 2) (hi : i < N)
    (hval : run C N (single i) p = true) :
    p = stop C N hc i := by
  have hs := singleton_stop (hc := hc) rfl (stop_idem (hc := hc) (by omega)) hd
      p (lt_trans (reads_increases hc hm) hb) hval
  by_contra hn
  exact hor (end_of_reader hs hn hm).2

-- A pair accepted without either singleton must combine them at an AND gate.
lemma joint_gate {C : Circuit} {N i j : ℕ} (hc : CleanCircuit N C) :
    ∀ w < N + C.gates.length,
      run C N (pair i j) w = true →
      run C N (single i) w = false → run C N (single j) w = false →
      ∃ q ∈ gateWires C N, isOr C N q ≠ true ∧
        ((run C N (single i) (left C N q) = true ∧
          run C N (single j) (right C N q) = true) ∨
         (run C N (single j) (left C N q) = true ∧
          run C N (single i) (right C N q) = true)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hb hpair hi hj
    by_cases hw : w < N
    · rw [run_input _ hw, pair, decide_eq_true_eq] at hpair
      rw [run_input _ hw, single, decide_eq_false_iff_not] at hi hj
      exact (hpair.elim hi hj).elim
    · have hg := gateWires_iff.mpr ⟨by omega, hb⟩
      obtain ⟨_, hl, hr, _⟩ := gate_data hc hg
      rw [run_gate hc _ hg] at hpair hi hj
      by_cases hor : isOr C N w = true
      · simp only [hor, ↓reduceIte, Bool.or_eq_true, Bool.or_eq_false_iff] at hpair hi hj
        exact hpair.elim (fun h => ih _ hl (by omega) h hi.1 hj.1)
          (fun h => ih _ hr (by omega) h hi.2 hj.2)
      · simp only [ite_eq_right hor, Bool.and_eq_true, Bool.and_eq_false_iff] at hpair hi hj
        by_cases hli : run C N (single i) (left C N w) = true
        · have hri := hi.resolve_left (by simp [hli])
          by_cases hrj : run C N (single j) (right C N w) = true
          · exact ⟨w, hg, hor, Or.inl ⟨hli, hrj⟩⟩
          · exact ih _ hr (by omega) hpair.2 hri (by simpa using hrj)
        · by_cases hlj : run C N (single j) (left C N w) = true
          · have hrj := hj.resolve_left (by simp [hlj])
            by_cases hri : run C N (single i) (right C N w) = true
            · exact ⟨w, hg, hor, Or.inr ⟨hlj, hri⟩⟩
            · exact ih _ hr (by omega) hpair.2 (by simpa using hri) hrj
          · exact ih _ hl (by omega) hpair.1 (by simpa using hli) (by simpa using hlj)


lemma pair_comm (i j : ℕ) : pair i j = pair j i := by
  funext w
  simp [pair, or_comm]

lemma pair_diff {i j u w : ℕ} (h : pair i u w ≠ pair j u w) : w = i ∨ w = j := by
  by_contra! hn
  exact h (by simp [pair, hn.1, hn.2])

lemma reader_unique {C : Circuit} {N p a b : ℕ}
    (hd : (reads C N p).card < 2) (ha : a ∈ reads C N p) (hb : b ∈ reads C N p) :
    a = b := by
  exact Finset.card_le_one.mp (by omega) _ ha _ hb

def sideDistinct {k : ℕ} (C : Circuit) (N : ℕ) (r c : Fin k → ℕ) : Prop :=
  ∀ a b : Fin k, a ≠ b → ∃ d : Fin k,
    run C N (pair (r a) (c d)) C.output ≠ run C N (pair (r b) (c d)) C.output

lemma side_swap {k : ℕ} {C : Circuit} {N : ℕ} {r c : Fin k → ℕ}
    (hdiag : ∀ a, run C N (pair (r a) (c a)) C.output = false)
    (hcross : ∀ a b, a ≠ b → run C N (pair (r a) (c b)) C.output = true ∨
      run C N (pair (r b) (c a)) C.output = true) :
    sideDistinct C N r c ∧ sideDistinct C N c r := by
  have aux : ∀ (r c : Fin k → ℕ),
      (∀ a, run C N (pair (r a) (c a)) C.output = false) →
      (∀ a b, a ≠ b → run C N (pair (r a) (c b)) C.output = true ∨
        run C N (pair (r b) (c a)) C.output = true) → sideDistinct C N r c := by
    intro r c hd ht a b hab
    rcases ht a b hab with h | h
    · exact ⟨b, by rw [h, hd b]; decide⟩
    · exact ⟨a, by rw [hd a, h]; decide⟩
  refine ⟨aux r c hdiag hcross, aux c r ?_ ?_⟩
  · intro a
    rw [pair_comm]
    exact hdiag a
  · intro a b hab
    rw [pair_comm (c a), pair_comm (c b), or_comm]
    exact hcross a b hab

lemma stops_injective {k : ℕ} {C : Circuit} {N : ℕ} {r c : Fin k → ℕ}
    (hc : CleanCircuit N C) (hout : C.output < N + C.gates.length)
    (ho : stop C N hc C.output = C.output)
    (hr : ∀ a, r a < N) (hd : sideDistinct C N r c) :
    Function.Injective (fun a => stop C N hc (r a)) := by
  intro a b hab
  by_contra hn
  obtain ⟨d, hdiff⟩ := hd a b hn
  have h := stop_diff (hc := hc) (pair (r a) (c d)) (pair (r b) (c d))
    (hr a) (hr b) (by simp [pair]) (by simp [pair]) (fun _ => pair_diff) hab _ hout hdiff
  exact h.2 (ho.symm.trans h.1)

lemma missing_le_one {k : ℕ} {C : Circuit} {N : ℕ} {r c : Fin k → ℕ}
    (hc : CleanCircuit N C) (hout : C.output ∈ gateWires C N)
    (hd : sideDistinct C N r c) :
    ((Finset.univ : Finset (Fin k)).filter fun a => ¬ (reads C N (r a)).Nonempty).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  by_contra hn
  obtain ⟨d, hdiff⟩ := hd a b hn
  apply hdiff
  apply run_eq_unread hc _ _ _ _ hout
  intro p hp
  by_contra h
  rcases pair_diff h with rfl | rfl
  · exact ha' hp
  · exact hb' hp

def shared (C : Circuit) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + C.gates.length)).filter fun p => 2 ≤ (reads C N p).card

lemma shared_bad_le {k : ℕ} {C : Circuit} {N : ℕ} (hc : CleanCircuit N C)
    (r : Fin k → ℕ) (hr : ∀ a, r a < N)
    (hi : Function.Injective (fun a => stop C N hc (r a))) :
    ((Finset.univ : Finset (Fin k)).filter
      fun a => 2 ≤ (reads C N (stop C N hc (r a))).card).card ≤ (shared C N).card := by
  apply Finset.card_le_card_of_injOn (fun a => stop C N hc (r a)) _ hi.injOn
  intro a ha
  have ha' := (Finset.mem_filter.mp (show a ∈ _ from ha)).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (stop_bounded (hc := hc) (by have := hr a; omega)).2, ha'⟩

lemma sparse_rows_le_three {ι : Type} [DecidableEq ι] (T : Finset ι) (f : ι → ι → Bool)
    (hcross : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → f a b = true ∨ f b a = true)
    (huniq : ∀ a ∈ T, ∀ b ∈ T, ∀ d ∈ T, f a b = true → f a d = true → b = d) :
    T.card ≤ 3 := by
  let E := (T ×ˢ T).filter fun p => f p.1 p.2 = true
  let F := (T ×ˢ T).filter fun p => p.1 ≠ p.2
  let D := (T ×ˢ T).filter fun p => p.1 = p.2
  have he : E.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp (show p ∈ E from hp)).1).1
    · rintro ⟨a, b⟩ hp ⟨a', d⟩ hq heq
      change a = a' at heq
      subst a'
      obtain ⟨hp, h₁⟩ := Finset.mem_filter.mp (show (a, b) ∈ E from hp)
      obtain ⟨hq, h₂⟩ := Finset.mem_filter.mp (show (a, d) ∈ E from hq)
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨_, hd⟩ := Finset.mem_product.mp hq
      rw [huniq a ha b hb d hd h₁ h₂]
  have hsub : F ⊆ E ∪ E.image Prod.swap := by
    rintro ⟨a, b⟩ hp
    obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    apply Finset.mem_union.mpr
    rcases hcross a ha b hb hne with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨(b, a), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hb, ha⟩, h⟩, rfl⟩)
  have hf := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hswap : (E.image Prod.swap).card ≤ E.card := Finset.card_image_le
  have hd : D.card = T.card := by
    have heq : D = T.image (fun a => (a, a)) := by
      ext ⟨a, b⟩
      simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨x, hx, rfl, rfl⟩
        exact ⟨⟨hx, hx⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  have htotal : F.card + D.card = T.card * T.card := by
    simpa only [F, D, not_not, Finset.card_product] using
      Finset.card_filter_add_card_filter_not (s := T ×ˢ T) (fun p : ι × ι => p.1 ≠ p.2)
  by_contra! hn
  have hm := Nat.mul_le_mul_right T.card (show 4 ≤ T.card by omega)
  omega


lemma gate_count (C : Circuit) (N : ℕ) :
    (gateWires C N).card = C.gates.length := by
  have hinj : Function.Injective (N + ·) := by
    intro x y h
    change N + x = N + y at h
    omega
  rw [gateWires, Finset.card_image_of_injective _ hinj, Finset.card_range]

lemma total_reads {C : Circuit} {N : ℕ} (hc : CleanCircuit N C) :
    ∑ p ∈ Finset.range (N + C.gates.length), (reads C N p).card = 2 * C.gates.length := by
  classical
  let U := Finset.range (N + C.gates.length)
  let readPair := fun p q => left C N q = p ∨ right C N q = p
  change ∑ p ∈ U, (reads C N p).card = _
  calc
    _ = ∑ p ∈ U, ∑ q ∈ gateWires C N, (if readPair p q then 1 else 0 : ℕ) := by
      simp [reads, readPair]
    _ = ∑ q ∈ gateWires C N, ∑ p ∈ U, (if readPair p q then 1 else 0 : ℕ) :=
      Finset.sum_comm
    _ = 2 * C.gates.length := by
      have he : ∀ q ∈ gateWires C N,
          ∑ p ∈ U, (if readPair p q then 1 else 0 : ℕ) = 2 := by
        intro q hq
        rw [Finset.sum_boole]
        obtain ⟨_, hl, hr, hne⟩ := gate_data hc hq
        have hqb := (gateWires_iff.mp hq).2
        have he : U.filter (fun p => readPair p q) = {left C N q, right C N q} := by
          have h₁ : left C N q ∈ U := Finset.mem_range.mpr (by omega)
          have h₂ : right C N q ∈ U := Finset.mem_range.mpr (by omega)
          ext p
          simp only [Finset.mem_filter, readPair, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.2.imp Eq.symm Eq.symm, by
            rintro (rfl | rfl)
            · exact ⟨h₁, Or.inl rfl⟩
            · exact ⟨h₂, Or.inr rfl⟩⟩
        rw [he, Finset.card_pair hne]
        rfl
      rw [Finset.sum_congr rfl he]
      simp [gate_count, Nat.mul_comm]

def usedInputs (C : Circuit) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun p => (reads C N p).Nonempty

lemma used_lower {k : ℕ} {C : Circuit} {N : ℕ} {r c : Fin k → ℕ}
    (hc : CleanCircuit N C) (hout : C.output ∈ gateWires C N)
    (hr : ∀ a, r a < N) (hci : ∀ a, c a < N) (hdis : ∀ a b, r a ≠ c b)
    (hd : sideDistinct C N r c) (hd' : sideDistinct C N c r)
    (hir : Function.Injective r) (hic : Function.Injective c) :
    2 * k ≤ (usedInputs C N).card + 2 := by
  let R := (Finset.univ : Finset (Fin k)).filter fun a => (reads C N (r a)).Nonempty
  let S := (Finset.univ : Finset (Fin k)).filter fun a => (reads C N (c a)).Nonempty
  have hrk : k ≤ R.card + 1 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun a => (reads C N (r a)).Nonempty)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    have hm := missing_le_one hc hout hd
    change R.card + _ = k at hsum
    omega
  have hsk : k ≤ S.card + 1 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun a => (reads C N (c a)).Nonempty)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    have hm := missing_le_one hc hout hd'
    change S.card + _ = k at hsum
    omega
  have hsubset : R.image r ∪ S.image c ⊆ usedInputs C N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hr a), (Finset.mem_filter.mp ha).2⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hci a), (Finset.mem_filter.mp ha).2⟩
  have hdisj : Disjoint (R.image r) (S.image c) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hq
    exact hdis a b (ha.trans hb.symm)
  have hl := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hir,
    Finset.card_image_of_injective _ hic] at hl
  omega

lemma excess_bound {C : Circuit} {N : ℕ} (hc : CleanCircuit N C)
    (hout : C.output ∈ gateWires C N) :
    (usedInputs C N).card + (shared C N).card ≤ C.gates.length + 1 := by
  classical
  let U := Finset.range (N + C.gates.length)
  let T := usedInputs C N ∪ (gateWires C N).erase C.output
  have ht : T ⊆ U := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (gateWires_iff.mp (Finset.mem_of_mem_erase hp)).2
  have hnon : ∀ p ∈ T, 1 ≤ (reads C N p).card := by
    intro p hp
    apply Finset.card_pos.mpr
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2
    · obtain ⟨hne, hg⟩ := Finset.mem_erase.mp hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
      have hj' := Finset.mem_range.mp hj
      rcases hc.2.2 j hj' with ho | ⟨q, hq, _, hmem⟩
      · exact (hne ho.symm).elim
      · have hq' : N + q ∈ gateWires C N := gateWires_iff.mpr ⟨by omega, by omega⟩
        rw [← gateAt_eq (N := N) hq, (gate_data hc hq').1] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact ⟨N + q, mem_reads.mpr ⟨hq', hmem.imp Eq.symm Eq.symm⟩⟩
  have hdis : Disjoint (usedInputs C N) ((gateWires C N).erase C.output) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have h₁ := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have h₂ := (gateWires_iff.mp (Finset.mem_of_mem_erase hq)).1
    omega
  have htcard : T.card = (usedInputs C N).card + (C.gates.length - 1) := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_erase_of_mem hout, gate_count]
  have hshared : shared C N ⊆ U := Finset.filter_subset _ _
  have hsum : T.card + (shared C N).card ≤ ∑ p ∈ U, (reads C N p).card := by
    rw [Finset.card_eq_sum_ite ht, Finset.card_eq_sum_ite hshared, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hps : p ∈ shared C N
    · have h := (Finset.mem_filter.mp hps).2
      split_ifs <;> omega
    · by_cases hpt : p ∈ T
      · have h := hnon p hpt
        simpa [hps, hpt] using h
      · simp [hps, hpt]
  rw [htcard, total_reads hc] at hsum
  have hpos := (gateWires_iff.mp hout).2
  omega


-- Removing the indices that stop at shared wires leaves at most one edge per row.
lemma shared_lower {k : ℕ} {C : Circuit} {N : ℕ} {r c : Fin k → ℕ}
    (hc : CleanCircuit N C) (hout : C.output < N + C.gates.length)
    (hr : ∀ a, r a < N) (hci : ∀ a, c a < N)
    (hir : Function.Injective (fun a => stop C N hc (r a)))
    (hic : Function.Injective (fun a => stop C N hc (c a)))
    (hdiag : ∀ a, run C N (pair (r a) (c a)) C.output = false)
    (hcross : ∀ a b, a ≠ b → run C N (pair (r a) (c b)) C.output = true ∨
      run C N (pair (r b) (c a)) C.output = true) :
    k ≤ 2 * (shared C N).card + 3 := by
  classical
  let R := fun a => stop C N hc (r a)
  let S := fun a => stop C N hc (c a)
  let badR := (Finset.univ : Finset (Fin k)).filter fun a => 2 ≤ (reads C N (R a)).card
  let badS := (Finset.univ : Finset (Fin k)).filter fun a => 2 ≤ (reads C N (S a)).card
  let T := (Finset.univ : Finset (Fin k)).filter fun a => a ∉ badR ∪ badS
  have hcard : T.card + (badR ∪ badS).card = k := by
    have he : (Finset.univ : Finset (Fin k)).filter (fun a => ¬ a ∉ badR ∪ badS) =
        badR ∪ badS := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    have hd := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun a => a ∉ badR ∪ badS)
    change T.card + _ = _ at hd
    rw [he] at hd
    simpa using hd
  have hunion := Finset.card_union_le badR badS
  have hbR : badR.card ≤ (shared C N).card := shared_bad_le hc r hr hir
  have hbS : badS.card ≤ (shared C N).card := shared_bad_le hc c hci hic
  have hgood : ∀ a ∈ T, (reads C N (R a)).card < 2 ∧ (reads C N (S a)).card < 2 := by
    intro a ha
    simpa [T, badR, badS, not_or] using ha
  have hsingR : ∀ a, run C N (single (r a)) C.output = false := by
    intro a
    by_contra h
    have h' : run C N (single (r a)) C.output = true := by simpa using h
    have he := run_mono hc (single (r a)) (pair (r a) (c a)) (fun w hw => by
      simp only [single, decide_eq_true_eq] at hw
      simp [pair, hw]) _ hout h'
    rw [hdiag a] at he
    contradiction
  have hsingS : ∀ a, run C N (single (c a)) C.output = false := by
    intro a
    by_contra h
    have h' : run C N (single (c a)) C.output = true := by simpa using h
    have he := run_mono hc (single (c a)) (pair (r a) (c a)) (fun w hw => by
      simp only [single, decide_eq_true_eq] at hw
      simp [pair, hw]) _ hout h'
    rw [hdiag a] at he
    contradiction
  have ports : ∀ a ∈ T, ∀ b ∈ T, run C N (pair (r a) (c b)) C.output = true →
      ∃ q ∈ reads C N (R a),
        (left C N q = R a ∧ right C N q = S b) ∨
        (right C N q = R a ∧ left C N q = S b) := by
    intro a ha b hb he
    obtain ⟨q, hq, hor, hp⟩ := joint_gate hc _ hout he (hsingR a) (hsingS b)
    have hqb := (gateWires_iff.mp hq).2
    have hl : q ∈ reads C N (left C N q) := mem_reads.mpr ⟨hq, Or.inl rfl⟩
    have hr' : q ∈ reads C N (right C N q) := mem_reads.mpr ⟨hq, Or.inr rfl⟩
    rcases hp with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
    · have h₁ : left C N q = R a := and_port hqb hl hor (hgood a ha).1 (hr a) ha'
      have h₂ : right C N q = S b := and_port hqb hr' hor (hgood b hb).2 (hci b) hb'
      exact ⟨q, h₁ ▸ hl, Or.inl ⟨h₁, h₂⟩⟩
    · have h₁ : right C N q = R a := and_port hqb hr' hor (hgood a ha).1 (hr a) ha'
      have h₂ : left C N q = S b := and_port hqb hl hor (hgood b hb).2 (hci b) hb'
      exact ⟨q, h₁ ▸ hr', Or.inr ⟨h₁, h₂⟩⟩
  have hthree : T.card ≤ 3 := by
    apply sparse_rows_le_three T (fun a b => run C N (pair (r a) (c b)) C.output)
    · intro a _ b _ hn
      exact hcross a b hn
    · intro a ha b hb d hd h₁ h₂
      obtain ⟨q, hq, hp⟩ := ports a ha b hb h₁
      obtain ⟨v, hv, hp'⟩ := ports a ha d hd h₂
      have hqv := reader_unique (hgood a ha).1 hq hv
      subst v
      have hne := (gate_data hc (mem_reads.mp hq).1).2.2.2
      rcases hp with hl | hr' <;> rcases hp' with hl' | hr''
      · exact hic (hl.2.symm.trans hl'.2)
      · exact (hne (hl.1.trans hr''.1.symm)).elim
      · exact (hne (hl'.1.trans hr'.1.symm)).elim
      · exact hic (hr'.2.symm.trans hr''.2)
  omega

lemma main_bound :
    ∀ (n m k s : ℕ) (A : Fin n → Fin m → Bool) (r : Fin k → Fin n) (c : Fin k → Fin m),
      (∀ a : Fin k, A (r a) (c a) = false) →
      (∀ a b : Fin k, a ≠ b → A (r a) (c b) = true ∨ A (r b) (c a) = true) →
      RepSizeAtMost A s → 5 * k ≤ 2 * s + 9 := by
  classical
  intro n m k s A r c hdiag hcross hsize
  by_cases hk : k ≤ 1
  · omega
  let a₀ : Fin k := ⟨0, by omega⟩
  let a₁ : Fin k := ⟨1, by omega⟩
  have hne : a₀ ≠ a₁ := by
    intro h
    have he := congrArg Fin.val h
    change 0 = 1 at he
    omega
  have hnm : 0 < n + m := by have := (r a₀).isLt; omega
  have hex : ∃ t, RepSizeAtMost A t := ⟨s, hsize⟩
  obtain ⟨C, hm, hsz, hrep⟩ := Nat.find_spec hex
  have hmin : ∀ C', Monotone2 C' → Represents A C' → C.size ≤ C'.size :=
    fun _ hm' hrep' => hsz.trans (Nat.find_min' hex ⟨_, hm', le_rfl, hrep'⟩)
  have hs : C.gates.length ≤ s := hsz.trans (Nat.find_min' hex hsize)
  obtain ⟨a, b, hab⟩ : ∃ a b, A (r a) (c b) = true :=
    (hcross a₀ a₁ hne).elim (fun h => ⟨a₀, a₁, h⟩) (fun h => ⟨a₁, a₀, h⟩)
  have hlow : n + m ≤ C.output := by
    by_contra! h
    have he := hrep (r a) (c b)
    rw [eval_eq_val, val_input C _ _ (by simpa [oneEach_length] using h),
      pair_input _ _ _ h, hab, pair, decide_eq_true_eq] at he
    rcases he with he | he
    · have hd := hrep (r a) (c a)
      rw [eval_eq_val, val_input C _ _ (by simpa [oneEach_length] using h),
        pair_input _ _ _ h, hdiag a] at hd
      simp [pair, he] at hd
    · have hd := hrep (r b) (c b)
      rw [eval_eq_val, val_input C _ _ (by simpa [oneEach_length] using h),
        pair_input _ _ _ h, hdiag b] at hd
      simp [pair, he] at hd
  have hhigh : C.output < n + m + C.gates.length := by
    by_contra! h
    have he := hrep (r a) (c b)
    rw [eval_eq_val, val_ge C _ _ (by simpa [oneEach_length] using h), hab] at he
    contradiction
  obtain ⟨hc, hlast⟩ := minimal_clean hnm (r a₀) (c a₀) (hdiag a₀) C hm hrep hmin hlow hhigh
  have ho : stop C (n + m) hc C.output = C.output := by
    apply stop_fixed
    rintro ⟨q, hq⟩
    have hm := forward_mem hq
    have hlt := reads_increases hc hm
    have hqb := (gateWires_iff.mp (mem_reads.mp hm).1).2
    omega
  let R := fun a => (r a).val
  let S := fun a => n + (c a).val
  have hr : ∀ a, R a < n + m := fun a => by have := (r a).isLt; change (r a).val < _; omega
  have hci : ∀ a, S a < n + m := fun a => by have := (c a).isLt; change n + (c a).val < _; omega
  have hdis : ∀ a b, R a ≠ S b := by
    intro a b
    have := (r a).isLt
    change (r a).val ≠ n + (c b).val
    omega
  have hd : ∀ a, run C (n + m) (pair (R a) (S a)) C.output = false :=
    fun a => (pair_rep hrep (r a) (c a)).trans (hdiag a)
  have ht : ∀ a b, a ≠ b → run C (n + m) (pair (R a) (S b)) C.output = true ∨
      run C (n + m) (pair (R b) (S a)) C.output = true := by
    intro a b hab
    change run C (n + m) (pair (r a) (n + (c b).val)) C.output = true ∨
      run C (n + m) (pair (r b) (n + (c a).val)) C.output = true
    rw [pair_rep hrep, pair_rep hrep]
    exact hcross a b hab
  obtain ⟨hR, hS⟩ := side_swap hd ht
  have hiR := stops_injective hc hhigh ho hr hR
  have hiS := stops_injective hc hhigh ho hci hS
  have hu := used_lower hc (gateWires_iff.mpr ⟨hlow, hhigh⟩) hr hci hdis hR hS
    (fun _ _ h => hiR (congrArg (stop C (n + m) hc) h))
    (fun _ _ h => hiS (congrArg (stop C (n + m) hc) h))
  have he := excess_bound hc (gateWires_iff.mpr ⟨hlow, hhigh⟩)
  have hl := shared_lower hc hhigh hr hci hiR hiS hd ht
  omega

end PEqualNP.Outside.L_meta_7628

theorem PEqualNP.Outside.L_meta_7628 :
    ∀ (n m k s : ℕ) (A : Fin n → Fin m → Bool) (r : Fin k → Fin n) (c : Fin k → Fin m), (∀ a : Fin k, A (r a) (c a) = false) → (∀ a b : Fin k, a ≠ b → A (r a) (c b) = true ∨ A (r b) (c a) = true) → PEqualNP.Represents.RepSizeAtMost A s → 5 * k ≤ 2 * s + 9 :=
  PEqualNP.Outside.L_meta_7628.main_bound
