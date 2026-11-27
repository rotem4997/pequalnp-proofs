import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7147

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def LT (n : ℕ) (u v : Fin n) : Bool := decide (u < v)

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

lemma op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  have hop' : op = GateOp.and ∨ op = GateOp.or := by simpa using hop
  rcases hop' with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      have hm : l₁[i] ∈ l₁ := List.getElem_mem hi1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
      exact h _ hm
    have h2 := hle i h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h2
    exact h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem ha
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hget
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma W_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (W gs w₁).getD i false = true → (W gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem g hg'))
    · rw [step_len, step_len, hlen]
    · intro i hi
      by_cases hlt : i < w₁.length
      · unfold step at hi ⊢
        rw [getD_append_lt w₁ _ i hlt] at hi
        rw [getD_append_lt w₂ _ i (by omega)]
        exact hle i hi
      · by_cases heq : i = w₁.length
        · subst heq
          unfold step at hi ⊢
          rw [getD_append_len] at hi
          rw [hlen, getD_append_len]
          apply op_mono g.op (hm g (List.mem_cons_self ..)) _ _ (by simp) _ hi
          intro k hk
          by_cases hklt : k < g.inputs.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hklt)] at hk ⊢
            simp only [Option.getD_some, List.getElem_map] at hk ⊢
            exact hle _ hk
          · rw [getD_ge _ _ (by simp; omega)] at hk
            exact False.elim (Bool.false_ne_true hk)
        · rw [getD_ge _ _ (by rw [step_len]; omega)] at hi
          exact False.elim (Bool.false_ne_true hi)

lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true :=
  W_mono C.gates (fun g hg => (hm g hg).1) x y hlen hle C.output

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

lemma minimal_clean (n : ℕ) (hn : 2 ≤ n) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (LT n) C)
    (hmin : ∀ C', Monotone2 C' → Represents (LT n) C' → C.size ≤ C'.size) :
    CleanCircuit (2 * n) C ∧ 1 ≤ C.gates.length ∧ C.output = 2 * n + (C.gates.length - 1) := by
  have hlt01 : LT n ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by simp [LT]
  have hlt00 : LT n ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by simp [LT]
  have hout_ge : 2 * n ≤ C.output := by
    by_contra hlt
    push Not at hlt
    by_cases h1 : C.output < n
    · have h := hr ⟨C.output, h1⟩ ⟨0, by omega⟩
      rw [eval_eq_val, val_input C _ _ (by rw [oneEach_length]; omega), oneEach_getD] at h
      simp [h1, LT] at h
    · have h2 : C.output - n < n := by omega
      have h := hr ⟨n - 1, by omega⟩ ⟨C.output - n, h2⟩
      rw [eval_eq_val, val_input C _ _ (by rw [oneEach_length]; omega), oneEach_getD] at h
      have hnlt : ¬ (n - 1 < C.output - n) := by omega
      have hlt2 : C.output < n + n := by omega
      simp [h1, hlt2, LT, hnlt] at h
  have hout_lt : C.output < 2 * n + C.gates.length := by
    by_contra hge
    push Not at hge
    have h := hr ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [eval_eq_val, val_ge C _ _ (by rw [oneEach_length]; omega)] at h
    rw [hlt01] at h
    exact Bool.false_ne_true h
  have hpos : 1 ≤ C.gates.length := by omega
  have hbin : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, C.gates[j].inputs = [a, b] ∧ a < 2 * n + j ∧ b < 2 * n + j ∧ a ≠ b := by
    intro j hj
    have hg := hm _ (List.getElem_mem hj)
    have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hg.1
    have hlen2 : C.gates[j].inputs.length ≤ 2 := hg.2
    match h_in : C.gates[j].inputs with
    | [] =>
      rcases hop with hop | hop
      · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = true := by
          intro x hx
          rw [← hx, val_gate C x j hj, hop, h_in]
          rfl
        have hne_out : C.output ≠ 2 * n + j := by
          intro heq
          have h := hr ⟨0, by omega⟩ ⟨0, by omega⟩
          rw [eval_eq_val, heq, hv _ (by rw [oneEach_length]; omega), hlt00] at h
          exact Bool.false_ne_true h.symm
        have hrep' : Represents (LT n) (elimConst C (2 * n) j true) := by
          intro u v
          rw [elimConst_eval C (2 * n) j true hm hj _ (by rw [oneEach_length]; omega)
            (hv _ (by rw [oneEach_length]; omega)) (fun _ => hne_out)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (2 * n) j true hm) hrep'
        rw [elimConst_size C (2 * n) j true hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
      · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = false := by
          intro x hx
          rw [← hx, val_gate C x j hj, hop, h_in]
          rfl
        have hrep' : Represents (LT n) (elimConst C (2 * n) j false) := by
          intro u v
          rw [elimConst_eval C (2 * n) j false hm hj _ (by rw [oneEach_length]; omega)
            (hv _ (by rw [oneEach_length]; omega)) (by simp)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (2 * n) j false hm) hrep'
        rw [elimConst_size C (2 * n) j false hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
    | [a] =>
      by_cases ha : a < 2 * n + j
      · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x a := by
          intro x hx
          rw [← hx, val_gate C x j hj, h_in]
          have ha' : a < x.length + j := by omega
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
        have hrep' : Represents (LT n) (elimAlias C (2 * n) j a) := by
          intro u v
          rw [elimAlias_eval C (2 * n) j a hj ha _ (by rw [oneEach_length]; omega)
            (Or.inl (hv _ (by rw [oneEach_length]; omega)))]
          exact hr u v
        have hle := hmin _ (elimAlias_mono C (2 * n) j a hm) hrep'
        rw [elimAlias_size C (2 * n) j a hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
      · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = false := by
          intro x hx
          rw [← hx, val_gate C x j hj, h_in]
          have ha' : ¬ (a < x.length + j) := by omega
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
        have hrep' : Represents (LT n) (elimConst C (2 * n) j false) := by
          intro u v
          rw [elimConst_eval C (2 * n) j false hm hj _ (by rw [oneEach_length]; omega)
            (hv _ (by rw [oneEach_length]; omega)) (by simp)]
          exact hr u v
        have hle := hmin _ (elimConst_mono C (2 * n) j false hm) hrep'
        rw [elimConst_size C (2 * n) j false hj] at hle
        change C.gates.length ≤ C.gates.length - 1 at hle
        omega
    | [a, b] =>
      by_cases ha : a < 2 * n + j
      · by_cases hb : b < 2 * n + j
        · by_cases hab : a = b
          · subst hab
            have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x a := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in]
              have ha' : a < x.length + j := by omega
              rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha']
            have hrep' : Represents (LT n) (elimAlias C (2 * n) j a) := by
              intro u v
              rw [elimAlias_eval C (2 * n) j a hj ha _ (by rw [oneEach_length]; omega)
                (Or.inl (hv _ (by rw [oneEach_length]; omega)))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (2 * n) j a hm) hrep'
            rw [elimAlias_size C (2 * n) j a hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · exact ⟨a, b, rfl, ha, hb, hab⟩
        · rcases hop with hop | hop
          · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = false := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have hb' : ¬ (b < x.length + j) := by omega
              simp [GateOp.eval, hb']
            have hrep' : Represents (LT n) (elimConst C (2 * n) j false) := by
              intro u v
              rw [elimConst_eval C (2 * n) j false hm hj _ (by rw [oneEach_length]; omega)
                (hv _ (by rw [oneEach_length]; omega)) (by simp)]
              exact hr u v
            have hle := hmin _ (elimConst_mono C (2 * n) j false hm) hrep'
            rw [elimConst_size C (2 * n) j false hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x a := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : a < x.length + j := by omega
              have hb' : ¬ (b < x.length + j) := by omega
              simp [GateOp.eval, ha', hb']
            have hrep' : Represents (LT n) (elimAlias C (2 * n) j a) := by
              intro u v
              rw [elimAlias_eval C (2 * n) j a hj ha _ (by rw [oneEach_length]; omega)
                (Or.inl (hv _ (by rw [oneEach_length]; omega)))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (2 * n) j a hm) hrep'
            rw [elimAlias_size C (2 * n) j a hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
      · by_cases hb : b < 2 * n + j
        · rcases hop with hop | hop
          · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = false := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : ¬ (a < x.length + j) := by omega
              simp [GateOp.eval, ha']
            have hrep' : Represents (LT n) (elimConst C (2 * n) j false) := by
              intro u v
              rw [elimConst_eval C (2 * n) j false hm hj _ (by rw [oneEach_length]; omega)
                (hv _ (by rw [oneEach_length]; omega)) (by simp)]
              exact hr u v
            have hle := hmin _ (elimConst_mono C (2 * n) j false hm) hrep'
            rw [elimConst_size C (2 * n) j false hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
          · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x b := by
              intro x hx
              rw [← hx, val_gate C x j hj, h_in, hop]
              have ha' : ¬ (a < x.length + j) := by omega
              have hb' : b < x.length + j := by omega
              simp [GateOp.eval, ha', hb']
            have hrep' : Represents (LT n) (elimAlias C (2 * n) j b) := by
              intro u v
              rw [elimAlias_eval C (2 * n) j b hj hb _ (by rw [oneEach_length]; omega)
                (Or.inl (hv _ (by rw [oneEach_length]; omega)))]
              exact hr u v
            have hle := hmin _ (elimAlias_mono C (2 * n) j b hm) hrep'
            rw [elimAlias_size C (2 * n) j b hj] at hle
            change C.gates.length ≤ C.gates.length - 1 at hle
            omega
        · have hv : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = false := by
            intro x hx
            rw [← hx, val_gate C x j hj, h_in]
            have ha' : ¬ (a < x.length + j) := by omega
            have hb' : ¬ (b < x.length + j) := by omega
            rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha', hb']
          have hrep' : Represents (LT n) (elimConst C (2 * n) j false) := by
            intro u v
            rw [elimConst_eval C (2 * n) j false hm hj _ (by rw [oneEach_length]; omega)
              (hv _ (by rw [oneEach_length]; omega)) (by simp)]
            exact hr u v
          have hle := hmin _ (elimConst_mono C (2 * n) j false hm) hrep'
          rw [elimConst_size C (2 * n) j false hj] at hle
          change C.gates.length ≤ C.gates.length - 1 at hle
          omega
    | _ :: _ :: _ :: _ =>
      rw [h_in] at hlen2
      simp at hlen2
  have hused : ∀ j, j < C.gates.length →
      C.output = 2 * n + j ∨ ∃ k, ∃ hk : k < C.gates.length, j < k ∧ 2 * n + j ∈ C.gates[k].inputs := by
    intro j hj
    by_contra h
    push Not at h
    have hrep' : Represents (LT n) (elimAlias C (2 * n) j 0) := by
      intro u v
      rw [elimAlias_eval C (2 * n) j 0 hj (by omega) _ (by rw [oneEach_length]; omega)
        (Or.inr ⟨h.1, fun k hk hjk => h.2 k hk hjk⟩)]
      exact hr u v
    have hle := hmin _ (elimAlias_mono C (2 * n) j 0 hm) hrep'
    rw [elimAlias_size C (2 * n) j 0 hj] at hle
    change C.gates.length ≤ C.gates.length - 1 at hle
    omega
  have hout_last : C.output = 2 * n + (C.gates.length - 1) := by
    rcases hused (C.gates.length - 1) (by omega) with h | ⟨k, hk, hlt, _⟩
    · exact h
    · omega
  exact ⟨⟨hm, hbin, hused⟩, hpos, hout_last⟩

-- Section 3: Zero-propagation circuit restriction

def isZero (Z : Finset ℕ) (C : Circuit) (N : ℕ) (w : ℕ) : Bool :=
  if w < N then
    decide (w ∈ Z)
  else if h2 : w - N < C.gates.length then
    let g := C.gates[w - N]
    if isAndOp g.op then
      g.inputs.any (fun i => if _ : i < w then isZero Z C N i else true)
    else
      g.inputs.all (fun i => if _ : i < w then isZero Z C N i else true)
  else
    true
termination_by w

def isKilled (Z : Finset ℕ) (C : Circuit) (N : ℕ) (j : ℕ) : Bool :=
  if hj : j < C.gates.length then
    (C.gates[j]).inputs.any (fun i => isZero Z C N i)
  else
    true

def keptCount (Z : Finset ℕ) (C : Circuit) (N : ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => !isKilled Z C N j)).card

def redir (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) (w : ℕ) : ℕ :=
  let D := N' + keptCount Z C N C.gates.length
  if isZero Z C N w then
    D
  else if w < N then
    match inv w with
    | some i => i
    | none => D
  else if h2 : w - N < C.gates.length then
    if !isKilled Z C N (w - N) then
      N' + keptCount Z C N (w - N)
    else
      match C.gates[w - N].inputs with
      | [a, b] =>
        if _ : a < w then
          if !isZero Z C N a then redir Z C N N' inv a
          else if _ : b < w then redir Z C N N' inv b
          else D
        else D
      | _ => D
  else
    D
termination_by w

def restrictGatesAux (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 =>
    let prev := restrictGatesAux Z C N N' inv k
    if hk : k < C.gates.length then
      if !isKilled Z C N k then
        let g := C.gates[k]
        prev ++ [{ op := g.op, inputs := g.inputs.map (redir Z C N N' inv) }]
      else
        prev
    else
      prev

def restrictCircuit (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) : Circuit :=
  { gates := restrictGatesAux Z C N N' inv C.gates.length
    output := redir Z C N N' inv C.output }

lemma isZero_input (Z : Finset ℕ) (C : Circuit) (N w : ℕ) (hw : w < N) :
    isZero Z C N w = decide (w ∈ Z) := by
  rw [isZero]
  simp [hw]

lemma isZero_gate (Z : Finset ℕ) (C : Circuit) (N j : ℕ) (hc : CleanCircuit N C)
    (hj : j < C.gates.length) :
    isZero Z C N (N + j) =
      if isAndOp C.gates[j].op then
        C.gates[j].inputs.any (fun i => isZero Z C N i)
      else
        C.gates[j].inputs.all (fun i => isZero Z C N i) := by
  rw [isZero]
  have h1 : ¬ (N + j < N) := by omega
  have h2 : N + j - N = j := by omega
  obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hj
  simp only [h1, ↓reduceIte, h2, hj, ↓reduceDIte, hab]
  cases isAndOp C.gates[j].op <;> simp [ha, hb]

lemma keptCount_succ (Z : Finset ℕ) (C : Circuit) (N k : ℕ) :
    keptCount Z C N (k + 1) =
      keptCount Z C N k + (if !isKilled Z C N k then 1 else 0) := by
  unfold keptCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma keptCount_mono (Z : Finset ℕ) (C : Circuit) (N : ℕ) {a b : ℕ} (h : a ≤ b) :
    keptCount Z C N a ≤ keptCount Z C N b := by
  unfold keptCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

lemma keptCount_strict_of_survive (Z : Finset ℕ) (C : Circuit) (N : ℕ) {j k : ℕ}
    (hjk : j < k) (hsurv : isKilled Z C N j = false) :
    keptCount Z C N j < keptCount Z C N k := by
  have h1 : keptCount Z C N (j + 1) ≤ keptCount Z C N k := keptCount_mono Z C N (by omega)
  rw [keptCount_succ, hsurv] at h1
  simp only [Bool.not_false, ↓reduceIte] at h1
  omega

lemma restrictGatesAux_length (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) :
    ∀ k ≤ C.gates.length, (restrictGatesAux Z C N N' inv k).length = keptCount Z C N k := by
  intro k
  induction k with
  | zero => intro _; simp [restrictGatesAux, keptCount]
  | succ k ih =>
    intro hk
    have hlt : k < C.gates.length := by omega
    unfold restrictGatesAux
    simp only [hlt, ↓reduceDIte]
    rw [keptCount_succ]
    split_ifs with hs
    · simp [ih (by omega)]
    · simp [ih (by omega)]

lemma restrictGatesAux_getElem (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) :
    ∀ (k : ℕ) (hk : k ≤ C.gates.length) (j : ℕ) (hj : j < k), (hs : isKilled Z C N j = false) →
      (hidx : keptCount Z C N j < (restrictGatesAux Z C N N' inv k).length) →
      (restrictGatesAux Z C N N' inv k)[keptCount Z C N j] =
        { op := (C.gates[j]'(by omega)).op
          inputs := (C.gates[j]'(by omega)).inputs.map (redir Z C N N' inv) } := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj hs hidx
    have hlt : k < C.gates.length := by omega
    by_cases hjk : j = k
    · subst hjk
      have hprev : (restrictGatesAux Z C N N' inv j).length = keptCount Z C N j :=
        restrictGatesAux_length Z C N N' inv j (by omega)
      simp only [restrictGatesAux, hlt, ↓reduceDIte, hs, Bool.not_false, ↓reduceIte]
      rw [List.getElem_append_right (by rw [hprev])]
      simp [hprev]
    · have hjlt : j < k := by omega
      have hprev : (restrictGatesAux Z C N N' inv k).length = keptCount Z C N k :=
        restrictGatesAux_length Z C N N' inv k (by omega)
      have hlt_kc : keptCount Z C N j < keptCount Z C N k :=
        keptCount_strict_of_survive Z C N hjlt hs
      simp only [restrictGatesAux, hlt, ↓reduceDIte]
      split_ifs with hsk
      · rw [List.getElem_append_left (by omega)]
        exact ih (by omega) j hjlt hs (by omega)
      · exact ih (by omega) j hjlt hs (by omega)

lemma restrictGatesAux_mono (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ)
    (hm : Monotone2 C) :
    ∀ k, ∀ g ∈ restrictGatesAux Z C N N' inv k,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [restrictGatesAux] at hg
  | succ k ih =>
    intro g hg
    unfold restrictGatesAux at hg
    split_ifs at hg with hk hs
    · simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with h1 | rfl
      · exact ih g h1
      · have h := hm _ (List.getElem_mem hk)
        exact ⟨h.1, by simp [h.2]⟩
    · exact ih g hg
    · exact ih g hg

lemma restrictCircuit_mono (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ)
    (hm : Monotone2 C) : Monotone2 (restrictCircuit Z C N N' inv) :=
  restrictGatesAux_mono Z C N N' inv hm C.gates.length

lemma restrictCircuit_size (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ) :
    (restrictCircuit Z C N N' inv).size +
      ((Finset.range C.gates.length).filter (fun j => isKilled Z C N j)).card = C.gates.length := by
  have h1 : (restrictCircuit Z C N N' inv).size = keptCount Z C N C.gates.length :=
    restrictGatesAux_length Z C N N' inv C.gates.length (le_refl _)
  rw [h1]
  unfold keptCount
  have hdisj : Disjoint
      ((Finset.range C.gates.length).filter (fun j => !isKilled Z C N j))
      ((Finset.range C.gates.length).filter (fun j => isKilled Z C N j)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [Finset.mem_filter] at hj1 hj2
    rw [hj2.2] at hj1
    exact Bool.false_ne_true hj1.2
  have hunion :
      ((Finset.range C.gates.length).filter (fun j => !isKilled Z C N j)) ∪
      ((Finset.range C.gates.length).filter (fun j => isKilled Z C N j)) =
      Finset.range C.gates.length := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      cases hk : isKilled Z C N j
      · exact Or.inl ⟨h, by simp⟩
      · exact Or.inr ⟨h, rfl⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]

lemma isZero_val_false (Z : Finset ℕ) (C : Circuit) (N : ℕ) (hc : CleanCircuit N C)
    (x : List Bool) (hx : x.length = N)
    (hxZ : ∀ w ∈ Z, x.getD w false = false) :
    ∀ w, isZero Z C N w = true → val C x w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hz
    by_cases h1 : w < N
    · rw [isZero_input Z C N w h1, decide_eq_true_eq] at hz
      rw [val_input C x w (by omega)]
      exact hxZ w hz
    · by_cases h2 : w - N < C.gates.length
      · set j := w - N
        have hw : w = N + j := by omega
        rw [hw] at hz ⊢
        rw [isZero_gate Z C N j hc h2] at hz
        rw [← hx, val_gate C x j h2]
        obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j h2
        have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
          have h := (hc.1 _ (List.getElem_mem h2)).1
          simpa using h
        rcases hop with hop | hop
        · simp only [hop, isAndOp, ↓reduceIte, hab, List.any_cons, List.any_nil, Bool.or_false,
            Bool.or_eq_true] at hz
          have ha' : a < x.length + j := by omega
          have hb' : b < x.length + j := by omega
          simp only [hop, hab, List.map_cons, List.map_nil, ha', hb', ↓reduceIte, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases hz with hza | hzb
          · rw [ih a (by omega) hza]; rfl
          · rw [ih b (by omega) hzb]; simp
        · simp only [hop, isAndOp, Bool.false_eq_true, ↓reduceIte, hab, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true] at hz
          have ha' : a < x.length + j := by omega
          have hb' : b < x.length + j := by omega
          simp only [hop, hab, List.map_cons, List.map_nil, ha', hb', ↓reduceIte, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ih a (by omega) hz.1, ih b (by omega) hz.2]
          rfl
      · exact val_ge C x w (by omega)

lemma redir_lt_or_D (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ)
    (hc : CleanCircuit N C)
    (hinv : ∀ w i, inv w = some i → i < N') :
    ∀ w j, j ≤ C.gates.length → w < N + j →
      redir Z C N N' inv w = N' + keptCount Z C N C.gates.length ∨
      redir Z C N N' inv w < N' + keptCount Z C N j := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro j hj hw
    rw [redir]
    split_ifs with hz hlt h2 hs
    · left; rfl
    · cases h : inv w with
      | none => left; rfl
      | some i =>
        right
        dsimp only
        have hi := hinv w i h
        omega
    · right
      have hlt_j : w - N < j := by omega
      have hs' : isKilled Z C N (w - N) = false := by
        cases h : isKilled Z C N (w - N)
        · rfl
        · simp [h] at hs
      have hkc := keptCount_strict_of_survive Z C N hlt_j hs'
      omega
    · obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 (w - N) h2
      simp only [hab]
      have haw : a < w := by omega
      have hbw : b < w := by omega
      split_ifs with hza
      · exact ih a haw j hj (by omega)
      · exact ih b hbw j hj (by omega)
    · left; rfl

lemma restrictCircuit_val (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ)
    (hc : CleanCircuit N C)
    (x' x : List Bool) (hx' : x'.length = N') (hx : x.length = N)
    (hinv : ∀ w i, inv w = some i → i < N')
    (hxZ : ∀ w ∈ Z, x.getD w false = false)
    (hlift : ∀ w < N, w ∉ Z →
      match inv w with
      | some i => x.getD w false = x'.getD i false
      | none => x.getD w false = false) :
    ∀ w < N + C.gates.length,
      val (restrictCircuit Z C N N' inv) x' (redir Z C N N' inv w) = val C x w := by
  subst hx
  subst hx'
  set C' := restrictCircuit Z C x.length x'.length inv
  have hC'len : C'.gates.length = keptCount Z C x.length C.gates.length :=
    restrictGatesAux_length Z C x.length x'.length inv C.gates.length (le_refl _)
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hz : isZero Z C x.length w = true
    · have hred : redir Z C x.length x'.length inv w =
          x'.length + keptCount Z C x.length C.gates.length := by
        rw [redir]; simp [hz]
      rw [hred, val_ge C' x' _ (by rw [hC'len]), isZero_val_false Z C x.length hc x rfl hxZ w hz]
    · have hzf : isZero Z C x.length w = false := Bool.eq_false_iff.mpr hz
      by_cases hlt : w < x.length
      · have hnotZ : w ∉ Z := by
          rw [isZero_input Z C x.length w hlt, decide_eq_false_iff_not] at hzf
          exact hzf
        have hred : redir Z C x.length x'.length inv w =
            match inv w with
            | some i => i
            | none => x'.length + keptCount Z C x.length C.gates.length := by
          rw [redir]; simp [hzf, hlt]
        rw [hred, val_input C x w hlt]
        have hl := hlift w hlt hnotZ
        cases hinvw : inv w with
        | none =>
          rw [hinvw] at hl
          rw [val_ge C' x' _ (by rw [hC'len]), hl]
        | some i =>
          rw [hinvw] at hl
          have hi := hinv w i hinvw
          rw [val_input C' x' i hi, hl]
      · set j := w - x.length with hj_def
        have hj : j < C.gates.length := by omega
        have hw_eq : w = x.length + j := by omega
        obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hj
        by_cases hsurv : isKilled Z C x.length j = false
        · have hred : redir Z C x.length x'.length inv w =
              x'.length + keptCount Z C x.length j := by
            rw [redir]
            simp only [hzf, Bool.false_eq_true, ↓reduceIte, hlt, ← hj_def, hj, ↓reduceDIte,
              hsurv, Bool.not_false]
          rw [hred]
          have hklt : keptCount Z C x.length j < C'.gates.length := by
            rw [hC'len]
            exact keptCount_strict_of_survive Z C x.length hj hsurv
          rw [val_gate C' x' (keptCount Z C x.length j) hklt]
          have hgate : C'.gates[keptCount Z C x.length j] =
              { op := C.gates[j].op
                inputs := C.gates[j].inputs.map (redir Z C x.length x'.length inv) } :=
            restrictGatesAux_getElem Z C x.length x'.length inv C.gates.length (le_refl _) j hj hsurv hklt
          rw [hgate, hw_eq, val_gate C x j hj]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi_mem
          have hi_lt : i < x.length + j := by
            rw [hab] at hi_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_mem
            rcases hi_mem with rfl | rfl <;> omega
          simp only [Function.comp_apply, hi_lt, ↓reduceIte]
          have hih := ih i (by omega) (by omega)
          rcases redir_lt_or_D Z C x.length x'.length inv hc hinv i j (Nat.le_of_lt hj) hi_lt with hD | hlt'
          · have hge' : ¬ (redir Z C x.length x'.length inv i <
                x'.length + keptCount Z C x.length j) := by
              rw [hD]
              have hle := keptCount_mono Z C x.length (Nat.le_of_lt hj)
              omega
            simp only [hge', ↓reduceIte]
            rw [← hih, hD, val_ge C' x' _ (by rw [hC'len])]
          · simp only [hlt', ↓reduceIte]
            exact hih
        · have hkill : isKilled Z C x.length j = true := by
            cases hk : isKilled Z C x.length j
            · exact False.elim (hsurv hk)
            · rfl
          have hop : C.gates[j].op = GateOp.or := by
            have h := (hc.1 _ (List.getElem_mem hj)).1
            have h' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using h
            rcases h' with hand | hor
            · exfalso
              have hzero : isZero Z C x.length (x.length + j) = true := by
                rw [isZero_gate Z C x.length j hc hj, hand]
                simp only [isAndOp, ↓reduceIte]
                unfold isKilled at hkill
                simp only [hj, ↓reduceDIte] at hkill
                exact hkill
              rw [← hw_eq] at hzero
              exact hz hzero
            · exact hor
          have hnotboth : ¬ (isZero Z C x.length a = true ∧ isZero Z C x.length b = true) := by
            rintro ⟨hza, hzb⟩
            have hzero : isZero Z C x.length (x.length + j) = true := by
              rw [isZero_gate Z C x.length j hc hj, hop, hab]
              simp [isAndOp, hza, hzb]
            rw [← hw_eq] at hzero
            exact hz hzero
          have hor_kill : isZero Z C x.length a = true ∨ isZero Z C x.length b = true := by
            unfold isKilled at hkill
            simp only [hj, ↓reduceDIte, hab, List.any_cons, List.any_nil, Bool.or_false,
              Bool.or_eq_true] at hkill
            exact hkill
          have haw : a < w := by omega
          have hbw : b < w := by omega
          have hred : redir Z C x.length x'.length inv w =
              if !isZero Z C x.length a then redir Z C x.length x'.length inv a
              else redir Z C x.length x'.length inv b := by
            rw [redir]
            simp only [hzf, Bool.false_eq_true, ↓reduceIte, hlt, ← hj_def, hj, ↓reduceDIte,
              hkill, Bool.not_true, hab, haw, hbw]
          rw [hred, hw_eq, val_gate C x j hj, hop, hab]
          simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          by_cases hza : isZero Z C x.length a = true
          · simp only [hza, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [ih b hbw (by omega), isZero_val_false Z C x.length hc x rfl hxZ a hza, Bool.false_or]
          · have hzb : isZero Z C x.length b = true := hor_kill.resolve_left hza
            have hza' : isZero Z C x.length a = false := Bool.eq_false_iff.mpr hza
            simp only [hza', Bool.not_false, ↓reduceIte]
            rw [ih a haw (by omega), isZero_val_false Z C x.length hc x rfl hxZ b hzb, Bool.or_false]

lemma restrictCircuit_eval (Z : Finset ℕ) (C : Circuit) (N N' : ℕ) (inv : ℕ → Option ℕ)
    (hc : CleanCircuit N C) (hout : C.output < N + C.gates.length)
    (x' x : List Bool) (hx' : x'.length = N') (hx : x.length = N)
    (hinv : ∀ w i, inv w = some i → i < N')
    (hxZ : ∀ w ∈ Z, x.getD w false = false)
    (hlift : ∀ w < N, w ∉ Z →
      match inv w with
      | some i => x.getD w false = x'.getD i false
      | none => x.getD w false = false) :
    (restrictCircuit Z C N N' inv).eval x' = C.eval x :=
  restrictCircuit_val Z C N N' inv hc x' x hx' hx hinv hxZ hlift C.output hout

-- Section 4: Universal Counting Identity

def readers (C : Circuit) (w : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j =>
    if hj : j < C.gates.length then decide (w ∈ C.gates[j].inputs) else false)

def deg (C : Circuit) (w : ℕ) : ℕ := (readers C w).card

def ZGates (Z : Finset ℕ) (C : Circuit) (N : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => isZero Z C N (N + j))

def KGates (Z : Finset ℕ) (C : Circuit) (N : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => isKilled Z C N j)

def inZero (Z : Finset ℕ) (C : Circuit) (N : ℕ) (j : ℕ) : ℕ :=
  if hj : j < C.gates.length then
    (C.gates[j].inputs.filter (fun u => isZero Z C N u)).length
  else 0

lemma mem_readers_iff (C : Circuit) (w j : ℕ) :
    j ∈ readers C w ↔ ∃ hj : j < C.gates.length, w ∈ C.gates[j].inputs := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, h⟩
    simp only [hj, ↓reduceDIte, decide_eq_true_eq] at h
    exact ⟨hj, h⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, by simp [hj, h]⟩

lemma ZGates_subset_KGates (Z : Finset ℕ) (C : Circuit) (N : ℕ) (hc : CleanCircuit N C) :
    ZGates Z C N ⊆ KGates Z C N := by
  intro j hj
  unfold ZGates at hj
  rw [Finset.mem_filter, Finset.mem_range] at hj
  unfold KGates
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨hj.1, ?_⟩
  have hzg := hj.2
  rw [isZero_gate Z C N j hc hj.1] at hzg
  obtain ⟨a, b, hab, _, _, _⟩ := hc.2.1 j hj.1
  unfold isKilled
  simp only [hj.1, ↓reduceDIte, hab, List.any_cons, List.any_nil, Bool.or_false]
  split_ifs at hzg
  · simp only [hab, List.any_cons, List.any_nil, Bool.or_false] at hzg
    exact hzg
  · simp only [hab, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hzg
    simp [hzg.1]

lemma inZero_eq_pair (Z : Finset ℕ) (C : Circuit) (N j a b : ℕ)
    (hj : j < C.gates.length) (hab : C.gates[j].inputs = [a, b]) :
    inZero Z C N j =
      (if isZero Z C N a then 1 else 0) + (if isZero Z C N b then 1 else 0) := by
  unfold inZero
  simp only [hj, ↓reduceDIte, hab, List.filter_cons, List.filter_nil]
  cases isZero Z C N a <;> cases isZero Z C N b <;> rfl

lemma inZero_le_two (Z : Finset ℕ) (C : Circuit) (N j : ℕ) (hc : CleanCircuit N C)
    (hj : j < C.gates.length) : inZero Z C N j ≤ 2 := by
  obtain ⟨a, b, hab, _, _, _⟩ := hc.2.1 j hj
  rw [inZero_eq_pair Z C N j a b hj hab]
  split_ifs <;> omega

lemma inZero_eq_zero_of_not_killed (Z : Finset ℕ) (C : Circuit) (N j : ℕ) (hc : CleanCircuit N C)
    (hj : j < C.gates.length) (hk : j ∉ KGates Z C N) : inZero Z C N j = 0 := by
  obtain ⟨a, b, hab, _, _, _⟩ := hc.2.1 j hj
  rw [inZero_eq_pair Z C N j a b hj hab]
  unfold KGates isKilled at hk
  rw [Finset.mem_filter, Finset.mem_range] at hk
  push Not at hk
  have h1 := hk hj
  simp only [hj, ↓reduceDIte, hab, List.any_cons, List.any_nil, Bool.or_false] at h1
  cases hza : isZero Z C N a <;> cases hzb : isZero Z C N b <;> simp_all

lemma inZero_eq_one_of_killed_not_zero (Z : Finset ℕ) (C : Circuit) (N j : ℕ)
    (hc : CleanCircuit N C) (hj : j < C.gates.length)
    (hk : j ∈ KGates Z C N) (hz : j ∉ ZGates Z C N) : inZero Z C N j = 1 := by
  obtain ⟨a, b, hab, _, _, _⟩ := hc.2.1 j hj
  rw [inZero_eq_pair Z C N j a b hj hab]
  unfold KGates isKilled at hk
  rw [Finset.mem_filter, Finset.mem_range] at hk
  have h1 := hk.2
  simp only [hj, ↓reduceDIte, hab, List.any_cons, List.any_nil, Bool.or_false] at h1
  unfold ZGates at hz
  rw [Finset.mem_filter, Finset.mem_range] at hz
  push Not at hz
  have h2 := hz hj
  rw [isZero_gate Z C N j hc hj] at h2
  split_ifs at h2 with hop
  · simp only [hab, List.any_cons, List.any_nil, Bool.or_false] at h2
    exact False.elim (h2 h1)
  · simp only [hab, List.all_cons, List.all_nil, Bool.and_true] at h2
    cases hza : isZero Z C N a <;> cases hzb : isZero Z C N b <;> simp_all

lemma killed_card_identity (Z : Finset ℕ) (C : Circuit) (N : ℕ) (hc : CleanCircuit N C)
    (hZ : ∀ w ∈ Z, w < N)
    (hout_nz : isZero Z C N C.output = false) :
    (KGates Z C N).card =
      (∑ w ∈ Z, deg C w) +
      (∑ j ∈ ZGates Z C N, (deg C (N + j) - 1)) +
      (∑ j ∈ ZGates Z C N, (2 - inZero Z C N j)) := by
  let S := Finset.range C.gates.length
  let ZW := Z ∪ (ZGates Z C N).image (fun j => N + j)
  have hdisj : Disjoint Z ((ZGates Z C N).image (fun j => N + j)) := by
    rw [Finset.disjoint_left]
    intro w hw hmem
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨j, _, rfl⟩
    have := hZ _ hw
    omega
  have hmem_ZW : ∀ u < N + C.gates.length, u ∈ ZW ↔ isZero Z C N u = true := by
    intro u hu
    simp only [ZW, Finset.mem_union, Finset.mem_image, ZGates, Finset.mem_filter, Finset.mem_range]
    by_cases hlt : u < N
    · rw [isZero_input Z C N u hlt, decide_eq_true_eq]
      constructor
      · rintro (h | ⟨j, _, rfl⟩)
        · exact h
        · omega
      · exact Or.inl
    · constructor
      · rintro (h | ⟨j, ⟨_, hzj⟩, rfl⟩)
        · have := hZ u h; omega
        · exact hzj
      · intro hzu
        right
        exact ⟨u - N, ⟨by omega, by rwa [show N + (u - N) = u by omega]⟩, by omega⟩
  have hdouble :
      ∑ j ∈ S, inZero Z C N j = ∑ u ∈ ZW, deg C u := by
    have h1 : ∀ j ∈ S,
        inZero Z C N j = ∑ u ∈ ZW, (if j ∈ readers C u then 1 else 0) := by
      intro j hj
      have hj' : j < C.gates.length := Finset.mem_range.mp hj
      obtain ⟨a, b, hab, ha, hb, hne⟩ := hc.2.1 j hj'
      rw [inZero_eq_pair Z C N j a b hj' hab]
      have hite : ∀ u ∈ ZW,
          (if j ∈ readers C u then (1 : ℕ) else 0) =
          (if u = a then 1 else 0) + (if u = b then 1 else 0) := by
        intro u _
        by_cases hua : u = a
        · subst hua
          have hmem : j ∈ readers C u := (mem_readers_iff C u j).mpr ⟨hj', by rw [hab]; simp⟩
          simp [hmem, hne]
        · by_cases hub : u = b
          · subst hub
            have hmem : j ∈ readers C u := (mem_readers_iff C u j).mpr ⟨hj', by rw [hab]; simp⟩
            simp [hmem, hua]
          · have hnot : j ∉ readers C u := by
              rw [mem_readers_iff]
              rintro ⟨_, hm⟩
              rw [hab] at hm
              simp [hua, hub] at hm
            simp [hnot, hua, hub]
      rw [Finset.sum_congr rfl hite, Finset.sum_add_distrib]
      have hsum_a : (∑ u ∈ ZW, if u = a then 1 else 0) = if isZero Z C N a then 1 else 0 := by
        rw [Finset.sum_ite_eq']
        have := hmem_ZW a (by omega)
        by_cases h : a ∈ ZW
        · simp [h, this.mp h]
        · have h' : ¬ (isZero Z C N a = true) := fun hz => h (this.mpr hz)
          simp [h, h']
      have hsum_b : (∑ u ∈ ZW, if u = b then 1 else 0) = if isZero Z C N b then 1 else 0 := by
        rw [Finset.sum_ite_eq']
        have := hmem_ZW b (by omega)
        by_cases h : b ∈ ZW
        · simp [h, this.mp h]
        · have h' : ¬ (isZero Z C N b = true) := fun hz => h (this.mpr hz)
          simp [h, h']
      rw [hsum_a, hsum_b]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    unfold deg
    have hsub : readers C u ⊆ S := Finset.filter_subset _ _
    rw [← Finset.card_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hsub h, h⟩⟩
  have hrhs : ∑ u ∈ ZW, deg C u = (∑ w ∈ Z, deg C w) + ∑ j ∈ ZGates Z C N, deg C (N + j) := by
    rw [Finset.sum_union hdisj, Finset.sum_image]
    intro a _ b _ hab
    dsimp only at hab
    omega
  have hlhs : ∑ j ∈ S, inZero Z C N j =
      ((KGates Z C N) \ (ZGates Z C N)).card + ∑ j ∈ ZGates Z C N, inZero Z C N j := by
    have hKsub : KGates Z C N ⊆ S := Finset.filter_subset _ _
    have hZsub : ZGates Z C N ⊆ KGates Z C N := ZGates_subset_KGates Z C N hc
    rw [← Finset.sum_sdiff hKsub]
    have hzero_out : ∑ j ∈ S \ KGates Z C N, inZero Z C N j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_sdiff] at hj
      exact inZero_eq_zero_of_not_killed Z C N j hc (Finset.mem_range.mp hj.1) hj.2
    rw [hzero_out, zero_add, ← Finset.sum_sdiff hZsub]
    have hones : ∑ j ∈ KGates Z C N \ ZGates Z C N, inZero Z C N j =
        (KGates Z C N \ ZGates Z C N).card := by
      calc ∑ j ∈ KGates Z C N \ ZGates Z C N, inZero Z C N j
          = ∑ _j ∈ KGates Z C N \ ZGates Z C N, 1 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_sdiff] at hj
            exact inZero_eq_one_of_killed_not_zero Z C N j hc
              (Finset.mem_range.mp (hKsub hj.1)) hj.1 hj.2
        _ = (KGates Z C N \ ZGates Z C N).card := by simp
    rw [hones]
  have hdeg_pos : ∀ j ∈ ZGates Z C N, 1 ≤ deg C (N + j) := by
    intro j hj
    unfold ZGates at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have hne : C.output ≠ N + j := by
      intro heq
      rw [heq, hj.2] at hout_nz
      exact Bool.false_ne_true hout_nz.symm
    rcases hc.2.2 j hj.1 with h | ⟨k, hk, _, hmem⟩
    · exact False.elim (hne h)
    · have hkmem : k ∈ readers C (N + j) := (mem_readers_iff C (N + j) k).mpr ⟨hk, hmem⟩
      exact Finset.card_pos.mpr ⟨k, hkmem⟩
  have hsum_deg : ∑ j ∈ ZGates Z C N, deg C (N + j) =
      (ZGates Z C N).card + ∑ j ∈ ZGates Z C N, (deg C (N + j) - 1) := by
    have h1 : ∀ j ∈ ZGates Z C N, deg C (N + j) = 1 + (deg C (N + j) - 1) := by
      intro j hj
      have := hdeg_pos j hj
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    simp
  have hsum_in : (∑ j ∈ ZGates Z C N, inZero Z C N j) +
      (∑ j ∈ ZGates Z C N, (2 - inZero Z C N j)) = 2 * (ZGates Z C N).card := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ j ∈ ZGates Z C N, inZero Z C N j + (2 - inZero Z C N j) = 2 := by
      intro j hj
      unfold ZGates at hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have := inZero_le_two Z C N j hc hj.1
      omega
    rw [Finset.sum_congr rfl h1]
    simp [Nat.mul_comm]
  have hcard_sdiff : (KGates Z C N \ ZGates Z C N).card + (ZGates Z C N).card =
      (KGates Z C N).card :=
    Finset.card_sdiff_add_card_eq_card (ZGates_subset_KGates Z C N hc)
  omega

-- Section 5: Structural properties, Move 1, Move 2, and strong induction

def Active (n w : ℕ) : Prop := w < n - 1 ∨ (n < w ∧ w < 2 * n)

lemma eval_eq_of_iso (C : Circuit) (N : ℕ) (hc : CleanCircuit N C)
    (hout : C.output < N + C.gates.length)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (Blocked : ℕ → Prop)
    (h_inp : ∀ i < N, ¬ Blocked i → x.getD i false = y.getD i false)
    (h_out : ¬ Blocked C.output)
    (h_gate : ∀ j (hj : j < C.gates.length), ¬ Blocked (N + j) →
      val C x (N + j) = val C y (N + j) ∨
      ∀ u ∈ C.gates[j].inputs, ¬ Blocked u) :
    C.eval x = C.eval y := by
  have hval : ∀ w < N + C.gates.length, ¬ Blocked w → val C x w = val C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnb
      by_cases hlt : w < N
      · rw [val_input C x w (by omega), val_input C y w (by omega)]
        exact h_inp w hlt hnb
      · set j := w - N
        have hj : j < C.gates.length := by omega
        have hw_eq : w = N + j := by omega
        rw [hw_eq] at hnb ⊢
        rcases h_gate j hj hnb with heq | hinputs
        · exact heq
        · rw [← hx, val_gate C x j hj, hx, ← hy, val_gate C y j hj, hy]
          congr 1
          apply List.map_congr_left
          intro u hu
          obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hj
          have hu_lt : u < N + j := by
            rw [hab] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl <;> omega
          simp only [hu_lt, ↓reduceIte]
          exact ih u (by omega) (by omega) (hinputs u hu)
  rw [eval_eq_val, eval_eq_val]
  exact hval C.output hout h_out

lemma dummy_unread_left (n : ℕ) (hn : 2 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output < 2 * n + C.gates.length)
    (hr : Represents (LT n) C)
    (hmin : ∀ C', Monotone2 C' → Represents (LT n) C' → C.size ≤ C'.size) :
    deg C (n - 1) = 0 := by
  by_contra hne
  have hpos : 0 < (readers C (n - 1)).card := by unfold deg at hne; omega
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hpos
  obtain ⟨hj₀lt, hj₀mem⟩ := (mem_readers_iff C (n - 1) j₀).mp hj₀
  let Z : Finset ℕ := {n - 1}
  let inv : ℕ → Option ℕ := fun w => if w = n - 1 then none else if w < 2 * n then some w else none
  let C' := restrictCircuit Z C (2 * n) (2 * n) inv
  have hinv : ∀ w i, inv w = some i → i < 2 * n := by
    intro w i h
    unfold inv at h
    by_cases h1 : w = n - 1
    · simp [h1] at h
    · by_cases h2 : w < 2 * n
      · simp [h1, h2] at h; omega
      · simp [h1, h2] at h
  have hj₀kill : j₀ ∈ KGates Z C (2 * n) := by
    unfold KGates isKilled
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hj₀lt, ?_⟩
    simp only [hj₀lt, ↓reduceDIte, List.any_eq_true]
    refine ⟨n - 1, hj₀mem, ?_⟩
    rw [isZero_input Z C (2 * n) (n - 1) (by omega)]
    simp [Z]
  have hkill_pos : 1 ≤ (KGates Z C (2 * n)).card := Finset.card_pos.mpr ⟨j₀, hj₀kill⟩
  have hsize : C'.size + (KGates Z C (2 * n)).card = C.gates.length :=
    restrictCircuit_size Z C (2 * n) (2 * n) inv
  have hrep' : Represents (LT n) C' := by
    intro u v
    by_cases hu : u.val = n - 1
    · let x : List Bool := List.ofFn (fun i : Fin (2 * n) =>
        if i.val = n - 1 then false else (oneEach u v).getD i.val false)
      have hxlen : x.length = 2 * n := by simp [x]
      have hxget : ∀ w < 2 * n, x.getD w false =
          if w = n - 1 then false else (oneEach u v).getD w false := by
        intro w hw
        unfold x
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hw)]
        simp
      have heval : C'.eval (oneEach u v) = C.eval x := by
        apply restrictCircuit_eval Z C (2 * n) (2 * n) inv hc hout (oneEach u v) x
          (by rw [oneEach_length]; omega) hxlen hinv
        · intro w hw
          simp only [Z, Finset.mem_singleton] at hw
          subst hw
          rw [hxget (n - 1) (by omega)]
          simp
        · intro w hw hnotZ
          have hne_w : w ≠ n - 1 := by simpa [Z] using hnotZ
          simp only [inv, hne_w, ↓reduceIte, hw]
          rw [hxget w hw]
          simp [hne_w]
      rw [heval]
      have hfalse : C.eval (oneEach u v) = false := by
        rw [hr u v]
        simp only [LT, decide_eq_false_iff_not, Fin.lt_def]
        omega
      cases hxval : C.eval x
      · rw [← hfalse, hr u v]
      · exfalso
        have hmono : C.eval (oneEach u v) = true := by
          apply eval_mono C hc.1 x (oneEach u v) (by rw [hxlen, oneEach_length]; omega) _ hxval
          intro i hi
          by_cases hilt : i < 2 * n
          · rw [hxget i hilt] at hi
            by_cases h1 : i = n - 1
            · simp [h1] at hi
            · simp [h1] at hi; exact hi
          · rw [getD_ge x i (by rw [hxlen]; omega)] at hi
            exact False.elim (Bool.false_ne_true hi)
        rw [hmono] at hfalse
        exact Bool.false_ne_true hfalse.symm
    · have heval : C'.eval (oneEach u v) = C.eval (oneEach u v) := by
        apply restrictCircuit_eval Z C (2 * n) (2 * n) inv hc hout (oneEach u v) (oneEach u v)
          (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) hinv
        · intro w hw
          simp only [Z, Finset.mem_singleton] at hw
          subst hw
          rw [oneEach_getD]
          have hlt1 : n - 1 < n := by omega
          simp [hlt1, Ne.symm hu]
        · intro w hw hnotZ
          have hne_w : w ≠ n - 1 := by simpa [Z] using hnotZ
          simp only [inv, hne_w, ↓reduceIte, hw]
      rw [heval, hr u v]
  have hle := hmin C' (restrictCircuit_mono Z C (2 * n) (2 * n) inv hc.1) hrep'
  change C.gates.length ≤ C'.size at hle
  omega

lemma dummy_unread_right (n : ℕ) (hn : 2 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output < 2 * n + C.gates.length)
    (hr : Represents (LT n) C)
    (hmin : ∀ C', Monotone2 C' → Represents (LT n) C' → C.size ≤ C'.size) :
    deg C n = 0 := by
  by_contra hne
  have hpos : 0 < (readers C n).card := by unfold deg at hne; omega
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hpos
  obtain ⟨hj₀lt, hj₀mem⟩ := (mem_readers_iff C n j₀).mp hj₀
  let Z : Finset ℕ := {n}
  let inv : ℕ → Option ℕ := fun w => if w = n then none else if w < 2 * n then some w else none
  let C' := restrictCircuit Z C (2 * n) (2 * n) inv
  have hinv : ∀ w i, inv w = some i → i < 2 * n := by
    intro w i h
    unfold inv at h
    by_cases h1 : w = n
    · simp [h1] at h
    · by_cases h2 : w < 2 * n
      · simp [h1, h2] at h; omega
      · simp [h1, h2] at h
  have hj₀kill : j₀ ∈ KGates Z C (2 * n) := by
    unfold KGates isKilled
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hj₀lt, ?_⟩
    simp only [hj₀lt, ↓reduceDIte, List.any_eq_true]
    refine ⟨n, hj₀mem, ?_⟩
    rw [isZero_input Z C (2 * n) n (by omega)]
    simp [Z]
  have hkill_pos : 1 ≤ (KGates Z C (2 * n)).card := Finset.card_pos.mpr ⟨j₀, hj₀kill⟩
  have hsize : C'.size + (KGates Z C (2 * n)).card = C.gates.length :=
    restrictCircuit_size Z C (2 * n) (2 * n) inv
  have hrep' : Represents (LT n) C' := by
    intro u v
    by_cases hv : v.val = 0
    · let x : List Bool := List.ofFn (fun i : Fin (2 * n) =>
        if i.val = n then false else (oneEach u v).getD i.val false)
      have hxlen : x.length = 2 * n := by simp [x]
      have hxget : ∀ w < 2 * n, x.getD w false =
          if w = n then false else (oneEach u v).getD w false := by
        intro w hw
        unfold x
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hw)]
        simp
      have heval : C'.eval (oneEach u v) = C.eval x := by
        apply restrictCircuit_eval Z C (2 * n) (2 * n) inv hc hout (oneEach u v) x
          (by rw [oneEach_length]; omega) hxlen hinv
        · intro w hw
          simp only [Z, Finset.mem_singleton] at hw
          rw [hw, hxget n (by omega)]
          simp
        · intro w hw hnotZ
          have hne_w : w ≠ n := by simpa [Z] using hnotZ
          simp only [inv, hne_w, ↓reduceIte, hw]
          rw [hxget w hw]
          simp [hne_w]
      rw [heval]
      have hfalse : C.eval (oneEach u v) = false := by
        rw [hr u v]
        simp only [LT, decide_eq_false_iff_not, Fin.lt_def]
        omega
      cases hxval : C.eval x
      · rw [← hfalse, hr u v]
      · exfalso
        have hmono : C.eval (oneEach u v) = true := by
          apply eval_mono C hc.1 x (oneEach u v) (by rw [hxlen, oneEach_length]; omega) _ hxval
          intro i hi
          by_cases hilt : i < 2 * n
          · rw [hxget i hilt] at hi
            by_cases h1 : i = n
            · simp [h1] at hi
            · simp [h1] at hi; exact hi
          · rw [getD_ge x i (by rw [hxlen]; omega)] at hi
            exact False.elim (Bool.false_ne_true hi)
        rw [hmono] at hfalse
        exact Bool.false_ne_true hfalse.symm
    · have heval : C'.eval (oneEach u v) = C.eval (oneEach u v) := by
        apply restrictCircuit_eval Z C (2 * n) (2 * n) inv hc hout (oneEach u v) (oneEach u v)
          (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) hinv
        · intro w hw
          simp only [Z, Finset.mem_singleton] at hw
          rw [hw, oneEach_getD]
          have hlt2 : n < n + n := by omega
          simp [hlt2, Ne.symm hv]
        · intro w hw hnotZ
          have hne_w : w ≠ n := by simpa [Z] using hnotZ
          simp only [inv, hne_w, ↓reduceIte, hw]
      rw [heval, hr u v]
  have hle := hmin C' (restrictCircuit_mono Z C (2 * n) (2 * n) inv hc.1) hrep'
  change C.gates.length ≤ C'.size at hle
  omega

lemma active_read (n : ℕ) (hn : 2 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output = 2 * n + (C.gates.length - 1))
    (hpos : 1 ≤ C.gates.length)
    (hr : Represents (LT n) C)
    (hdL : deg C (n - 1) = 0) (hdR : deg C n = 0)
    (w : ℕ) (hw : Active n w) : 1 ≤ deg C w := by
  by_contra hlt
  have hzero : deg C w = 0 := by omega
  have hnotread : ∀ u, deg C u = 0 → ∀ j (hj : j < C.gates.length), u ∉ C.gates[j].inputs := by
    intro u hu j hj hmem
    have h1 : j ∈ readers C u := (mem_readers_iff C u j).mpr ⟨hj, hmem⟩
    have h2 : 0 < deg C u := Finset.card_pos.mpr ⟨j, h1⟩
    omega
  rcases hw with hwL | ⟨hwR1, hwR2⟩
  · let x := oneEach (⟨w, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
    let y := oneEach (⟨n - 1, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
    have heq : C.eval x = C.eval y := by
      apply eval_eq_of_iso C (2 * n) hc (by omega) x y
        (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega)
        (fun i => i = w ∨ i = n - 1)
      · intro i hi hnb
        push Not at hnb
        simp only [x, y, oneEach_getD]
        by_cases h1 : i < n
        · simp [h1, hnb.1, hnb.2]
        · simp [h1]
      · omega
      · intro j hj _
        right
        intro u hu hbl
        rcases hbl with huw | hun
        · rw [huw] at hu; exact hnotread w hzero j hj hu
        · rw [hun] at hu; exact hnotread (n - 1) hdL j hj hu
    have hx_eval : C.eval x = true := by rw [hr]; simp [LT]; omega
    have hy_eval : C.eval y = false := by rw [hr]; simp [LT]
    rw [hx_eval, hy_eval] at heq
    exact Bool.false_ne_true heq.symm
  · let x := oneEach (⟨0, by omega⟩ : Fin n) (⟨w - n, by omega⟩ : Fin n)
    let y := oneEach (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)
    have heq : C.eval x = C.eval y := by
      apply eval_eq_of_iso C (2 * n) hc (by omega) x y
        (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega)
        (fun i => i = w ∨ i = n)
      · intro i hi hnb
        push Not at hnb
        simp only [x, y, oneEach_getD]
        by_cases h1 : i < n
        · simp [h1]
        · by_cases h2 : i < n + n
          · have hne1 : i - n ≠ w - n := by omega
            have hne2 : i - n ≠ 0 := by omega
            simp [h1, h2, hne1, hne2]
          · simp [h1, h2]
      · omega
      · intro j hj _
        right
        intro u hu hbl
        rcases hbl with huw | hun
        · rw [huw] at hu; exact hnotread w hzero j hj hu
        · rw [hun] at hu; exact hnotread n hdR j hj hu
    have hx_eval : C.eval x = true := by rw [hr]; simp [LT]; omega
    have hy_eval : C.eval y = false := by rw [hr]; simp [LT]
    rw [hx_eval, hy_eval] at heq
    exact Bool.false_ne_true heq.symm

def skip1 (k i : ℕ) : ℕ := if i < k then i else i + 1

def invSkip1 (k w : ℕ) : Option ℕ :=
  if w < k then some w else if w = k then none else some (w - 1)

lemma invSkip1_lt (k m w i : ℕ) (hk : k < m) (hw : w < m) (h : invSkip1 k w = some i) :
    i < m - 1 := by
  unfold invSkip1 at h
  by_cases h1 : w < k
  · simp [h1] at h; omega
  · by_cases h2 : w = k
    · simp [h2] at h
    · simp [h1, h2] at h; omega

lemma skip1_lt_iff (r c i j : ℕ) (hrc : c = r ∨ c = r + 1) :
    skip1 r i < skip1 c j ↔ i < j := by
  unfold skip1
  rcases hrc with rfl | rfl <;> split_ifs <;> omega

lemma reduce1 (n : ℕ) (hn : 3 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output < 2 * n + C.gates.length)
    (hr : Represents (LT n) C)
    (r c : ℕ) (hrn : r < n) (hcn : c < n) (hrc : c = r ∨ c = r + 1) :
    let Z : Finset ℕ := {r, n + c}
    isZero Z C (2 * n) C.output = false ∧
    RepSizeAtMost (LT (n - 1)) (C.gates.length - (KGates Z C (2 * n)).card) := by
  intro Z
  let inv : ℕ → Option ℕ := fun w =>
    if w < n then invSkip1 r w
    else if w < 2 * n then (invSkip1 c (w - n)).map (fun j => (n - 1) + j)
    else none
  have hinv : ∀ w i, inv w = some i → i < 2 * (n - 1) := by
    intro w i h
    unfold inv at h
    by_cases h1 : w < n
    · simp only [h1, ↓reduceIte] at h
      have := invSkip1_lt r n w i hrn h1 h
      omega
    · by_cases h2 : w < 2 * n
      · simp only [h1, h2, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        have := invSkip1_lt c n (w - n) j hcn (by omega) hj
        omega
      · simp [h1, h2] at h
  have h_oneEach : ∀ (u v : Fin (n - 1)),
      let u' : Fin n := ⟨skip1 r u.val, by unfold skip1; split_ifs <;> omega⟩
      let v' : Fin n := ⟨skip1 c v.val, by unfold skip1; split_ifs <;> omega⟩
      (∀ w ∈ Z, (oneEach u' v').getD w false = false) ∧
      (∀ w < 2 * n, w ∉ Z →
        match inv w with
        | some i => (oneEach u' v').getD w false = (oneEach u v).getD i false
        | none => (oneEach u' v').getD w false = false) := by
    intro u v u' v'
    constructor
    · intro w hw
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw
      · rw [hw, oneEach_getD]
        simp only [hrn, ↓reduceIte]
        rw [decide_eq_false_iff_not]
        simp only [u', skip1]
        split_ifs <;> omega
      · rw [hw, oneEach_getD]
        have h1 : ¬ (n + c < n) := by omega
        have h2 : n + c < n + n := by omega
        have h3 : n + c - n = c := by omega
        simp only [h1, ↓reduceIte, h2, h3]
        rw [decide_eq_false_iff_not]
        simp only [v', skip1]
        split_ifs <;> omega
    · intro w hw hnotZ
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hnotZ
      push Not at hnotZ
      unfold inv invSkip1
      by_cases h1 : w < n
      · simp only [h1, ↓reduceIte]
        by_cases h2 : w < r
        · simp only [h2, ↓reduceIte]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w < n - 1 := by omega
          simp only [h1, h3, ↓reduceIte, u', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
        · simp only [h2, ↓reduceIte, hnotZ.1]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w - 1 < n - 1 := by omega
          simp only [h1, h3, ↓reduceIte, u', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
      · simp only [h1, hw, ↓reduceIte]
        have hne_c : w - n ≠ c := by omega
        by_cases h2 : w - n < c
        · simp only [h2, ↓reduceIte, Option.map_some]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w < n + n := by omega
          have h4 : ¬ (n - 1 + (w - n) < n - 1) := by omega
          have h5 : n - 1 + (w - n) < (n - 1) + (n - 1) := by omega
          have h6 : n - 1 + (w - n) - (n - 1) = w - n := by omega
          simp only [h1, h3, h4, h5, h6, ↓reduceIte, v', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
        · simp only [h2, ↓reduceIte, hne_c, Option.map_some]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w < n + n := by omega
          have h4 : ¬ (n - 1 + (w - n - 1) < n - 1) := by omega
          have h5 : n - 1 + (w - n - 1) < (n - 1) + (n - 1) := by omega
          have h6 : n - 1 + (w - n - 1) - (n - 1) = w - n - 1 := by omega
          simp only [h1, h3, h4, h5, h6, ↓reduceIte, v', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
  constructor
  · by_contra hnz
    have hzt : isZero Z C (2 * n) C.output = true := by
      cases h : isZero Z C (2 * n) C.output
      · exact False.elim (hnz h)
      · rfl
    let u0 : Fin (n - 1) := ⟨0, by omega⟩
    let v1 : Fin (n - 1) := ⟨1, by omega⟩
    let u' : Fin n := ⟨skip1 r u0.val, by unfold skip1; split_ifs <;> omega⟩
    let v' : Fin n := ⟨skip1 c v1.val, by unfold skip1; split_ifs <;> omega⟩
    have hfalse : C.eval (oneEach u' v') = false :=
      isZero_val_false Z C (2 * n) hc (oneEach u' v') (by rw [oneEach_length]; omega)
        (h_oneEach u0 v1).1 C.output hzt
    have htrue : C.eval (oneEach u' v') = true := by
      rw [hr u' v']
      simp only [LT, decide_eq_true_eq, Fin.lt_def, u', v']
      exact (skip1_lt_iff r c u0.val v1.val hrc).mpr (by simp [u0, v1])
    rw [htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  · let C' := restrictCircuit Z C (2 * n) (2 * (n - 1)) inv
    refine ⟨C', restrictCircuit_mono Z C (2 * n) (2 * (n - 1)) inv hc.1, ?_, ?_⟩
    · have hs := restrictCircuit_size Z C (2 * n) (2 * (n - 1)) inv
      change C'.size + (KGates Z C (2 * n)).card = C.gates.length at hs
      omega
    · intro u v
      let u' : Fin n := ⟨skip1 r u.val, by unfold skip1; split_ifs <;> omega⟩
      let v' : Fin n := ⟨skip1 c v.val, by unfold skip1; split_ifs <;> omega⟩
      have heval : C'.eval (oneEach u v) = C.eval (oneEach u' v') :=
        restrictCircuit_eval Z C (2 * n) (2 * (n - 1)) inv hc hout
          (oneEach u v) (oneEach u' v')
          (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) hinv
          (h_oneEach u v).1 (h_oneEach u v).2
      rw [heval, hr u' v']
      simp only [LT, Fin.lt_def, u', v']
      exact decide_eq_decide.mpr (skip1_lt_iff r c u.val v.val hrc)

lemma reduce2 (n : ℕ) (hn : 4 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output < 2 * n + C.gates.length)
    (hr : Represents (LT n) C)
    (b a : ℕ) (hba : b + 2 ≤ a) (han : a + 1 < n) :
    let Z : Finset ℕ := {b, a, n + (b + 1), n + (a + 1)}
    isZero Z C (2 * n) C.output = false ∧
    RepSizeAtMost (LT (n - 2)) (C.gates.length - (KGates Z C (2 * n)).card) := by
  intro Z
  let inv : ℕ → Option ℕ := fun w =>
    if w < n then (invSkip1 a w).bind (invSkip1 b)
    else if w < 2 * n then ((invSkip1 (a + 1) (w - n)).bind (invSkip1 (b + 1))).map (fun j => (n - 2) + j)
    else none
  have hinv : ∀ w i, inv w = some i → i < 2 * (n - 2) := by
    intro w i h
    unfold inv at h
    by_cases h1 : w < n
    · simp only [h1, ↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨j, hj1, hj2⟩ := h
      have hjlt := invSkip1_lt a n w j (by omega) h1 hj1
      have hilt := invSkip1_lt b (n - 1) j i (by omega) hjlt hj2
      omega
    · by_cases h2 : w < 2 * n
      · simp only [h1, h2, ↓reduceIte, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
        obtain ⟨k, ⟨j, hj1, hj2⟩, rfl⟩ := h
        have hjlt := invSkip1_lt (a + 1) n (w - n) j han (by omega) hj1
        have hklt := invSkip1_lt (b + 1) (n - 1) j k (by omega) hjlt hj2
        omega
      · simp [h1, h2] at h
  have hlt2_iff : ∀ i j : ℕ,
      skip1 a (skip1 b i) < skip1 (a + 1) (skip1 (b + 1) j) ↔ i < j := by
    intro i j
    rw [skip1_lt_iff a (a + 1) (skip1 b i) (skip1 (b + 1) j) (Or.inr rfl),
        skip1_lt_iff b (b + 1) i j (Or.inr rfl)]
  have h_oneEach : ∀ (u v : Fin (n - 2)),
      let u' : Fin n := ⟨skip1 a (skip1 b u.val), by unfold skip1; split_ifs <;> omega⟩
      let v' : Fin n := ⟨skip1 (a + 1) (skip1 (b + 1) v.val), by unfold skip1; split_ifs <;> omega⟩
      (∀ w ∈ Z, (oneEach u' v').getD w false = false) ∧
      (∀ w < 2 * n, w ∉ Z →
        match inv w with
        | some i => (oneEach u' v').getD w false = (oneEach u v).getD i false
        | none => (oneEach u' v').getD w false = false) := by
    intro u v u' v'
    constructor
    · intro w hw
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw | hw
      · rw [hw, oneEach_getD]
        have hlt : b < n := by omega
        simp only [hlt, ↓reduceIte]
        rw [decide_eq_false_iff_not]
        simp only [u', skip1]
        split_ifs <;> omega
      · rw [hw, oneEach_getD]
        have hlt : a < n := by omega
        simp only [hlt, ↓reduceIte]
        rw [decide_eq_false_iff_not]
        simp only [u', skip1]
        split_ifs <;> omega
      · rw [hw, oneEach_getD]
        have h1 : ¬ (n + (b + 1) < n) := by omega
        have h2 : n + (b + 1) < n + n := by omega
        have h3 : n + (b + 1) - n = b + 1 := by omega
        simp only [h1, ↓reduceIte, h2, h3]
        rw [decide_eq_false_iff_not]
        simp only [v', skip1]
        split_ifs <;> omega
      · rw [hw, oneEach_getD]
        have h1 : ¬ (n + (a + 1) < n) := by omega
        have h2 : n + (a + 1) < n + n := by omega
        have h3 : n + (a + 1) - n = a + 1 := by omega
        simp only [h1, ↓reduceIte, h2, h3]
        rw [decide_eq_false_iff_not]
        simp only [v', skip1]
        split_ifs <;> omega
    · intro w hw hnotZ
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hnotZ
      push Not at hnotZ
      obtain ⟨hneb, hnea, hneb1, hnea1⟩ := hnotZ
      unfold inv invSkip1
      by_cases h1 : w < n
      · simp only [h1, ↓reduceIte]
        by_cases hwa : w < a
        · simp only [hwa, ↓reduceIte, Option.bind_some]
          by_cases hwb : w < b
          · simp only [hwb, ↓reduceIte]
            rw [oneEach_getD, oneEach_getD]
            have h3 : w < n - 2 := by omega
            simp only [h1, h3, ↓reduceIte, u', skip1]
            apply decide_eq_decide.mpr
            split_ifs <;> omega
          · simp only [hwb, ↓reduceIte, hneb]
            rw [oneEach_getD, oneEach_getD]
            have h3 : w - 1 < n - 2 := by omega
            simp only [h1, h3, ↓reduceIte, u', skip1]
            apply decide_eq_decide.mpr
            split_ifs <;> omega
        · simp only [hwa, ↓reduceIte, hnea, Option.bind_some]
          have hnotb1 : ¬ (w - 1 < b) := by omega
          have hneb2 : w - 1 ≠ b := by omega
          simp only [hnotb1, hneb2, ↓reduceIte]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w - 1 - 1 < n - 2 := by omega
          simp only [h1, h3, ↓reduceIte, u', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
      · simp only [h1, hw, ↓reduceIte]
        have hnea' : w - n ≠ a + 1 := by omega
        have hneb' : w - n ≠ b + 1 := by omega
        by_cases hwa : w - n < a + 1
        · simp only [hwa, ↓reduceIte, Option.bind_some]
          by_cases hwb : w - n < b + 1
          · simp only [hwb, ↓reduceIte, Option.map_some]
            rw [oneEach_getD, oneEach_getD]
            have h3 : w < n + n := by omega
            have h4 : ¬ (n - 2 + (w - n) < n - 2) := by omega
            have h5 : n - 2 + (w - n) < (n - 2) + (n - 2) := by omega
            have h6 : n - 2 + (w - n) - (n - 2) = w - n := by omega
            simp only [h1, h3, h4, h5, h6, ↓reduceIte, v', skip1]
            apply decide_eq_decide.mpr
            split_ifs <;> omega
          · simp only [hwb, ↓reduceIte, hneb', Option.map_some]
            rw [oneEach_getD, oneEach_getD]
            have h3 : w < n + n := by omega
            have h4 : ¬ (n - 2 + (w - n - 1) < n - 2) := by omega
            have h5 : n - 2 + (w - n - 1) < (n - 2) + (n - 2) := by omega
            have h6 : n - 2 + (w - n - 1) - (n - 2) = w - n - 1 := by omega
            simp only [h1, h3, h4, h5, h6, ↓reduceIte, v', skip1]
            apply decide_eq_decide.mpr
            split_ifs <;> omega
        · simp only [hwa, ↓reduceIte, hnea', Option.bind_some]
          have hnotb1 : ¬ (w - n - 1 < b + 1) := by omega
          have hneb2 : w - n - 1 ≠ b + 1 := by omega
          simp only [hnotb1, hneb2, ↓reduceIte, Option.map_some]
          rw [oneEach_getD, oneEach_getD]
          have h3 : w < n + n := by omega
          have h4 : ¬ (n - 2 + (w - n - 1 - 1) < n - 2) := by omega
          have h5 : n - 2 + (w - n - 1 - 1) < (n - 2) + (n - 2) := by omega
          have h6 : n - 2 + (w - n - 1 - 1) - (n - 2) = w - n - 1 - 1 := by omega
          simp only [h1, h3, h4, h5, h6, ↓reduceIte, v', skip1]
          apply decide_eq_decide.mpr
          split_ifs <;> omega
  constructor
  · by_contra hnz
    have hzt : isZero Z C (2 * n) C.output = true := by
      cases h : isZero Z C (2 * n) C.output
      · exact False.elim (hnz h)
      · rfl
    let u0 : Fin (n - 2) := ⟨0, by omega⟩
    let v1 : Fin (n - 2) := ⟨1, by omega⟩
    let u' : Fin n := ⟨skip1 a (skip1 b u0.val), by unfold skip1; split_ifs <;> omega⟩
    let v' : Fin n := ⟨skip1 (a + 1) (skip1 (b + 1) v1.val), by unfold skip1; split_ifs <;> omega⟩
    have hfalse : C.eval (oneEach u' v') = false :=
      isZero_val_false Z C (2 * n) hc (oneEach u' v') (by rw [oneEach_length]; omega)
        (h_oneEach u0 v1).1 C.output hzt
    have htrue : C.eval (oneEach u' v') = true := by
      rw [hr u' v']
      simp only [LT, decide_eq_true_eq, Fin.lt_def, u', v']
      exact (hlt2_iff u0.val v1.val).mpr (by simp [u0, v1])
    rw [htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  · let C' := restrictCircuit Z C (2 * n) (2 * (n - 2)) inv
    refine ⟨C', restrictCircuit_mono Z C (2 * n) (2 * (n - 2)) inv hc.1, ?_, ?_⟩
    · have hs := restrictCircuit_size Z C (2 * n) (2 * (n - 2)) inv
      change C'.size + (KGates Z C (2 * n)).card = C.gates.length at hs
      omega
    · intro u v
      let u' : Fin n := ⟨skip1 a (skip1 b u.val), by unfold skip1; split_ifs <;> omega⟩
      let v' : Fin n := ⟨skip1 (a + 1) (skip1 (b + 1) v.val), by unfold skip1; split_ifs <;> omega⟩
      have heval : C'.eval (oneEach u v) = C.eval (oneEach u' v') :=
        restrictCircuit_eval Z C (2 * n) (2 * (n - 2)) inv hc hout
          (oneEach u v) (oneEach u' v')
          (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) hinv
          (h_oneEach u v).1 (h_oneEach u v).2
      rw [heval, hr u' v']
      simp only [LT, Fin.lt_def, u', v']
      exact decide_eq_decide.mpr (hlt2_iff u.val v.val)

-- Reachability in circuit DAG for Move 2

def reaches (C : Circuit) (N : ℕ) (w u : ℕ) : Bool :=
  decide (w = u) ||
  if h : N ≤ w ∧ w - N < C.gates.length then
    C.gates[w - N].inputs.any (fun a => if _ : a < w then reaches C N a u else false)
  else
    false
termination_by w

lemma reaches_self (C : Circuit) (N w : ℕ) : reaches C N w w = true := by
  rw [reaches]; simp

lemma reaches_le (C : Circuit) (N : ℕ) : ∀ w u, reaches C N w u = true → u ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hr
    rw [reaches] at hr
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | hr
    · exact le_refl _
    · by_cases h : N ≤ w ∧ w - N < C.gates.length
      · rw [dite_eq_left_of_eq_true (eq_true h), List.any_eq_true] at hr
        rcases hr with ⟨a, _, ha⟩
        by_cases haw : a < w
        · rw [dite_eq_left_of_eq_true (eq_true haw)] at ha
          exact (ih a haw u ha).trans (Nat.le_of_lt haw)
        · rw [dite_eq_right_of_eq_false (eq_false haw)] at ha
          exact False.elim (Bool.false_ne_true ha)
      · rw [dite_eq_right_of_eq_false (eq_false h)] at hr
        exact False.elim (Bool.false_ne_true hr)

lemma reaches_gate_iff (C : Circuit) (N j u : ℕ) (hc : CleanCircuit N C)
    (hj : j < C.gates.length) :
    reaches C N (N + j) u = true ↔
      N + j = u ∨ ∃ a ∈ C.gates[j].inputs, reaches C N a u = true := by
  rw [reaches]
  have h1 : N ≤ N + j ∧ N + j - N < C.gates.length := by omega
  have h2 : N + j - N = j := by omega
  obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hj
  rw [dite_eq_left_of_eq_true (eq_true h1)]
  simp only [Bool.or_eq_true, decide_eq_true_eq, h2, List.any_eq_true]
  constructor
  · rintro (h | ⟨x, hx, hrx⟩)
    · exact Or.inl h
    · right
      have hxlt : x < N + j := by
        rw [hab] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega
      rw [dite_eq_left_of_eq_true (eq_true hxlt)] at hrx
      exact ⟨x, hx, hrx⟩
  · rintro (h | ⟨x, hx, hrx⟩)
    · exact Or.inl h
    · right
      have hxlt : x < N + j := by
        rw [hab] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega
      exact ⟨x, hx, by rw [dite_eq_left_of_eq_true (eq_true hxlt)]; exact hrx⟩

lemma reaches_trans (C : Circuit) (N : ℕ) (hc : CleanCircuit N C) :
    ∀ w v u, w < N + C.gates.length →
      reaches C N w v = true → reaches C N v u = true → reaches C N w u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v u hw hwv hvu
    by_cases hlt : w < N
    · have hle := reaches_le C N w v hwv
      rw [reaches] at hwv
      have hnot : ¬ (N ≤ w ∧ w - N < C.gates.length) := by omega
      simp only [hnot, ↓reduceDIte, Bool.or_false, decide_eq_true_eq] at hwv
      subst hwv
      exact hvu
    · set j := w - N
      have hj : j < C.gates.length := by omega
      have hw_eq : w = N + j := by omega
      rw [hw_eq] at hwv ⊢
      rw [reaches_gate_iff C N j v hc hj] at hwv
      rcases hwv with rfl | ⟨a, ha, hav⟩
      · exact hvu
      · rw [reaches_gate_iff C N j u hc hj]
        right
        obtain ⟨x, y, hxy, hx, hy, _⟩ := hc.2.1 j hj
        have halt : a < N + j := by
          rw [hxy] at ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> omega
        exact ⟨a, ha, ih a (by omega) v u (by omega) hav hvu⟩

lemma reaches_step_out (C : Circuit) (N : ℕ) (hc : CleanCircuit N C) :
    ∀ w u, w < N + C.gates.length → u < w → reaches C N w u = true →
      ∃ j, ∃ hj : j < C.gates.length, N + j ≤ w ∧
        reaches C N w (N + j) = true ∧ u ∈ C.gates[j].inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hw huw hr
    by_cases hlt : w < N
    · rw [reaches] at hr
      have hnot : ¬ (N ≤ w ∧ w - N < C.gates.length) := by omega
      simp only [hnot, ↓reduceDIte, Bool.or_false, decide_eq_true_eq] at hr
      omega
    · set j := w - N
      have hj : j < C.gates.length := by omega
      have hw_eq : w = N + j := by omega
      rw [hw_eq] at hr ⊢
      rw [reaches_gate_iff C N j u hc hj] at hr
      rcases hr with heq | ⟨a, ha, hau⟩
      · omega
      · by_cases heq : a = u
        · subst heq
          exact ⟨j, hj, le_refl _, reaches_self C N (N + j), ha⟩
        · obtain ⟨x, y, hxy, hx, hy, _⟩ := hc.2.1 j hj
          have halt : a < N + j := by
            rw [hxy] at ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl <;> omega
          have hle := reaches_le C N a u hau
          obtain ⟨j', hj', hle', hra, humem⟩ := ih a (by omega) u (by omega) (by omega) hau
          refine ⟨j', hj', by omega, ?_, humem⟩
          rw [reaches_gate_iff C N j (N + j') hc hj]
          exact Or.inr ⟨a, ha, hra⟩

lemma val_all_or_iff (C : Circuit) (N k : ℕ) (hc : CleanCircuit N C)
    (hk : k < C.gates.length)
    (hor : ∀ (j : ℕ) (hj : j ≤ k), (C.gates[j]'(by omega)).op = GateOp.or)
    (x : List Bool) (hx : x.length = N) :
    ∀ w ≤ N + k, val C x w = true ↔ ∃ i < N, reaches C N w i = true ∧ x.getD i false = true := by
  subst hx
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < x.length
    · rw [val_input C x w hlt]
      constructor
      · intro h
        exact ⟨w, hlt, reaches_self C x.length w, h⟩
      · rintro ⟨i, _, hri, hi⟩
        rw [reaches] at hri
        have hnot : ¬ (x.length ≤ w ∧ w - x.length < C.gates.length) := by omega
        simp only [hnot, ↓reduceDIte, Bool.or_false, decide_eq_true_eq] at hri
        subst hri
        exact hi
    · set j := w - x.length
      have hj : j ≤ k := by omega
      have hjlt : j < C.gates.length := by omega
      have hw_eq : w = x.length + j := by omega
      rw [hw_eq, val_gate C x j hjlt, hor j hj]
      obtain ⟨a, b, hab, ha, hb, _⟩ := hc.2.1 j hjlt
      simp only [hab, List.map_cons, List.map_nil, ha, hb, ↓reduceIte, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
      rw [ih a (by omega) (by omega), ih b (by omega) (by omega)]
      constructor
      · rintro (⟨i, hi, hra, hxi⟩ | ⟨i, hi, hrb, hxi⟩)
        · refine ⟨i, hi, ?_, hxi⟩
          rw [reaches_gate_iff C x.length j i hc hjlt]
          exact Or.inr ⟨a, by rw [hab]; simp, hra⟩
        · refine ⟨i, hi, ?_, hxi⟩
          rw [reaches_gate_iff C x.length j i hc hjlt]
          exact Or.inr ⟨b, by rw [hab]; simp, hrb⟩
      · rintro ⟨i, hi, hri, hxi⟩
        rw [reaches_gate_iff C x.length j i hc hjlt] at hri
        rcases hri with heq | ⟨u, hu, hru⟩
        · omega
        · rw [hab] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact Or.inl ⟨i, hi, hru, hxi⟩
          · exact Or.inr ⟨i, hi, hru, hxi⟩

lemma val_of_reaches_or (C : Circuit) (N k : ℕ) (hc : CleanCircuit N C)
    (hk : k < C.gates.length)
    (hor : ∀ (j : ℕ) (hj : j ≤ k), (C.gates[j]'(by omega)).op = GateOp.or)
    (x : List Bool) (hx : x.length = N)
    (w u : ℕ) (hw : w ≤ N + k) (hru : reaches C N w u = true)
    (hvu : val C x u = true) : val C x w = true := by
  have hle : u ≤ w := reaches_le C N w u hru
  rw [val_all_or_iff C N k hc hk hor x hx u (by omega)] at hvu
  rw [val_all_or_iff C N k hc hk hor x hx w hw]
  obtain ⟨i, hi, hrui, hxi⟩ := hvu
  exact ⟨i, hi, reaches_trans C N hc w u i (by omega) hru hrui, hxi⟩

lemma exists_and_gate (n : ℕ) (hn : 2 ≤ n) (C : Circuit)
    (hc : CleanCircuit (2 * n) C) (hout : C.output = 2 * n + (C.gates.length - 1))
    (hpos : 1 ≤ C.gates.length) (hr : Represents (LT n) C) :
    ∃ j, ∃ hj : j < C.gates.length, C.gates[j].op = GateOp.and := by
  by_contra h
  push Not at h
  have hor : ∀ (j : ℕ) (hj : j ≤ C.gates.length - 1), (C.gates[j]'(by omega)).op = GateOp.or := by
    intro j hj
    have hjlt : j < C.gates.length := by omega
    have hop := (hc.1 _ (List.getElem_mem hjlt)).1
    have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
    exact hop'.resolve_left (h j hjlt)
  have h01 : C.eval (oneEach (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)) = true := by
    rw [hr]; simp [LT]
  rw [eval_eq_val, hout, val_all_or_iff C (2 * n) (C.gates.length - 1) hc (by omega) hor
    _ (by rw [oneEach_length]; omega) _ (le_refl _)] at h01
  obtain ⟨i, hi, hri, hxi⟩ := h01
  rw [oneEach_getD] at hxi
  by_cases h1 : i < n
  · simp only [h1, ↓reduceIte, decide_eq_true_eq] at hxi
    subst hxi
    have h00 : C.eval (oneEach (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)) = true := by
      rw [eval_eq_val, hout, val_all_or_iff C (2 * n) (C.gates.length - 1) hc (by omega) hor
        _ (by rw [oneEach_length]; omega) _ (le_refl _)]
      exact ⟨0, by omega, hri, by rw [oneEach_getD]; simp [show 0 < n by omega]⟩
    rw [hr] at h00
    simp [LT] at h00
  · have h2 : i < n + n := by omega
    simp only [h1, h2, ↓reduceIte, decide_eq_true_eq] at hxi
    have hi_eq : i = n + 1 := by omega
    subst hi_eq
    have hn1 : C.eval (oneEach (⟨n - 1, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)) = true := by
      rw [eval_eq_val, hout, val_all_or_iff C (2 * n) (C.gates.length - 1) hc (by omega) hor
        _ (by rw [oneEach_length]; omega) _ (le_refl _)]
      refine ⟨n + 1, by omega, hri, ?_⟩
      rw [oneEach_getD]
      have ha : ¬ (n + 1 < n) := by omega
      have hb : n + 1 < n + n := by omega
      have hc' : n + 1 - n = 1 := by omega
      simp [ha, hb, hc']
    rw [hr] at hn1
    simp only [LT, decide_eq_true_eq, Fin.lt_def] at hn1
    omega

lemma move_step (n : ℕ) (hn : 3 ≤ n) (C : Circuit)
    (hm : Monotone2 C) (hr : Represents (LT n) C)
    (hmin : ∀ C', Monotone2 C' → Represents (LT n) C' → C.size ≤ C'.size) :
    (3 ≤ C.gates.length ∧ RepSizeAtMost (LT (n - 1)) (C.gates.length - 3)) ∨
    (4 ≤ n ∧ 5 ≤ C.gates.length ∧ RepSizeAtMost (LT (n - 2)) (C.gates.length - 5)) := by
  obtain ⟨hc, hpos, hout_last⟩ := minimal_clean n (by omega) C hm hr hmin
  have hout : C.output < 2 * n + C.gates.length := by omega
  have hdL : deg C (n - 1) = 0 := dummy_unread_left n (by omega) C hc hout hr hmin
  have hdR : deg C n = 0 := dummy_unread_right n (by omega) C hc hout hr hmin
  have hact : ∀ w, Active n w → 1 ≤ deg C w :=
    active_read n (by omega) C hc hout_last hpos hr hdL hdR
  have hnotread_dummy : ∀ j (hj : j < C.gates.length),
      n - 1 ∉ C.gates[j].inputs ∧ n ∉ C.gates[j].inputs := by
    intro j hj
    constructor
    · intro hm1
      have : 0 < deg C (n - 1) := Finset.card_pos.mpr ⟨j, (mem_readers_iff C (n - 1) j).mpr ⟨hj, hm1⟩⟩
      omega
    · intro hm2
      have : 0 < deg C n := Finset.card_pos.mpr ⟨j, (mem_readers_iff C n j).mpr ⟨hj, hm2⟩⟩
      omega
  -- Check Move 1 condition
  by_cases hmove1 : ∃ w, Active n w ∧
      (2 ≤ deg C w ∨ ∃ j, ∃ hj : j < C.gates.length, C.gates[j].op = GateOp.and ∧ w ∈ C.gates[j].inputs)
  · left
    obtain ⟨w, hw_act, hw_cond⟩ := hmove1
    -- Pick adjacent pair {r, n + (r + 1)} containing w
    have hex_pair : ∃ r < n - 1, w = r ∨ w = n + (r + 1) := by
      rcases hw_act with hL | ⟨hR1, hR2⟩
      · exact ⟨w, hL, Or.inl rfl⟩
      · exact ⟨w - n - 1, by omega, Or.inr (by omega)⟩
    obtain ⟨r, hrn, hw_eq⟩ := hex_pair
    let Z : Finset ℕ := {r, n + (r + 1)}
    have hZ_lt : ∀ u ∈ Z, u < 2 * n := by
      intro u hu
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    have hred := reduce1 n hn C hc hout hr r (r + 1) (by omega) (by omega) (Or.inr rfl)
    have hout_nz : isZero Z C (2 * n) C.output = false := hred.1
    have hid := killed_card_identity Z C (2 * n) hc hZ_lt hout_nz
    have hne_pair : r ≠ n + (r + 1) := by omega
    have hsumZ : ∑ u ∈ Z, deg C u = deg C r + deg C (n + (r + 1)) := by
      simp [Z, Finset.sum_pair hne_pair]
    have hdeg_r : 1 ≤ deg C r := hact r (Or.inl hrn)
    have hdeg_c : 1 ≤ deg C (n + (r + 1)) := hact (n + (r + 1)) (Or.inr ⟨by omega, by omega⟩)
    have hkill3 : 3 ≤ (KGates Z C (2 * n)).card := by
      rcases hw_cond with hdeg2 | ⟨g₁, hg₁, hg₁and, hwg₁⟩
      · rcases hw_eq with rfl | rfl <;> omega
      · by_cases hsum3 : 3 ≤ deg C r + deg C (n + (r + 1))
        · omega
        · have hdr1 : deg C r = 1 := by omega
          have hdc1 : deg C (n + (r + 1)) = 1 := by omega
          have hg₁Z : g₁ ∈ ZGates Z C (2 * n) := by
            unfold ZGates
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hg₁, ?_⟩
            rw [isZero_gate Z C (2 * n) g₁ hc hg₁, hg₁and]
            simp only [isAndOp, ↓reduceIte, List.any_eq_true]
            refine ⟨w, hwg₁, ?_⟩
            rw [isZero_input Z C (2 * n) w (by rcases hw_eq with rfl | rfl <;> omega)]
            simp only [decide_eq_true_eq, Z, Finset.mem_insert, Finset.mem_singleton]
            exact hw_eq
          have hZG_ne : (ZGates Z C (2 * n)).Nonempty := ⟨g₁, hg₁Z⟩
          let j₀ := (ZGates Z C (2 * n)).min' hZG_ne
          have hj₀Z : j₀ ∈ ZGates Z C (2 * n) := Finset.min'_mem _ hZG_ne
          have hj₀lt : j₀ < C.gates.length := by
            unfold ZGates at hj₀Z; rw [Finset.mem_filter, Finset.mem_range] at hj₀Z; exact hj₀Z.1
          by_cases hin1 : inZero Z C (2 * n) j₀ ≤ 1
          · have hterm : 2 - inZero Z C (2 * n) j₀ ≤
                ∑ j ∈ ZGates Z C (2 * n), (2 - inZero Z C (2 * n) j) :=
              Finset.single_le_sum (f := fun j => 2 - inZero Z C (2 * n) j) (fun _ _ => Nat.zero_le _) hj₀Z
            omega
          · -- inZero j₀ = 2, so both inputs of j₀ are in Z (since j₀ is min of ZGates)
            exfalso
            obtain ⟨a, b, hab, ha, hb, hneab⟩ := hc.2.1 j₀ hj₀lt
            have hin_eq := inZero_eq_pair Z C (2 * n) j₀ a b hj₀lt hab
            have hza : isZero Z C (2 * n) a = true := by
              cases h : isZero Z C (2 * n) a
              · simp [h] at hin_eq; split_ifs at hin_eq <;> omega
              · rfl
            have hzb : isZero Z C (2 * n) b = true := by
              cases h : isZero Z C (2 * n) b
              · simp [h, hza] at hin_eq; omega
              · rfl
            have h_in_Z : ∀ u, u < 2 * n + j₀ → isZero Z C (2 * n) u = true → u ∈ Z := by
              intro u hult hzu
              by_cases huN : u < 2 * n
              · rw [isZero_input Z C (2 * n) u huN, decide_eq_true_eq] at hzu
                exact hzu
              · exfalso
                have hj'Z : u - 2 * n ∈ ZGates Z C (2 * n) := by
                  unfold ZGates
                  rw [Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, by rwa [show 2 * n + (u - 2 * n) = u by omega]⟩
                have hle := Finset.min'_le (ZGates Z C (2 * n)) (u - 2 * n) hj'Z
                change j₀ ≤ u - 2 * n at hle
                omega
            have haZ : a ∈ Z := h_in_Z a ha hza
            have hbZ : b ∈ Z := h_in_Z b hb hzb
            have hpair : (a = r ∧ b = n + (r + 1)) ∨ (a = n + (r + 1) ∧ b = r) := by
              simp only [Z, Finset.mem_insert, Finset.mem_singleton] at haZ hbZ
              rcases haZ with rfl | rfl <;> rcases hbZ with rfl | rfl
              · exact False.elim (hneab rfl)
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
              · exact False.elim (hneab rfl)
            have hj₀_eq_g₁ : j₀ = g₁ := by
              have hmem_w : w ∈ C.gates[j₀].inputs := by
                rw [hab]
                rcases hw_eq with rfl | rfl <;> rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
              have h1 : j₀ ∈ readers C w := (mem_readers_iff C w j₀).mpr ⟨hj₀lt, hmem_w⟩
              have h2 : g₁ ∈ readers C w := (mem_readers_iff C w g₁).mpr ⟨hg₁, hwg₁⟩
              have hdeg1 : (readers C w).card = 1 := by
                rcases hw_eq with rfl | rfl
                · exact hdr1
                · exact hdc1
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdeg1
              rw [hx, Finset.mem_singleton] at h1 h2
              exact h1.trans h2.symm
            subst hj₀_eq_g₁
            -- Now g₁ is an AND gate with inputs {r, n + (r + 1)}, and deg r = deg (n + r + 1) = 1
            have hunique_r : ∀ j (hj : j < C.gates.length), r ∈ C.gates[j].inputs → j = j₀ := by
              intro j hj hmr
              have h1 : j ∈ readers C r := (mem_readers_iff C r j).mpr ⟨hj, hmr⟩
              have h2 : j₀ ∈ readers C r := (mem_readers_iff C r j₀).mpr ⟨hj₀lt, by
                rw [hab]; rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdr1
              rw [hx, Finset.mem_singleton] at h1 h2
              exact h1.trans h2.symm
            have hunique_c : ∀ j (hj : j < C.gates.length), n + (r + 1) ∈ C.gates[j].inputs → j = j₀ := by
              intro j hj hmc
              have h1 : j ∈ readers C (n + (r + 1)) := (mem_readers_iff C (n + (r + 1)) j).mpr ⟨hj, hmc⟩
              have h2 : j₀ ∈ readers C (n + (r + 1)) := (mem_readers_iff C (n + (r + 1)) j₀).mpr ⟨hj₀lt, by
                rw [hab]; rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdc1
              rw [hx, Finset.mem_singleton] at h1 h2
              exact h1.trans h2.symm
            by_cases hrcase : r + 2 < n
            · let x := oneEach (⟨r, by omega⟩ : Fin n) (⟨r + 2, hrcase⟩ : Fin n)
              let y := oneEach (⟨n - 1, by omega⟩ : Fin n) (⟨r + 2, hrcase⟩ : Fin n)
              have hg₁_val : ∀ z : List Bool, z.length = 2 * n → z.getD (n + (r + 1)) false = false →
                  val C z (2 * n + j₀) = false := by
                intro z hz hzf
                rw [← hz, val_gate C z j₀ hj₀lt, hg₁and, hab]
                have ha' : a < z.length + j₀ := by omega
                have hb' : b < z.length + j₀ := by omega
                simp only [List.map_cons, List.map_nil, ha', hb', ↓reduceIte, GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rcases hpair with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
                · rw [hb_eq, val_input C z (n + (r + 1)) (by omega), hzf]; simp
                · rw [ha_eq, val_input C z (n + (r + 1)) (by omega), hzf]; simp
              have hxf : x.getD (n + (r + 1)) false = false := by
                rw [oneEach_getD]
                have h1 : ¬ (n + (r + 1) < n) := by omega
                have h2 : n + (r + 1) < n + n := by omega
                have h3 : n + (r + 1) - n = r + 1 := by omega
                simp [h1, h2, h3]
              have hyf : y.getD (n + (r + 1)) false = false := by
                rw [oneEach_getD]
                have h1 : ¬ (n + (r + 1) < n) := by omega
                have h2 : n + (r + 1) < n + n := by omega
                have h3 : n + (r + 1) - n = r + 1 := by omega
                simp [h1, h2, h3]
              have heq : C.eval x = C.eval y := by
                apply eval_eq_of_iso C (2 * n) hc hout x y
                  (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega)
                  (fun i => i = r ∨ i = n - 1)
                · intro i hi hnb
                  push Not at hnb
                  simp only [x, y, oneEach_getD]
                  by_cases h1 : i < n
                  · simp [h1, hnb.1, hnb.2]
                  · simp [h1]
                · omega
                · intro j hj _
                  by_cases hjj : j = j₀
                  · subst hjj
                    left
                    rw [hg₁_val x (by rw [oneEach_length]; omega) hxf,
                        hg₁_val y (by rw [oneEach_length]; omega) hyf]
                  · right
                    intro u hu
                    rintro (rfl | rfl)
                    · exact hjj (hunique_r j hj hu)
                    · exact (hnotread_dummy j hj).1 hu
              have hx_eval : C.eval x = true := by rw [hr]; simp [LT]
              have hy_eval : C.eval y = false := by rw [hr]; simp [LT]; omega
              rw [hx_eval, hy_eval] at heq
              exact Bool.false_ne_true heq.symm
            · have hrpos : 0 < r := by omega
              let x := oneEach (⟨r - 1, by omega⟩ : Fin n) (⟨r + 1, by omega⟩ : Fin n)
              let y := oneEach (⟨r - 1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)
              have hg₁_val : ∀ z : List Bool, z.length = 2 * n → z.getD r false = false →
                  val C z (2 * n + j₀) = false := by
                intro z hz hzf
                rw [← hz, val_gate C z j₀ hj₀lt, hg₁and, hab]
                have ha' : a < z.length + j₀ := by omega
                have hb' : b < z.length + j₀ := by omega
                simp only [List.map_cons, List.map_nil, ha', hb', ↓reduceIte, GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rcases hpair with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
                · rw [ha_eq, val_input C z r (by omega), hzf]; simp
                · rw [hb_eq, val_input C z r (by omega), hzf]; simp
              have hxf : x.getD r false = false := by
                rw [oneEach_getD]
                have h1 : r < n := by omega
                have h2 : r ≠ r - 1 := by omega
                simp [h1, h2]
              have hyf : y.getD r false = false := by
                rw [oneEach_getD]
                have h1 : r < n := by omega
                have h2 : r ≠ r - 1 := by omega
                simp [h1, h2]
              have heq : C.eval x = C.eval y := by
                apply eval_eq_of_iso C (2 * n) hc hout x y
                  (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega)
                  (fun i => i = n + (r + 1) ∨ i = n)
                · intro i hi hnb
                  push Not at hnb
                  simp only [x, y, oneEach_getD]
                  by_cases h1 : i < n
                  · simp [h1]
                  · by_cases h2 : i < n + n
                    · have hne1 : i - n ≠ r + 1 := by omega
                      have hne2 : i - n ≠ 0 := by omega
                      simp [h1, h2, hne1, hne2]
                    · simp [h1, h2]
                · omega
                · intro j hj _
                  by_cases hjj : j = j₀
                  · subst hjj
                    left
                    rw [hg₁_val x (by rw [oneEach_length]; omega) hxf,
                        hg₁_val y (by rw [oneEach_length]; omega) hyf]
                  · right
                    intro u hu
                    rintro (rfl | rfl)
                    · exact hjj (hunique_c j hj hu)
                    · exact (hnotread_dummy j hj).2 hu
              have hx_eval : C.eval x = true := by rw [hr]; simp [LT]
              have hy_eval : C.eval y = false := by rw [hr]; simp [LT]
              rw [hx_eval, hy_eval] at heq
              exact Bool.false_ne_true heq.symm
    have hkill_le : (KGates Z C (2 * n)).card ≤ C.gates.length := by
      have hsub : KGates Z C (2 * n) ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
      exact (Finset.card_le_card hsub).trans (by simp)
    refine ⟨by omega, ?_⟩
    obtain ⟨C', hm', hs', hr'⟩ := hred.2
    change C'.size ≤ C.gates.length - (KGates Z C (2 * n)).card at hs'
    exact ⟨C', hm', by omega, hr'⟩
  · -- Move 2: every active input has deg = 1 and is only read by OR gates
    push Not at hmove1
    have hact_deg1 : ∀ w, Active n w → deg C w = 1 := by
      intro w hw
      have h1 := hact w hw
      have h2 := (hmove1 w hw).1
      omega
    have hact_no_and : ∀ w, Active n w → ∀ j (hj : j < C.gates.length),
        w ∈ C.gates[j].inputs → C.gates[j].op = GateOp.or := by
      intro w hw j hj hmem
      have hop := (hc.1 _ (List.getElem_mem hj)).1
      have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
      exact hop'.resolve_left (fun hand => (hmove1 w hw).2 j hj hand hmem)
    -- Step A: Find first AND gate gStar
    obtain ⟨gAny, hgAny, hgAnyAnd⟩ := exists_and_gate n (by omega) C hc hout_last hpos hr
    let andSet := (Finset.range C.gates.length).filter (fun j =>
      if hj : j < C.gates.length then isAndOp C.gates[j].op else false)
    have hand_ne : andSet.Nonempty := by
      refine ⟨gAny, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hgAny, ?_⟩⟩
      simp [hgAny, hgAnyAnd, isAndOp]
    let gStar := andSet.min' hand_ne
    have hgStar_mem : gStar ∈ andSet := Finset.min'_mem _ hand_ne
    have hgStar_lt : gStar < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hgStar_mem).1
    have hgStar_and : C.gates[gStar].op = GateOp.and := by
      have h := (Finset.mem_filter.mp hgStar_mem).2
      simp only [hgStar_lt, ↓reduceDIte] at h
      have hop := (hc.1 _ (List.getElem_mem hgStar_lt)).1
      have hop' : C.gates[gStar].op = GateOp.and ∨ C.gates[gStar].op = GateOp.or := by simpa using hop
      rcases hop' with h1 | h2
      · exact h1
      · simp [h2, isAndOp] at h
    have hbefore_or : ∀ (j : ℕ) (hj : j < gStar), (C.gates[j]'(by omega)).op = GateOp.or := by
      intro j hj
      have hjlt : j < C.gates.length := by omega
      have hop := (hc.1 _ (List.getElem_mem hjlt)).1
      have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
      rcases hop' with hand | hor
      · exfalso
        have hmem : j ∈ andSet := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hjlt, by simp [hjlt, hand, isAndOp]⟩
        have hle := Finset.min'_le andSet j hmem
        change gStar ≤ j at hle
        omega
      · exact hor
    -- Step B: Find min k < gStar with deg (2n + k) >= 2 or read by an AND gate
    let Tset := (Finset.range gStar).filter (fun j =>
      decide (2 ≤ deg C (2 * n + j)) ||
      (List.range C.gates.length).any (fun h =>
        if hh : h < C.gates.length then
          isAndOp C.gates[h].op && decide (2 * n + j ∈ C.gates[h].inputs)
        else false))
    have hT_ne : Tset.Nonempty := by
      obtain ⟨a, b, hab, ha, _, _⟩ := hc.2.1 gStar hgStar_lt
      have ha_mem : a ∈ C.gates[gStar].inputs := by rw [hab]; simp
      have ha_ge : 2 * n ≤ a := by
        by_contra hlt
        push Not at hlt
        by_cases hd1 : a = n - 1
        · subst hd1; exact (hnotread_dummy gStar hgStar_lt).1 ha_mem
        · by_cases hd2 : a = n
          · subst hd2; exact (hnotread_dummy gStar hgStar_lt).2 ha_mem
          · have hact_a : Active n a := by unfold Active; omega
            have hor_g := hact_no_and a hact_a gStar hgStar_lt ha_mem
            rw [hgStar_and] at hor_g
            exact GateOp.noConfusion hor_g
      refine ⟨a - 2 * n, ?_⟩
      unfold Tset
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      simp only [Bool.or_eq_true]
      right
      rw [List.any_eq_true]
      refine ⟨gStar, List.mem_range.mpr hgStar_lt, ?_⟩
      simp only [hgStar_lt, ↓reduceDIte, hgStar_and, isAndOp, Bool.true_and, decide_eq_true_eq]
      rwa [show 2 * n + (a - 2 * n) = a by omega]
    let k := Tset.min' hT_ne
    have hk_mem : k ∈ Tset := Finset.min'_mem _ hT_ne
    have hk_lt_gStar : k < gStar := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
    have hk_lt : k < C.gates.length := by omega
    have hk_cond : 2 ≤ deg C (2 * n + k) ∨
        ∃ h, ∃ hh : h < C.gates.length, C.gates[h].op = GateOp.and ∧ 2 * n + k ∈ C.gates[h].inputs := by
      have h := (Finset.mem_filter.mp hk_mem).2
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h1 | h2
      · exact Or.inl h1
      · right
        rw [List.any_eq_true] at h2
        obtain ⟨h', hh', hcond⟩ := h2
        have hh'lt : h' < C.gates.length := List.mem_range.mp hh'
        simp only [hh'lt, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hcond
        have hop := (hc.1 _ (List.getElem_mem hh'lt)).1
        have hop' : C.gates[h'].op = GateOp.and ∨ C.gates[h'].op = GateOp.or := by simpa using hop
        rcases hop' with hand | hor
        · exact ⟨h', hh'lt, hand, hcond.2⟩
        · simp [hor, isAndOp] at hcond
    have hk_all_or : ∀ (j : ℕ) (hj : j ≤ k), (C.gates[j]'(by omega)).op = GateOp.or :=
      fun j hj => hbefore_or j (by omega)
    have hdeg_le1_lt_k : ∀ w < 2 * n + k, deg C w ≤ 1 := by
      intro w hw
      by_cases hwN : w < 2 * n
      · by_cases hd1 : w = n - 1
        · subst hd1; omega
        · by_cases hd2 : w = n
          · subst hd2; omega
          · have : Active n w := by unfold Active; omega
            have := hact_deg1 w this
            omega
      · set r := w - 2 * n
        have hrk : r < k := by omega
        by_contra hgt
        push Not at hgt
        have hrT : r ∈ Tset := by
          unfold Tset
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          left
          rwa [show 2 * n + r = w by omega]
        have hle := Finset.min'_le Tset r hrT
        change k ≤ r at hle
        omega
    -- Isolation lemma for k
    have hk_iso : ∀ x y : List Bool, x.length = 2 * n → y.length = 2 * n →
        (∀ i < 2 * n, reaches C (2 * n) (2 * n + k) i = false → i ≠ n - 1 → i ≠ n →
          x.getD i false = y.getD i false) →
        val C x (2 * n + k) = val C y (2 * n + k) →
        C.eval x = C.eval y := by
      intro x y hx hy h_inp hvalk
      apply eval_eq_of_iso C (2 * n) hc hout x y hx hy
        (fun w => (w < 2 * n + k ∧ reaches C (2 * n) (2 * n + k) w = true) ∨ w = n - 1 ∨ w = n)
      · intro i hi hnb
        push Not at hnb
        have hrf : reaches C (2 * n) (2 * n + k) i = false := by
          cases h : reaches C (2 * n) (2 * n + k) i
          · rfl
          · exact False.elim (hnb.1 (by omega) h)
        exact h_inp i hi hrf hnb.2.1 hnb.2.2
      · omega
      · intro j hj hnb
        by_cases hjk : j = k
        · subst hjk; exact Or.inl hvalk
        · right
          intro u hu
          rintro (⟨hult, hru⟩ | rfl | rfl)
          · obtain ⟨j', hj', hle', hrj', humem'⟩ :=
              reaches_step_out C (2 * n) hc (2 * n + k) u (by omega) hult hru
            have hj_eq : j = j' := by
              have h1 : j ∈ readers C u := (mem_readers_iff C u j).mpr ⟨hj, hu⟩
              have h2 : j' ∈ readers C u := (mem_readers_iff C u j').mpr ⟨hj', humem'⟩
              have hd : (readers C u).card ≤ 1 := hdeg_le1_lt_k u hult
              have hpos_u : 1 ≤ (readers C u).card := Finset.card_pos.mpr ⟨j, h1⟩
              obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (by omega : (readers C u).card = 1)
              rw [hz, Finset.mem_singleton] at h1 h2
              exact h1.trans h2.symm
            subst hj_eq
            have hjlt : 2 * n + j < 2 * n + k := by omega
            exact hnb (Or.inl ⟨hjlt, hrj'⟩)
          · exact (hnotread_dummy j hj).1 hu
          · exact (hnotread_dummy j hj).2 hu
    -- Cone inputs of any wire w <= 2*n + k
    let coneIn (w : ℕ) : Finset ℕ :=
      (Finset.range (2 * n)).filter (fun i => reaches C (2 * n) w i)
    -- No dummy wire in coneIn (2*n + k)
    have hcone_no_dummy : n - 1 ∉ coneIn (2 * n + k) ∧ n ∉ coneIn (2 * n + k) := by
      constructor
      · intro hm1
        have hr1 : reaches C (2 * n) (2 * n + k) (n - 1) = true := (Finset.mem_filter.mp hm1).2
        obtain ⟨j', hj', _, _, hmem⟩ :=
          reaches_step_out C (2 * n) hc (2 * n + k) (n - 1) (by omega) (by omega) hr1
        exact (hnotread_dummy j' hj').1 hmem
      · intro hm2
        have hr2 : reaches C (2 * n) (2 * n + k) n = true := (Finset.mem_filter.mp hm2).2
        obtain ⟨j', hj', _, _, hmem⟩ :=
          reaches_step_out C (2 * n) hc (2 * n + k) n (by omega) (by omega) hr2
        exact (hnotread_dummy j' hj').2 hmem
    -- At most 1 left active wire and at most 1 right active wire in coneIn (2*n + k)
    have hcone_left_uniq : ∀ i₁ ∈ coneIn (2 * n + k), ∀ i₂ ∈ coneIn (2 * n + k),
        i₁ < n - 1 → i₂ < n - 1 → i₁ = i₂ := by
      intro i₁ hi₁ i₂ hi₂ h1 h2
      by_contra hne
      wlog hlt12 : i₁ < i₂ generalizing i₁ i₂
      · exact this i₂ hi₂ i₁ hi₁ h2 h1 (Ne.symm hne) (by omega)
      have hr₁ : reaches C (2 * n) (2 * n + k) i₁ = true := (Finset.mem_filter.mp hi₁).2
      have hr₂ : reaches C (2 * n) (2 * n + k) i₂ = true := (Finset.mem_filter.mp hi₂).2
      let x := oneEach (⟨i₁, by omega⟩ : Fin n) (⟨i₁ + 1, by omega⟩ : Fin n)
      let y := oneEach (⟨i₂, by omega⟩ : Fin n) (⟨i₁ + 1, by omega⟩ : Fin n)
      have hvk_x : val C x (2 * n + k) = true := by
        rw [val_all_or_iff C (2 * n) k hc hk_lt hk_all_or x (by rw [oneEach_length]; omega) _ (le_refl _)]
        exact ⟨i₁, by omega, hr₁, by rw [oneEach_getD]; simp [show i₁ < n by omega]⟩
      have hvk_y : val C y (2 * n + k) = true := by
        rw [val_all_or_iff C (2 * n) k hc hk_lt hk_all_or y (by rw [oneEach_length]; omega) _ (le_refl _)]
        exact ⟨i₂, by omega, hr₂, by rw [oneEach_getD]; simp [show i₂ < n by omega]⟩
      have heq : C.eval x = C.eval y := by
        apply hk_iso x y (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) _ (by rw [hvk_x, hvk_y])
        intro i hi hrf _ _
        have hne1 : i ≠ i₁ := fun h => by rw [h, hr₁] at hrf; exact Bool.false_ne_true hrf.symm
        have hne2 : i ≠ i₂ := fun h => by rw [h, hr₂] at hrf; exact Bool.false_ne_true hrf.symm
        simp only [x, y, oneEach_getD]
        by_cases hin : i < n
        · simp [hin, hne1, hne2]
        · simp [hin]
      have hx_eval : C.eval x = true := by rw [hr]; simp [LT]
      have hy_eval : C.eval y = false := by rw [hr]; simp [LT]; omega
      rw [hx_eval, hy_eval] at heq
      exact Bool.false_ne_true heq.symm
    have hcone_right_uniq : ∀ i₁ ∈ coneIn (2 * n + k), ∀ i₂ ∈ coneIn (2 * n + k),
        n < i₁ → n < i₂ → i₁ = i₂ := by
      intro i₁ hi₁ i₂ hi₂ h1 h2
      have hi₁_lt : i₁ < 2 * n := Finset.mem_range.mp (Finset.mem_filter.mp hi₁).1
      have hi₂_lt : i₂ < 2 * n := Finset.mem_range.mp (Finset.mem_filter.mp hi₂).1
      by_contra hne
      wlog hlt12 : i₁ < i₂ generalizing i₁ i₂
      · exact this i₂ hi₂ i₁ hi₁ h2 h1 hi₂_lt hi₁_lt (Ne.symm hne) (by omega)
      have hr₁ : reaches C (2 * n) (2 * n + k) i₁ = true := (Finset.mem_filter.mp hi₁).2
      have hr₂ : reaches C (2 * n) (2 * n + k) i₂ = true := (Finset.mem_filter.mp hi₂).2
      let x := oneEach (⟨i₂ - n - 1, by omega⟩ : Fin n) (⟨i₂ - n, by omega⟩ : Fin n)
      let y := oneEach (⟨i₂ - n - 1, by omega⟩ : Fin n) (⟨i₁ - n, by omega⟩ : Fin n)
      have hvk_x : val C x (2 * n + k) = true := by
        rw [val_all_or_iff C (2 * n) k hc hk_lt hk_all_or x (by rw [oneEach_length]; omega) _ (le_refl _)]
        refine ⟨i₂, by omega, hr₂, ?_⟩
        rw [oneEach_getD]
        have ha : ¬ (i₂ < n) := by omega
        have hb : i₂ < n + n := by omega
        simp [ha, hb]
      have hvk_y : val C y (2 * n + k) = true := by
        rw [val_all_or_iff C (2 * n) k hc hk_lt hk_all_or y (by rw [oneEach_length]; omega) _ (le_refl _)]
        refine ⟨i₁, by omega, hr₁, ?_⟩
        rw [oneEach_getD]
        have ha : ¬ (i₁ < n) := by omega
        have hb : i₁ < n + n := by omega
        simp [ha, hb]
      have heq : C.eval x = C.eval y := by
        apply hk_iso x y (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega) _ (by rw [hvk_x, hvk_y])
        intro i hi hrf _ _
        have hne1 : i ≠ i₁ := fun h => by rw [h, hr₁] at hrf; exact Bool.false_ne_true hrf.symm
        have hne2 : i ≠ i₂ := fun h => by rw [h, hr₂] at hrf; exact Bool.false_ne_true hrf.symm
        simp only [x, y, oneEach_getD]
        by_cases hin : i < n
        · simp [hin]
        · by_cases hi2 : i < n + n
          · have hn1 : i - n ≠ i₁ - n := by omega
            have hn2 : i - n ≠ i₂ - n := by omega
            simp [hin, hi2, hn1, hn2]
          · simp [hin, hi2]
      have hx_eval : C.eval x = true := by rw [hr]; simp [LT]; omega
      have hy_eval : C.eval y = false := by rw [hr]; simp [LT]; omega
      rw [hx_eval, hy_eval] at heq
      exact Bool.false_ne_true heq.symm
    have hcone_card_le2 : (coneIn (2 * n + k)).card ≤ 2 := by
      let Lset := (coneIn (2 * n + k)).filter (fun i => i < n - 1)
      let Rset := (coneIn (2 * n + k)).filter (fun i => n < i)
      have hsub : coneIn (2 * n + k) ⊆ Lset ∪ Rset := by
        intro i hi
        have hilt : i < 2 * n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have hne1 : i ≠ n - 1 := fun h => hcone_no_dummy.1 (h ▸ hi)
        have hne2 : i ≠ n := fun h => hcone_no_dummy.2 (h ▸ hi)
        rw [Finset.mem_union]
        by_cases h1 : i < n - 1
        · exact Or.inl (Finset.mem_filter.mpr ⟨hi, h1⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨hi, by omega⟩)
      have hLle1 : Lset.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
        rw [Finset.mem_filter] at ha hb
        exact hcone_left_uniq a ha.1 b hb.1 ha.2 hb.2
      have hRle1 : Rset.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
        rw [Finset.mem_filter] at ha hb
        exact hcone_right_uniq a ha.1 b hb.1 ha.2 hb.2
      calc (coneIn (2 * n + k)).card
          ≤ (Lset ∪ Rset).card := Finset.card_le_card hsub
        _ ≤ Lset.card + Rset.card := Finset.card_union_le Lset Rset
        _ ≤ 2 := by omega
    -- Disjointness of coneIn for inputs of any gate j <= k
    have hdisj_cone : ∀ (j : ℕ) (hjk : j ≤ k), ∀ u v, (C.gates[j]'(by omega)).inputs = [u, v] →
        Disjoint (coneIn u) (coneIn v) := by
      intro j hjk u v huv
      have hjlt : j < C.gates.length := by omega
      obtain ⟨a', b', hab', ha', hb', hne'⟩ := hc.2.1 j hjlt
      rw [huv] at hab'
      injection hab' with h1 h2
      injection h2 with h3 _
      subst h1; subst h3
      rw [Finset.disjoint_left]
      intro i₀ hi₀u hi₀v
      have hru : reaches C (2 * n) u i₀ = true := (Finset.mem_filter.mp hi₀u).2
      have hrv : reaches C (2 * n) v i₀ = true := (Finset.mem_filter.mp hi₀v).2
      have hi₀lt : i₀ < 2 * n := Finset.mem_range.mp (Finset.mem_filter.mp hi₀u).1
      let common := (Finset.range (2 * n + j)).filter (fun m =>
        reaches C (2 * n) u m && reaches C (2 * n) v m)
      have hcomm_ne : common.Nonempty := by
        refine ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
        simp [hru, hrv]
      let m := common.max' hcomm_ne
      have hm_mem : m ∈ common := Finset.max'_mem _ hcomm_ne
      have hm_lt : m < 2 * n + j := Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1
      have hm_cond : reaches C (2 * n) u m = true ∧ reaches C (2 * n) v m = true := by
        have h := (Finset.mem_filter.mp hm_mem).2
        simp only [Bool.and_eq_true] at h
        exact h
      have hmu_le : m ≤ u := reaches_le C (2 * n) u m hm_cond.1
      have hmv_le : m ≤ v := reaches_le C (2 * n) v m hm_cond.2
      by_cases hmeq : m = u ∨ m = v
      · rcases hmeq with hmu | hmv
        · have hrvu : reaches C (2 * n) v u = true := hmu ▸ hm_cond.2
          have hval_eq : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x v := by
            intro x hx
            rw [← hx, val_gate C x j hjlt, hk_all_or j hjk, huv]
            have ha'' : u < x.length + j := by omega
            have hb'' : v < x.length + j := by omega
            simp only [List.map_cons, List.map_nil, ha'', hb'', ↓reduceIte, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            cases hvu : val C x u
            · simp
            · have hvv : val C x v = true :=
                val_of_reaches_or C (2 * n) k hc hk_lt hk_all_or x hx v u (by omega) hrvu hvu
              simp [hvv]
          have hrep' : Represents (LT n) (elimAlias C (2 * n) j v) := by
            intro p q
            rw [elimAlias_eval C (2 * n) j v hjlt hb' _ (by rw [oneEach_length]; omega)
              (Or.inl (hval_eq _ (by rw [oneEach_length]; omega)))]
            exact hr p q
          have hle := hmin _ (elimAlias_mono C (2 * n) j v hm) hrep'
          rw [elimAlias_size C (2 * n) j v hjlt] at hle
          change C.gates.length ≤ C.gates.length - 1 at hle
          omega
        · have hruv : reaches C (2 * n) u v = true := hmv ▸ hm_cond.1
          have hval_eq : ∀ x : List Bool, x.length = 2 * n → val C x (2 * n + j) = val C x u := by
            intro x hx
            rw [← hx, val_gate C x j hjlt, hk_all_or j hjk, huv]
            have ha'' : u < x.length + j := by omega
            have hb'' : v < x.length + j := by omega
            simp only [List.map_cons, List.map_nil, ha'', hb'', ↓reduceIte, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            cases hvv : val C x v
            · simp
            · have hvu : val C x u = true :=
                val_of_reaches_or C (2 * n) k hc hk_lt hk_all_or x hx u v (by omega) hruv hvv
              simp [hvu]
          have hrep' : Represents (LT n) (elimAlias C (2 * n) j u) := by
            intro p q
            rw [elimAlias_eval C (2 * n) j u hjlt ha' _ (by rw [oneEach_length]; omega)
              (Or.inl (hval_eq _ (by rw [oneEach_length]; omega)))]
            exact hr p q
          have hle := hmin _ (elimAlias_mono C (2 * n) j u hm) hrep'
          rw [elimAlias_size C (2 * n) j u hjlt] at hle
          change C.gates.length ≤ C.gates.length - 1 at hle
          omega
      · push Not at hmeq
        obtain ⟨j₁, hj₁, hle₁, hru₁, hm₁⟩ :=
          reaches_step_out C (2 * n) hc u m (by omega) (by omega) hm_cond.1
        obtain ⟨j₂, hj₂, hle₂, hrv₂, hm₂⟩ :=
          reaches_step_out C (2 * n) hc v m (by omega) (by omega) hm_cond.2
        have hj_eq : j₁ = j₂ := by
          have h1 : j₁ ∈ readers C m := (mem_readers_iff C m j₁).mpr ⟨hj₁, hm₁⟩
          have h2 : j₂ ∈ readers C m := (mem_readers_iff C m j₂).mpr ⟨hj₂, hm₂⟩
          have hd : (readers C m).card ≤ 1 := hdeg_le1_lt_k m (by omega)
          have hpos_m : 1 ≤ (readers C m).card := Finset.card_pos.mpr ⟨j₁, h1⟩
          obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (by omega : (readers C m).card = 1)
          rw [hz, Finset.mem_singleton] at h1 h2
          exact h1.trans h2.symm
        subst hj_eq
        have hmem_next : 2 * n + j₁ ∈ common := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          simp [hru₁, hrv₂]
        have hle_max := Finset.le_max' common (2 * n + j₁) hmem_next
        change 2 * n + j₁ ≤ m at hle_max
        obtain ⟨x₁, y₁, hxy₁, hx₁, hy₁, _⟩ := hc.2.1 j₁ hj₁
        have hm_lt1 : m < 2 * n + j₁ := by
          rw [hxy₁] at hm₁
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm₁
          rcases hm₁ with rfl | rfl <;> omega
        omega
    -- Lower bound on (coneIn w).card for w <= 2*n + k
    have hcone_card_ge : ∀ w ≤ 2 * n + k,
        (if w < 2 * n then 1 else 2) ≤ (coneIn w).card := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < 2 * n
        · simp only [hlt, ↓reduceIte]
          apply Finset.card_pos.mpr
          refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, reaches_self C (2 * n) w⟩⟩
        · simp only [hlt, ↓reduceIte]
          set j := w - 2 * n
          have hjk : j ≤ k := by omega
          have hjlt : j < C.gates.length := by omega
          have hw_eq : w = 2 * n + j := by omega
          obtain ⟨u, v, huv, hu, hv, _⟩ := hc.2.1 j hjlt
          have hsub : coneIn u ∪ coneIn v ⊆ coneIn w := by
            intro i hi
            rw [Finset.mem_union] at hi
            rw [Finset.mem_filter, Finset.mem_range]
            rcases hi with hiu | hiv
            · have hi' := Finset.mem_filter.mp hiu
              refine ⟨Finset.mem_range.mp hi'.1, ?_⟩
              rw [hw_eq, reaches_gate_iff C (2 * n) j i hc hjlt]
              exact Or.inr ⟨u, by rw [huv]; simp, hi'.2⟩
            · have hi' := Finset.mem_filter.mp hiv
              refine ⟨Finset.mem_range.mp hi'.1, ?_⟩
              rw [hw_eq, reaches_gate_iff C (2 * n) j i hc hjlt]
              exact Or.inr ⟨v, by rw [huv]; simp, hi'.2⟩
          have hdisj := hdisj_cone j hjk u v huv
          have hcu := ih u (by omega) (by omega)
          have hcv := ih v (by omega) (by omega)
          have h1 : 1 ≤ (coneIn u).card := by split_ifs at hcu <;> omega
          have h2 : 1 ≤ (coneIn v).card := by split_ifs at hcv <;> omega
          have h3 := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisj] at h3
          omega
    -- Therefore BOTH inputs of k are input wires < 2*n!
    obtain ⟨u_k, v_k, huv_k, hu_k, hv_k, hne_k⟩ := hc.2.1 k hk_lt
    have huk_inp : u_k < 2 * n := by
      by_contra hge
      have hdisj := hdisj_cone k (le_refl k) u_k v_k huv_k
      have hsub : coneIn u_k ∪ coneIn v_k ⊆ coneIn (2 * n + k) := by
        intro i hi
        rw [Finset.mem_union] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hi with hiu | hiv
        · have hi' := Finset.mem_filter.mp hiu
          exact ⟨Finset.mem_range.mp hi'.1, (reaches_gate_iff C (2 * n) k i hc hk_lt).mpr
            (Or.inr ⟨u_k, by rw [huv_k]; simp, hi'.2⟩)⟩
        · have hi' := Finset.mem_filter.mp hiv
          exact ⟨Finset.mem_range.mp hi'.1, (reaches_gate_iff C (2 * n) k i hc hk_lt).mpr
            (Or.inr ⟨v_k, by rw [huv_k]; simp, hi'.2⟩)⟩
      have hcu := hcone_card_ge u_k (by omega)
      have hcv := hcone_card_ge v_k (by omega)
      simp only [hge, ↓reduceIte] at hcu
      have hcv1 : 1 ≤ (coneIn v_k).card := by split_ifs at hcv <;> omega
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at h3
      omega
    have hvk_inp : v_k < 2 * n := by
      by_contra hge
      have hdisj := hdisj_cone k (le_refl k) u_k v_k huv_k
      have hsub : coneIn u_k ∪ coneIn v_k ⊆ coneIn (2 * n + k) := by
        intro i hi
        rw [Finset.mem_union] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hi with hiu | hiv
        · have hi' := Finset.mem_filter.mp hiu
          exact ⟨Finset.mem_range.mp hi'.1, (reaches_gate_iff C (2 * n) k i hc hk_lt).mpr
            (Or.inr ⟨u_k, by rw [huv_k]; simp, hi'.2⟩)⟩
        · have hi' := Finset.mem_filter.mp hiv
          exact ⟨Finset.mem_range.mp hi'.1, (reaches_gate_iff C (2 * n) k i hc hk_lt).mpr
            (Or.inr ⟨v_k, by rw [huv_k]; simp, hi'.2⟩)⟩
      have hcu := hcone_card_ge u_k (by omega)
      have hcv := hcone_card_ge v_k (by omega)
      simp only [hge, ↓reduceIte] at hcv
      have hcu1 : 1 ≤ (coneIn u_k).card := by simp only [huk_inp, ↓reduceIte] at hcu; exact hcu
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at h3
      omega
    have huk_mem_cone : u_k ∈ coneIn (2 * n + k) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨huk_inp, (reaches_gate_iff C (2 * n) k u_k hc hk_lt).mpr
        (Or.inr ⟨u_k, by rw [huv_k]; simp, reaches_self C (2 * n) u_k⟩)⟩
    have hvk_mem_cone : v_k ∈ coneIn (2 * n + k) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hvk_inp, (reaches_gate_iff C (2 * n) k v_k hc hk_lt).mpr
        (Or.inr ⟨v_k, by rw [huv_k]; simp, reaches_self C (2 * n) v_k⟩)⟩
    -- So one of {u_k, v_k} is a < n - 1 and the other is n + bR with 1 <= bR < n
    have hpair_LR : ∃ a bR, a < n - 1 ∧ 1 ≤ bR ∧ bR < n ∧
        ((u_k = a ∧ v_k = n + bR) ∨ (u_k = n + bR ∧ v_k = a)) := by
      have hu_nd1 : u_k ≠ n - 1 := fun h => hcone_no_dummy.1 (h ▸ huk_mem_cone)
      have hu_nd2 : u_k ≠ n := fun h => hcone_no_dummy.2 (h ▸ huk_mem_cone)
      have hv_nd1 : v_k ≠ n - 1 := fun h => hcone_no_dummy.1 (h ▸ hvk_mem_cone)
      have hv_nd2 : v_k ≠ n := fun h => hcone_no_dummy.2 (h ▸ hvk_mem_cone)
      by_cases huL : u_k < n - 1
      · by_cases hvL : v_k < n - 1
        · exact False.elim (hne_k (hcone_left_uniq u_k huk_mem_cone v_k hvk_mem_cone huL hvL))
        · exact ⟨u_k, v_k - n, huL, by omega, by omega, Or.inl ⟨rfl, by omega⟩⟩
      · by_cases hvL : v_k < n - 1
        · exact ⟨v_k, u_k - n, hvL, by omega, by omega, Or.inr ⟨by omega, rfl⟩⟩
        · exact False.elim (hne_k (hcone_right_uniq u_k huk_mem_cone v_k hvk_mem_cone (by omega) (by omega)))
    obtain ⟨a, bR, ha_lt, hbR_ge, hbR_lt, hpair_k⟩ := hpair_LR
    -- Prove bR <= a (otherwise a < bR contradicts LT n via leaf-gate isolation!)
    have h_leaf_no_edge : ∀ g (hg : g < C.gates.length), ∀ r c,
        r < n - 1 → 1 ≤ c → c < n → r < c →
        ¬ (r ∈ C.gates[g].inputs ∧ n + c ∈ C.gates[g].inputs) := by
      intro g hg r c hrlt hcge hclt hrc ⟨hmr, hmc⟩
      have hor_g : C.gates[g].op = GateOp.or :=
        hact_no_and r (Or.inl hrlt) g hg hmr
      have huniq_c : ∀ j (hj : j < C.gates.length), n + c ∈ C.gates[j].inputs → j = g := by
        intro j hj hm
        have h1 : j ∈ readers C (n + c) := (mem_readers_iff C (n + c) j).mpr ⟨hj, hm⟩
        have h2 : g ∈ readers C (n + c) := (mem_readers_iff C (n + c) g).mpr ⟨hg, hmc⟩
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hact_deg1 (n + c) (Or.inr ⟨by omega, by omega⟩))
        rw [hz, Finset.mem_singleton] at h1 h2
        exact h1.trans h2.symm
      let x := oneEach (⟨r, by omega⟩ : Fin n) (⟨c, hclt⟩ : Fin n)
      let y := oneEach (⟨r, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)
      have hvg_true : ∀ z : List Bool, z.length = 2 * n → z.getD r false = true →
          val C z (2 * n + g) = true := by
        intro z hz hzr
        rw [← hz, val_gate C z g hg, hor_g]
        simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
        refine ⟨true, ⟨r, hmr, ?_⟩, rfl⟩
        have hrltz : r < z.length + g := by omega
        simp only [hrltz, ↓reduceIte]
        rw [val_input C z r (by omega), hzr]
      have hxr : x.getD r false = true := by rw [oneEach_getD]; simp [show r < n by omega]
      have hyr : y.getD r false = true := by rw [oneEach_getD]; simp [show r < n by omega]
      have heq : C.eval x = C.eval y := by
        apply eval_eq_of_iso C (2 * n) hc hout x y
          (by rw [oneEach_length]; omega) (by rw [oneEach_length]; omega)
          (fun i => i = n + c ∨ i = n)
        · intro i hi hnb
          push Not at hnb
          simp only [x, y, oneEach_getD]
          by_cases h1 : i < n
          · simp [h1]
          · by_cases h2 : i < n + n
            · have hn1 : i - n ≠ c := by omega
              have hn2 : i - n ≠ 0 := by omega
              simp [h1, h2, hn1, hn2]
            · simp [h1, h2]
        · omega
        · intro j hj _
          by_cases hjg : j = g
          · subst hjg
            left
            rw [hvg_true x (by rw [oneEach_length]; omega) hxr,
                hvg_true y (by rw [oneEach_length]; omega) hyr]
          · right
            intro u hu
            rintro (rfl | rfl)
            · exact hjg (huniq_c j hj hu)
            · exact (hnotread_dummy j hj).2 hu
      have hx_eval : C.eval x = true := by rw [hr]; simp [LT]; exact hrc
      have hy_eval : C.eval y = false := by rw [hr]; simp [LT]
      rw [hx_eval, hy_eval] at heq
      exact Bool.false_ne_true heq.symm
    have ha_mem_k : a ∈ C.gates[k].inputs := by
      rw [huv_k]; rcases hpair_k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hbR_mem_k : n + bR ∈ C.gates[k].inputs := by
      rw [huv_k]; rcases hpair_k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hbR_le_a : bR ≤ a := by
      by_contra hlt
      exact h_leaf_no_edge k hk_lt a bR ha_lt hbR_ge hbR_lt (by omega) ⟨ha_mem_k, hbR_mem_k⟩
    have huniq_a : ∀ j (hj : j < C.gates.length), a ∈ C.gates[j].inputs → j = k := by
      intro j hj hm
      have h1 : j ∈ readers C a := (mem_readers_iff C a j).mpr ⟨hj, hm⟩
      have h2 : k ∈ readers C a := (mem_readers_iff C a k).mpr ⟨hk_lt, ha_mem_k⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hact_deg1 a (Or.inl ha_lt))
      rw [hz, Finset.mem_singleton] at h1 h2
      exact h1.trans h2.symm
    have huniq_bR : ∀ j (hj : j < C.gates.length), n + bR ∈ C.gates[j].inputs → j = k := by
      intro j hj hm
      have h1 : j ∈ readers C (n + bR) := (mem_readers_iff C (n + bR) j).mpr ⟨hj, hm⟩
      have h2 : k ∈ readers C (n + bR) := (mem_readers_iff C (n + bR) k).mpr ⟨hk_lt, hbR_mem_k⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hact_deg1 (n + bR) (Or.inr ⟨by omega, by omega⟩))
      rw [hz, Finset.mem_singleton] at h1 h2
      exact h1.trans h2.symm
    -- Split Case 2A (bR = a) vs Case 2B (bR < a)
    by_cases hcase2A : bR = a
    · -- Case 2A: zero Z = {a, n + a} -> LT (n - 1), kills >= 3 gates
      left
      subst hcase2A
      let Z : Finset ℕ := {bR, n + bR}
      have hZ_lt : ∀ u ∈ Z, u < 2 * n := by
        intro u hu
        simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> omega
      have hred := reduce1 n hn C hc hout hr bR bR (by omega) (by omega) (Or.inl rfl)
      have hid := killed_card_identity Z C (2 * n) hc hZ_lt hred.1
      have hsumZ : ∑ u ∈ Z, deg C u = 2 := by
        have hne : bR ≠ n + bR := by omega
        rw [Finset.sum_pair hne, hact_deg1 bR (Or.inl ha_lt),
            hact_deg1 (n + bR) (Or.inr ⟨by omega, by omega⟩)]
      have hkZ : k ∈ ZGates Z C (2 * n) := by
        unfold ZGates
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_⟩
        rw [isZero_gate Z C (2 * n) k hc hk_lt, hk_all_or k (le_refl k), huv_k]
        simp only [isAndOp, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil,
          Bool.and_true, Bool.and_eq_true]
        rcases hpair_k with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [hu, hv, isZero_input Z C (2 * n) bR (by omega), isZero_input Z C (2 * n) (n + bR) (by omega)]
          simp [Z]
        · rw [hu, hv, isZero_input Z C (2 * n) (n + bR) (by omega), isZero_input Z C (2 * n) bR (by omega)]
          simp [Z]
      have hkill3 : 3 ≤ (KGates Z C (2 * n)).card := by
        rcases hk_cond with hdeg2 | ⟨h₁, hh₁, hh₁and, hkh₁⟩
        · have hterm : deg C (2 * n + k) - 1 ≤
              ∑ j ∈ ZGates Z C (2 * n), (deg C (2 * n + j) - 1) :=
            Finset.single_le_sum (f := fun j => deg C (2 * n + j) - 1) (fun _ _ => Nat.zero_le _) hkZ
          omega
        · have hh₁Z : h₁ ∈ ZGates Z C (2 * n) := by
            unfold ZGates
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hh₁, ?_⟩
            rw [isZero_gate Z C (2 * n) h₁ hc hh₁, hh₁and]
            simp only [isAndOp, ↓reduceIte, List.any_eq_true]
            refine ⟨2 * n + k, hkh₁, ?_⟩
            unfold ZGates at hkZ; exact (Finset.mem_filter.mp hkZ).2
          have hh₁_ne_k : h₁ ≠ k := by
            obtain ⟨x, y, hxy, hx, hy, _⟩ := hc.2.1 h₁ hh₁
            rw [hxy] at hkh₁
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hkh₁
            rcases hkh₁ with h1 | h2 <;> omega
          let rem := (ZGates Z C (2 * n)).erase k
          have hrem_ne : rem.Nonempty := ⟨h₁, Finset.mem_erase.mpr ⟨hh₁_ne_k, hh₁Z⟩⟩
          let k₁ := rem.min' hrem_ne
          have hk₁_mem : k₁ ∈ rem := Finset.min'_mem _ hrem_ne
          have hk₁_ne : k₁ ≠ k := (Finset.mem_erase.mp hk₁_mem).1
          have hk₁Z : k₁ ∈ ZGates Z C (2 * n) := (Finset.mem_erase.mp hk₁_mem).2
          have hk₁lt : k₁ < C.gates.length := by
            unfold ZGates at hk₁Z; exact Finset.mem_range.mp (Finset.mem_filter.mp hk₁Z).1
          by_cases hin1 : inZero Z C (2 * n) k₁ ≤ 1
          · have hterm : 2 - inZero Z C (2 * n) k₁ ≤
                ∑ j ∈ ZGates Z C (2 * n), (2 - inZero Z C (2 * n) j) :=
              Finset.single_le_sum (f := fun j => 2 - inZero Z C (2 * n) j) (fun _ _ => Nat.zero_le _) hk₁Z
            omega
          · -- Impossible: k₁ has 2 distinct inputs in Z ∪ {2n + k}, cannot read bR or n + bR
            exfalso
            obtain ⟨u₁, v₁, huv₁, hu₁, hv₁, hne₁⟩ := hc.2.1 k₁ hk₁lt
            have hin_eq := inZero_eq_pair Z C (2 * n) k₁ u₁ v₁ hk₁lt huv₁
            have hzu₁ : isZero Z C (2 * n) u₁ = true := by
              cases h : isZero Z C (2 * n) u₁
              · simp [h] at hin_eq; split_ifs at hin_eq <;> omega
              · rfl
            have hzv₁ : isZero Z C (2 * n) v₁ = true := by
              cases h : isZero Z C (2 * n) v₁
              · simp [h, hzu₁] at hin_eq; omega
              · rfl
            have h_eq_k : ∀ u, u < 2 * n + k₁ → u ∈ C.gates[k₁].inputs →
                isZero Z C (2 * n) u = true → u = 2 * n + k := by
              intro u hult humem hzu
              by_cases huN : u < 2 * n
              · rw [isZero_input Z C (2 * n) u huN, decide_eq_true_eq] at hzu
                simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hzu
                rcases hzu with rfl | rfl
                · exact False.elim (hk₁_ne (huniq_a k₁ hk₁lt humem))
                · exact False.elim (hk₁_ne (huniq_bR k₁ hk₁lt humem))
              · set r' := u - 2 * n
                have hr'Z : r' ∈ ZGates Z C (2 * n) := by
                  unfold ZGates
                  rw [Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, by rwa [show 2 * n + r' = u by omega]⟩
                by_cases hrk : r' = k
                · omega
                · have hr'rem : r' ∈ rem := Finset.mem_erase.mpr ⟨hrk, hr'Z⟩
                  have hle := Finset.min'_le rem r' hr'rem
                  change k₁ ≤ r' at hle
                  omega
            have heq1 := h_eq_k u₁ hu₁ (by rw [huv₁]; simp) hzu₁
            have heq2 := h_eq_k v₁ hv₁ (by rw [huv₁]; simp) hzv₁
            exact hne₁ (heq1.trans heq2.symm)
      have hkill_le : (KGates Z C (2 * n)).card ≤ C.gates.length := by
        have hsub : KGates Z C (2 * n) ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
        exact (Finset.card_le_card hsub).trans (by simp)
      refine ⟨by omega, ?_⟩
      obtain ⟨C', hm', hs', hr'⟩ := hred.2
      change C'.size ≤ C.gates.length - (KGates Z C (2 * n)).card at hs'
      exact ⟨C', hm', by omega, hr'⟩
    · -- Case 2B: bR < a, so set b = bR - 1, b + 2 <= a, a + 1 < n, n >= 4
      right
      set b := bR - 1
      have hba : b + 2 ≤ a := by omega
      have han : a + 1 < n := by omega
      have hn4 : 4 ≤ n := by omega
      have hbR_eq : b + 1 = bR := by omega
      let Z : Finset ℕ := {b, a, n + (b + 1), n + (a + 1)}
      have hZ_lt : ∀ u ∈ Z, u < 2 * n := by
        intro u hu
        simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> omega
      have hred := reduce2 n hn4 C hc hout hr b a hba han
      have hid := killed_card_identity Z C (2 * n) hc hZ_lt hred.1
      have hsumZ : ∑ u ∈ Z, deg C u = 4 := by
        have h1 : b ∉ ({a, n + (b + 1), n + (a + 1)} : Finset ℕ) := by simp; omega
        have h2 : a ∉ ({n + (b + 1), n + (a + 1)} : Finset ℕ) := by simp; omega
        have h3 : n + (b + 1) ≠ n + (a + 1) := by omega
        change ∑ u ∈ insert b (insert a {n + (b + 1), n + (a + 1)}), deg C u = 4
        rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_pair h3,
            hact_deg1 b (Or.inl (by omega)), hact_deg1 a (Or.inl ha_lt),
            hact_deg1 (n + (b + 1)) (Or.inr ⟨by omega, by omega⟩),
            hact_deg1 (n + (a + 1)) (Or.inr ⟨by omega, by omega⟩)]
        rfl
      have hkZ : k ∈ ZGates Z C (2 * n) := by
        unfold ZGates
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_⟩
        rw [isZero_gate Z C (2 * n) k hc hk_lt, hk_all_or k (le_refl k), huv_k]
        simp only [isAndOp, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil,
          Bool.and_true, Bool.and_eq_true]
        rcases hpair_k with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [hu, hv, isZero_input Z C (2 * n) a (by omega), isZero_input Z C (2 * n) (n + bR) (by omega), ← hbR_eq]
          simp [Z]
        · rw [hu, hv, isZero_input Z C (2 * n) (n + bR) (by omega), isZero_input Z C (2 * n) a (by omega), ← hbR_eq]
          simp [Z]
      have hkill5 : 5 ≤ (KGates Z C (2 * n)).card := by
        rcases hk_cond with hdeg2 | ⟨h₁, hh₁, hh₁and, hkh₁⟩
        · have hterm : deg C (2 * n + k) - 1 ≤
              ∑ j ∈ ZGates Z C (2 * n), (deg C (2 * n + j) - 1) :=
            Finset.single_le_sum (f := fun j => deg C (2 * n + j) - 1) (fun _ _ => Nat.zero_le _) hkZ
          omega
        · have hh₁Z : h₁ ∈ ZGates Z C (2 * n) := by
            unfold ZGates
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hh₁, ?_⟩
            rw [isZero_gate Z C (2 * n) h₁ hc hh₁, hh₁and]
            simp only [isAndOp, ↓reduceIte, List.any_eq_true]
            refine ⟨2 * n + k, hkh₁, ?_⟩
            unfold ZGates at hkZ; exact (Finset.mem_filter.mp hkZ).2
          have hh₁_ne_k : h₁ ≠ k := by
            obtain ⟨x, y, hxy, hx, hy, _⟩ := hc.2.1 h₁ hh₁
            rw [hxy] at hkh₁
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hkh₁
            rcases hkh₁ with h1 | h2 <;> omega
          let rem := (ZGates Z C (2 * n)).erase k
          have hrem_ne : rem.Nonempty := ⟨h₁, Finset.mem_erase.mpr ⟨hh₁_ne_k, hh₁Z⟩⟩
          let k₁ := rem.min' hrem_ne
          have hk₁_mem : k₁ ∈ rem := Finset.min'_mem _ hrem_ne
          have hk₁_ne : k₁ ≠ k := (Finset.mem_erase.mp hk₁_mem).1
          have hk₁Z : k₁ ∈ ZGates Z C (2 * n) := (Finset.mem_erase.mp hk₁_mem).2
          have hk₁lt : k₁ < C.gates.length := by
            unfold ZGates at hk₁Z; exact Finset.mem_range.mp (Finset.mem_filter.mp hk₁Z).1
          by_cases hin1 : inZero Z C (2 * n) k₁ ≤ 1
          · have hterm : 2 - inZero Z C (2 * n) k₁ ≤
                ∑ j ∈ ZGates Z C (2 * n), (2 - inZero Z C (2 * n) j) :=
              Finset.single_le_sum (f := fun j => 2 - inZero Z C (2 * n) j) (fun _ _ => Nat.zero_le _) hk₁Z
            omega
          · -- k₁ has 2 distinct inputs in {b, n + (a + 1), 2n + k}
            obtain ⟨u₁, v₁, huv₁, hu₁, hv₁, hne₁⟩ := hc.2.1 k₁ hk₁lt
            have hin_eq := inZero_eq_pair Z C (2 * n) k₁ u₁ v₁ hk₁lt huv₁
            have hzu₁ : isZero Z C (2 * n) u₁ = true := by
              cases h : isZero Z C (2 * n) u₁
              · simp [h] at hin_eq; split_ifs at hin_eq <;> omega
              · rfl
            have hzv₁ : isZero Z C (2 * n) v₁ = true := by
              cases h : isZero Z C (2 * n) v₁
              · simp [h, hzu₁] at hin_eq; omega
              · rfl
            have h_in_tri : ∀ u, u < 2 * n + k₁ → u ∈ C.gates[k₁].inputs →
                isZero Z C (2 * n) u = true →
                u = b ∨ u = n + (a + 1) ∨ u = 2 * n + k := by
              intro u hult humem hzu
              by_cases huN : u < 2 * n
              · rw [isZero_input Z C (2 * n) u huN, decide_eq_true_eq] at hzu
                simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hzu
                rcases hzu with rfl | rfl | rfl | rfl
                · exact Or.inl rfl
                · exact False.elim (hk₁_ne (huniq_a k₁ hk₁lt humem))
                · rw [hbR_eq] at humem
                  exact False.elim (hk₁_ne (huniq_bR k₁ hk₁lt humem))
                · exact Or.inr (Or.inl rfl)
              · set r' := u - 2 * n
                have hr'Z : r' ∈ ZGates Z C (2 * n) := by
                  unfold ZGates
                  rw [Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, by rwa [show 2 * n + r' = u by omega]⟩
                by_cases hrk : r' = k
                · exact Or.inr (Or.inr (by omega))
                · have hr'rem : r' ∈ rem := Finset.mem_erase.mpr ⟨hrk, hr'Z⟩
                  have hle := Finset.min'_le rem r' hr'rem
                  change k₁ ≤ r' at hle
                  omega
            have hu1_tri := h_in_tri u₁ hu₁ (by rw [huv₁]; simp) hzu₁
            have hv1_tri := h_in_tri v₁ hv₁ (by rw [huv₁]; simp) hzv₁
            have hk₁_reads_k_and_act : 2 * n + k ∈ C.gates[k₁].inputs ∧
                (b ∈ C.gates[k₁].inputs ∨ n + (a + 1) ∈ C.gates[k₁].inputs) := by
              rcases hu1_tri with rfl | rfl | rfl <;> rcases hv1_tri with rfl | rfl | rfl
              · exact False.elim (hne₁ rfl)
              · exfalso
                exact h_leaf_no_edge k₁ hk₁lt b (a + 1) (by omega) (by omega) han (by omega)
                  ⟨by rw [huv₁]; simp, by rw [huv₁]; simp⟩
              · exact ⟨by rw [huv₁]; simp, Or.inl (by rw [huv₁]; simp)⟩
              · exfalso
                exact h_leaf_no_edge k₁ hk₁lt b (a + 1) (by omega) (by omega) han (by omega)
                  ⟨by rw [huv₁]; simp, by rw [huv₁]; simp⟩
              · exact False.elim (hne₁ rfl)
              · exact ⟨by rw [huv₁]; simp, Or.inr (by rw [huv₁]; simp)⟩
              · exact ⟨by rw [huv₁]; simp, Or.inl (by rw [huv₁]; simp)⟩
              · exact ⟨by rw [huv₁]; simp, Or.inr (by rw [huv₁]; simp)⟩
              · exact False.elim (hne₁ rfl)
            have hk₁_or : C.gates[k₁].op = GateOp.or := by
              rcases hk₁_reads_k_and_act.2 with hmb | hma1
              · exact hact_no_and b (Or.inl (by omega)) k₁ hk₁lt hmb
              · exact hact_no_and (n + (a + 1)) (Or.inr ⟨by omega, by omega⟩) k₁ hk₁lt hma1
            have hk₁_ne_h₁ : k₁ ≠ h₁ := by
              intro heq
              subst heq
              rw [hh₁and] at hk₁_or
              exact GateOp.noConfusion hk₁_or
            have hdeg_k2 : 2 ≤ deg C (2 * n + k) := by
              have h1 : k₁ ∈ readers C (2 * n + k) :=
                (mem_readers_iff C (2 * n + k) k₁).mpr ⟨hk₁lt, hk₁_reads_k_and_act.1⟩
              have h2 : h₁ ∈ readers C (2 * n + k) :=
                (mem_readers_iff C (2 * n + k) h₁).mpr ⟨hh₁, hkh₁⟩
              have hsub : ({k₁, h₁} : Finset ℕ) ⊆ readers C (2 * n + k) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption
              have hcard := Finset.card_le_card hsub
              rw [Finset.card_pair hk₁_ne_h₁] at hcard
              exact hcard
            have hterm : deg C (2 * n + k) - 1 ≤
                ∑ j ∈ ZGates Z C (2 * n), (deg C (2 * n + j) - 1) :=
              Finset.single_le_sum (f := fun j => deg C (2 * n + j) - 1) (fun _ _ => Nat.zero_le _) hkZ
            omega
      have hkill_le : (KGates Z C (2 * n)).card ≤ C.gates.length := by
        have hsub : KGates Z C (2 * n) ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
        exact (Finset.card_le_card hsub).trans (by simp)
      refine ⟨hn4, by omega, ?_⟩
      obtain ⟨C', hm', hs', hr'⟩ := hred.2
      change C'.size ≤ C.gates.length - (KGates Z C (2 * n)).card at hs'
      exact ⟨C', hm', by omega, hr'⟩

lemma main_bound : ∀ n s : ℕ, RepSizeAtMost (LT n) s → 5 * n ≤ 2 * s + 8 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hs
    by_cases hn0 : n ≤ 1
    · omega
    · by_cases hn2 : n = 2
      · subst hn2
        obtain ⟨C, hm, hsize, hrep⟩ := hs
        have hpos : 1 ≤ C.gates.length := by
          by_contra h0
          have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
          have h01 := hrep ⟨0, by omega⟩ ⟨1, by omega⟩
          have h00 := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
          have h11 := hrep ⟨1, by omega⟩ ⟨1, by omega⟩
          rw [eval_eq_val, val, wires_eq_W, hnil, W_nil] at h01 h00 h11
          rw [oneEach_getD] at h01 h00 h11
          generalize C.output = o at h01 h00 h11
          rcases o with _ | _ | _ | _ | k
          · simp [LT] at h00
          · simp [LT] at h01
          · simp [LT] at h01
          · simp [LT] at h11
          · simp [LT] at h01
        change C.gates.length ≤ s at hsize
        omega
      · have hn3 : 3 ≤ n := by omega
        classical
        have hex : ∃ k : ℕ, RepSizeAtMost (LT n) k := ⟨s, hs⟩
        let s₀ := Nat.find hex
        have hs₀ : RepSizeAtMost (LT n) s₀ := Nat.find_spec hex
        have hs₀_le : s₀ ≤ s := Nat.find_min' hex hs
        obtain ⟨C, hm, hCsize, hCrep⟩ := hs₀
        have hmin : ∀ C', Monotone2 C' → Represents (LT n) C' → C.size ≤ C'.size := by
          intro C' hm' hr'
          have hle : s₀ ≤ C'.size := Nat.find_min' hex ⟨C', hm', le_refl _, hr'⟩
          exact hCsize.trans hle
        have hCs₀ : C.gates.length ≤ s := hCsize.trans hs₀_le
        rcases move_step n hn3 C hm hCrep hmin with ⟨h3, hrep1⟩ | ⟨hn4, h5, hrep2⟩
        · have hih := ih (n - 1) (by omega) (C.gates.length - 3) hrep1
          omega
        · have hih := ih (n - 2) (by omega) (C.gates.length - 5) hrep2
          omega

end PEqualNP.Outside.L_meta_7147

theorem PEqualNP.Outside.L_meta_7147 :
    ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u < v)) s → 5 * n ≤ 2 * s + 8 :=
  PEqualNP.Outside.L_meta_7147.main_bound
