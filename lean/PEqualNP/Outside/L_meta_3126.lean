import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3126_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma drun_nil (x : List Bool) : drun [] x = x := rfl

lemma drun_append (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

lemma drun_length (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

lemma drun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [drun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

-- The wires a gate really reads: a NOT gate reads only its first wire.
def rel (g : Gate) : List ℕ := if isNot g.op then g.inputs.take 1 else g.inputs

lemma eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ rel g, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  unfold rel at h
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte] at h
    rw [(isNot_iff _).mp hn]
    rcases hi : g.inputs with _ | ⟨r, t⟩
    · rfl
    · rw [hi] at h
      have := h r (by simp)
      simp [GateOp.eval, this]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    rw [List.map_congr_left h]

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if isOr op ∈ l then isOr op else !isOr op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def genAO (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (isOr g.op), [])
  else fin3 (isOr g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def genN (ρ : List (Bool ⊕ ℕ)) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl true, [])
  | r :: _ => (ρ.getD r (Sum.inl false)).elim (fun c => (Sum.inl (!c), []))
      (fun w => (Sum.inr N, [⟨GateOp.not, [w]⟩]))

def gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if isNot g.op then genN ρ N g.inputs else genAO ρ N g

lemma fin3_len (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) : (fin3 a op N l).2.length ≤ 1 := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma genN_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (l : List ℕ) : (genN ρ N l).2.length ≤ 1 := by
  rcases l with _ | ⟨r, t⟩
  · simp [genN]
  · rcases h : ρ.getD r (Sum.inl false) with c | w <;>
      simp only [genN, h, Sum.elim_inl, Sum.elim_inr, List.length_nil, List.length_singleton] <;> omega

lemma gen_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (gen ρ N g).2.length ≤ 1 := by
  unfold gen
  split_ifs
  · exact genN_len _ _ _
  · unfold genAO
    split_ifs
    · simp
    · exact fin3_len _ _ _ _

lemma filterMap_lt (l : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ l) :
    (l.filterMap Sum.getRight?).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h
      have := List.length_filterMap_le Sum.getRight? t
      change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
      omega
    · have := ih h
      rcases c with c | c
      · change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
        omega
      · change (t.filterMap Sum.getRight?).length + 1 + 1 ≤ t.length + 1
        omega

lemma fin3_short (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (h : l.length ≤ 1) :
    (fin3 a op N l).2 = [] := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · rfl
  · rfl
  · simp at h

-- A gate that really reads a wire of constant value emits no gate.
lemma gen_short (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (r : ℕ) (hr : r ∈ rel g) (c : Bool) (hc : ρ.getD r (Sum.inl false) = Sum.inl c) :
    (gen ρ N g).2 = [] := by
  unfold gen
  unfold rel at hr
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte] at hr ⊢
    rcases hi : g.inputs with _ | ⟨r0, t⟩
    · rfl
    · rw [hi] at hr
      have hr0 : r = r0 := by simpa using hr
      subst hr0
      simp only [genN, hc, Sum.elim_inl]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    unfold genAO
    split_ifs
    · rfl
    · apply fin3_short
      have hm : Sum.inl c ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) :=
        List.mem_map.mpr ⟨r, hr, hc⟩
      have := filterMap_lt _ c hm
      simp only [List.length_map] at this
      omega

lemma gen_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hlen : g.inputs.length ≤ 2) :
    ∀ g' ∈ (gen ρ N g).2, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
      g'.inputs.length ≤ 2 := by
  unfold gen
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte]
    rcases hi : g.inputs with _ | ⟨r, t⟩
    · simp [genN]
    · rcases h : ρ.getD r (Sum.inl false) with c | w <;>
        simp only [genN, h, Sum.elim_inl, Sum.elim_inr] <;> simp
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    unfold genAO
    split_ifs
    · simp
    · intro g' hg'
      generalize hl : (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at hg'
      have hll : l.length ≤ 2 := by
        rw [← hl]
        exact (List.length_filterMap_le _ _).trans (by simpa using hlen)
      rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
      · simp [fin3] at hg'
      · simp [fin3] at hg'
      · simp only [fin3, List.mem_singleton] at hg'
        subst hg'
        refine ⟨?_, hll⟩
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd ((isNot_iff _).mpr h) hn

def Rp (W' : List Bool) (v : Bool) : Bool ⊕ ℕ → Prop
  | Sum.inl b => v = b
  | Sum.inr w => w < W'.length ∧ W'.getD w false = v

lemma Rp_mono (W' : List Bool) (e : List Gate) (v : Bool) (r : Bool ⊕ ℕ) (hr : Rp W' v r) :
    Rp (drun e W') v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by rw [drun_length]; exact Nat.lt_add_right _ hr.1, by rw [drun_getD _ _ _ hr.1]; exact hr.2⟩

lemma Rp_app (W' : List Bool) (a v : Bool) (r : Bool ⊕ ℕ) (hr : Rp W' v r) :
    Rp (W' ++ [a]) v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by have := hr.1; simp; omega, by rw [List.getD_append _ _ _ _ hr.1]; exact hr.2⟩

lemma genAO_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (vals : ℕ → Bool)
    (hr : ∀ r ∈ g.inputs, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (genAO ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (genAO ρ W'.length g).1 := by
  rw [eval_ao g.op _ hop]
  unfold genAO
  by_cases hin : Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = isOr g.op := h1
    have hmem : isOr g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
    simp only [hmem, ↓reduceIte]
    exact rfl
  · simp only [hin, ↓reduceIte]
    have key1 : ∀ w ∈ (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?,
        w < W'.length ∧ ∃ r ∈ g.inputs, W'.getD w false = vals r := by
      intro w hw
      obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
      obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
      have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
      have h1 := hr r hrm
      rw [hre, hc'] at h1
      exact ⟨h1.1, r, hrm, h1.2⟩
    have key2 : isOr g.op ∈ g.inputs.map vals ↔ isOr g.op ∈
        ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?).map
          (fun w => W'.getD w false) := by
      constructor
      · intro hm
        obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hm
        have h1 := hr r hrm
        rcases hc : ρ.getD r (Sum.inl false) with b | w
        · rw [hc] at h1
          have h2 : vals r = b := h1
          exact absurd (List.mem_map.mpr ⟨r, hrm, by rw [hc, ← h2, hre]⟩) hin
        · rw [hc] at h1
          refine List.mem_map.mpr ⟨w, List.mem_filterMap.mpr ⟨Sum.inr w, List.mem_map.mpr ⟨r, hrm, hc⟩, rfl⟩, ?_⟩
          rw [h1.2, hre]
      · intro hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain ⟨_, r, hrm, hre⟩ := key1 w hw
        exact List.mem_map.mpr ⟨r, hrm, by rw [← hre, hwe]⟩
    simp only [key2]
    generalize (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at key1
    rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · simp [fin3, Rp]
    · have hw := (key1 w (by simp)).1
      refine ⟨hw, ?_⟩
      change W'.getD w false = _
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      generalize W'.getD w false = c
      cases isOr g.op <;> cases c <;> simp
    · refine ⟨by simp [fin3, drun], ?_⟩
      simp only [fin3, drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact eval_ao g.op _ hop

lemma genN_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (l : List ℕ) (vals : ℕ → Bool)
    (hr : ∀ r ∈ l.take 1, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (genN ρ W'.length l).2 W') (GateOp.not.eval (l.map vals)) (genN ρ W'.length l).1 := by
  rcases l with _ | ⟨r, t⟩
  · change (!false) = true
    rfl
  · have h := hr r (by simp)
    rcases hc : ρ.getD r (Sum.inl false) with c | w
    · rw [hc] at h
      have h' : vals r = c := h
      simp only [genN, hc, Sum.elim_inl]
      change (!((r :: t).map vals).headD false) = !c
      simp [h']
    · rw [hc] at h
      obtain ⟨hw, hv⟩ := h
      simp only [genN, hc, Sum.elim_inr]
      refine ⟨by simp [drun], ?_⟩
      show (drun [⟨GateOp.not, [w]⟩] W').getD W'.length false = GateOp.not.eval ((r :: t).map vals)
      rw [drun_cons, drun_nil, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil, GateOp.eval,
        List.headD_cons, hv]

lemma gen_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (vals : ℕ → Bool)
    (hr : ∀ r ∈ rel g, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (gen ρ W'.length g).1 := by
  unfold gen
  unfold rel at hr
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte] at hr ⊢
    rw [(isNot_iff _).mp hn]
    exact genN_sem ρ W' g.inputs vals hr
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ((isNot_iff _).mpr h) hn
    exact genAO_sem ρ W' g hop' vals hr


-- The simplifier with a constancy oracle: a gate wire the oracle calls constant becomes that
-- constant; any other gate is simplified as before, and the indices of emitted gates are kept.
def sim2 (cst : ℕ → Option Bool) (n0 : ℕ) : List (Bool ⊕ ℕ) → ℕ → ℕ → List Gate →
    List (Bool ⊕ ℕ) × List Gate × List ℕ
  | ρ, _, _, [] => (ρ, [], [])
  | ρ, N, k, g :: gs =>
    match cst (n0 + k) with
    | some c => sim2 cst n0 (ρ ++ [Sum.inl c]) N (k + 1) gs
    | none =>
      ((sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).1,
       (gen ρ N g).2 ++ (sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).2.1,
       (if (gen ρ N g).2.length = 0 then [] else [k]) ++
         (sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).2.2)

lemma sim2_nil (cst : ℕ → Option Bool) (n0 : ℕ) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ) :
    sim2 cst n0 ρ N k [] = (ρ, [], []) := rfl

lemma sim2_some (cst : ℕ → Option Bool) (n0 : ℕ) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ) (g : Gate)
    (gs : List Gate) (c : Bool) (h : cst (n0 + k) = some c) :
    sim2 cst n0 ρ N k (g :: gs) = sim2 cst n0 (ρ ++ [Sum.inl c]) N (k + 1) gs := by
  simp only [sim2, h]

lemma sim2_none (cst : ℕ → Option Bool) (n0 : ℕ) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ) (g : Gate)
    (gs : List Gate) (h : cst (n0 + k) = none) :
    sim2 cst n0 ρ N k (g :: gs) =
      ((sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).1,
       (gen ρ N g).2 ++ (sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).2.1,
       (if (gen ρ N g).2.length = 0 then [] else [k]) ++
         (sim2 cst n0 (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1) gs).2.2) := by
  simp only [sim2, h]

lemma sim2_count (cst : ℕ → Option Bool) (n0 : ℕ) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ),
    (sim2 cst n0 ρ N k gs).2.1.length = (sim2 cst n0 ρ N k gs).2.2.length := by
  intro gs
  induction gs with
  | nil => intro ρ N k; rfl
  | cons g gs ih =>
    intro ρ N k
    rcases h : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ N k g gs h]
      simp only [List.length_append]
      rw [ih]
      have := gen_len ρ N g
      split_ifs with h0
      · simp [h0]
      · simp only [List.length_singleton]
        omega
    · rw [sim2_some cst n0 ρ N k g gs c h]
      exact ih _ _ _

lemma sim2_idx (cst : ℕ → Option Bool) (n0 : ℕ) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ),
    (∀ i ∈ (sim2 cst n0 ρ N k gs).2.2, k ≤ i ∧ i < k + gs.length) ∧
      (sim2 cst n0 ρ N k gs).2.2.Pairwise (· < ·) := by
  intro gs
  induction gs with
  | nil => intro ρ N k; simp [sim2_nil]
  | cons g gs ih =>
    intro ρ N k
    rcases h : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ N k g gs h]
      obtain ⟨i1, i2⟩ := ih (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1)
      constructor
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · split_ifs at hi
          · simp at hi
          · simp only [List.mem_singleton] at hi
            subst hi
            simp
        · have := i1 i hi
          simp only [List.length_cons]
          omega
      · refine List.pairwise_append.mpr ⟨?_, i2, ?_⟩
        · split_ifs <;> simp
        · intro a ha b hb
          split_ifs at ha
          · simp at ha
          · simp only [List.mem_singleton] at ha
            have := (i1 b hb).1
            omega
    · rw [sim2_some cst n0 ρ N k g gs c h]
      obtain ⟨i1, i2⟩ := ih (ρ ++ [Sum.inl c]) N (k + 1)
      refine ⟨fun i hi => ?_, i2⟩
      have := i1 i hi
      simp only [List.length_cons]
      omega

lemma sim2_mem (cst : ℕ → Option Bool) (n0 : ℕ) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    ∀ g' ∈ (sim2 cst n0 ρ N k gs).2.1, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
      g'.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro ρ N k _; simp [sim2_nil]
  | cons g gs ih =>
    intro ρ N k hops
    rcases h : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ N k g gs h]
      intro g' hg'
      rcases List.mem_append.mp hg' with hm | hm
      · exact gen_mem ρ N g (hops g (by simp)).1 (hops g (by simp)).2 g' hm
      · exact ih _ _ _ (fun g2 hg2 => hops g2 (by simp [hg2])) g' hm
    · rw [sim2_some cst n0 ρ N k g gs c h]
      exact ih _ _ _ (fun g2 hg2 => hops g2 (by simp [hg2]))

lemma sim2_fst (cst : ℕ → Option Bool) (n0 : ℕ) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ),
    ∃ L : List (Bool ⊕ ℕ), (sim2 cst n0 ρ N k gs).1 = ρ ++ L := by
  intro gs
  induction gs with
  | nil => intro ρ N k; exact ⟨[], by simp [sim2_nil]⟩
  | cons g gs ih =>
    intro ρ N k
    rcases h : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ N k g gs h]
      obtain ⟨L, hL⟩ := ih (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) (k + 1)
      exact ⟨[(gen ρ N g).1] ++ L, by rw [hL]; simp⟩
    · rw [sim2_some cst n0 ρ N k g gs c h]
      obtain ⟨L, hL⟩ := ih (ρ ++ [Sum.inl c]) N (k + 1)
      exact ⟨[Sum.inl c] ++ L, by rw [hL]; simp⟩

lemma sim2_sem (cst : ℕ → Option Bool) (n0 : ℕ) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ))
    (Wo W' : List Bool) (k : ℕ),
    ρ.length = Wo.length → Wo.length = n0 + k →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ w c, cst w = some c → (drun gs Wo).getD w false = c) →
    (∀ i, Rp W' (Wo.getD i false) (ρ.getD i (Sum.inl false))) →
    ∀ i, Rp (drun (sim2 cst n0 ρ W'.length k gs).2.1 W') ((drun gs Wo).getD i false)
      ((sim2 cst n0 ρ W'.length k gs).1.getD i (Sum.inl false)) := by
  intro gs
  induction gs with
  | nil =>
    intro ρ Wo W' k _ _ _ _ h
    simpa [sim2_nil, drun] using h
  | cons g gs ih =>
    intro ρ Wo W' k hlen hk hops hcst hinv
    have hg := hops g (by simp)
    set v := g.op.eval (g.inputs.map fun i => Wo.getD i false) with hv
    have hrun : drun (g :: gs) Wo = drun gs (Wo ++ [v]) := rfl
    have hvat : (drun gs (Wo ++ [v])).getD Wo.length false = v := by
      rw [drun_getD _ _ _ (by simp), List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    -- extend the invariant by one entry
    have extend : ∀ (d : Bool ⊕ ℕ) (W'' : List Bool), (∀ i, Rp W' (Wo.getD i false) (ρ.getD i (Sum.inl false)) →
        Rp W'' (Wo.getD i false) (ρ.getD i (Sum.inl false))) → Rp W'' v d →
        ∀ i, Rp W'' ((Wo ++ [v]).getD i false) ((ρ ++ [d]).getD i (Sum.inl false)) := by
      intro d W'' hmono hd i
      rcases lt_trichotomy i Wo.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ (by omega)]
        exact hmono i (hinv i)
      · subst h1
        rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
        simpa [hlen] using hd
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        exact rfl
    rcases hc : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ W'.length k g gs hc, hrun]
      have hd : Rp (drun (gen ρ W'.length g).2 W') v (gen ρ W'.length g).1 :=
        gen_sem ρ W' g hg (fun i => Wo.getD i false) (fun r _ => hinv r)
      have key := ih (ρ ++ [(gen ρ W'.length g).1]) (Wo ++ [v]) (drun (gen ρ W'.length g).2 W') (k + 1)
        (by simp [hlen]) (by simp [hk]; omega) (fun g' hg' => hops g' (by simp [hg']))
        (fun w c h => by rw [← hrun]; exact hcst w c h)
        (extend _ _ (fun i h => Rp_mono _ _ _ _ h) hd)
      rw [drun_length] at key
      simpa only [drun_append] using key
    · rw [sim2_some cst n0 ρ W'.length k g gs c hc, hrun]
      have hvc : v = c := by
        have := hcst (n0 + k) c hc
        rw [hrun, ← hk, hvat] at this
        exact this
      exact ih (ρ ++ [Sum.inl c]) (Wo ++ [v]) W' (k + 1) (by simp [hlen]) (by simp [hk]; omega)
        (fun g' hg' => hops g' (by simp [hg'])) (fun w c' h => by rw [← hrun]; exact hcst w c' h)
        (extend _ _ (fun i h => h) hvc)

-- Every emitted gate reads only wires the abstract run keeps as wires; those wires vary.
lemma gen_inr (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (he : (gen ρ N g).2 ≠ []) : ∀ r ∈ rel g, ∃ w, ρ.getD r (Sum.inl false) = Sum.inr w := by
  intro r hr
  rcases h : ρ.getD r (Sum.inl false) with c | w
  · exact absurd (gen_short ρ N g hlen r hr c h) he
  · exact ⟨w, rfl⟩

lemma sim2_good (cst : ℕ → Option Bool) (n0 : ℕ) (NC : ℕ → Prop)
    (hNC : ∀ w, cst w = none → NC w) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (N k : ℕ),
    ρ.length = n0 + k → (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ w, (∃ v, ρ.getD w (Sum.inl false) = Sum.inr v) → NC w) →
    ∀ i ∈ (sim2 cst n0 ρ N k gs).2.2, ∃ h : i - k < gs.length, ∀ r ∈ rel gs[i - k],
      r < n0 + i ∧ NC r := by
  intro gs
  induction gs with
  | nil => intro ρ N k _ _ _ i hi; simp [sim2_nil] at hi
  | cons g gs ih =>
    intro ρ N k hlen hfan hP i hi
    rcases hc : cst (n0 + k) with _ | c
    · rw [sim2_none cst n0 ρ N k g gs hc] at hi
      rcases List.mem_append.mp hi with hi | hi
      · split_ifs at hi with h0
        · simp at hi
        · simp only [List.mem_singleton] at hi
          subst hi
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [Nat.sub_self, List.getElem_cons_zero] at hr
          have hne : (gen ρ N g).2 ≠ [] := fun e => h0 (by rw [e]; rfl)
          obtain ⟨w, hw⟩ := gen_inr ρ N g (hfan g (by simp)) hne r hr
          refine ⟨?_, hP r ⟨w, hw⟩⟩
          by_contra hge
          rw [List.getD_eq_default _ _ (by omega)] at hw
          cases hw
      · have hP' : ∀ w, (∃ v, (ρ ++ [(gen ρ N g).1]).getD w (Sum.inl false) = Sum.inr v) → NC w := by
          intro w ⟨v, hv⟩
          rcases lt_trichotomy w ρ.length with h1 | h1 | h1
          · rw [List.getD_append _ _ _ _ h1] at hv
            exact hP w ⟨v, hv⟩
          · subst h1
            rw [hlen]
            exact hNC _ hc
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
            cases hv
        obtain ⟨h1, h2⟩ := ih _ _ (k + 1) (by simp [hlen]; omega) (fun g' hg' => hfan g' (by simp [hg'])) hP' i hi
        have hik : k + 1 ≤ i := (sim2_idx cst n0 gs _ _ (k + 1)).1 i hi |>.1
        have hb : i - k < (g :: gs).length := by simp; omega
        refine ⟨hb, ?_⟩
        have e : (g :: gs)[i - k] = gs[i - (k + 1)] := by
          rw [List.getElem_cons]
          simp [show i - k ≠ 0 by omega, Nat.sub_sub]
        rw [e]
        exact h2
    · rw [sim2_some cst n0 ρ N k g gs c hc] at hi
      have hP' : ∀ w, (∃ v, (ρ ++ [Sum.inl c]).getD w (Sum.inl false) = Sum.inr v) → NC w := by
        intro w ⟨v, hv⟩
        rcases lt_trichotomy w ρ.length with h1 | h1 | h1
        · rw [List.getD_append _ _ _ _ h1] at hv
          exact hP w ⟨v, hv⟩
        · subst h1
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hv
          simp at hv
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
          cases hv
      obtain ⟨h1, h2⟩ := ih _ _ (k + 1) (by simp [hlen]; omega) (fun g' hg' => hfan g' (by simp [hg'])) hP' i hi
      have hik : k + 1 ≤ i := (sim2_idx cst n0 gs _ _ (k + 1)).1 i hi |>.1
      have hb : i - k < (g :: gs).length := by simp; omega
      refine ⟨hb, ?_⟩
      have e : (g :: gs)[i - k] = gs[i - (k + 1)] := by
        rw [List.getElem_cons]
        simp [show i - k ≠ 0 by omega, Nat.sub_sub]
      rw [e]
      exact h2

lemma fan_of (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  rcases h1 with h1 | h1 | h1 <;> simp [h1]

def inp (x2 : List (Option (Fin 7))) (y : Fin 7 → Bool) : List Bool :=
  x2.map (fun o => o.elim false y)

theorem m26 (C : Circuit) (x2 : List (Option (Fin 7))) (hfan : FanInTwo C)
    (hnc : ∃ y z : Fin 7 → Bool, C.eval (inp x2 y) ≠ C.eval (inp x2 z)) :
    ∃ S : Finset (Fin C.gates.length),
      (∀ k ∈ S, ∀ r ∈ (C.gates.get k).inputs, (C.gates.get k).op ≠ GateOp.not ∨
          (C.gates.get k).inputs[0]? = some r →
        ∃ y z : Fin 7 → Bool, (Circuit.wires ⟨C.gates.take k, 0⟩ (inp x2 y)).getD r false ≠
          (Circuit.wires ⟨C.gates.take k, 0⟩ (inp x2 z)).getD r false) ∧
      HasCircuitSize 7 (fun y => C.eval (inp x2 y)) S.card := by
  classical
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa using h1
  let V : (Fin 7 → Bool) → ℕ → Bool := fun y w => (drun C.gates (inp x2 y)).getD w false
  let cst : ℕ → Option Bool := fun w => if h : ∃ c, ∀ y, V y w = c then some h.choose else none
  have sound : ∀ w c, cst w = some c → ∀ y, V y w = c := by
    intro w c h y
    simp only [cst] at h
    split_ifs at h with hh
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact hh.choose_spec y
  have complete : ∀ w, cst w = none → ∃ y z, V y w ≠ V z w := by
    intro w h
    simp only [cst] at h
    split_ifs at h with hh
    push_neg at hh
    obtain ⟨z, hz⟩ := hh (V (fun _ => false) w)
    exact ⟨fun _ => false, z, fun e => hz e.symm⟩
  let n0 := x2.length
  let ρ0 : List (Bool ⊕ ℕ) := x2.map (fun o => o.elim (Sum.inl false) (fun v => Sum.inr (v : ℕ)))
  have hρlen : ρ0.length = n0 := by simp [ρ0, n0]
  let R := sim2 cst n0 ρ0 7 0 C.gates
  have hsem : ∀ y : Fin 7 → Bool, ∀ i, Rp (drun R.2.1 (List.ofFn y)) (V y i) (R.1.getD i (Sum.inl false)) := by
    intro y
    have := sim2_sem cst n0 C.gates ρ0 (inp x2 y) (List.ofFn y) 0 (by simp [ρ0, inp]) (by simp [inp, n0])
      (fun g hg => (hops g hg).1) (fun w c h => sound w c h y) (by
        intro i
        by_cases hi : i < x2.length
        · rw [List.getD_eq_getElem _ _ (by simpa [inp] using hi), List.getD_eq_getElem _ _ (by simpa [ρ0] using hi)]
          simp only [inp, ρ0, List.getElem_map]
          rcases x2[i] with _ | v
          · rfl
          · refine ⟨by simp, ?_⟩
            show (List.ofFn y).getD (v : ℕ) false = y v
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        · rw [List.getD_eq_default _ _ (by simp [inp]; omega), List.getD_eq_default _ _ (by simp [ρ0]; omega)]
          rfl)
    simpa only [List.length_ofFn] using this
  have hidx := sim2_idx cst n0 C.gates ρ0 7 0
  have hcount := sim2_count cst n0 C.gates ρ0 7 0
  have hgood := sim2_good cst n0 (fun r => ∃ y z, V y r ≠ V z r) complete C.gates ρ0 7 0 (by simp [hρlen])
    (fun g hg => (hops g hg).2) (by
      intro w ⟨v, hv⟩
      by_cases hw : w < x2.length
      · rw [List.getD_eq_getElem _ _ (by simpa [ρ0] using hw)] at hv
        simp only [ρ0, List.getElem_map] at hv
        rcases hx : x2[w] with _ | u
        · rw [hx] at hv
          cases hv
        · have hvw : ∀ y, V y w = y u := by
            intro y
            simp only [V]
            rw [drun_getD _ _ _ (by simpa [inp] using hw), List.getD_eq_getElem _ _ (by simpa [inp] using hw)]
            simp [inp, hx]
          exact ⟨fun _ => true, fun _ => false, by rw [hvw, hvw]; simp⟩
      · rw [List.getD_eq_default _ _ (by simp [ρ0]; omega)] at hv
        cases hv)
  -- the output
  rcases hout : R.1.getD C.output (Sum.inl false) with c | w
  · exfalso
    obtain ⟨y, z, hyz⟩ := hnc
    have a := hsem y C.output
    have b := hsem z C.output
    rw [hout] at a b
    exact hyz ((show C.eval (inp x2 y) = c from a).trans (show C.eval (inp x2 z) = c from b).symm)
  · let S : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => (k : ℕ) ∈ R.2.2)
    have hS : S.card = R.2.2.length := by
      have hnd : R.2.2.Nodup := hidx.2.imp (fun h => Nat.ne_of_lt h)
      rw [← List.toFinset_card_of_nodup hnd]
      have : S.map Fin.valEmbedding = R.2.2.toFinset := by
        ext i
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
          List.mem_toFinset, S]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact hk
        · intro hi
          have := (hidx.1 i hi).2
          exact ⟨⟨i, by simpa using this⟩, hi, rfl⟩
      rw [← this, Finset.card_map]
    refine ⟨S, ?_, ⟨⟨R.2.1, w⟩, fan_of _ _ (sim2_mem cst n0 C.gates ρ0 7 0 hops), ?_, fun y => ?_⟩⟩
    · intro k hk r hr hrel
      have hkR : (k : ℕ) ∈ R.2.2 := (Finset.mem_filter.mp hk).2
      obtain ⟨hlt, hrs⟩ := hgood k hkR
      have hrel' : r ∈ rel C.gates[(k : ℕ)] := by
        unfold rel
        change r ∈ (C.gates[(k : ℕ)]).inputs at hr
        change (C.gates[(k : ℕ)]).op ≠ GateOp.not ∨ (C.gates[(k : ℕ)]).inputs[0]? = some r at hrel
        by_cases hn : isNot (C.gates[(k : ℕ)]).op = true
        · simp only [hn, ↓reduceIte]
          rcases hrel with h | h
          · exact absurd ((isNot_iff _).mp hn) h
          · rcases hi : (C.gates[(k : ℕ)]).inputs with _ | ⟨a, t⟩
            · rw [hi] at h
              simp at h
            · rw [hi] at h
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              simp
        · simp only [hn, Bool.false_eq_true, ↓reduceIte]
          exact hr
      have hk0 : (k : ℕ) - 0 = (k : ℕ) := Nat.sub_zero _
      obtain ⟨hrlt, y, z, hyz⟩ := hrs r (by simpa [hk0] using hrel')
      refine ⟨y, z, ?_⟩
      have pre : ∀ u : Fin 7 → Bool, (Circuit.wires ⟨C.gates.take k, 0⟩ (inp x2 u)).getD r false = V u r := by
        intro u
        change (drun (C.gates.take k) (inp x2 u)).getD r false = (drun C.gates (inp x2 u)).getD r false
        conv_rhs => rw [← List.take_append_drop k C.gates, drun_append]
        rw [drun_getD (C.gates.drop k) (drun (C.gates.take k) (inp x2 u)) r
          (by rw [drun_length, List.length_take]; simp [inp]; omega)]
      rw [pre, pre]
      exact hyz
    · show R.2.1.length ≤ S.card
      rw [hS, hcount]
    · have a := hsem y C.output
      rw [hout] at a
      show (drun R.2.1 (List.ofFn y)).getD w false = C.eval (inp x2 y)
      exact a.2

end PEqualNP.Outside.L_meta_3126_aux

theorem PEqualNP.Outside.L_meta_3126 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Option (Fin (7 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x1 →     have x4 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x4 : Fin (7 : ℕ) → Bool) => List.map (fun (x5 : Option (Fin (7 : ℕ))) => x5.elim Bool.false x4) x2;     have x5 : Fin x1.gates.length → Prop := fun (x5 : Fin x1.gates.length) =>       have x6 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x5;       ∀ x7 ∈ x6.inputs, x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∨ x6.inputs[(0 : ℕ)]? = Option.some x7 → ∃ (x10 : Fin (7 : ℕ) → Bool) (x11 : Fin (7 : ℕ) → Bool), ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x10)).getD x7 Bool.false ≠ ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x11)).getD x7 Bool.false;     (∃ (x6 : Fin (7 : ℕ) → Bool) (x7 : Fin (7 : ℕ) → Bool), x1.eval (x4 x6) ≠ x1.eval (x4 x7)) → ∃ (x7 : Finset (Fin x1.gates.length)), (∀ x8 ∈ x7, x5 x8) ∧ PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x8 : Fin (7 : ℕ) → Bool) => x1.eval (x4 x8)) x7.card := by
  intro x1 x2 hfan
  exact PEqualNP.Outside.L_meta_3126_aux.m26 x1 x2 hfan
