import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4548_aux

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

def sim (ρ : List (Bool ⊕ ℕ)) (N : ℕ) : List Gate → List (Bool ⊕ ℕ) × List Gate
  | [] => (ρ, [])
  | g :: gs => ((sim (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) gs).1,
      (gen ρ N g).2 ++ (sim (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) gs).2)

lemma sim_cons (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (gs : List Gate) :
    sim ρ N (g :: gs) = ((sim (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) gs).1,
      (gen ρ N g).2 ++ (sim (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length) gs).2) := rfl

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

lemma sim_fst (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate) :
    ∃ L : List (Bool ⊕ ℕ), (sim ρ N gs).1 = ρ ++ L ∧ L.length = gs.length := by
  induction gs generalizing ρ N with
  | nil => exact ⟨[], by simp [sim]⟩
  | cons g gs ih =>
    obtain ⟨L, hL, hl⟩ := ih (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length)
    refine ⟨(gen ρ N g).1 :: L, ?_, by simp [hl]⟩
    rw [sim_cons, hL]
    simp

lemma sim_getD (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate) (r : ℕ) (hr : r < ρ.length) :
    (sim ρ N gs).1.getD r (Sum.inl false) = ρ.getD r (Sum.inl false) := by
  obtain ⟨L, hL, _⟩ := sim_fst ρ N gs
  rw [hL, List.getD_append _ _ _ _ hr]

lemma sim_len1 (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate) :
    (sim ρ N gs).1.length = ρ.length + gs.length := by
  obtain ⟨L, hL, hl⟩ := sim_fst ρ N gs
  rw [hL, List.length_append, hl]

lemma sim_len2 (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate) :
    (sim ρ N gs).2.length ≤ gs.length := by
  induction gs generalizing ρ N with
  | nil => simp [sim]
  | cons g gs ih =>
    rw [sim_cons]
    simp only [List.length_append, List.length_cons]
    have := gen_len ρ N g
    have := ih (ρ ++ [(gen ρ N g).1]) (N + (gen ρ N g).2.length)
    omega

lemma sim_append (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (A B : List Gate) :
    sim ρ N (A ++ B) = ((sim (sim ρ N A).1 (N + (sim ρ N A).2.length) B).1,
      (sim ρ N A).2 ++ (sim (sim ρ N A).1 (N + (sim ρ N A).2.length) B).2) := by
  induction A generalizing ρ N with
  | nil => simp [sim]
  | cons g A ih =>
    rw [List.cons_append, sim_cons, ih, sim_cons]
    simp only [List.length_append, List.append_assoc, Nat.add_assoc]

lemma sim_split (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (s : List (Bool ⊕ ℕ) × List Gate) (hs : s = sim ρ N (gs.take k))
    (e : (Bool ⊕ ℕ) × List Gate) (he : e = gen s.1 (N + s.2.length) gs[k]) :
    sim ρ N gs = ((sim (s.1 ++ [e.1]) (N + s.2.length + e.2.length) (gs.drop (k + 1))).1,
      s.2 ++ (e.2 ++ (sim (s.1 ++ [e.1]) (N + s.2.length + e.2.length) (gs.drop (k + 1))).2)) := by
  subst hs he
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk]
  rw [sim_append, sim_cons]

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

lemma sim_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g' ∈ (sim ρ N gs).2, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
      g'.inputs.length ≤ 2 := by
  induction gs generalizing ρ N with
  | nil => simp [sim]
  | cons g gs ih =>
    rw [sim_cons]
    intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact gen_mem ρ N g (hops g (by simp)).1 (hops g (by simp)).2 g' h
    · exact ih _ _ (fun g2 hg2 => hops g2 (by simp [hg2])) g' h

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

lemma sim_sem (ok : ℕ → Prop) : ∀ (gs : List Gate) (ρ : List (Bool ⊕ ℕ)) (Wo W' : List Bool),
    ρ.length = Wo.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ gs, ∀ r ∈ rel g, ok r) →
    (∀ i, ok i → Rp W' (Wo.getD i false) (ρ.getD i (Sum.inl false))) →
    ∀ i, ok i → Rp (drun (sim ρ W'.length gs).2 W') ((drun gs Wo).getD i false)
      ((sim ρ W'.length gs).1.getD i (Sum.inl false)) := by
  intro gs
  induction gs with
  | nil =>
    intro ρ Wo W' _ _ _ h
    simpa [sim, drun] using h
  | cons g gs ih =>
    intro ρ Wo W' hlen hops hrel hinv
    have hg := hops g (by simp)
    have hd : Rp (drun (gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map fun i => Wo.getD i false))
        (gen ρ W'.length g).1 :=
      gen_sem ρ W' g hg (fun i => Wo.getD i false) (fun r hr => hinv r (hrel g (by simp) r hr))
    have key := ih (ρ ++ [(gen ρ W'.length g).1])
      (Wo ++ [g.op.eval (g.inputs.map fun i => Wo.getD i false)]) (drun (gen ρ W'.length g).2 W')
      (by simp [hlen]) (fun g' hg' => hops g' (by simp [hg'])) (fun g' hg' => hrel g' (by simp [hg']))
      (by
        intro i hi
        rcases lt_trichotomy i Wo.length with h1 | h1 | h1
        · rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ (by omega)]
          exact Rp_mono _ _ _ _ (hinv i hi)
        · subst h1
          rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
          simpa [hlen] using hd
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          exact rfl)
    rw [drun_length] at key
    rw [sim_cons, drun_cons]
    simpa only [drun_append] using key


lemma gen_fst_bound (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate)
    (hρ : ∀ r w, ρ.getD r (Sum.inl false) = Sum.inr w → w < N) (w : ℕ)
    (hw : (gen ρ N g).1 = Sum.inr w) : w < N + (gen ρ N g).2.length := by
  unfold gen at hw ⊢
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte] at hw ⊢
    rcases hi : g.inputs with _ | ⟨r, t⟩
    · rw [hi] at hw
      simp [genN] at hw
    · rw [hi] at hw
      rcases h : ρ.getD r (Sum.inl false) with c | v
      · simp only [genN, h, Sum.elim_inl] at hw
        cases hw
      · simp only [genN, h, Sum.elim_inr] at hw ⊢
        have hvw : N = w := Sum.inr.inj hw
        subst hvw
        simp
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    unfold genAO at hw ⊢
    by_cases hc : Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
    · rw [if_pos hc] at hw
      cases hw
    · rw [if_neg hc] at hw ⊢
      generalize hl : (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at hw ⊢
      have hbound : ∀ i ∈ l, i < N := by
        intro i hi'
        rw [← hl, List.mem_filterMap] at hi'
        obtain ⟨a, ha, hga⟩ := hi'
        rw [List.mem_map] at ha
        obtain ⟨r, _, hr⟩ := ha
        rw [Sum.getRight?_eq_some_iff] at hga
        rw [hga] at hr
        exact hρ r i hr
      rcases l with _ | ⟨v, _ | ⟨v2, t⟩⟩
      · simp [fin3] at hw
      · simp only [fin3] at hw ⊢
        have hvw : v = w := Sum.inr.inj hw
        subst hvw
        have := hbound v (by simp)
        simp only [List.length_nil, Nat.add_zero]
        exact this
      · simp only [fin3] at hw ⊢
        have hvw : N = w := Sum.inr.inj hw
        subst hvw
        simp

lemma gen_clean (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hlen : g.inputs.length ≤ 2)
    (hρ : ∀ r w, ρ.getD r (Sum.inl false) = Sum.inr w → w < N) :
    ∀ g' ∈ (gen ρ N g).2, (∀ i ∈ g'.inputs, i < N) ∧
      (g'.op = GateOp.not ∧ g'.inputs.length = 1 ∨
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2) := by
  unfold gen
  by_cases hn : isNot g.op = true
  · simp only [hn, ↓reduceIte]
    rcases hi : g.inputs with _ | ⟨r, t⟩
    · simp [genN]
    · rcases h : ρ.getD r (Sum.inl false) with c | w
      · simp only [genN, h, Sum.elim_inl]
        intro g' hg'
        cases hg'
      · simp only [genN, h, Sum.elim_inr, List.mem_singleton]
        rintro g' rfl
        refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
        intro i hi'
        simp only [List.mem_singleton] at hi'
        subst hi'
        exact hρ r _ h
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    unfold genAO
    split_ifs
    · simp
    · intro g' hg'
      generalize hl : (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at hg'
      have hll : l.length ≤ 2 := by
        rw [← hl]
        exact (List.length_filterMap_le _ _).trans (by simpa using hlen)
      have hbound : ∀ i ∈ l, i < N := by
        intro i hi'
        rw [← hl, List.mem_filterMap] at hi'
        obtain ⟨a, ha, hga⟩ := hi'
        rw [List.mem_map] at ha
        obtain ⟨r, _, hr⟩ := ha
        rw [Sum.getRight?_eq_some_iff] at hga
        rw [hga] at hr
        exact hρ r i hr
      rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
      · simp [fin3] at hg'
      · simp [fin3] at hg'
      · simp only [fin3, List.mem_singleton] at hg'
        subst hg'
        refine ⟨hbound, Or.inr ⟨?_, ?_⟩⟩
        · rcases hop with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd ((isNot_iff _).mpr h) hn
        · simp only [List.length_cons] at hll ⊢
          omega

lemma sim_clean (gs : List Gate) : ∀ (ρ : List (Bool ⊕ ℕ)) (N : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ r w, ρ.getD r (Sum.inl false) = Sum.inr w → w < N) →
    ∀ (idx : ℕ) (g' : Gate), (sim ρ N gs).2[idx]? = some g' →
      (∀ i ∈ g'.inputs, i < N + idx) ∧
        (g'.op = GateOp.not ∧ g'.inputs.length = 1 ∨
          (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2) := by
  induction gs with
  | nil =>
    intro ρ N _ _ idx g' h
    simp [sim] at h
  | cons g gs ih =>
    intro ρ N hops hρ idx g' h
    rw [sim_cons] at h
    have hg := hops g (by simp)
    by_cases hidx : idx < (gen ρ N g).2.length
    · rw [List.getElem?_append_left hidx] at h
      have hmem : g' ∈ (gen ρ N g).2 := List.mem_of_getElem? h
      obtain ⟨hb, hs⟩ := gen_clean ρ N g hg.1 hg.2 hρ g' hmem
      exact ⟨fun i hi => by have := hb i hi; omega, hs⟩
    · rw [List.getElem?_append_right (by omega)] at h
      have hρ' : ∀ r w, (ρ ++ [(gen ρ N g).1]).getD r (Sum.inl false) = Sum.inr w →
          w < N + (gen ρ N g).2.length := by
        intro r w hr
        rcases lt_trichotomy r ρ.length with h1 | h1 | h1
        · rw [List.getD_append _ _ _ _ h1] at hr
          have := hρ r w hr
          omega
        · subst h1
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hr
          exact gen_fst_bound ρ N g hρ w hr
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hr
          cases hr
      obtain ⟨hb, hs⟩ := ih _ _ (fun g2 hg2 => hops g2 (by simp [hg2])) hρ' _ g' h
      refine ⟨fun i hi => ?_, hs⟩
      have := hb i hi
      omega

def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 4 || x 6]

theorem inp_len (x : Fin 9 → Bool) : (inp x).length = 10 := by simp [inp]

def ρ0 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr

theorem ρ0_getD (i : ℕ) : ρ0.getD i (Sum.inl false) = if i < 10 then Sum.inr i else Sum.inl false := by
  unfold ρ0
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem main (fP : (Fin 9 → Bool) → Bool) (h0 : fP (fun _ => false) = false) (h1 : ∃ y, fP y = true)
    (gs : List Gate) (out : ℕ)
    (hfan : FanInTwo ({ gates := gs, output := 0 } : Circuit))
    (hcomp : ∀ x : Fin 9 → Bool, (drun gs (inp x)).getD out false = fP x) :
    ∃ (gs' : List Gate) (w : ℕ), gs'.length ≤ gs.length ∧ w < 10 + gs'.length ∧
      (∀ (k : ℕ) (g' : Gate), gs'[k]? = some g' → (∀ i ∈ g'.inputs, i < 10 + k) ∧
        (g'.op = GateOp.not ∧ g'.inputs.length = 1 ∨
          (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2)) ∧
      ∀ x : Fin 9 → Bool, (drun gs' (inp x)).getD w false = fP x := by
  have hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨k1, k2⟩ := hfan g hg
    refine ⟨?_, k2⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using k1
  have sem : ∀ x : Fin 9 → Bool, Rp (drun (sim ρ0 10 gs).2 (inp x)) (fP x)
      ((sim ρ0 10 gs).1.getD out (Sum.inl false)) := by
    intro x
    have key := sim_sem (fun _ => True) gs ρ0 (inp x) (inp x) (by simp [ρ0, inp_len])
      (fun g hg => (hops g hg).1) (fun _ _ _ _ => trivial)
      (by
        intro i _
        rw [ρ0_getD]
        split_ifs with h
        · exact ⟨by rw [inp_len]; exact h, rfl⟩
        · show (inp x).getD i false = false
          exact List.getD_eq_default _ _ (by rw [inp_len]; omega))
      out trivial
    rw [inp_len, hcomp x] at key
    exact key
  rcases hv : (sim ρ0 10 gs).1.getD out (Sum.inl false) with b | w
  · exfalso
    have e0 := sem (fun _ => false)
    rw [hv] at e0
    obtain ⟨y, hy⟩ := h1
    have e1 := sem y
    rw [hv] at e1
    simp only [Rp] at e0 e1
    rw [h0] at e0
    rw [hy, ← e0] at e1
    exact Bool.noConfusion e1
  · refine ⟨(sim ρ0 10 gs).2, w, sim_len2 _ _ _, ?_, ?_, ?_⟩
    · have e := sem (fun _ => false)
      rw [hv] at e
      have := e.1
      rw [drun_length, inp_len] at this
      omega
    · intro k g' hk
      exact sim_clean gs ρ0 10 hops (by
        intro r w' h
        rw [ρ0_getD] at h
        by_cases hr : r < 10
        · rw [if_pos hr] at h
          have : r = w' := Sum.inr.inj h
          omega
        · rw [if_neg hr] at h
          cases h) k g' hk
    · intro x
      have e := sem x
      rw [hv] at e
      exact e.2

end PEqualNP.Outside.L_meta_4548_aux

theorem PEqualNP.Outside.L_meta_4548 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (4 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) => (∀ x5 ∈ x4.inputs, x5 < (10 : ℕ) + x3) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x4.inputs.length = (1 : ℕ) ∨ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x4.inputs.length = (2 : ℕ)); ∀ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x7 : Fin (9 : ℕ) → Bool), ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x7)).getD x5 Bool.false = x1 x7) → ∃ (x8 : List PEqualNP.CircuitLowerBounds.Gate) (x9 : ℕ), x8.length ≤ x4.length ∧ x9 < (10 : ℕ) + x8.length ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x8[x10]? = Option.some x11 → x3 x10 x11) ∧ ∀ (x10 : Fin (9 : ℕ) → Bool), ({ gates := x8, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x10)).getD x9 Bool.false = x1 x10 := by
  dsimp only
  intro x4 x5 hfan hcomp
  exact PEqualNP.Outside.L_meta_4548_aux.main _ (by decide) ⟨fun i => decide (i = 0 ∨ i = 1), by decide⟩ x4 x5 hfan hcomp
