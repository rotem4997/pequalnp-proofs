import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2553

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem run_append_one (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w
      = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

def val (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def act : GateOp → List (Bool ⊕ ℕ) → Option (Bool ⊕ ℕ)
  | GateOp.not, [] => some (Sum.inl true)
  | GateOp.not, Sum.inl b :: _ => some (Sum.inl (!b))
  | GateOp.and, [] => some (Sum.inl true)
  | GateOp.and, [s] => some s
  | GateOp.and, [Sum.inl b, s] => some (if b then s else Sum.inl false)
  | GateOp.and, [Sum.inr k, Sum.inl b] => some (if b then Sum.inr k else Sum.inl false)
  | GateOp.or, [] => some (Sum.inl false)
  | GateOp.or, [s] => some s
  | GateOp.or, [Sum.inl b, s] => some (if b then Sum.inl true else s)
  | GateOp.or, [Sum.inr k, Sum.inl b] => some (if b then Sum.inl true else Sum.inr k)
  | _, _ => none

def ins (a : List (Bool ⊕ ℕ)) : List ℕ := a.filterMap Sum.getRight?

theorem act_some (w : List Bool) (op : GateOp) (a : List (Bool ⊕ ℕ)) (s : Bool ⊕ ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = some s) : val w s = op.eval (a.map (val w)) := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; subst h; simp [val, GateOp.eval])
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> subst h <;> simp [val, GateOp.eval])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> subst h <;> simp [val, GateOp.eval])

theorem act_none (w : List Bool) (op : GateOp) (a : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = none) :
    op.eval ((ins a).map fun k => w.getD k false) = op.eval (a.map (val w)) := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; done)
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> simp [val, GateOp.eval, ins])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> simp [val, GateOp.eval, ins])

theorem act_mem (op : GateOp) (a : List (Bool ⊕ ℕ)) (k : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = some (Sum.inr k)) : Sum.inr k ∈ a := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; done)
  | (simp [act] at h; subst h; simp; done)
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> simp [h])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> simp [h])

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def step (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  match act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => (st.1 ++ [s], st.2)
  | none => (st.1 ++ [Sum.inr (n2 + st.2.length)],
      st.2 ++ [⟨g.op, ins (g.inputs.map fun i => st.1.getD i (Sum.inl false))⟩])

theorem val_append (w e : List Bool) (s : Bool ⊕ ℕ)
    (h : ∀ k, s = Sum.inr k → k < w.length) : val (w ++ e) s = val w s := by
  rcases s with b | k
  · rfl
  · have hk := h k rfl
    simp [val, List.getElem?_append_left hk]

theorem val_getD (w : List Bool) (m : List (Bool ⊕ ℕ)) (i : ℕ) :
    val w (m.getD i (Sum.inl false)) = (m.map (val w)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> simp [val]

theorem getD_mem (m : List (Bool ⊕ ℕ)) (i k : ℕ)
    (h : m.getD i (Sum.inl false) = Sum.inr k) : Sum.inr k ∈ m := by
  simp only [List.getD_eq_getElem?_getD] at h
  cases hm : m[i]? with
  | none => simp [hm] at h
  | some s =>
    simp [hm] at h
    subst h
    exact List.mem_of_getElem? hm

theorem step_inv (y : List Bool) (n2 : ℕ) (hn : y.length = n2) (g : Gate) (W : List Bool)
    (st : List (Bool ⊕ ℕ) × List Gate) (hg : Good g)
    (h1 : st.1.map (val (run st.2 y)) = W)
    (h3 : ∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length)
    (h4 : ∀ g' ∈ st.2, Good g') :
    (step n2 st g).1.map (val (run (step n2 st g).2 y))
        = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] ∧
      (∀ k, Sum.inr k ∈ (step n2 st g).1 → k < n2 + (step n2 st g).2.length) ∧
      (∀ g' ∈ (step n2 st g).2, Good g') := by
  obtain ⟨m, gs⟩ := st
  simp only at h1 h3 h4
  have hlen : (run gs y).length = n2 + gs.length := by rw [run_length, hn]
  have ha : (g.inputs.map fun i => m.getD i (Sum.inl false)).map (val (run gs y))
      = g.inputs.map fun i => W.getD i false := by
    rw [← h1, List.map_map]
    apply List.map_congr_left
    intro i _
    exact val_getD _ _ _
  have hal : (g.inputs.map fun i => m.getD i (Sum.inl false)).length ≤ 2 := by
    simpa using hg.2
  have hmem : ∀ k, Sum.inr k ∈ (g.inputs.map fun i => m.getD i (Sum.inl false)) →
      k < n2 + gs.length := by
    intro k hk
    obtain ⟨i, _, hi⟩ := List.mem_map.1 hk
    exact h3 k (getD_mem m i k hi)
  unfold step
  cases hact : act g.op (g.inputs.map fun i => m.getD i (Sum.inl false)) with
  | some s =>
    simp only
    refine ⟨?_, ?_, h4⟩
    · rw [List.map_append, h1, List.map_singleton, act_some _ _ _ _ hg.1 hal hact, ha]
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · exact h3 k hk
      · have hs : Sum.inr k = s := by simpa using hk
        subst hs
        exact hmem k (act_mem _ _ _ hg.1 hal hact)
  | none =>
    simp only
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_append, run_append_one, List.map_singleton]
      congr 1
      · rw [← h1]
        apply List.map_congr_left
        intro s hs
        apply val_append
        intro k hk
        subst hk
        rw [hlen]
        exact h3 k hs
      · simp only [val]
        rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [act_none _ _ _ hg.1 hal hact, ha]
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · have := h3 k hk
        simp only [List.length_append, List.length_singleton]
        omega
      · have hs : k = n2 + gs.length := by simpa using hk
        simp only [List.length_append, List.length_singleton]
        omega
    · intro g' hg'
      rcases List.mem_append.1 hg' with hg' | hg'
      · exact h4 g' hg'
      · have hs : g' = ⟨g.op, ins (g.inputs.map fun i => m.getD i (Sum.inl false))⟩ := by
          simpa using hg'
        subst hs
        refine ⟨hg.1, le_trans (List.length_filterMap_le _ _) hal⟩

theorem main (y : List Bool) (n2 : ℕ) (hn : y.length = n2) :
    ∀ (L : List Gate) (W : List Bool) (st : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ L, Good g) → st.1.map (val (run st.2 y)) = W →
      (∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length) → (∀ g' ∈ st.2, Good g') →
      (L.foldl (step n2) st).1.map (val (run (L.foldl (step n2) st).2 y)) = run L W ∧
      (∀ g' ∈ (L.foldl (step n2) st).2, Good g') := by
  intro L
  induction L with
  | nil =>
    intro W st _ h1 _ h4
    exact ⟨h1, h4⟩
  | cons g L ih =>
    intro W st hL h1 h3 h4
    obtain ⟨a, b, c⟩ := step_inv y n2 hn g W st (hL g (by simp)) h1 h3 h4
    rw [List.foldl_cons, run_cons]
    exact ih _ _ (fun g' hg' => hL g' (by simp [hg'])) a b c

def Reads (v : ℕ) (g : Gate) : Prop :=
  v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = Option.some v)

theorem reads_act (v : ℕ) (m : List (Bool ⊕ ℕ)) (g : Gate) (hg : Good g)
    (hm : m.getD v (Sum.inl false) = Sum.inl false) (hr : Reads v g) :
    ∃ s, act g.op (g.inputs.map fun i => m.getD i (Sum.inl false)) = some s := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := hg
  obtain ⟨hr1, hr2⟩ := hr
  simp only at hop hl hr1 hr2 ⊢
  rcases hop with rfl | rfl | rfl
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · simp at hr1
    · simp at hr1
      subst hr1
      simp [act]
    · simp at hr1
      rcases hr1 with rfl | rfl
      · simp only [List.map_cons, List.map_nil, hm]
        simp [act]
      · simp only [List.map_cons, List.map_nil, hm]
        rcases m.getD a (Sum.inl false) with (_ | _) | k <;> simp [act]
    · simp only [List.length_cons] at hl
      omega
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · simp at hr1
    · simp at hr1
      subst hr1
      simp [act]
    · simp at hr1
      rcases hr1 with rfl | rfl
      · simp only [List.map_cons, List.map_nil, hm]
        simp [act]
      · simp only [List.map_cons, List.map_nil, hm]
        rcases m.getD a (Sum.inl false) with (_ | _) | k <;> simp [act]
    · simp only [List.length_cons] at hl
      omega
  · have h := hr2 rfl
    rcases inputs with _ | ⟨a, r⟩
    · simp at h
    · simp at h
      subst h
      simp only [List.map_cons, hm]
      simp [act]

theorem step_fst (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    ∃ s, (step n2 st g).1 = st.1 ++ [s] := by
  unfold step
  cases act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => exact ⟨s, rfl⟩
  | none => exact ⟨_, rfl⟩

theorem step_snd_le (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (step n2 st g).2.length ≤ st.2.length + 1 := by
  unfold step
  cases act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => simp
  | none => simp

theorem step_snd_eq (n2 v : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : Good g)
    (hm : st.1.getD v (Sum.inl false) = Sum.inl false) (hr : Reads v g) :
    (step n2 st g).2 = st.2 := by
  obtain ⟨s, hs⟩ := reads_act v st.1 g hg hm hr
  unfold step
  rw [hs]

theorem step_keep (n2 v : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hv : v < st.1.length) (hm : st.1.getD v (Sum.inl false) = Sum.inl false) :
    v < (step n2 st g).1.length ∧ (step n2 st g).1.getD v (Sum.inl false) = Sum.inl false := by
  obtain ⟨s, hs⟩ := step_fst n2 st g
  rw [hs]
  refine ⟨by simp; omega, ?_⟩
  rw [List.getD_append _ _ _ _ hv]
  exact hm

theorem cnt0 (n2 : ℕ) : ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
    (L.foldl (step n2) st).2.length ≤ st.2.length + L.length := by
  intro L
  induction L with
  | nil => intro st; simp
  | cons g L ih =>
    intro st
    have h1 := ih (step n2 st g)
    have h2 := step_snd_le n2 st g
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem cnt1 (n2 v : ℕ) : ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (i : ℕ)
    (gi : Gate), (∀ g ∈ L, Good g) → v < st.1.length →
    st.1.getD v (Sum.inl false) = Sum.inl false → L[i]? = some gi → Reads v gi →
    (L.foldl (step n2) st).2.length + 1 ≤ st.2.length + L.length := by
  intro L
  induction L with
  | nil => intro st i gi _ _ _ hi; simp at hi
  | cons g L ih =>
    intro st i gi hL hv hm hi hr
    obtain ⟨kv, km⟩ := step_keep n2 v st g hv hm
    simp only [List.foldl_cons, List.length_cons]
    cases i with
    | zero =>
      simp at hi
      subst hi
      have h1 := cnt0 n2 L (step n2 st g)
      rw [step_snd_eq n2 v st g (hL g (by simp)) hm hr] at h1
      omega
    | succ i =>
      simp at hi
      have h1 := ih (step n2 st g) i gi (fun g' hg' => hL g' (by simp [hg'])) kv km hi hr
      have h2 := step_snd_le n2 st g
      omega

theorem cnt2 (n2 v : ℕ) : ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (i j : ℕ)
    (gi gj : Gate), (∀ g ∈ L, Good g) → v < st.1.length →
    st.1.getD v (Sum.inl false) = Sum.inl false → i < j → L[i]? = some gi → L[j]? = some gj →
    Reads v gi → Reads v gj →
    (L.foldl (step n2) st).2.length + 2 ≤ st.2.length + L.length := by
  intro L
  induction L with
  | nil => intro st i j gi gj _ _ _ _ hi; simp at hi
  | cons g L ih =>
    intro st i j gi gj hL hv hm hij hi hj hri hrj
    obtain ⟨kv, km⟩ := step_keep n2 v st g hv hm
    have hL' : ∀ g' ∈ L, Good g' := fun g' hg' => hL g' (by simp [hg'])
    simp only [List.foldl_cons, List.length_cons]
    cases j with
    | zero => omega
    | succ j =>
      simp at hj
      cases i with
      | zero =>
        simp at hi
        subst hi
        have h1 := cnt1 n2 v L (step n2 st g) j gj hL' kv km hj hrj
        rw [step_snd_eq n2 v st g (hL g (by simp)) hm hri] at h1
        omega
      | succ i =>
        simp at hi
        have h1 := ih (step n2 st g) i j gi gj hL' kv km (by omega) hi hj hri hrj
        have h2 := step_snd_le n2 st g
        omega

end PEqualNP.Outside.L_meta_2553

theorem PEqualNP.Outside.L_meta_2553 : ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x1) (x6 : Fin x1 → Fin x2),   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => x7 ∈ x8.inputs ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not → x8.inputs.head? = Option.some x7);   have x8 : (Fin x2 → Bool) → Bool := fun (x8 : Fin x2 → Bool) => x4.eval (List.ofFn fun (x9 : Fin x1) => if x9 = x5 then Bool.false else x8 (x6 x9));   PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ x3 + (2 : ℕ) → (x8 fun (x11 : Fin x2) => Bool.false) = Bool.false → (∃ (x12 : Fin x4.gates.length) (x13 : Fin x4.gates.length), x12 ≠ x13 ∧ x7 (↑x5) (x4.gates.get x12) ∧ x7 (↑x5) (x4.gates.get x13)) → PEqualNP.MetaComplexity.HasCircuitSize x2 x8 x3 := by
  intro n1 n2 s C x5 x6 P f hF hsize hzero hex
  obtain ⟨i, j, hij, hi, hj⟩ := hex
  have hG : ∀ g ∈ C.gates, L_meta_2553.Good g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hF g hg
    refine ⟨?_, h2⟩
    simpa using h1
  let st0 : List (Bool ⊕ ℕ) × List Gate :=
    (List.ofFn (fun k : Fin n1 => if k = x5 then Sum.inl false else Sum.inr (x6 k).val), [])
  let st := C.gates.foldl (L_meta_2553.step n2) st0
  have hmain : ∀ y : Fin n2 → Bool,
      st.1.map (L_meta_2553.val (L_meta_2553.run st.2 (List.ofFn y)))
        = L_meta_2553.run C.gates
            (List.ofFn fun k : Fin n1 => if k = x5 then false else y (x6 k)) ∧
      (∀ g' ∈ st.2, L_meta_2553.Good g') := by
    intro y
    apply L_meta_2553.main (List.ofFn y) n2 (by simp) C.gates _ st0 hG
    · simp only [st0, L_meta_2553.run, Circuit.wires, List.foldl_nil, List.map_ofFn]
      congr 1
      funext k
      by_cases hk : k = x5
      · simp [hk, L_meta_2553.val]
      · simp [hk, L_meta_2553.val]
    · intro k hk
      simp only [st0, List.mem_ofFn] at hk
      obtain ⟨a, ha⟩ := hk
      by_cases hk : a = x5
      · simp [hk] at ha
      · simp [hk] at ha
        have := (x6 a).isLt
        omega
    · intro g' hg'
      cases hg'
  have hval : ∀ y : Fin n2 → Bool,
      f y = L_meta_2553.val (L_meta_2553.run st.2 (List.ofFn y))
        (st.1.getD C.output (Sum.inl false)) := by
    intro y
    rw [L_meta_2553.val_getD, (hmain y).1]
    rfl
  have hcnt : st.2.length + 2 ≤ C.gates.length := by
    have hv : (x5 : ℕ) < st0.1.length := by simp [st0]
    have hm : st0.1.getD (x5 : ℕ) (Sum.inl false) = Sum.inl false := by
      simp [st0]
    have hi' : C.gates[(i : ℕ)]? = some (C.gates.get i) := by simp
    have hj' : C.gates[(j : ℕ)]? = some (C.gates.get j) := by simp
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := L_meta_2553.cnt2 n2 x5 C.gates st0 i j _ _ hG hv hm hlt hi' hj' hi hj
      simpa [st0] using this
    · have := L_meta_2553.cnt2 n2 x5 C.gates st0 j i _ _ hG hv hm hlt hj' hi' hj hi
      simpa [st0] using this
  have hsz : st.2.length ≤ s := by
    have : C.gates.length ≤ s + 2 := hsize
    omega
  cases hout : st.1.getD C.output (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have h := hval (fun _ => false)
      rw [hout] at h
      exact h.symm.trans hzero
    subst hb
    refine ⟨⟨st.2, n2 + st.2.length⟩, ?_, hsz, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := (hmain (fun _ => false)).2 g hg
      refine ⟨?_, h2⟩
      simpa using h1
    · intro y
      rw [hval y, hout]
      change (L_meta_2553.run st.2 (List.ofFn y)).getD (n2 + st.2.length) false = false
      rw [List.getD_eq_default]
      rw [L_meta_2553.run_length]
      simp
  | inr k =>
    refine ⟨⟨st.2, k⟩, ?_, hsz, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := (hmain (fun _ => false)).2 g hg
      refine ⟨?_, h2⟩
      simpa using h1
    · intro y
      rw [hval y, hout]
      rfl
