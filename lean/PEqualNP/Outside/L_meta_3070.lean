import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3070

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


def pred (P : List ℕ) (g : Gate) : Bool :=
  P.any fun v => (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).contains v

theorem pred_reads (P : List ℕ) (g : Gate) (hg : Good g) (h : pred P g = true) :
    ∃ v ∈ P, Reads v g := by
  obtain ⟨v, hv, hc⟩ := List.any_eq_true.1 h
  refine ⟨v, hv, ?_⟩
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, _⟩ := hg
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp [GateOp.eval] at hc
    exact ⟨hc, by simp⟩
  · simp [GateOp.eval] at hc
    exact ⟨hc, by simp⟩
  · simp [GateOp.eval] at hc
    rcases inputs with _ | ⟨a, r⟩
    · simp at hc
    · simp at hc
      subst hc
      exact ⟨by simp, fun _ => rfl⟩

theorem cntP (n2 : ℕ) (P : List ℕ) : ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
    (∀ g ∈ L, Good g) →
    (∀ v ∈ P, v < st.1.length ∧ st.1.getD v (Sum.inl false) = Sum.inl false) →
    (L.foldl (step n2) st).2.length + (L.filter (pred P)).length ≤ st.2.length + L.length := by
  intro L
  induction L with
  | nil => intro st _ _; simp
  | cons g L ih =>
    intro st hL hV
    have hV' : ∀ v ∈ P, v < (step n2 st g).1.length ∧
        (step n2 st g).1.getD v (Sum.inl false) = Sum.inl false :=
      fun v hv => step_keep n2 v st g (hV v hv).1 (hV v hv).2
    have hL' : ∀ g' ∈ L, Good g' := fun g' hg' => hL g' (by simp [hg'])
    have h1 := ih (step n2 st g) hL' hV'
    simp only [List.foldl_cons, List.length_cons]
    by_cases hp : pred P g = true
    · rw [List.filter_cons_of_pos hp, List.length_cons]
      obtain ⟨v, hv, hr⟩ := pred_reads P g (hL g (by simp)) hp
      rw [step_snd_eq n2 v st g (hL g (by simp)) (hV v hv).2 hr] at h1
      omega
    · rw [List.filter_cons_of_neg hp]
      have h2 := step_snd_le n2 st g
      omega

end PEqualNP.Outside.L_meta_3070

theorem PEqualNP.Outside.L_meta_3070 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 : List ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x6 ∈ x4, x3[x6]? = Option.some Option.none) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x7) x3) ≠ x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x8) x3)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x4.any fun (x10 : ℕ) => (if x9.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains x10) x2.gates).length ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.map (fun (x10 : Option (Fin x1)) => x10.elim Bool.false x9) x3) := by
  intro n C ρ P hF hP hnc
  have hG : ∀ g ∈ C.gates, L_meta_3070.Good g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hF g hg
    refine ⟨?_, h2⟩
    simpa using h1
  obtain ⟨st0, hst0⟩ : ∃ st0 : List (Bool ⊕ ℕ) × List Gate,
      st0 = (ρ.map (fun o => o.elim (Sum.inl false) (fun j => Sum.inr j.val)), []) := ⟨_, rfl⟩
  obtain ⟨st, hst⟩ : ∃ st : List (Bool ⊕ ℕ) × List Gate,
      st = C.gates.foldl (L_meta_3070.step n) st0 := ⟨_, rfl⟩
  have hmain : ∀ y : Fin n → Bool,
      st.1.map (L_meta_3070.val (L_meta_3070.run st.2 (List.ofFn y)))
        = L_meta_3070.run C.gates (ρ.map fun o => o.elim false y) ∧
      (∀ g' ∈ st.2, L_meta_3070.Good g') := by
    intro y
    rw [hst]
    apply L_meta_3070.main (List.ofFn y) n (by simp) C.gates _ st0 hG
    · rw [hst0, List.map_map]
      apply List.map_congr_left
      intro o _
      cases o with
      | none => rfl
      | some j => simp [L_meta_3070.run, Circuit.wires, L_meta_3070.val]
    · intro k hk
      rw [hst0] at hk
      obtain ⟨o, _, ho⟩ := List.mem_map.1 hk
      cases o with
      | none => cases ho
      | some j =>
        have hj : j.val = k := Sum.inr.inj ho
        have := j.isLt
        rw [hst0]
        simp only [List.length_nil]
        omega
    · intro g' hg'
      rw [hst0] at hg'
      cases hg'
  have hval : ∀ y : Fin n → Bool,
      C.eval (ρ.map fun o => o.elim false y) = L_meta_3070.val (L_meta_3070.run st.2 (List.ofFn y))
        (st.1.getD C.output (Sum.inl false)) := by
    intro y
    rw [L_meta_3070.val_getD, (hmain y).1]
    rfl
  have hcnt : st.2.length + (C.gates.filter (L_meta_3070.pred P)).length ≤ C.gates.length := by
    have := L_meta_3070.cntP n P C.gates st0 hG (by
      intro v hv
      have h := hP v hv
      have hlt : v < ρ.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at h
        cases h
      refine ⟨by rw [hst0]; simpa using hlt, ?_⟩
      rw [hst0]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, h]
      rfl)
    have h0 : st0.2.length = 0 := by rw [hst0]; rfl
    rw [hst]
    omega
  have hcnt' : st.2.length + (C.gates.filter (fun g => P.any fun v =>
      (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).contains v)).length
      ≤ C.size := hcnt
  cases hout : st.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨a, b', hne⟩ := hnc
    apply hne
    rw [hval a, hval b', hout]
    rfl
  | inr k =>
    refine ⟨⟨st.2, k⟩, ?_, hcnt', ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := (hmain (fun _ => false)).2 g hg
      refine ⟨?_, h2⟩
      simpa using h1
    · intro y
      rw [hval y, hout]
      rfl
