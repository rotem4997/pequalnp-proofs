import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18649



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emitAO (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl


theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  rcases hop with hop | hop | hop
  · exact emitAO N hs op (Or.inl hop) rs hl hv
  · exact emitAO N hs op (Or.inr hop) rs hl hv
  · subst hop
    rcases rs with _ | ⟨r, rs⟩
    · exact ⟨.inl true, [], by simp, by simp, by simp, fun y _ => by simp [GateOp.eval, rv]⟩
    · rcases r with c | t
      · exact ⟨.inl (!c), [], by simp, by simp, by simp, fun y _ => by simp [GateOp.eval, rv]⟩
      · refine ⟨.inr (N + hs.length), [⟨GateOp.not, [t]⟩], by simp, by simp [fok], by simp, fun y hy => ?_⟩
        have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
        simp only [rv]
        rw [run_snoc, hlen, getD_at]
        simp [GateOp.eval, rv]

theorem engine4 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F P : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hdis : ∀ j ∈ F, j ∉ P)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, (∀ i ∈ P, w ≠ n + i) ∧ ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false))
    (hP : ∀ j ∈ P, j < C.gates.length ∧ C.output ≠ n + j ∧ ∀ i (hi : i < C.gates.length), n + j ∈ C.gates[i].inputs → i ∈ F ∨ i ∈ P) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card + P.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + ((F ∪ P).filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (∀ i ∈ P, w ≠ n + i) → (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw _
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F ∪ P then 1 else 0) ≤ 1 →
          (∀ x : X, (∀ i ∈ P, n + k ≠ n + i) → (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + ((F ∪ P).filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (∀ i ∈ P, w ≠ n + i) → (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : ((F ∪ P).filter fun j => j < k + 1) ⊆ ((F ∪ P).filter fun j => j < k) ∪ (if k ∈ F ∪ P then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F ∪ P
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw hlive
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x hlive
          · rw [Function.update_of_ne hwe, h4 x w (by omega) hlive]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · have hkFP : k ∈ F ∪ P := Finset.mem_union_left _ hkF
        rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hwl, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by rw [if_pos hkFP]; simp) (fun x _ => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by rw [if_pos hkFP]; simp) (fun x _ => ?_)
          rw [List.append_nil, ← h4 x w hw hwl]
          exact hb x
      · by_cases hkP : k ∈ P
        · have hkFP : k ∈ F ∪ P := Finset.mem_union_right _ hkP
          exact fin (.inl false) [] (by simp) (by simp) (by rw [if_pos hkFP]; simp) (fun x hl => absurd rfl (hl k hkP))
        · have hkFP : k ∉ F ∪ P := by
            rw [Finset.mem_union]
            rintro (h | h)
            · exact hkF h
            · exact hkP h
          have hg := hC _ (List.getElem_mem hk')
          have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
          let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
          obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
            intro r hr t ht
            obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
            simp only [m'] at ht
            split_ifs at ht with h
            exact h3 i t h ht)
          refine fin r e e2 e3 (by rw [if_neg hkFP]; omega) (fun x _ => ?_)
          rw [e4 _ (htgt x)]
          have rg := run_gate C.gates (src x) k hk'
          rw [hsrc] at rg
          rw [rg, List.map_map]
          congr 1
          refine List.map_congr_left fun i hi => ?_
          simp only [Function.comp, m']
          split_ifs with h
          · refine h4 x i h ?_
            intro j hj hij
            subst hij
            rcases (hP j hj).2.2 k hk' hi with h' | h'
            · exact hkF h'
            · exact hkP h'
          · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : ((F ∪ P).filter fun j => j < C.gates.length) = F ∪ P := Finset.filter_true_of_mem fun j hj => by
    rcases Finset.mem_union.1 hj with h | h
    · exact (hF j h).1
    · exact (hP j h).1
  rw [hFc, Finset.card_union_of_disjoint (Finset.disjoint_left.2 hdis)] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout (fun i hi => (hP i hi).2.1)
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, by simp only [Circuit.size]; omega, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem head_of_len1 (l : List ℕ) (v : ℕ) (h1 : l.length = 1) (hv : v ∈ l) : l.head? = some v := by
  rcases l with _ | ⟨a, _ | ⟨c, l⟩⟩
  · simp at h1
  · simp at hv
    simp [hv]
  · simp at h1

theorem elim2 {X : Type} (op : GateOp) (l : List ℕ) (v : ℕ) (b : Bool) (B : ℕ) (f g : X → ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (hn : op = GateOp.not → l.head? = some v) (hv : v ∈ l)
    (hfv : ∀ x, f x v = b) (hfg : ∀ x i, i < B → f x i = g x i) (hfo : ∀ x i, B ≤ i → f x i = false) :
    (∃ c, ∀ x, op.eval (l.map (f x)) = c) ∨ (∃ w ∈ l, w < B ∧ ∀ x, op.eval (l.map (f x)) = g x w) := by
  have two : ∀ w : ℕ, (∃ c, ∀ x, f x w = c) ∨ (w < B ∧ ∀ x, f x w = g x w) := by
    intro w
    by_cases hw : w < B
    · exact Or.inr ⟨hw, fun x => hfg x w hw⟩
    · exact Or.inl ⟨false, fun x => hfo x w (by omega)⟩
  rcases hop with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
    · simp at hv
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      exact Or.inl ⟨b, fun x => by simp [GateOp.eval, hfv]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · cases b
        · exact Or.inl ⟨false, fun x => by simp [GateOp.eval, hfv]⟩
        · rcases two c with ⟨c', hc'⟩ | ⟨hcB, hcg⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨c, by simp, hcB, fun x => by simp [GateOp.eval, hfv, hcg]⟩
      · cases b
        · exact Or.inl ⟨false, fun x => by simp [GateOp.eval, hfv]⟩
        · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨a, by simp, haB, fun x => by simp [GateOp.eval, hfv, hag]⟩
    · simp at hl
  · rcases l with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
    · simp at hv
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      exact Or.inl ⟨b, fun x => by simp [GateOp.eval, hfv]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · cases b
        · rcases two c with ⟨c', hc'⟩ | ⟨hcB, hcg⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨c, by simp, hcB, fun x => by simp [GateOp.eval, hfv, hcg]⟩
        · exact Or.inl ⟨true, fun x => by simp [GateOp.eval, hfv]⟩
      · cases b
        · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨a, by simp, haB, fun x => by simp [GateOp.eval, hfv, hag]⟩
        · exact Or.inl ⟨true, fun x => by simp [GateOp.eval, hfv]⟩
    · simp at hl
  · have hh := hn rfl
    rcases l with _ | ⟨a, l⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      exact Or.inl ⟨!b, fun x => by simp [GateOp.eval, hfv]⟩

theorem gate_case2 {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (src : (Fin n → Bool) → List Bool)
    (hsrc : ∀ x, (src x).length = n) (i : ℕ) (hi : i < C.gates.length) (v : ℕ) (b : Bool)
    (hn : C.gates[i].op = GateOp.not → C.gates[i].inputs.head? = some v) (hv : v ∈ C.gates[i].inputs)
    (hfv : ∀ x, (if v < n + i then (run C.gates (src x)).getD v false else false) = b) :
    (∃ c, ∀ x, (run C.gates (src x)).getD (n + i) false = c) ∨
      ∃ w ∈ C.gates[i].inputs, w < n + i ∧ ∀ x, (run C.gates (src x)).getD (n + i) false = (run C.gates (src x)).getD w false := by
  have hval : ∀ x, (run C.gates (src x)).getD (n + i) false = C.gates[i].op.eval (C.gates[i].inputs.map
      fun w => if w < n + i then (run C.gates (src x)).getD w false else false) := by
    intro x
    have rg := run_gate C.gates (src x) i hi
    rw [hsrc x] at rg
    exact rg
  have hg := hC _ (List.getElem_mem hi)
  have hop : C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or ∨ C.gates[i].op = GateOp.not := by
    simpa using hg.1
  rcases elim2 (X := Fin n → Bool) C.gates[i].op C.gates[i].inputs v b (n + i)
      (fun x w => if w < n + i then (run C.gates (src x)).getD w false else false)
      (fun x w => (run C.gates (src x)).getD w false) hop hg.2 hn hv hfv
      (fun x w hw => by simp only [if_pos hw]) (fun x w hw => by simp only [if_neg (by omega : ¬ w < n + i)])
    with ⟨c, hc⟩ | ⟨w, hwl, hw, hwv⟩
  · exact Or.inl ⟨c, fun x => (hval x).trans (hc x)⟩
  · exact Or.inr ⟨w, hwl, hw, fun x => (hval x).trans (hwv x)⟩

theorem src_h0 {n : ℕ} (v : Fin n) (b : Bool) : ∀ w < n,
    (∃ c, ∀ x : Fin n → Bool, (List.ofFn (Function.update x v b)).getD w false = c) ∨
      ∃ t < n, ∀ x : Fin n → Bool, (List.ofFn (Function.update x v b)).getD w false = (List.ofFn x).getD t false := by
  intro w hw
  by_cases hwv : w = v.val
  · left
    refine ⟨b, fun x => ?_⟩
    subst hwv
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  · right
    refine ⟨w, hw, fun x => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp only [List.getElem_ofFn]
    rw [Function.update_of_ne (fun h => hwv (by rw [← h]))]

end PEqualNP.Outside.L_meta_18649

open PEqualNP.Outside.L_meta_18649 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18649 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K P : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → Disjoint K P → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) → (∀ p ∈ P, n + p.val ≠ C.output ∧ ∀ k : Fin C.gates.length, n + p.val ∈ (C.gates.get k).inputs → k ∈ P ∨ (k ∈ K ∧ ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = c)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card + P.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) := by
  intro n C v b K P hC hnot hfalse hKP hK hP
  classical
  have hKle : K.card + P.card ≤ C.gates.length := by
    have := Finset.card_le_univ (K ∪ P)
    rw [Finset.card_union_of_disjoint hKP] at this
    simpa using this
  by_cases hconst : ∃ c, ∀ x : Fin n → Bool, C.eval (List.ofFn (Function.update x v b)) = c
  · obtain ⟨c, hc⟩ := hconst
    obtain ⟨y, hy⟩ := hfalse
    have hcf : c = false := by rw [← hc y, hy]
    subst hcf
    refine ⟨⟨[], n⟩, fun g hg => by simp at hg, ?_, fun x => ?_⟩
    · simp only [Circuit.size, List.length_nil, Nat.zero_add]
      exact hKle
    · rw [hc x]
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
  · let F : Finset ℕ := K.map ⟨Fin.val, Fin.val_injective⟩
    let P' : Finset ℕ := P.map ⟨Fin.val, Fin.val_injective⟩
    have hFcard : F.card = K.card := Finset.card_map _
    have hPcard : P'.card = P.card := Finset.card_map _
    have memF : ∀ j : ℕ, j ∈ F ↔ ∃ h : j < C.gates.length, (⟨j, h⟩ : Fin C.gates.length) ∈ K := by
      intro j
      simp only [F, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.isLt, hi⟩
      · rintro ⟨h, hj⟩
        exact ⟨_, hj, rfl⟩
    have memP : ∀ j : ℕ, j ∈ P' ↔ ∃ h : j < C.gates.length, (⟨j, h⟩ : Fin C.gates.length) ∈ P := by
      intro j
      simp only [P', Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.isLt, hi⟩
      · rintro ⟨h, hj⟩
        exact ⟨_, hj, rfl⟩
    have hsrc : ∀ x : Fin n → Bool, (List.ofFn (Function.update x v b)).length = n := fun x => by simp
    have htgt : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => by simp
    obtain ⟨D, d1, d2, d3⟩ := engine4 (X := Fin n → Bool) n n C (fun x => List.ofFn (Function.update x v b))
      (fun x => List.ofFn x) hsrc htgt F P' hC (src_h0 v b)
      (by
        rintro ⟨c, hc⟩
        exact hconst ⟨c, hc⟩)
      (by
        intro j hjF hjP
        obtain ⟨h1, h1'⟩ := (memF j).1 hjF
        obtain ⟨h2, h2'⟩ := (memP j).1 hjP
        exact Finset.disjoint_left.1 hKP h1' h2')
      (by
        intro j hj
        obtain ⟨hjl, hjK⟩ := (memF j).1 hj
        refine ⟨hjl, ?_⟩
        by_cases hcj : ∃ c, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (Function.update x v b))).getD (n + j) false = c
        · exact Or.inl hcj
        · rcases hK ⟨j, hjl⟩ hjK with ⟨c, hc⟩ | ⟨w, hw, c, hc⟩
          · exact absurd ⟨c, fun x => hc x⟩ hcj
          · simp only [List.get_eq_getElem] at hw
            rcases gate_case2 C hC (fun x => List.ofFn (Function.update x v b)) hsrc j hjl w
              (if w < n + j then c else false)
              (fun hop => head_of_len1 _ _ (hnot _ (List.getElem_mem hjl) hop) hw) hw
              (fun x => by
                by_cases hlt : w < n + j
                · rw [if_pos hlt, if_pos hlt]
                  exact hc x
                · rw [if_neg hlt, if_neg hlt]) with hc2 | ⟨w', hw'l, hw', hcopy⟩
            · exact absurd hc2 hcj
            · refine Or.inr ⟨w', hw', ?_, hcopy⟩
              intro i hi hwi
              obtain ⟨hil, hiP⟩ := (memP i).1 hi
              have hread : n + (⟨i, hil⟩ : Fin C.gates.length).val ∈ (C.gates.get ⟨j, hjl⟩).inputs := by
                simp only [List.get_eq_getElem]
                rw [← hwi]
                exact hw'l
              rcases (hP ⟨i, hil⟩ hiP).2 ⟨j, hjl⟩ hread with h | ⟨_, c', hc'⟩
              · exact Finset.disjoint_left.1 hKP hjK h
              · exact hcj ⟨c', fun x => hc' x⟩)
      (by
        intro j hj
        obtain ⟨hjl, hjP⟩ := (memP j).1 hj
        refine ⟨hjl, fun h => (hP ⟨j, hjl⟩ hjP).1 h.symm, fun i hi hread => ?_⟩
        rcases (hP ⟨j, hjl⟩ hjP).2 ⟨i, hi⟩ (by simpa using hread) with h | ⟨h, _⟩
        · exact Or.inr ((memP i).2 ⟨hi, h⟩)
        · exact Or.inl ((memF i).2 ⟨hi, h⟩))
    exact ⟨D, d1, by rw [← hFcard, ← hPcard]; exact d2, fun x => d3 x⟩
