import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity



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



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩




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

theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
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
      · intro x w hw
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
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
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
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
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

theorem elim {X : Type} (op : GateOp) (l : List ℕ) (v : ℕ) (b : Bool) (B : ℕ) (f g : X → ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (hn : op = GateOp.not → l.head? = some v) (hv : v ∈ l)
    (hfv : ∀ x, f x v = b) (hfg : ∀ x i, i < B → f x i = g x i) (hfo : ∀ x i, B ≤ i → f x i = false) :
    (∃ c, ∀ x, op.eval (l.map (f x)) = c) ∨ (∃ w < B, ∀ x, op.eval (l.map (f x)) = g x w) := by
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
          · exact Or.inr ⟨c, hcB, fun x => by simp [GateOp.eval, hfv, hcg]⟩
      · cases b
        · exact Or.inl ⟨false, fun x => by simp [GateOp.eval, hfv]⟩
        · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨a, haB, fun x => by simp [GateOp.eval, hfv, hag]⟩
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
          · exact Or.inr ⟨c, hcB, fun x => by simp [GateOp.eval, hfv, hcg]⟩
        · exact Or.inl ⟨true, fun x => by simp [GateOp.eval, hfv]⟩
      · cases b
        · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
          · exact Or.inl ⟨c', fun x => by simp [GateOp.eval, hfv, hc']⟩
          · exact Or.inr ⟨a, haB, fun x => by simp [GateOp.eval, hfv, hag]⟩
        · exact Or.inl ⟨true, fun x => by simp [GateOp.eval, hfv]⟩
    · simp at hl
  · have hh := hn rfl
    rcases l with _ | ⟨a, l⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      exact Or.inl ⟨!b, fun x => by simp [GateOp.eval, hfv]⟩

theorem gate_case {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (src : (Fin n → Bool) → List Bool)
    (hsrc : ∀ x, (src x).length = n) (i : ℕ) (hi : i < C.gates.length) (v : ℕ) (b : Bool)
    (hn : C.gates[i].op = GateOp.not → C.gates[i].inputs.head? = some v) (hv : v ∈ C.gates[i].inputs)
    (hfv : ∀ x, (if v < n + i then (run C.gates (src x)).getD v false else false) = b) :
    (∃ c, ∀ x, (run C.gates (src x)).getD (n + i) false = c) ∨
      ∃ w < n + i, ∀ x, (run C.gates (src x)).getD (n + i) false = (run C.gates (src x)).getD w false := by
  have hval : ∀ x, (run C.gates (src x)).getD (n + i) false = C.gates[i].op.eval (C.gates[i].inputs.map
      fun w => if w < n + i then (run C.gates (src x)).getD w false else false) := by
    intro x
    have rg := run_gate C.gates (src x) i hi
    rw [hsrc x] at rg
    exact rg
  have hg := hC _ (List.getElem_mem hi)
  have hop : C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or ∨ C.gates[i].op = GateOp.not := by
    simpa using hg.1
  rcases elim (X := Fin n → Bool) C.gates[i].op C.gates[i].inputs v b (n + i)
      (fun x w => if w < n + i then (run C.gates (src x)).getD w false else false)
      (fun x w => (run C.gates (src x)).getD w false) hop hg.2 hn hv hfv
      (fun x w hw => by simp only [if_pos hw]) (fun x w hw => by simp only [if_neg (by omega : ¬ w < n + i)])
    with ⟨c, hc⟩ | ⟨w, hw, hwv⟩
  · exact Or.inl ⟨c, fun x => (hval x).trans (hc x)⟩
  · exact Or.inr ⟨w, hw, fun x => (hval x).trans (hwv x)⟩

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

theorem src_input {n : ℕ} (C : Circuit) (v : Fin n) (b : Bool) (x : Fin n → Bool) :
    (run C.gates (List.ofFn (Function.update x v b))).getD v.val false = b := by
  rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

end PEqualNP.Outside.L_meta_18545

open PEqualNP.Outside.L_meta_18545 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18545 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) := by
  intro n C v b K hC hnot hfalse hK
  classical
  have hKle : K.card ≤ C.gates.length := by
    have := Finset.card_le_univ K
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
    have hFcard : F.card = K.card := Finset.card_map _
    have hsrc : ∀ x : Fin n → Bool, (List.ofFn (Function.update x v b)).length = n := fun x => by simp
    have htgt : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => by simp
    obtain ⟨D, d1, d2, d3⟩ := engine3 (X := Fin n → Bool) n n C (fun x => List.ofFn (Function.update x v b))
      (fun x => List.ofFn x) hsrc htgt F hC (src_h0 v b)
      (by
        rintro ⟨c, hc⟩
        exact hconst ⟨c, hc⟩)
      (by
        intro j hj
        simp only [F, Finset.mem_map, Function.Embedding.coeFn_mk] at hj
        obtain ⟨i, hi, rfl⟩ := hj
        refine ⟨i.isLt, ?_⟩
        rcases hK i hi with ⟨c, hc⟩ | ⟨w, hw, c, hc⟩
        · exact Or.inl ⟨c, fun x => hc x⟩
        · simp only [List.get_eq_getElem] at hw
          exact gate_case C hC (fun x => List.ofFn (Function.update x v b)) hsrc i.val i.isLt w
            (if w < n + i.val then c else false)
            (fun hop => head_of_len1 _ _ (hnot _ (List.getElem_mem i.isLt) hop) hw) hw
            (fun x => by
              by_cases hlt : w < n + i.val
              · rw [if_pos hlt, if_pos hlt]
                exact hc x
              · rw [if_neg hlt, if_neg hlt]))
    exact ⟨D, d1, by rw [← hFcard]; exact d2, fun x => d3 x⟩
