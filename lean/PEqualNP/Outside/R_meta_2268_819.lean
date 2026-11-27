import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2268_819
    (hMono : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      H.Colorable (2 : ℕ) →
      (∀ v : Fin m, (H.neighborSet v).ncard = (3 : ℕ)) →
      (∀ (v : Fin m) (p : H.Walk v v), p.IsCycle → (7 : ℕ) ≤ p.length) →
      (∃ u v : Fin m, H.Adj u v) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size + (1 : ℕ) < (2 : ℕ) * m →
        (∀ x : Fin m → Bool, C.eval (List.ofFn x) = Bool.true ↔
          ∃ u v : Fin m, H.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) →
        ∃ u v : Fin m, u ≠ v ∧ ¬H.Adj u v ∧ ∃ t : ℕ, t + (8 : ℕ) ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize m
            (fun x : Fin m → Bool => C.eval (List.ofFn (Function.update (Function.update x u Bool.false) v Bool.false))) t)
    (hWithNot : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      H.Colorable (2 : ℕ) →
      (∀ v : Fin m, (H.neighborSet v).ncard = (3 : ℕ)) →
      (∀ (v : Fin m) (p : H.Walk v v), p.IsCycle → (7 : ℕ) ≤ p.length) →
      (∃ u v : Fin m, H.Adj u v) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        C.size + (1 : ℕ) < (2 : ℕ) * m →
        (∀ x : Fin m → Bool, C.eval (List.ofFn x) = Bool.true ↔
          ∃ u v : Fin m, H.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) →
        ∃ u v : Fin m, u ≠ v ∧ ¬H.Adj u v ∧ ∃ t : ℕ, t + (8 : ℕ) ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize m
            (fun x : Fin m → Bool => C.eval (List.ofFn (Function.update (Function.update x u Bool.false) v Bool.false))) t)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  have notEval_nil : PEqualNP.CircuitLowerBounds.GateOp.not.eval [] = true := rfl
  have notEval_cons : ∀ b bs, PEqualNP.CircuitLowerBounds.GateOp.not.eval (b :: bs) = !b := fun _ _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    simp [run, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
  have getD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have getD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b
    simp [List.getD_eq_getElem?_getD]
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have := run_prefix [] gs x i (by simpa using hi)
    simpa [run] using this
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
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
        rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  let rv : List Bool → Bool ⊕ ℕ → Bool := fun w r => Sum.elim id (fun t => w.getD t false) r
  let fok : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2
  have rv_ext : ∀ (hs e : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool) (r : Bool ⊕ ℕ),
      (∀ t, r = Sum.inr t → t < y.length + hs.length) →
      rv (run (hs ++ e) y) r = rv (run hs y) r := by
    intro hs e y r h
    rcases r with b | t
    · rfl
    · exact run_prefix hs e y t (h t rfl)
  have emitAO : ∀ (N : ℕ) (hs : List PEqualNP.CircuitLowerBounds.Gate) (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (rs : List (Bool ⊕ ℕ)), rs.length ≤ 2 →
      (∀ r ∈ rs, ∀ t, r = Sum.inr t → t < N + hs.length) →
      ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
        (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro N hs op hop rs hl hv
    have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = Sum.inr t → t < N + hs.length) →
        (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
          (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
      intro r h1 h2
      exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
    have add : ∀ g : PEqualNP.CircuitLowerBounds.Gate, fok g →
        (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
          (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
      intro g h1 h2
      refine ⟨Sum.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
      · intro t ht; cases ht; simp
      · have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
        dsimp only [rv, Sum.elim]
        rw [run_snoc, hlen, getD_at]
        exact h2 y hy
    rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
    · rcases hop with rfl | rfl
      · exact keep (Sum.inl true) (by simp) (by intro y _; rfl)
      · exact keep (Sum.inl false) (by simp) (by intro y _; rfl)
    · have hr := hv r (by simp)
      rcases hop with rfl | rfl
      · exact keep r hr (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons])
      · exact keep r hr (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons])
    · have hr := hv r (by simp)
      have hs' := hv s (by simp)
      rcases hop with rfl | rfl
      · rcases r with b | t
        · cases b
          · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
          · exact keep s hs' (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
            · exact keep (Sum.inr t) hr (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩
              (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
      · rcases r with b | t
        · cases b
          · exact keep s hs' (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
          · exact keep (Sum.inl true) (by simp) (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inr t) hr (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
            · exact keep (Sum.inl true) (by simp) (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩
              (by intro y _; simp [andEval, orEval, notEval_nil, notEval_cons, rv])
    · simp at hl
  have emit : ∀ (N : ℕ) (hs : List PEqualNP.CircuitLowerBounds.Gate) (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∀ (rs : List (Bool ⊕ ℕ)), rs.length ≤ 2 →
      (∀ r ∈ rs, ∀ t, r = Sum.inr t → t < N + hs.length) →
      ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
        (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro N hs op hop rs hl hv
    rcases hop with hop | hop | hop
    · exact emitAO N hs op (Or.inl hop) rs hl hv
    · exact emitAO N hs op (Or.inr hop) rs hl hv
    · subst hop
      rcases rs with _ | ⟨r, rs⟩
      · exact ⟨Sum.inl true, [], by simp, by simp, by simp, fun y _ => by simp [andEval, orEval, notEval_nil, notEval_cons, rv]⟩
      · rcases r with c | t
        · exact ⟨Sum.inl (!c), [], by simp, by simp, by simp, fun y _ => by simp [andEval, orEval, notEval_nil, notEval_cons, rv]⟩
        · refine ⟨Sum.inr (N + hs.length), [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [t]⟩], by simp, by simp [fok], by simp, fun y hy => ?_⟩
          have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
          dsimp only [rv, Sum.elim]
          rw [run_snoc, hlen, getD_at]
          simp [andEval, orEval, notEval_nil, notEval_cons, rv]
  have engine3 : ∀ {X : Type} (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (src tgt : X → List Bool), (∀ x, (src x).length = n) → (∀ x, (tgt x).length = M) →
      ∀ (F : Finset ℕ), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false) →
      (¬∃ b, ∀ x, C.eval (src x) = b) →
      (∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
        ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
    intro X n M C src tgt hsrc htgt F hC h0 hne hF
    have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
        (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
        (∀ w t, w < n + k → m w = Sum.inr t → t < M + hs.length) ∧
        ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then Sum.inr h.choose
          else if hb : ∃ b, ∀ x, (src x).getD w false = b then Sum.inl hb.choose else Sum.inl false, by simp, by simp, ?_, ?_⟩
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
        have fin : ∀ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate),
            (∀ g ∈ e, fok g) → (∀ t, r = Sum.inr t → t < M + hs.length + e.length) →
            e.length + (if k ∈ F then 1 else 0) ≤ 1 →
            (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
            ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
              (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
              (∀ w t, w < n + (k + 1) → m w = Sum.inr t → t < M + hs.length) ∧
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
          · exact fin (Sum.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
          · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
            rw [List.append_nil, ← h4 x w hw]
            exact hb x
        · have hg := hC _ (List.getElem_mem hk')
          have hop : C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
              C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hg.1
          let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else Sum.inl false
          obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m')
            (by rw [List.length_map]; exact hg.2) (by
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
  have elim : ∀ {X : Type} (op : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ) (v : ℕ) (b : Bool) (B : ℕ)
      (f g : X → ℕ → Bool),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        op = PEqualNP.CircuitLowerBounds.GateOp.not) → l.length ≤ 2 →
      (op = PEqualNP.CircuitLowerBounds.GateOp.not → l.head? = some v) → v ∈ l →
      (∀ x, f x v = b) → (∀ x i, i < B → f x i = g x i) → (∀ x i, B ≤ i → f x i = false) →
      (∃ c, ∀ x, op.eval (l.map (f x)) = c) ∨ (∃ w < B, ∀ x, op.eval (l.map (f x)) = g x w) := by
    intro X op l v b B f g hop hl hn hv hfv hfg hfo
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
        exact Or.inl ⟨b, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · cases b
          · exact Or.inl ⟨false, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
          · rcases two c with ⟨c', hc'⟩ | ⟨hcB, hcg⟩
            · exact Or.inl ⟨c', fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hc']⟩
            · exact Or.inr ⟨c, hcB, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hcg]⟩
        · cases b
          · exact Or.inl ⟨false, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
          · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
            · exact Or.inl ⟨c', fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hc']⟩
            · exact Or.inr ⟨a, haB, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hag]⟩
      · simp at hl
    · rcases l with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
      · simp at hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        subst hv
        exact Or.inl ⟨b, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · cases b
          · rcases two c with ⟨c', hc'⟩ | ⟨hcB, hcg⟩
            · exact Or.inl ⟨c', fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hc']⟩
            · exact Or.inr ⟨c, hcB, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hcg]⟩
          · exact Or.inl ⟨true, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
        · cases b
          · rcases two a with ⟨c', hc'⟩ | ⟨haB, hag⟩
            · exact Or.inl ⟨c', fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hc']⟩
            · exact Or.inr ⟨a, haB, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv, hag]⟩
          · exact Or.inl ⟨true, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
      · simp at hl
    · have hh := hn rfl
      rcases l with _ | ⟨a, l⟩
      · simp at hh
      · simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        exact Or.inl ⟨!b, fun x => by simp [andEval, orEval, notEval_nil, notEval_cons, hfv]⟩
  have hStripOne : ∀ (n k : ℕ) (F : (Fin n → Bool) → Bool) (p : Fin n),
      PEqualNP.MetaComplexity.HasCircuitSize n F k →
      (∃ x, F (Function.update x p false) ≠ F (Function.update x p true)) →
      (∃ x y, F (Function.update x p false) ≠ F (Function.update y p false)) →
      1 ≤ k ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x p false)) (k - 1) := by
    intro n k F p hFk hdep hnc
    obtain ⟨C, hC, hCsz, hCev⟩ := hFk
    obtain ⟨x0, hx0⟩ := hdep
    obtain ⟨y0, y1, hy01⟩ := hnc
    have hout_ne : C.output ≠ p.val := by
      intro heq
      have hval : ∀ x : Fin n → Bool, F x = x p := by
        intro x
        rw [← hCev x]
        change (run C.gates (List.ofFn x)).getD C.output false = x p
        rw [heq, run_input _ _ _ (by simp [p.isLt])]
        simp [List.getD_eq_getElem?_getD, p.isLt]
      apply hy01
      rw [hval, hval, Function.update_self, Function.update_self]
    have hreader : ∃ j : ℕ, ∃ hj : j < C.gates.length,
        p.val ∈ C.gates[j].inputs ∧
        (C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.not → C.gates[j].inputs.head? = some p.val) := by
      by_contra hno
      have hsame : ∀ t ≤ C.gates.length, ∀ w < n + t, w ≠ p.val →
          (run C.gates (List.ofFn (Function.update x0 p false))).getD w false =
          (run C.gates (List.ofFn (Function.update x0 p true))).getD w false := by
        intro t
        induction t with
        | zero =>
          intro _ w hw hne
          have hwn : w < n := by omega
          rw [run_input _ _ _ (by simp [hwn]), run_input _ _ _ (by simp [hwn])]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hwn, ↓reduceDIte, Option.getD_some]
          have hfin : (⟨w, hwn⟩ : Fin n) ≠ p := fun he => hne (congrArg Fin.val he)
          rw [Function.update_of_ne hfin, Function.update_of_ne hfin]
        | succ t ih =>
          intro ht w hw hne
          by_cases hlt : w < n + t
          · exact ih (by omega) w hlt hne
          · have hwe : w = n + t := by omega
            subst hwe
            have ht' : t < C.gates.length := by omega
            have rg1 := run_gate C.gates (List.ofFn (Function.update x0 p false)) t ht'
            have rg2 := run_gate C.gates (List.ofFn (Function.update x0 p true)) t ht'
            simp only [List.length_ofFn] at rg1 rg2
            rw [rg1, rg2]
            have hg := hC _ (List.getElem_mem ht')
            have hop : C.gates[t].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                C.gates[t].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
                C.gates[t].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hg.1
            rcases hop with hop | hop | hop
            · have hp_not : p.val ∉ C.gates[t].inputs := by
                intro hmem
                exact hno ⟨t, ht', hmem, fun h => by rw [hop] at h; cases h⟩
              congr 1
              refine List.map_congr_left fun i hi => ?_
              have hip : i ≠ p.val := fun he => hp_not (he ▸ hi)
              split_ifs with h
              · exact ih (by omega) i h hip
              · rfl
            · have hp_not : p.val ∉ C.gates[t].inputs := by
                intro hmem
                exact hno ⟨t, ht', hmem, fun h => by rw [hop] at h; cases h⟩
              congr 1
              refine List.map_congr_left fun i hi => ?_
              have hip : i ≠ p.val := fun he => hp_not (he ▸ hi)
              split_ifs with h
              · exact ih (by omega) i h hip
              · rfl
            · rw [hop]
              rcases hlin : C.gates[t].inputs with _ | ⟨a, rest⟩
              · rfl
              · have hap : a ≠ p.val := by
                  intro he
                  apply hno
                  refine ⟨t, ht', ?_, ?_⟩
                  · rw [hlin, he]; simp
                  · intro _; rw [hlin, he]; rfl
                simp only [List.map_cons, andEval, orEval, notEval_nil, notEval_cons]
                split_ifs with h
                · congr 1; exact ih (by omega) a h hap
                · rfl
      apply hx0
      rw [← hCev, ← hCev]
      change (run C.gates (List.ofFn (Function.update x0 p false))).getD C.output false =
        (run C.gates (List.ofFn (Function.update x0 p true))).getD C.output false
      by_cases hout : C.output < n + C.gates.length
      · exact hsame C.gates.length le_rfl C.output hout hout_ne
      · rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
            List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
    obtain ⟨j, hj, hp_mem, hp_not⟩ := hreader
    let src : (Fin n → Bool) → List Bool := fun x => List.ofFn (Function.update x p false)
    let tgt : (Fin n → Bool) → List Bool := fun x => List.ofFn x
    have hsrc_len : ∀ x, (src x).length = n := fun x => by simp [src]
    have htgt_len : ∀ x, (tgt x).length = n := fun x => by simp [tgt]
    have hval_j : (∃ c, ∀ x, (run C.gates (src x)).getD (n + j) false = c) ∨
        ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false := by
      have hg := hC _ (List.getElem_mem hj)
      have hop : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hg.1
      have hrg : ∀ x, (run C.gates (src x)).getD (n + j) false =
          C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + j then (run C.gates (src x)).getD i false else false) := by
        intro x
        have := run_gate C.gates (src x) j hj
        rw [hsrc_len x] at this
        exact this
      have hp_val : ∀ x, (if p.val < n + j then (run C.gates (src x)).getD p.val false else false) = false := by
        intro x
        have hp_lt : p.val < n + j := by have := p.isLt; omega
        rw [if_pos hp_lt, run_input _ _ _ (by rw [hsrc_len]; exact p.isLt)]
        simp [src, List.getD_eq_getElem?_getD, p.isLt]
      rcases elim C.gates[j].op C.gates[j].inputs p.val false (n + j)
          (fun x i => if i < n + j then (run C.gates (src x)).getD i false else false)
          (fun x i => (run C.gates (src x)).getD i false)
          hop hg.2 hp_not hp_mem hp_val (fun x i hi => by rw [if_pos hi]) (fun x i hi => by rw [if_neg (by omega)]) with ⟨c, hc⟩ | ⟨w, hw, hwv⟩
      · exact Or.inl ⟨c, fun x => by rw [hrg x]; exact hc x⟩
      · exact Or.inr ⟨w, hw, fun x => by rw [hrg x]; exact hwv x⟩
    have h0_src : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨
        ∃ t, t < n ∧ ∀ x, (src x).getD w false = (tgt x).getD t false := by
      intro w hw
      by_cases hwp : w = p.val
      · subst hwp
        refine Or.inl ⟨false, fun x => ?_⟩
        simp [src, List.getD_eq_getElem?_getD, p.isLt]
      · refine Or.inr ⟨w, hw, fun x => ?_⟩
        simp only [src, tgt, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
        exact Function.update_of_ne (fun he => hwp (congrArg Fin.val he)) _ _
    have hne_src : ¬∃ b, ∀ x, C.eval (src x) = b := by
      rintro ⟨b, hb⟩
      apply hy01
      rw [← hCev, ← hCev]
      exact (hb y0).trans (hb y1).symm
    obtain ⟨D, hD, hDsz, hDev⟩ := engine3 n n C src tgt hsrc_len htgt_len {j} hC h0_src hne_src (by
      intro j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      exact ⟨hj, hval_j⟩)
    rw [Finset.card_singleton] at hDsz
    have hk1 : 1 ≤ k := by omega
    refine ⟨hk1, D, hD, by omega, fun x => ?_⟩
    rw [hDev x, hCev]
  have hAddOr : ∀ (n : ℕ) (h : (Fin n → Bool) → Bool) (t : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n h t → ∀ p : Fin n,
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => h x || x p) (t + 1) := by
    intro n h t hht p
    obtain ⟨C, hC, hCsz, hCev⟩ := hht
    by_cases hout : C.output < n + C.gates.length
    · refine ⟨⟨C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, p.val]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hC g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨by simp, by simp⟩
      · change (C.gates ++ [_]).length ≤ t + 1
        simp only [List.length_append, List.length_singleton]
        change C.gates.length ≤ t at hCsz
        omega
      · intro x
        change (run (C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, p.val]⟩]) (List.ofFn x)).getD (n + C.gates.length) false = (h x || x p)
        have hlen : n + C.gates.length = (run C.gates (List.ofFn x)).length := by rw [run_length, List.length_ofFn]
        rw [run_snoc, hlen, getD_at]
        simp only [andEval, orEval, notEval_nil, notEval_cons, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
        have he1 : (run C.gates (List.ofFn x)).getD C.output false = h x := hCev x
        have he2 : (run C.gates (List.ofFn x)).getD p.val false = x p := by
          rw [run_input _ _ _ (by simp [p.isLt])]
          simp [List.getD_eq_getElem?_getD, p.isLt]
        rw [he1, he2]
    · refine ⟨⟨[], p.val⟩, ?_, ?_, fun x => ?_⟩
      · intro g hg; cases hg
      · change 0 ≤ t + 1; omega
      · have hfalse : h x = false := by
          rw [← hCev x]
          change (run C.gates (List.ofFn x)).getD C.output false = false
          rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
        dsimp only
        rw [hfalse, Bool.false_or]
        change (List.ofFn x).getD p.val false = x p
        simp [List.getD_eq_getElem?_getD, p.isLt]
  have hRewire : ∀ (n m : ℕ) (r : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (k : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n h k →
      PEqualNP.MetaComplexity.HasCircuitSize m (fun x => h (fun i => x (r i))) k := by
    intro n m r h k hk
    obtain ⟨C, hC, hCsz, hCev⟩ := hk
    let mapW : ℕ → ℕ := fun w => if hw : w < n then (r ⟨w, hw⟩).val else m + (w - n)
    let gs' : List PEqualNP.CircuitLowerBounds.Gate := C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩
    have hsim : ∀ (x : Fin m → Bool) (t : ℕ), t ≤ C.gates.length →
        ∀ w : ℕ, (if w < n + t then (run C.gates (List.ofFn (fun i => x (r i)))).getD w false else false) =
          (if mapW w < m + t then (run gs' (List.ofFn x)).getD (mapW w) false else false) := by
      intro x t
      induction t with
      | zero =>
        intro _ w
        simp only [Nat.add_zero]
        by_cases hw : w < n
        · have hmw : mapW w < m := by simp only [mapW, dif_pos hw]; exact (r ⟨w, hw⟩).isLt
          rw [if_pos hw, if_pos hmw, run_input _ _ _ (by simp [hw]), run_input _ _ _ (by simp [hmw])]
          simp only [mapW, dif_pos hw, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, (r ⟨w, hw⟩).isLt, ↓reduceDIte, Option.getD_some]
        · have hmw : ¬ mapW w < m := by simp only [mapW, dif_neg hw]; omega
          rw [if_neg hw, if_neg hmw]
      | succ t ih =>
        intro ht w
        by_cases hlt : w < n + t
        · have hmw : mapW w < m + t := by
            dsimp only [mapW]
            split_ifs with hw
            · have := (r ⟨w, hw⟩).isLt; omega
            · omega
          have := ih (by omega) w
          rw [if_pos hlt, if_pos hmw] at this
          rw [if_pos (by omega), if_pos (by omega)]
          exact this
        · by_cases heq : w = n + t
          · subst heq
            have hwn : ¬ n + t < n := by omega
            have hmw_eq : mapW (n + t) = m + t := by simp only [mapW, dif_neg hwn]; omega
            rw [if_pos (by omega), hmw_eq, if_pos (by omega)]
            have ht' : t < C.gates.length := by omega
            have ht'' : t < gs'.length := by simp [gs', ht']
            have rg1 := run_gate C.gates (List.ofFn (fun i => x (r i))) t ht'
            have rg2 := run_gate gs' (List.ofFn x) t ht''
            simp only [List.length_ofFn] at rg1 rg2
            rw [rg1, rg2]
            have hget : gs'[t] = ⟨C.gates[t].op, C.gates[t].inputs.map mapW⟩ := by simp [gs']
            rw [hget, List.map_map]
            congr 1
            refine List.map_congr_left fun i _ => ?_
            exact ih (by omega) i
          · have hmw : ¬ mapW w < m + (t + 1) := by
              dsimp only [mapW]
              split_ifs with hw
              · omega
              · omega
            rw [if_neg (by omega), if_neg hmw]
    refine ⟨⟨gs', mapW C.output⟩, ?_, ?_, fun x => ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact ⟨(hC g0 hg0).1, by rw [List.length_map]; exact (hC g0 hg0).2⟩
    · change gs'.length ≤ k
      change C.gates.length ≤ k at hCsz
      simpa [gs'] using hCsz
    · dsimp only
      rw [← hCev (fun i => x (r i))]
      have hfinal := hsim x C.gates.length le_rfl C.output
      have h1 : (run C.gates (List.ofFn (fun i => x (r i)))).getD C.output false =
          if C.output < n + C.gates.length then (run C.gates (List.ofFn (fun i => x (r i)))).getD C.output false else false := by
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
      have h2 : (run gs' (List.ofFn x)).getD (mapW C.output) false =
          if mapW C.output < m + C.gates.length then (run gs' (List.ofFn x)).getD (mapW C.output) false else false := by
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; simp [gs']; omega)
      change (run gs' (List.ofFn x)).getD (mapW C.output) false =
        (run C.gates (List.ofFn (fun i => x (r i)))).getD C.output false
      rw [h1, h2, hfinal]
  have hOrChain : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List ℕ),
      ws ≠ [] → (∀ w ∈ ws, w < n + gs.length) →
      ∃ (e : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
        e.length + 1 = ws.length ∧ (∀ g ∈ e, fok g) ∧ out < n + gs.length + e.length ∧
        ∀ x : Fin n → Bool, (run (gs ++ e) (List.ofFn x)).getD out false =
          ws.any (fun w => (run gs (List.ofFn x)).getD w false) := by
    intro n gs ws
    induction ws with
    | nil => intro h; exact absurd rfl h
    | cons w rest ih =>
      intro _ hbd
      rcases rest with _ | ⟨u, rest'⟩
      · refine ⟨[], w, by simp, by simp, ?_, fun x => ?_⟩
        · simpa using hbd w (by simp)
        · simp
      · obtain ⟨e, out, helen, heok, hout, hev⟩ := ih (by simp) (fun z hz => hbd z (List.mem_cons_of_mem _ hz))
        let gnew : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [w, out]⟩
        refine ⟨e ++ [gnew], n + gs.length + e.length, ?_, ?_, ?_, fun x => ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil] at helen ⊢; omega
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact heok g hg
          · simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp [gnew], by simp [gnew]⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rw [← List.append_assoc, run_snoc]
          have hlen : n + gs.length + e.length = (run (gs ++ e) (List.ofFn x)).length := by
            rw [run_length, List.length_ofFn, List.length_append]; omega
          rw [hlen, getD_at]
          simp only [gnew, andEval, orEval, notEval_nil, notEval_cons, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
          rw [run_prefix gs e (List.ofFn x) w (by rw [List.length_ofFn]; exact hbd w (by simp)), hev x]
          simp [List.any_cons]
  have hStarCover : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset (Fin n)),
      (∀ i j, H.Adj i j → i ∈ T ∨ j ∈ T) →
      (∀ i ∈ T, ∀ j ∈ T, ¬H.Adj i j) →
      (∃ i j, H.Adj i j) →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => decide (∃ i j, H.Adj i j ∧ x i = true ∧ x j = true))
        (H.edgeFinset.card + T.card - 1) := by
    intro n H T hcov hind hedge
    have hBuildStars : ∀ (L : List (Fin n)), (∀ t ∈ L, (H.neighborFinset t).Nonempty) →
        ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (outs : List ℕ),
          outs.length = L.length ∧
          gs.length = (L.map fun t => (H.neighborFinset t).card).sum ∧
          (∀ g ∈ gs, fok g) ∧
          (∀ w ∈ outs, w < n + gs.length) ∧
          ∀ x : Fin n → Bool, outs.any (fun w => (run gs (List.ofFn x)).getD w false) =
            decide (∃ t ∈ L, x t = true ∧ ∃ u : Fin n, H.Adj t u ∧ x u = true) := by
      intro L
      induction L with
      | nil =>
        intro _
        refine ⟨[], [], rfl, rfl, by simp, by simp, fun x => by simp⟩
      | cons t rest ih =>
        intro hne
        obtain ⟨gs, outs, holen, hgslen, hgsok, houtsbd, houtsev⟩ := ih (fun z hz => hne z (List.mem_cons_of_mem _ hz))
        let nbs : List (Fin n) := (H.neighborFinset t).toList
        have hnbs_ne : nbs ≠ [] := by
          intro hempty
          obtain ⟨u, hu⟩ := hne t (by simp)
          have hmem : u ∈ nbs := Finset.mem_toList.2 hu
          rw [hempty] at hmem; cases hmem
        let ws : List ℕ := nbs.map Fin.val
        have hws_ne : ws ≠ [] := by simp [ws, hnbs_ne]
        have hws_len : ws.length = (H.neighborFinset t).card := by simp [ws, nbs]
        obtain ⟨e1, out1, he1len, he1ok, hout1bd, he1ev⟩ := hOrChain n gs ws hws_ne (by
          intro w hw
          obtain ⟨u, _, rfl⟩ := List.mem_map.1 hw
          have := u.isLt; omega)
        let gand : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t.val, out1]⟩
        let gs' := gs ++ (e1 ++ [gand])
        let out_t := n + gs.length + e1.length
        refine ⟨gs', out_t :: outs, by simp [holen], ?_, ?_, ?_, fun x => ?_⟩
        · simp only [gs', List.length_append, List.length_singleton, List.map_cons, List.sum_cons]
          omega
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact hgsok g hg
          · rcases List.mem_append.1 hg with hg | hg
            · exact he1ok g hg
            · simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp [gand], by simp [gand]⟩
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · simp only [gs', out_t, List.length_append, List.length_singleton]; omega
          · have := houtsbd w hw
            simp only [gs', List.length_append, List.length_singleton]; omega
        · simp only [List.any_cons]
          have hrest : outs.any (fun w => (run gs' (List.ofFn x)).getD w false) =
              outs.any (fun w => (run gs (List.ofFn x)).getD w false) := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true]
            refine exists_congr fun w => and_congr_right fun hw => ?_
            rw [run_prefix gs (e1 ++ [gand]) (List.ofFn x) w (by rw [List.length_ofFn]; exact houtsbd w hw)]
          have hcur : (run gs' (List.ofFn x)).getD out_t false =
              (x t && decide (∃ u : Fin n, H.Adj t u ∧ x u = true)) := by
            have hassoc : gs' = (gs ++ e1) ++ [gand] := by simp [gs', List.append_assoc]
            rw [hassoc, run_snoc]
            have hlen : out_t = (run (gs ++ e1) (List.ofFn x)).length := by
              rw [run_length, List.length_ofFn, List.length_append]; omega
            rw [hlen, getD_at]
            simp only [gand, andEval, orEval, notEval_nil, notEval_cons, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
            have hxt : (run (gs ++ e1) (List.ofFn x)).getD t.val false = x t := by
              rw [run_input _ _ _ (by simp [t.isLt])]
              simp [List.getD_eq_getElem?_getD, t.isLt]
            rw [hxt, he1ev x]
            congr 1
            apply Bool.eq_iff_iff.mpr
            simp only [ws, nbs, List.any_eq_true, List.mem_map, decide_eq_true_eq]
            constructor
            · rintro ⟨w, ⟨u, hu, rfl⟩, hxu⟩
              rw [Finset.mem_toList, H.mem_neighborFinset] at hu
              rw [run_input _ _ _ (by simp [u.isLt])] at hxu
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt, ↓reduceDIte, Option.getD_some] at hxu
              exact ⟨u, hu, hxu⟩
            · rintro ⟨u, hu, hxu⟩
              refine ⟨u.val, ⟨u, Finset.mem_toList.2 ((H.mem_neighborFinset t u).2 hu), rfl⟩, ?_⟩
              rw [run_input _ _ _ (by simp [u.isLt])]
              simp [List.getD_eq_getElem?_getD, u.isLt, hxu]
          rw [hcur, hrest, houtsev x]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
          constructor
          · rintro (⟨hxt, u, hu, hxu⟩ | ⟨z, hz, hxz, u, hu, hxu⟩)
            · exact ⟨t, Or.inl rfl, hxt, u, hu, hxu⟩
            · exact ⟨z, Or.inr hz, hxz, u, hu, hxu⟩
          · rintro ⟨z, rfl | hz, hxz, u, hu, hxu⟩
            · exact Or.inl ⟨hxz, u, hu, hxu⟩
            · exact Or.inr ⟨z, hz, hxz, u, hu, hxu⟩
    let T' : Finset (Fin n) := T.filter fun t => (H.neighborFinset t).Nonempty
    have hT'ne : T'.Nonempty := by
      obtain ⟨i, j, hij⟩ := hedge
      rcases hcov i j hij with hi | hj
      · exact ⟨i, Finset.mem_filter.2 ⟨hi, ⟨j, (H.mem_neighborFinset i j).2 hij⟩⟩⟩
      · exact ⟨j, Finset.mem_filter.2 ⟨hj, ⟨i, (H.mem_neighborFinset j i).2 hij.symm⟩⟩⟩
    let L : List (Fin n) := T'.toList
    have hLne : L ≠ [] := by
      intro h
      obtain ⟨t, ht⟩ := hT'ne
      have hmem : t ∈ L := Finset.mem_toList.2 ht
      rw [h] at hmem; cases hmem
    obtain ⟨gs, outs, holen, hgslen, hgsok, houtsbd, houtsev⟩ := hBuildStars L (fun t ht => (Finset.mem_filter.1 (Finset.mem_toList.1 ht)).2)
    have houts_ne : outs ≠ [] := by
      intro h; rw [h] at holen; exact hLne (List.eq_nil_of_length_eq_zero holen.symm)
    obtain ⟨e2, out2, he2len, he2ok, _, he2ev⟩ := hOrChain n gs outs houts_ne houtsbd
    have hsum_le : (L.map fun t => (H.neighborFinset t).card).sum ≤ H.edgeFinset.card := by
      have hsum_eq : (L.map fun t => (H.neighborFinset t).card).sum = ∑ t ∈ T', (H.neighborFinset t).card := by
        simpa [L] using (Finset.sum_toList T' (fun t => (H.neighborFinset t).card)).symm
      rw [hsum_eq]
      have hdisj : Set.PairwiseDisjoint (T' : Set (Fin n)) (fun t => (H.neighborFinset t).image fun u => s(t, u)) := by
        intro t1 ht1 t2 ht2 hne
        exact Finset.disjoint_left.2 fun e he1 he2 => by
          obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.1 he1
          obtain ⟨u2, hu2, heq⟩ := Finset.mem_image.1 he2
          have ht1T : t1 ∈ T := (Finset.mem_filter.1 ht1).1
          have ht2T : t2 ∈ T := (Finset.mem_filter.1 ht2).1
          have hadj1 : H.Adj t1 u1 := (H.mem_neighborFinset t1 u1).1 hu1
          have hu1nT : u1 ∉ T := fun h => hind t1 ht1T u1 h hadj1
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
          · exact hne rfl
          · exact hu1nT ht2T
      have hsub : T'.biUnion (fun t => (H.neighborFinset t).image fun u => s(t, u)) ⊆ H.edgeFinset := by
        intro e he
        obtain ⟨t, _, he'⟩ := Finset.mem_biUnion.1 he
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he'
        exact SimpleGraph.mem_edgeFinset.2 ((H.mem_neighborFinset t u).1 hu)
      calc
        ∑ t ∈ T', (H.neighborFinset t).card
            = ∑ t ∈ T', ((H.neighborFinset t).image fun u => s(t, u)).card := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Finset.card_image_of_injective]
              intro u1 u2 heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        _ = (T'.biUnion fun t => (H.neighborFinset t).image fun u => s(t, u)).card := (Finset.card_biUnion hdisj).symm
        _ ≤ H.edgeFinset.card := Finset.card_le_card hsub
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hLlen : L.length = T'.card := Finset.length_toList T'
    refine ⟨⟨gs ++ e2, out2⟩, ?_, ?_, fun x => ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ⟨by simpa using (hgsok g hg).1, (hgsok g hg).2⟩
      · exact ⟨by simpa using (he2ok g hg).1, (he2ok g hg).2⟩
    · change (gs ++ e2).length ≤ H.edgeFinset.card + T.card - 1
      rw [List.length_append]
      omega
    · change (run (gs ++ e2) (List.ofFn x)).getD out2 false = _
      rw [he2ev x, houtsev x]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨t, _, hxt, u, hu, hxu⟩
        exact ⟨t, u, hu, hxt, hxu⟩
      · rintro ⟨i, j, hij, hxi, hxj⟩
        rcases hcov i j hij with hi | hj
        · exact ⟨i, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨hi, ⟨j, (H.mem_neighborFinset i j).2 hij⟩⟩), hxi, j, hij, hxj⟩
        · exact ⟨j, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨hj, ⟨i, (H.mem_neighborFinset j i).2 hij.symm⟩⟩), hxj, i, hij.symm, hxi⟩
  intro n G A f hcolor hdeg hgirth hisol hedge hspec s hsize
  let E : (Fin n → Bool) → Bool := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  let bits : Finset (Fin n) → (Fin n → Bool) → Bool := fun T x => decide (∃ a ∈ T, x a = true)
  let F : Finset (Fin n) → (Fin n → Bool) → Bool := fun T x => E x || bits T x
  have eqF : f = F A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [F, E, bits, Bool.or_eq_true, decide_eq_true_eq]
    rw [or_comm]
    exact hspec x
  have bitsIns : ∀ (T : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool),
      bits (insert p T) x = (bits T x || x p) := by
    intro T p x
    apply Bool.eq_iff_iff.mpr
    simp only [bits, Bool.or_eq_true, decide_eq_true_eq]
    rw [Finset.exists_mem_insert]
    exact or_comm
  have insertF : ∀ (T : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool),
      F (insert p T) x = (F T x || x p) := by
    intro T p x
    simp only [F, bitsIns, Bool.or_assoc]
  have unchanged : ∀ (T : Finset (Fin n)) (p : Fin n), p ∈ A → p ∉ T →
      ∀ (x : Fin n → Bool) (b : Bool), F T (Function.update x p b) = F T x := by
    intro T p hp outside x b
    have sep : ∀ {i j : Fin n}, G.Adj i j → i ≠ p ∧ j ≠ p := fun h =>
      ⟨fun e => hisol _ _ h (e ▸ hp), fun e => hisol _ _ h.symm (e ▸ hp)⟩
    apply Bool.eq_iff_iff.mpr
    simp only [F, E, bits, Bool.or_eq_true, decide_eq_true_eq]
    apply or_congr
    · apply exists_congr; intro i
      apply exists_congr; intro j
      apply and_congr_right; intro adj
      rw [Function.update_of_ne (sep adj).1, Function.update_of_ne (sep adj).2]
    · apply exists_congr; intro i
      apply and_congr_right; intro mem
      rw [Function.update_of_ne (show i ≠ p from fun he => outside (he ▸ mem))]
  have hzero : ∀ T : Finset (Fin n), F T (fun _ => false) = false := fun T => by simp [F, E, bits]
  have hone : ∀ T : Finset (Fin n), F T (fun _ => true) = true := fun T => by simp [F, E, hedge]
  have hStripAll : ∀ T : Finset (Fin n), T ⊆ A → ∀ k, PEqualNP.MetaComplexity.HasCircuitSize n (F T) k →
      T.card ≤ k ∧ PEqualNP.MetaComplexity.HasCircuitSize n E (k - T.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ k hk
      have nilF : F ∅ = E := by funext x; simp [F, bits]
      simpa [nilF] using hk
    | @insert p T outside ih =>
      intro subset k hk
      have hp := subset (Finset.mem_insert_self p T)
      have hT : T ⊆ A := fun i hi => subset (Finset.mem_insert_of_mem hi)
      have off : ∀ x : Fin n → Bool, F (insert p T) (Function.update x p false) = F T x := by
        intro x; rw [insertF, unchanged _ _ hp outside, Function.update_self, Bool.or_false]
      have on : ∀ x : Fin n → Bool, F (insert p T) (Function.update x p true) = true := by
        intro x; rw [insertF, Function.update_self, Bool.or_true]
      obtain ⟨pos, hrest⟩ := hStripOne n k (F (insert p T)) p hk
        ⟨fun _ => false, by rw [off, on, hzero]; decide⟩
        ⟨fun _ => false, fun _ => true, by rw [off, off, hzero, hone]; decide⟩
      rw [show (fun x => F (insert p T) (Function.update x p false)) = F T from funext off] at hrest
      obtain ⟨le, core⟩ := ih hT (k - 1) hrest
      rw [Finset.card_insert_of_notMem outside]
      exact ⟨by omega, by convert core using 1; omega⟩
  have hAddAll : ∀ (T : Finset (Fin n)) (g : (Fin n → Bool) → Bool) (t : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n g t →
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => g x || bits T x) (t + T.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro g t hg
      simpa [bits] using hg
    | @insert p T outside ih =>
      intro g t hg
      rw [Finset.card_insert_of_notMem outside, ← Nat.add_assoc]
      have hstep := hAddOr n (fun x => g x || bits T x) (t + T.card) (ih g t hg) p
      convert hstep using 1
      funext x
      rw [bitsIns, Bool.or_assoc]
  obtain ⟨hAs, hcore⟩ := hStripAll A (Finset.Subset.refl A) s (eqF ▸ hsize)
  let k := s - A.card
  let active : Finset (Fin n) := Finset.univ \ A
  let m := active.card
  have hpair_core : ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬G.Adj u v ∧
      ∃ t : ℕ, t + 8 ≤ k ∧ PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => E (Function.update (Function.update x u false) v false)) t := by
    by_cases hsmall : k + 1 < 2 * m
    · obtain ⟨a0, b0, hab0⟩ := hedge
      let U := {v : Fin n // v ∉ A}
      have hcardU : Fintype.card U = m := by
        dsimp only [m, active, U]
        rw [Fintype.card_subtype]
        congr 1
        ext v; simp
      let e0 : Fin m ≃ U := (Equiv.cast (congrArg Fin hcardU.symm)).trans (Fintype.equivFin U).symm
      let emb : Fin m → Fin n := fun v => (e0 v).val
      have hinj : Function.Injective emb := fun _ _ h => e0.injective (Subtype.ext h)
      have inU : ∀ v : Fin m, emb v ∉ A := fun v => (e0 v).property
      let back : Fin n → Fin m := fun i => if h : i ∉ A then e0.symm ⟨i, h⟩ else e0.symm ⟨a0, hisol a0 b0 hab0⟩
      have sec_back : ∀ v : Fin m, back (emb v) = v := by
        intro v
        dsimp only [back]
        rw [dif_pos (inU v)]
        exact e0.symm_apply_apply v
      have sec_emb : ∀ i : Fin n, i ∉ A → emb (back i) = i := by
        intro i hi
        dsimp only [emb, back]
        rw [dif_pos hi]
        exact congrArg Subtype.val (e0.apply_symm_apply ⟨i, hi⟩)
      let H0 : SimpleGraph (Fin m) := G.comap emb
      have hH0col : H0.Colorable 2 := by
        obtain ⟨col⟩ := hcolor
        exact ⟨⟨fun v => col (emb v), fun h => col.valid h⟩⟩
      have hH0deg : ∀ v : Fin m, (H0.neighborSet v).ncard = 3 := by
        intro v
        rw [← hdeg (emb v) (inU v)]
        refine Set.ncard_congr (fun q _ => emb q) (fun _ h => h) (fun _ _ _ _ h => hinj h) ?_
        intro z hz
        change G.Adj (emb v) z at hz
        have hznA : z ∉ A := hisol z (emb v) hz.symm
        refine ⟨back z, ?_, sec_emb z hznA⟩
        change G.Adj (emb v) (emb (back z))
        rw [sec_emb z hznA]
        exact hz
      have hH0girth : ∀ (v : Fin m) (p : H0.Walk v v), p.IsCycle → 7 ≤ p.length := by
        intro v p hp
        let hom : H0 →g G := ⟨emb, fun h => h⟩
        have hcyc : (p.map hom).IsCycle := hp.map hinj
        have hlen := hgirth (emb v) (p.map hom) hcyc
        simpa using hlen
      have hH0edge : ∃ u v : Fin m, H0.Adj u v := by
        refine ⟨back a0, back b0, ?_⟩
        change G.Adj (emb (back a0)) (emb (back b0))
        rw [sec_emb a0 (hisol a0 b0 hab0), sec_emb b0 (hisol b0 a0 hab0.symm)]
        exact hab0
      have hH0size : PEqualNP.MetaComplexity.HasCircuitSize m (fun x => E (fun i => x (back i))) k :=
        hRewire n m back E k hcore
      obtain ⟨C0, hC0fin, hC0sz, hC0ev⟩ := hH0size
      have hC0spec : ∀ x : Fin m → Bool, C0.eval (List.ofFn x) = true ↔
          ∃ u v : Fin m, H0.Adj u v ∧ x u = true ∧ x v = true := by
        intro x
        rw [hC0ev x]
        simp only [E, decide_eq_true_eq]
        constructor
        · rintro ⟨i, j, hij, hxi, hxj⟩
          refine ⟨back i, back j, ?_, hxi, hxj⟩
          change G.Adj (emb (back i)) (emb (back j))
          rw [sec_emb i (hisol i j hij), sec_emb j (hisol j i hij.symm)]
          exact hij
        · rintro ⟨u, v, huv, hxu, hxv⟩
          exact ⟨emb u, emb v, huv, by rw [sec_back u]; exact hxu, by rw [sec_back v]; exact hxv⟩
      have hgot : ∃ u v : Fin m, u ≠ v ∧ ¬H0.Adj u v ∧ ∃ t : ℕ, t + 8 ≤ C0.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize m
            (fun x : Fin m → Bool => C0.eval (List.ofFn (Function.update (Function.update x u false) v false))) t := by
        by_cases hnot : ∃ g ∈ C0.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
        · exact hWithNot m H0 hH0col hH0deg hH0girth hH0edge C0 hC0fin hnot (by omega) hC0spec
        · have hC0mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
            intro g hg
            refine ⟨?_, (hC0fin g hg).2⟩
            have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
                g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using (hC0fin g hg).1
            rcases hop with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd ⟨g, hg, h⟩ hnot
          exact hMono m H0 hH0col hH0deg hH0girth hH0edge C0 hC0mono (by omega) hC0spec
      obtain ⟨u0, v0, huv0ne, huv0nadj, t, ht8, hHt⟩ := hgot
      have hback_circ : PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x => C0.eval (List.ofFn (Function.update (Function.update (fun i => x (emb i)) u0 false) v0 false))) t :=
        hRewire m n emb _ t hHt
      refine ⟨emb u0, emb v0, inU u0, inU v0, fun he => huv0ne (hinj he), huv0nadj, t, by omega, ?_⟩
      convert hback_circ using 1
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [hC0spec]
      simp only [E, decide_eq_true_eq]
      constructor
      · rintro ⟨i, j, hij, hxi, hxj⟩
        have hinA : i ∉ A := hisol i j hij
        have hjnA : j ∉ A := hisol j i hij.symm
        refine ⟨back i, back j, ?_, ?_, ?_⟩
        · change G.Adj (emb (back i)) (emb (back j))
          rw [sec_emb i hinA, sec_emb j hjnA]; exact hij
        · by_cases h1 : back i = v0
          · have : i = emb v0 := by rw [← sec_emb i hinA, h1]
            subst this; simp at hxi
          · rw [Function.update_of_ne h1]
            by_cases h2 : back i = u0
            · have : i = emb u0 := by rw [← sec_emb i hinA, h2]
              subst this
              have hne' : emb u0 ≠ emb v0 := fun he => huv0ne (hinj he)
              rw [Function.update_of_ne hne', Function.update_self] at hxi; cases hxi
            · rw [Function.update_of_ne h2, sec_emb i hinA]
              have hne1 : i ≠ emb v0 := fun he => h1 (by rw [he, sec_back v0])
              have hne2 : i ≠ emb u0 := fun he => h2 (by rw [he, sec_back u0])
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2] at hxi
              exact hxi
        · by_cases h1 : back j = v0
          · have : j = emb v0 := by rw [← sec_emb j hjnA, h1]
            subst this; simp at hxj
          · rw [Function.update_of_ne h1]
            by_cases h2 : back j = u0
            · have : j = emb u0 := by rw [← sec_emb j hjnA, h2]
              subst this
              have hne' : emb u0 ≠ emb v0 := fun he => huv0ne (hinj he)
              rw [Function.update_of_ne hne', Function.update_self] at hxj; cases hxj
            · rw [Function.update_of_ne h2, sec_emb j hjnA]
              have hne1 : j ≠ emb v0 := fun he => h1 (by rw [he, sec_back v0])
              have hne2 : j ≠ emb u0 := fun he => h2 (by rw [he, sec_back u0])
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2] at hxj
              exact hxj
      · rintro ⟨a, b, hab, hxa, hxb⟩
        refine ⟨emb a, emb b, hab, ?_, ?_⟩
        · by_cases h1 : a = v0
          · subst h1; simp at hxa
          · rw [Function.update_of_ne (fun he => h1 (hinj he))]
            by_cases h2 : a = u0
            · subst h2; rw [Function.update_of_ne h1, Function.update_self] at hxa; cases hxa
            · rw [Function.update_of_ne (fun he => h2 (hinj he))]
              rw [Function.update_of_ne h1, Function.update_of_ne h2] at hxa
              exact hxa
        · by_cases h1 : b = v0
          · subst h1; simp at hxb
          · rw [Function.update_of_ne (fun he => h1 (hinj he))]
            by_cases h2 : b = u0
            · subst h2; rw [Function.update_of_ne h1, Function.update_self] at hxb; cases hxb
            · rw [Function.update_of_ne (fun he => h2 (hinj he))]
              rw [Function.update_of_ne h1, Function.update_of_ne h2] at hxb
              exact hxb
    · obtain ⟨col⟩ := hcolor
      let side : Fin 2 → Finset (Fin n) := fun c => active.filter fun i => col i = c
      have memSide : ∀ (i : Fin n) (c : Fin 2), i ∈ side c ↔ i ∉ A ∧ col i = c := by
        intro i c; simp [side, active]
      have hpart : (side 0).card + (side 1).card = m := by
        have eq1 : active.filter (fun i => col i ≠ 0) = side 1 := by
          ext i
          simp only [side, Finset.mem_filter]
          have hc : col i = 0 ∨ col i = 1 := by
            have := (col i).isLt
            rcases (show (col i).val = 0 ∨ (col i).val = 1 by omega) with h0 | h1
            · exact Or.inl (Fin.ext h0)
            · exact Or.inr (Fin.ext h1)
          rcases hc with hc | hc <;> simp [hc]
        rw [← eq1]
        exact Finset.card_filter_add_card_filter_not (s := active) (fun i => col i = 0)
      let c0 : Fin 2 := if (side 0).card ≤ (side 1).card then 0 else 1
      let T : Finset (Fin n) := side c0
      have hTle : 2 * T.card ≤ m := by dsimp only [T, c0]; split_ifs <;> omega
      have hindT : ∀ i ∈ T, ∀ j ∈ T, ¬G.Adj i j := fun i hi j hj hadj =>
        col.valid hadj (((memSide i c0).1 hi).2.trans ((memSide j c0).1 hj).2.symm)
      have hcovT : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T := by
        intro i j hij
        have hi := hisol i j hij
        have hj := hisol j i hij.symm
        have hdiff : (col i).val ≠ (col j).val := fun e => col.valid hij (Fin.ext e)
        have h1 := (col i).isLt; have h2 := (col j).isLt; have h3 := c0.isLt
        rcases (show (col i).val = c0.val ∨ (col j).val = c0.val by omega) with e | e
        · exact Or.inl ((memSide i c0).2 ⟨hi, Fin.ext e⟩)
        · exact Or.inr ((memSide j c0).2 ⟨hj, Fin.ext e⟩)
      have hdeg3 : ∀ z : Fin n, z ∉ A → G.degree z = 3 := by
        intro z hz; rw [← G.ncard_neighborSet]; exact hdeg z hz
      have hdeg0 : ∀ z : Fin n, z ∈ A → G.degree z = 0 := by
        intro z hz
        rw [SimpleGraph.degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        exact hisol z w ((G.mem_neighborFinset z w).1 hw) hz
      have hGedges : 2 * G.edgeFinset.card = 3 * m := by
        have hsum := G.sum_degrees_eq_twice_card_edges
        rw [← hsum]
        have hsplit : ∑ v : Fin n, G.degree v = (∑ v ∈ active, G.degree v) + (∑ v ∈ A, G.degree v) := by
          have hunion : active ∪ A = Finset.univ := by ext v; simp [active]
          have hdisj : Disjoint active A := Finset.sdiff_disjoint
          rw [← Finset.sum_union hdisj, hunion]
        rw [hsplit, Finset.sum_eq_zero (fun v hv => hdeg0 v hv), Nat.add_zero]
        rw [Finset.sum_congr rfl (fun v hv => hdeg3 v (by simpa [active] using hv)), Finset.sum_const, smul_eq_mul]
        dsimp only [m]; ring
      obtain ⟨i0, j0, hij0⟩ := hedge
      have houtT : ∃ b : Fin n, b ∉ T ∧ b ∉ A := by
        rcases hcovT i0 j0 hij0 with hi | hj
        · exact ⟨j0, fun hj => hindT i0 hi j0 hj hij0, hisol j0 i0 hij0.symm⟩
        · exact ⟨i0, fun hi => hindT i0 hi j0 hj hij0, hisol i0 j0 hij0⟩
      obtain ⟨b, hbT, hbA⟩ := houtT
      let N := G.neighborFinset b
      have hNcard : N.card = 3 := by rw [G.card_neighborFinset_eq_degree]; exact hdeg3 b hbA
      have hNsub : N ⊆ T := fun w hw => (hcovT b w ((G.mem_neighborFinset b w).1 hw)).resolve_left hbT
      obtain ⟨u, hu⟩ := Finset.card_pos.1 (show 0 < N.card by omega)
      have h1 := Finset.card_erase_add_one hu
      obtain ⟨v, hv⟩ := Finset.card_pos.1 (show 0 < (N.erase u).card by omega)
      have h2 := Finset.card_erase_add_one hv
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (show 0 < ((N.erase u).erase v).card by omega)
      have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
      have huv : u ≠ v := hvu.symm
      have huT : u ∈ T := hNsub hu
      have hvT : v ∈ T := hNsub (Finset.mem_of_mem_erase hv)
      have huA : u ∉ A := ((memSide u c0).1 huT).1
      have hvA : v ∉ A := ((memSide v c0).1 hvT).1
      have huv_nadj : ¬G.Adj u v := hindT u huT v hvT
      let K := G.deleteIncidenceSet u
      let H := K.deleteIncidenceSet v
      have hKnb : K.neighborSet v = G.neighborSet v := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, K, SimpleGraph.deleteIncidenceSet_adj]
        exact ⟨And.left, fun hvz => ⟨hvz, hvu, fun e => huv_nadj (e ▸ hvz.symm)⟩⟩
      have hKdeg : K.degree v = 3 := by
        rw [← K.ncard_neighborSet, hKnb, G.ncard_neighborSet]; exact hdeg3 v hvA
      have hKedges : K.edgeFinset.card = G.edgeFinset.card - 3 := by
        simpa [hdeg3 u huA] using G.card_edgeFinset_deleteIncidenceSet u
      have hHedges : H.edgeFinset.card = K.edgeFinset.card - 3 := by
        simpa [hKdeg] using K.card_edgeFinset_deleteIncidenceSet v
      have hbw : G.Adj b w := (G.mem_neighborFinset b w).1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
      have hbnu : b ≠ u := fun e => hbT (e.symm ▸ huT)
      have hbnv : b ≠ v := fun e => hbT (e.symm ▸ hvT)
      have hwnu : w ≠ u := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hw)).1
      have hwnv : w ≠ v := (Finset.mem_erase.1 hw).1
      have hHedge : ∃ a1 a2, H.Adj a1 a2 :=
        ⟨b, w, SimpleGraph.deleteIncidenceSet_adj.2 ⟨SimpleGraph.deleteIncidenceSet_adj.2 ⟨hbw, hbnu, hwnu⟩, hbnv, hwnv⟩⟩
      let T' : Finset (Fin n) := (T.erase u).erase v
      have hT'card : T'.card + 2 = T.card := by
        have he1 := Finset.card_erase_add_one huT
        have hv_in : v ∈ T.erase u := Finset.mem_erase.2 ⟨hvu, hvT⟩
        have he2 := Finset.card_erase_add_one hv_in
        dsimp only [T']
        omega
      have hHcov : ∀ a1 a2, H.Adj a1 a2 → a1 ∈ T' ∨ a2 ∈ T' := by
        intro a1 a2 h12
        obtain ⟨hK12, h1v, h2v⟩ := SimpleGraph.deleteIncidenceSet_adj.1 h12
        obtain ⟨hG12, h1u, h2u⟩ := SimpleGraph.deleteIncidenceSet_adj.1 hK12
        rcases hcovT a1 a2 hG12 with h1T | h2T
        · exact Or.inl (Finset.mem_erase.2 ⟨h1v, Finset.mem_erase.2 ⟨h1u, h1T⟩⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨h2v, Finset.mem_erase.2 ⟨h2u, h2T⟩⟩)
      have hHind : ∀ a1 ∈ T', ∀ a2 ∈ T', ¬H.Adj a1 a2 := by
        intro a1 h1 a2 h2 h12
        have hG12 := (SimpleGraph.deleteIncidenceSet_adj.1 (SimpleGraph.deleteIncidenceSet_adj.1 h12).1).1
        exact hindT a1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1))
          a2 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h2)) hG12
      have hHcirc := hStarCover n H T' hHcov hHind hHedge
      have hTcard_ge : 3 ≤ T.card := by
        have := Finset.card_le_card hNsub
        omega
      have hsz_bound : H.edgeFinset.card + T'.card - 1 + 8 ≤ k := by omega
      have hfeq : (fun x => E (Function.update (Function.update x u false) v false)) =
          (fun x => decide (∃ i j, H.Adj i j ∧ x i = true ∧ x j = true)) := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp only [E, decide_eq_true_eq]
        constructor
        · rintro ⟨a1, a2, h12, hx1, hx2⟩
          have h1v : a1 ≠ v := by intro he; subst he; simp at hx1
          have h2v : a2 ≠ v := by intro he; subst he; simp at hx2
          rw [Function.update_of_ne h1v] at hx1
          rw [Function.update_of_ne h2v] at hx2
          have h1u : a1 ≠ u := by intro he; subst he; simp at hx1
          have h2u : a2 ≠ u := by intro he; subst he; simp at hx2
          rw [Function.update_of_ne h1u] at hx1
          rw [Function.update_of_ne h2u] at hx2
          exact ⟨a1, a2, SimpleGraph.deleteIncidenceSet_adj.2 ⟨SimpleGraph.deleteIncidenceSet_adj.2 ⟨h12, h1u, h2u⟩, h1v, h2v⟩, hx1, hx2⟩
        · rintro ⟨a1, a2, h12, hx1, hx2⟩
          obtain ⟨hK12, h1v, h2v⟩ := SimpleGraph.deleteIncidenceSet_adj.1 h12
          obtain ⟨hG12, h1u, h2u⟩ := SimpleGraph.deleteIncidenceSet_adj.1 hK12
          exact ⟨a1, a2, hG12, by rw [Function.update_of_ne h1v, Function.update_of_ne h1u]; exact hx1,
            by rw [Function.update_of_ne h2v, Function.update_of_ne h2u]; exact hx2⟩
      refine ⟨u, v, huA, hvA, huv, huv_nadj, H.edgeFinset.card + T'.card - 1, hsz_bound, ?_⟩
      rw [hfeq]
      obtain ⟨C, hC, hCsz, hCev⟩ := hHcirc
      refine ⟨C, hC, ?_, fun x => (hCev x).trans (Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]))⟩
      convert hCsz using 2
      congr 1
      apply congrArg Finset.card
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
  obtain ⟨u, v, huA, hvA, huv, huv_nadj, t, ht8, hEt⟩ := hpair_core
  refine ⟨u, v, huA, hvA, huv, huv_nadj, t + A.card, by omega, ?_⟩
  have hfinal := hAddAll A (fun x => E (Function.update (Function.update x u false) v false)) t hEt
  convert hfinal using 1
  funext x
  rw [eqF]
  dsimp only [F]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [bits, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hxa⟩
    have hau : a ≠ u := fun e => huA (e ▸ ha)
    have hav : a ≠ v := fun e => hvA (e ▸ ha)
    rw [Function.update_of_ne hav, Function.update_of_ne hau] at hxa
    exact ⟨a, ha, hxa⟩
  · rintro ⟨a, ha, hxa⟩
    have hau : a ≠ u := fun e => huA (e ▸ ha)
    have hav : a ≠ v := fun e => hvA (e ▸ ha)
    exact ⟨a, ha, by rw [Function.update_of_ne hav, Function.update_of_ne hau]; exact hxa⟩
