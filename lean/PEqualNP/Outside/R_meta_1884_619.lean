import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1884_619
    (hNot0 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D →
      D.size ≤ (18 : ℕ) →
      (11 : ℕ) ≤ D.output →
      D.output < (11 : ℕ) + D.size →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))]) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (hNot1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ (18 : ℕ) →
      (11 : ℕ) ≤ D.output →
      D.output < (11 : ℕ) + D.size →
      (∃ j : Fin D.gates.length, (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ k : Fin D.gates.length, (D.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not → k = j) →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))]) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (hNotGe2 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ (18 : ℕ) →
      (11 : ℕ) ≤ D.output →
      D.output < (11 : ℕ) + D.size →
      (∃ j1 j2 : Fin D.gates.length, j1 ≠ j2 ∧
        (D.gates.get j1).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (D.gates.get j2).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))]) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have hp10_false : p10 (fun _ => false) = false := by decide +kernel
  have hp10_true : p10 (fun _ => true) = true := by decide +kernel
  have hp10_single : ∀ w : Fin 10, p10 (fun i => decide (i = w)) = false := by decide +kernel
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
      · exact keep r hr (by intro y _; simp [andEval])
      · exact keep r hr (by intro y _; simp [orEval])
    · have hr := hv r (by simp)
      have hs' := hv s (by simp)
      rcases hop with rfl | rfl
      · rcases r with b | t
        · cases b
          · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, rv])
          · exact keep s hs' (by intro y _; simp [andEval, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, rv])
            · exact keep (Sum.inr t) hr (by intro y _; simp [andEval, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩
              (by intro y _; simp [andEval, rv])
      · rcases r with b | t
        · cases b
          · exact keep s hs' (by intro y _; simp [orEval, rv])
          · exact keep (Sum.inl true) (by simp) (by intro y _; simp [orEval, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inr t) hr (by intro y _; simp [orEval, rv])
            · exact keep (Sum.inl true) (by simp) (by intro y _; simp [orEval, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩
              (by intro y _; simp [orEval, rv])
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
      · exact ⟨Sum.inl true, [], by simp, by simp, by simp, fun y _ => by simp [notEval_nil, rv]⟩
      · rcases r with c | t
        · exact ⟨Sum.inl (!c), [], by simp, by simp, by simp, fun y _ => by simp [notEval_cons, rv]⟩
        · refine ⟨Sum.inr (N + hs.length), [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [t]⟩], by simp, by simp [fok], by simp, fun y hy => ?_⟩
          have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
          dsimp only [rv, Sum.elim]
          rw [run_snoc, hlen, getD_at]
          simp [notEval_cons]
  have hNormalize : ∀ {X : Type} (n M : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (src tgt : X → List Bool), (∀ x, (src x).length = n) → (∀ x, (tgt x).length = M) →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false) →
      (¬∃ b, ∀ x, C.eval (src x) = b) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size ≤ C.size ∧ D.output < M + D.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
    intro X n M C src tgt hsrc htgt hC h0 hne
    have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
        (∀ g ∈ hs, fok g) ∧ hs.length ≤ k ∧
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
        have hg := hC _ (List.getElem_mem hk')
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
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg'
          rcases List.mem_append.1 hg' with hg' | hg'
          · exact h1 g hg'
          · exact e2 g hg'
        · rw [List.length_append]; omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := e3 t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]
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
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
    obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
    have hout : C.output < n + C.gates.length := by
      by_contra h
      refine hne ⟨false, fun x => ?_⟩
      change (run C.gates (src x)).getD C.output false = false
      rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
    have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
    rcases hm : m C.output with b | t
    · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
    · refine ⟨⟨hs, t⟩, ?_, h2, h3 C.output t hout hm, fun x => ?_⟩
      · intro g hg
        exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
      · have := hev x
        rw [hm] at this
        exact this.symm
  intro C σ f hfan hsz
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) ≠ p10 x
  by_contra hno
  have hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = p10 x := by
    intro x
    by_contra hdiff
    exact hno ⟨x, hdiff⟩
  let src : (Fin 10 → Bool) → List Bool := fun x => List.ofFn (x ∘ σ) ++ [f (x 0)]
  let tgt : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  have hsrc_len : ∀ x, (src x).length = 11 := fun x => by simp [src]
  have htgt_len : ∀ x, (tgt x).length = 11 := fun x => by simp [tgt]
  have h0 : ∀ w < 11, (∃ b, ∀ x, (src x).getD w false = b) ∨
      ∃ t, t < 11 ∧ ∀ x, (src x).getD w false = (tgt x).getD t false := by
    intro w hw
    by_cases hw10 : w < 10
    · refine Or.inr ⟨(σ ⟨w, hw10⟩).val, by have := (σ ⟨w, hw10⟩).isLt; omega, fun x => ?_⟩
      have h1 : (src x).getD w false = x (σ ⟨w, hw10⟩) := by
        dsimp only [src]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw10]), List.getElem?_ofFn]
        simp [hw10]
      have h2 : (tgt x).getD (σ ⟨w, hw10⟩).val false = x (σ ⟨w, hw10⟩) := by
        dsimp only [tgt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [(σ ⟨w, hw10⟩).isLt]), List.getElem?_ofFn]
        simp [(σ ⟨w, hw10⟩).isLt]
      rw [h1, h2]
    · have hwe : w = 10 := by omega
      subst hwe
      have hsrc10 : ∀ x, (src x).getD 10 false = f (x 0) := fun x => by
        simp [src, List.getD_eq_getElem?_getD]
      have htgt0 : ∀ x, (tgt x).getD 0 false = x 0 := fun x => by
        simp [tgt, List.getD_eq_getElem?_getD]
      have htgt10 : ∀ x, (tgt x).getD 10 false = !x 0 := fun x => by
        simp [tgt, List.getD_eq_getElem?_getD]
      cases hf0 : f false <;> cases hf1 : f true
      · refine Or.inl ⟨false, fun x => ?_⟩
        rw [hsrc10 x]; cases h : x 0 <;> simp [hf0, hf1]
      · refine Or.inr ⟨0, by omega, fun x => ?_⟩
        rw [hsrc10 x, htgt0 x]; cases h : x 0 <;> simp [hf0, hf1]
      · refine Or.inr ⟨10, by omega, fun x => ?_⟩
        rw [hsrc10 x, htgt10 x]; cases h : x 0 <;> simp [hf0, hf1]
      · refine Or.inl ⟨true, fun x => ?_⟩
        rw [hsrc10 x]; cases h : x 0 <;> simp [hf0, hf1]
  have hne : ¬∃ b, ∀ x, C.eval (src x) = b := by
    rintro ⟨b, hb⟩
    have h1 := (hb (fun _ => false)).symm.trans ((hcomp (fun _ => false)).trans hp10_false)
    have h2 := (hb (fun _ => true)).symm.trans ((hcomp (fun _ => true)).trans hp10_true)
    exact Bool.false_ne_true (h1.symm.trans h2)
  obtain ⟨D, hDfan, hDsz, hDout_lt, hDev⟩ := hNormalize 11 11 C src tgt hsrc_len htgt_len hfan h0 hne
  have hDp10 : ∀ x : Fin 10 → Bool, D.eval (tgt x) = p10 x := fun x => (hDev x).trans (hcomp x)
  have hDout_ge : 11 ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < 11 := by omega
    have hDwire : ∀ x : Fin 10 → Bool, p10 x = (tgt x).getD D.output false := by
      intro x
      rw [← hDp10 x]
      change (run D.gates (tgt x)).getD D.output false = (tgt x).getD D.output false
      exact run_input D.gates (tgt x) D.output (by rw [htgt_len]; exact hlt')
    by_cases h10 : D.output = 10
    · have hf := hDwire (fun _ => false)
      rw [hp10_false, h10] at hf
      simp [tgt, List.getD_eq_getElem?_getD] at hf
    · have hw : D.output < 10 := by omega
      let v : Fin 10 := ⟨D.output, hw⟩
      have hs := hDwire (fun i => decide (i = v))
      rw [hp10_single v] at hs
      have hval : (tgt (fun i => decide (i = v))).getD D.output false = true := by
        dsimp only [tgt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_ofFn]
        simp [hw, v]
      rw [hval] at hs
      exact Bool.false_ne_true hs
  have hDsz18 : D.size ≤ 18 := le_trans hDsz hsz
  by_cases hhasNot : ∃ j : Fin D.gates.length, (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨j, hj⟩ := hhasNot
    by_cases htwo : ∃ k : Fin D.gates.length, k ≠ j ∧ (D.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not
    · obtain ⟨k, hkj, hk⟩ := htwo
      obtain ⟨x, hx⟩ := hNotGe2 D hDfan hDsz18 hDout_ge hDout_lt ⟨k, j, hkj, hk, hj⟩
      exact hx (hDp10 x)
    · have huniq : ∀ k : Fin D.gates.length, (D.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not → k = j := by
        intro k hk
        by_contra hkj
        exact htwo ⟨k, hkj, hk⟩
      obtain ⟨x, hx⟩ := hNot1 D hDfan hDsz18 hDout_ge hDout_lt ⟨j, hj, huniq⟩
      exact hx (hDp10 x)
  · have hDmono : PEqualNP.MetaComplexity.Monotone2 D := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
      have hfg := hDfan _ hg
      have hop : D.gates[i].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          D.gates[i].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          D.gates[i].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hfg.1
      refine ⟨?_, hfg.2⟩
      rcases hop with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact False.elim (hhasNot ⟨⟨i, hi⟩, by simpa using h1⟩)
    obtain ⟨x, hx⟩ := hNot0 D hDmono hDsz18 hDout_ge hDout_lt
    exact hx (hDp10 x)
