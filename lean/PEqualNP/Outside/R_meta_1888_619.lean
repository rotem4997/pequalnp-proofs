import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1888_619
    (hHintUnused : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      D.size ≤ (18 : ℕ) →
      D.output = (10 : ℕ) + (D.size - (1 : ℕ)) →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (hHintUsedMono : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (11 : ℕ) D →
      D.size ≤ (18 : ℕ) →
      D.output = (11 : ℕ) + (D.size - (1 : ℕ)) →
      (∃ j : Fin D.gates.length, (10 : ℕ) ∈ (D.gates.get j).inputs) →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ))]) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (hHintUsedNot : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) D →
      D.size ≤ (18 : ℕ) →
      D.output = (11 : ℕ) + (D.size - (1 : ℕ)) →
      (∀ j : Fin D.gates.length,
        ((D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.length = (1 : ℕ)) ∧
        ((D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.length = (2 : ℕ))) →
      (∃ j : Fin D.gates.length, (10 : ℕ) ∈ (D.gates.get j).inputs) →
      (∃ j : Fin D.gates.length, (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin (10 : ℕ) → Bool,
        D.eval (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ))]) ≠
          (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
           x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
           x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
           x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
           x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
           x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
           x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
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
    intro gs g x; change (gs ++ [g]).foldl _ x = _; rw [List.foldl_append]; rfl
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
  have getD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t h; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  have getD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b; simp [List.getD_eq_getElem?_getD]
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := run_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1; exact h1
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
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
      · have hjj : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
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
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)
  have rv_ext : ∀ (hs e : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool) (r : Bool ⊕ ℕ),
      (∀ t, r = Sum.inr t → t < y.length + hs.length) →
      rv (run (hs ++ e) y) r = rv (run hs y) r := by
    intro hs e y r h
    rcases r with b | t
    · rfl
    · exact run_prefix hs e y t (h t rfl)
  have emit : ∀ (N : ℕ) (hs : List PEqualNP.CircuitLowerBounds.Gate) (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∀ (rs : List (Bool ⊕ ℕ)), rs.length ≤ 2 →
      (∀ r ∈ rs, ∀ t, r = Sum.inr t → t < N + hs.length) →
      ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g ∧ ∀ i ∈ g.inputs, i < N + hs.length) ∧
        (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro N hs op hop rs hl hv
    have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = Sum.inr t → t < N + hs.length) →
        (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g ∧ ∀ i ∈ g.inputs, i < N + hs.length) ∧
          (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
      intro r h1 h2
      exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
    have add : ∀ g : PEqualNP.CircuitLowerBounds.Gate, fok g → (∀ i ∈ g.inputs, i < N + hs.length) →
        (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g ∧ ∀ i ∈ g.inputs, i < N + hs.length) ∧
          (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
      intro g h1 hrb h2
      refine ⟨Sum.inr (N + hs.length), [g], by simp, ?_, ?_, fun y hy => ?_⟩
      · intro g' hg'; rw [List.mem_singleton] at hg'; subst hg'; exact ⟨h1, hrb⟩
      · intro t ht; cases ht; simp
      · have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
        dsimp only [rv, Sum.elim]
        rw [run_snoc, hlen, getD_at]
        exact h2 y hy
    rcases hop with rfl | rfl | rfl
    · rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
      · exact keep (Sum.inl true) (by simp) (by intro y _; rfl)
      · exact keep r (hv r (by simp)) (by intro y _; simp [andEval])
      · have hr := hv r (by simp); have hs' := hv s (by simp)
        rcases r with b | t
        · cases b
          · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, rv])
          · exact keep s hs' (by intro y _; simp [andEval, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inl false) (by simp) (by intro y _; simp [andEval, rv])
            · exact keep (Sum.inr t) hr (by intro y _; simp [andEval, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t, q]⟩ (Or.inl ⟨Or.inl rfl, rfl⟩)
              (fun i hi => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; rcases hi with rfl | rfl; exact hr i rfl; exact hs' i rfl)
              (by intro y _; simp [andEval, rv])
      · simp at hl
    · rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
      · exact keep (Sum.inl false) (by simp) (by intro y _; rfl)
      · exact keep r (hv r (by simp)) (by intro y _; simp [orEval])
      · have hr := hv r (by simp); have hs' := hv s (by simp)
        rcases r with b | t
        · cases b
          · exact keep s hs' (by intro y _; simp [orEval, rv])
          · exact keep (Sum.inl true) (by simp) (by intro y _; simp [orEval, rv])
        · rcases s with b | q
          · cases b
            · exact keep (Sum.inr t) hr (by intro y _; simp [orEval, rv])
            · exact keep (Sum.inl true) (by simp) (by intro y _; simp [orEval, rv])
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [t, q]⟩ (Or.inl ⟨Or.inr rfl, rfl⟩)
              (fun i hi => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; rcases hi with rfl | rfl; exact hr i rfl; exact hs' i rfl)
              (by intro y _; simp [orEval, rv])
      · simp at hl
    · rcases rs with _ | ⟨r, rs⟩
      · exact keep (Sum.inl true) (by simp) (by intro y _; simp [notEval_nil, rv])
      · have hr := hv r (by simp)
        rcases r with c | t
        · exact keep (Sum.inl (!c)) (by simp) (by intro y _; simp [notEval_cons, rv])
        · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [t]⟩ (Or.inr ⟨rfl, rfl⟩)
            (fun i hi => by rw [List.mem_singleton] at hi; subst hi; exact hr i rfl)
            (by intro y _; simp [notEval_cons, rv])
  intro C σ hfan hsz
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) ≠ p10 x
  by_contra hno
  have hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) = p10 x := by
    intro x; by_contra hdiff; exact hno ⟨x, hdiff⟩
  let src : (Fin 10 → Bool) → List Bool := fun x => List.ofFn (x ∘ σ) ++ [x 0 || x 2]
  let tgt : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  have hsrc_len : ∀ x, (src x).length = 11 := fun x => by simp [src]
  have htgt_len : ∀ x, (tgt x).length = 11 := fun x => by simp [tgt]
  have h0 : ∀ w < 11, ∃ t, t < 11 ∧ ∀ x, (src x).getD w false = (tgt x).getD t false := by
    intro w hw
    by_cases hw10 : w < 10
    · refine ⟨(σ ⟨w, hw10⟩).val, by have := (σ ⟨w, hw10⟩).isLt; omega, fun x => ?_⟩
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
      refine ⟨10, by omega, fun x => ?_⟩
      dsimp only [src, tgt]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
      simp
  have hne : ¬∃ b, ∀ x, C.eval (src x) = b := by
    rintro ⟨b, hb⟩
    have h1 := (hb (fun _ => false)).symm.trans ((hcomp (fun _ => false)).trans hp10_false)
    have h2 := (hb (fun _ => true)).symm.trans ((hcomp (fun _ => true)).trans hp10_true)
    exact Bool.false_ne_true (h1.symm.trans h2)
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
      (∀ g ∈ hs, fok g) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 ⟨hs, 0⟩ ∧ hs.length ≤ k ∧
      (∀ w t, w < 11 + k → m w = Sum.inr t → t < 11 + hs.length) ∧
      ∀ x : Fin 10 → Bool, ∀ w < 11 + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : w < 11 then Sum.inr (h0 w h).choose else Sum.inl false,
        by simp, by intro j hj; exfalso; exact Nat.not_lt_zero j hj, by simp, ?_, ?_⟩
      · intro w t hw ht
        have hw11 : w < 11 := by omega
        beta_reduce at ht
        rw [dite_eq_left hw11] at ht
        cases ht
        simpa using (h0 w hw11).choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc_len]; exact hw)]
        beta_reduce
        rw [dite_eq_left hw]
        exact (h0 w hw).choose_spec.2 x
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, hrb, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have hg := hfan _ (List.getElem_mem hk')
      have hop : C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hg.1
      let m' : ℕ → Bool ⊕ ℕ := fun i => if i < 11 + k then m i else Sum.inl false
      obtain ⟨r, e, e1, e2, e3, e4⟩ := emit 11 hs C.gates[k].op hop (C.gates[k].inputs.map m')
        (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
      refine ⟨hs ++ e, Function.update m (11 + k) r, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg'
        rcases List.mem_append.1 hg' with hg' | hg'
        · exact h1 g hg'
        · exact (e2 g hg').1
      · intro j hj i hi
        change i ∈ ((hs ++ e).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
        rcases Nat.lt_or_ge j hs.length with hlt | hge
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
          exact hrb j hlt i hi
        · have he_len : e.length ≤ 1 := e1
          have hjeq : j = hs.length := by rw [List.length_append] at hj; omega
          subst hjeq
          have he_pos : 0 < e.length := by rw [List.length_append] at hj; omega
          have hmem : (hs ++ e).getD hs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ e := by
            rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right le_rfl]
            exact List.getElem_mem (by omega)
          exact (e2 _ hmem).2 i hi
      · rw [List.length_append]; omega
      · intro w t hw ht
        rw [List.length_append]
        by_cases hwe : w = 11 + k
        · subst hwe; rw [Function.update_self] at ht
          have := e3 t ht; omega
        · rw [Function.update_of_ne hwe] at ht
          have := h3 w t (by omega) ht; omega
      · intro x w hw
        by_cases hwe : w = 11 + k
        · subst hwe; rw [Function.update_self]
          rw [e4 _ (htgt_len x)]
          have rg := run_gate C.gates (src x) k hk'
          rw [hsrc_len] at rg
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
          rw [htgt_len]; exact this
  obtain ⟨hs, m, h1, hrb, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hout : C.output < 11 + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc_len]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | out0
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  have hout0_lt : out0 < 11 + hs.length := h3 C.output out0 hout hm
  have hD0p10 : ∀ x : Fin 10 → Bool, (run hs (tgt x)).getD out0 false = p10 x := fun x => by
    have := hev x; rw [hm] at this; exact this.symm.trans (hcomp x)
  have hout0_ge : 11 ≤ out0 := by
    by_contra hlt
    have hlt' : out0 < 11 := by omega
    have hwire : ∀ x : Fin 10 → Bool, p10 x = (tgt x).getD out0 false := by
      intro x; rw [← hD0p10 x]; exact run_input hs (tgt x) out0 (by rw [htgt_len]; exact hlt')
    by_cases h10 : out0 = 10
    · have hf := hwire (fun i => decide (i = 0))
      rw [hp10_single 0, h10] at hf
      dsimp only [tgt] at hf
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)] at hf
      simp at hf
    · have hw : out0 < 10 := by omega
      let v : Fin 10 := ⟨out0, hw⟩
      have hs' := hwire (fun i => decide (i = v))
      rw [hp10_single v] at hs'
      have hval : (tgt (fun i => decide (i = v))).getD out0 false = true := by
        dsimp only [tgt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_ofFn]
        simp [hw, v]
      rw [hval] at hs'; cases hs'
  let kCut : ℕ := out0 - 11 + 1
  have hkCut_le : kCut ≤ hs.length := by omega
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨hs.take kCut, out0⟩
  have hDsz : D.size = kCut := List.length_take_of_le hkCut_le
  have hCsz : C.gates.length ≤ 18 := hsz
  have hDsz18 : D.size ≤ 18 := by omega
  have hDout : D.output = 11 + (D.size - 1) := by change out0 = 11 + (D.size - 1); omega
  have hDfok : ∀ g ∈ D.gates, fok g := fun g hg => h1 g (List.mem_of_mem_take hg)
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    rcases hDfok g hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · refine ⟨?_, by omega⟩
      rcases hop with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl h)))
    · exact ⟨Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hop)))), by omega⟩
  have hDrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 D := by
    intro j hj i hi
    have hj' : j < kCut := hDsz ▸ hj
    have hjhs : j < hs.length := by omega
    have hgd : D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
        hs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      change (hs.take kCut).getD j _ = hs.getD j _
      rw [List.getD_eq_getElem _ _ (by rw [List.length_take_of_le hkCut_le]; exact hj'),
          List.getD_eq_getElem _ _ hjhs, List.getElem_take]
    change i ∈ (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
    rw [hgd] at hi
    exact hrb j hjhs i hi
  have hDp10 : ∀ x : Fin 10 → Bool, D.eval (tgt x) = p10 x := by
    intro x
    have hsp : hs = hs.take kCut ++ hs.drop kCut := (List.take_append_drop kCut hs).symm
    have h1 := run_prefix (hs.take kCut) (hs.drop kCut) (tgt x) out0
      (by rw [htgt_len, List.length_take_of_le hkCut_le]; omega)
    rw [← hsp] at h1
    exact h1.symm.trans (hD0p10 x)
  by_cases hUses10 : ∃ j : Fin D.gates.length, 10 ∈ (D.gates.get j).inputs
  · by_cases hHasNot : ∃ j : Fin D.gates.length, (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not
    · have hExactLen : ∀ j : Fin D.gates.length,
          ((D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.length = 1) ∧
          ((D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.length = 2) := by
        intro j
        rcases hDfok _ (List.get_mem D.gates j) with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
        · constructor
          · intro hn; rcases hop with h | h <;> (rw [h] at hn; cases hn)
          · intro _; exact hlen
        · constructor
          · intro _; exact hlen
          · intro hne; exact False.elim (hne hop)
      obtain ⟨x, hx⟩ := hHintUsedNot D hDfan hDrb hDsz18 hDout hExactLen hUses10 hHasNot
      exact hx (hDp10 x)
    · have hDao2 : PEqualNP.TopForm.IsAO2 11 D := by
        refine ⟨?_, hDrb, ?_⟩
        · intro g hg
          obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
          rcases hDfok _ (List.get_mem D.gates j) with ⟨hop, _⟩ | ⟨hop, _⟩
          · exact hop
          · exact False.elim (hHasNot ⟨j, hop⟩)
        · intro g hg
          obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
          rcases hDfok _ (List.get_mem D.gates j) with ⟨_, hlen⟩ | ⟨hop, _⟩
          · exact hlen
          · exact False.elim (hHasNot ⟨j, hop⟩)
      obtain ⟨x, hx⟩ := hHintUsedMono D hDao2 hDsz18 hDout hUses10
      exact hx (hDp10 x)
  · let sh (w : ℕ) : ℕ := if w < 10 then w else w - 1
    let shGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map sh⟩
    let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨D.gates.map shGate, out0 - 1⟩
    have hEsz : E.size = D.size := List.length_map shGate
    have hEfan : PEqualNP.MetaComplexity.FanInTwo E := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hDfan g' hg').1, by change (g'.inputs.map sh).length ≤ 2; rw [List.length_map]; exact (hDfan g' hg').2⟩
    have hErb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 E := by
      intro j hj i hi
      have hj' : j < D.gates.length := by change j < D.size; rw [← hEsz]; exact hj
      have hgd : E.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          shGate (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩) := by
        change (D.gates.map shGate).getD j _ = shGate (D.gates.getD j _)
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj', List.getElem_map]
      change i ∈ (E.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
      rw [hgd] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      have hwlt := hDrb j hj' w hw
      have hwne10 : w ≠ 10 := by
        intro h10; subst h10
        apply hUses10
        refine ⟨⟨j, hj'⟩, ?_⟩
        rw [List.getD_eq_getElem _ _ hj'] at hw
        exact hw
      dsimp only [sh]
      split_ifs <;> omega
    have hEwires : ∀ (x : Fin 10 → Bool) (w : ℕ), w < 11 + D.gates.length → w ≠ 10 →
        (run E.gates (List.ofFn x)).getD (sh w) false = (run D.gates (tgt x)).getD w false := by
      intro x w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hwne10
        by_cases hw10 : w < 10
        · have hsh : sh w = w := by simp [sh, hw10]
          rw [hsh, run_input E.gates (List.ofFn x) w (by simp [hw10]),
              run_input D.gates (tgt x) w (by rw [htgt_len]; omega)]
          dsimp only [tgt]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw10])]
        · let j : ℕ := w - 11
          have hwj : w = 11 + j := by omega
          have hjD : j < D.gates.length := by omega
          have hjE : j < E.gates.length := by change j < E.size; rw [hEsz]; exact hjD
          have hsh : sh w = 10 + j := by simp [sh, show ¬ w < 10 by omega]; omega
          rw [hsh, hwj]
          have rgE := run_gate E.gates (List.ofFn x) j hjE
          have rgD := run_gate D.gates (tgt x) j hjD
          rw [List.length_ofFn] at rgE
          rw [htgt_len] at rgD
          rw [rgE, rgD]
          have hEg : E.gates[j] = shGate D.gates[j] := List.getElem_map _
          rw [hEg]
          dsimp only [shGate]
          rw [List.map_map]
          congr 1
          refine List.map_congr_left fun u hu => ?_
          have hu' : u ∈ (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs := by
            rw [List.getD_eq_getElem _ _ hjD]; exact hu
          have hult := hDrb j hjD u hu'
          have hune10 : u ≠ 10 := fun h10 => hUses10 ⟨⟨j, hjD⟩, by subst h10; exact hu⟩
          have hsh_lt : sh u < 10 + j := by dsimp only [sh]; split_ifs <;> omega
          simp only [Function.comp, ite_eq_left hsh_lt, ite_eq_left hult]
          exact ih u (by omega) (by omega) hune10
    have hEp10 : ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = p10 x := by
      intro x
      have hsh_out : sh out0 = out0 - 1 := by simp [sh, show ¬ out0 < 10 by omega]
      have h1 := hEwires x out0 (by change out0 < 11 + D.size; omega) (by omega)
      rw [hsh_out] at h1
      exact h1.trans (hDp10 x)
    obtain ⟨x, hx⟩ := hHintUnused E hEfan hErb (by omega) (by change out0 - 1 = 10 + (E.size - 1); omega)
    exact hx (hEp10 x)
