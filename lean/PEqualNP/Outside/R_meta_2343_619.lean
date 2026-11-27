import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2343_619
    (hNoExtra : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 26 D →
      D.output = 26 + (D.size - 1) →
      let S : Finset (Fin 13) := {0, 1, 3, 9}
      let flag : Fin 13 → Fin 13 → List Bool := fun p l =>
        (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
      let quad : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ q ∈ Q, q - i ∉ S)
      (∀ p l : Fin 13, p - l ∈ S → D.eval (flag p l) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, {q ∈ Q | q - l ∈ S}.card ≤ 2) → D.eval (quad Q) = false) →
      63 ≤ D.size)
    (hSameSide : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (t : List ℕ),
      t ∈ ([[0, 1], [13, 14]] : List (List ℕ)) →
      PEqualNP.TopForm.IsAO2 27 D →
      D.output = 27 + (D.size - 1) →
      (∃ j : Fin D.gates.length, 26 ∈ (D.gates.get j).inputs) →
      let S : Finset (Fin 13) := {0, 1, 3, 9}
      let flag : Fin 13 → Fin 13 → List Bool := fun p l =>
        (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
      let quad : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ q ∈ Q, q - i ∉ S)
      let ext : List Bool → List Bool := fun v => v ++ [t.any fun i => v.getD i false]
      (∀ p l : Fin 13, p - l ∈ S → D.eval (ext (flag p l)) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, {q ∈ Q | q - l ∈ S}.card ≤ 2) → D.eval (ext (quad Q)) = false) →
      63 ≤ D.size)
    (hCross : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (t : List ℕ),
      t ∈ ([[0, 13], [0, 14]] : List (List ℕ)) →
      PEqualNP.TopForm.IsAO2 27 D →
      D.output = 27 + (D.size - 1) →
      (∃ j : Fin D.gates.length, 26 ∈ (D.gates.get j).inputs) →
      let S : Finset (Fin 13) := {0, 1, 3, 9}
      let flag : Fin 13 → Fin 13 → List Bool := fun p l =>
        (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
      let quad : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ q ∈ Q, q - i ∉ S)
      let ext : List Bool → List Bool := fun v => v ++ [t.any fun i => v.getD i false]
      (∀ p l : Fin 13, p - l ∈ S → D.eval (ext (flag p l)) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, {q ∈ Q | q - l ∈ S}.card ≤ 2) → D.eval (ext (quad Q)) = false) →
      63 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
      x2.length ≤ (2 : ℕ) →
      PEqualNP.MetaComplexity.Monotone2 x1 →
      (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →
      have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) =>
        (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++
        List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);
      have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) =>
        (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++
        List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);
      have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) =>
        x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);
      have x10 : List Bool → List Bool := fun (x10 : List Bool) =>
        x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];
      (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) →
      (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) →
      (63 : ℕ) ≤ x1.size := by
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x; simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs; induction gs using List.reverseRecOn with
    | nil => intro x; simp [run]
    | append_singleton gs g ih => intro x; rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]; omega
  have getD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length → (l ++ [b]).getD t false = l.getD t false := by
    intro l b t ht; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have getD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs; induction hs using List.reverseRecOn with
    | nil => intro x i _; simp [run]
    | append_singleton hs g ih =>
      intro x i hi
      rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih x i hi]
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h := run_prefix [] gs x i (by simpa using hi)
    simpa [run] using h
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x j hj
    have hsp : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
      have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := List.take_succ_eq_append_getElem hj
      rw [← h1, List.take_append_drop]
    have htl : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have h1 : (run gs x).getD (x.length + j) false = (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
      conv_lhs => rw [hsp]
      exact run_prefix _ _ _ _ (by rw [List.length_append, htl, List.length_singleton]; omega)
    rw [h1, run_snoc]
    have hlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, htl]
    conv_lhs => rw [← hlen, getD_at]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases hilt : i < x.length + j
    · rw [if_pos hilt]
      conv_rhs => rw [hsp, List.append_assoc]
      exact (run_prefix (gs.take j) _ x i (by rw [htl]; exact hilt)).symm
    · rw [if_neg hilt, List.getD_eq_default _ _ (by omega)]
  let rv : List Bool → Bool ⊕ ℕ → Bool := fun w r => Sum.elim id (fun t => w.getD t false) r
  let aok : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2
  have rv_ext : ∀ (hs e : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool) (r : Bool ⊕ ℕ),
      (∀ t, r = Sum.inr t → t < y.length + hs.length) → rv (run (hs ++ e) y) r = rv (run hs y) r := by
    intro hs e y r hr
    rcases r with b | t
    · rfl
    · exact run_prefix hs e y t (hr t rfl)
  have emit : ∀ (N : ℕ) (hs : List PEqualNP.CircuitLowerBounds.Gate) (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (rs : List (Bool ⊕ ℕ)), rs.length ≤ 2 →
      (∀ r ∈ rs, ∀ t, r = Sum.inr t → t < N + hs.length) →
      ∃ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate),
        e.length ≤ 1 ∧
        (∀ g ∈ e, aok g ∧ ∀ i ∈ g.inputs, i < N + hs.length) ∧
        (∀ t, r = Sum.inr t → t < N + hs.length + e.length) ∧
        ∀ (y : List Bool), y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro N hs op hop rs hl hv
    have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = Sum.inr t → t < N + hs.length) →
        (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r' : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate),
          e.length ≤ 1 ∧ (∀ g ∈ e, aok g ∧ ∀ i ∈ g.inputs, i < N + hs.length) ∧
          (∀ t, r' = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r' = op.eval (rs.map (rv (run hs y))) := by
      intro r hr h2
      refine ⟨r, [], by simp, by simp, fun t ht => by have := hr t ht; simp; omega, fun y hy => ?_⟩
      simpa using h2 y hy
    have add : ∀ g : PEqualNP.CircuitLowerBounds.Gate, aok g → (∀ i ∈ g.inputs, i < N + hs.length) →
        (∀ y : List Bool, y.length = N →
          g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
        ∃ (r' : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate),
          e.length ≤ 1 ∧ (∀ g' ∈ e, aok g' ∧ ∀ i ∈ g'.inputs, i < N + hs.length) ∧
          (∀ t, r' = Sum.inr t → t < N + hs.length + e.length) ∧
          ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r' = op.eval (rs.map (rv (run hs y))) := by
      intro g h1 hrb h2
      refine ⟨Sum.inr (N + hs.length), [g], by simp, ?_, ?_, fun y hy => ?_⟩
      · intro g' hg'; rw [List.mem_singleton] at hg'; subst hg'; exact ⟨h1, hrb⟩
      · intro t ht; cases ht; simp
      · have hlen : N + hs.length = (run hs y).length := by rw [run_length, hy]
        dsimp only [rv, Sum.elim]
        rw [run_snoc, hlen, getD_at]
        exact h2 y hy
    rcases hop with rfl | rfl
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
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t, q]⟩ ⟨Or.inl rfl, rfl⟩
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
          · exact add ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [t, q]⟩ ⟨Or.inr rfl, rfl⟩
              (fun i hi => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; rcases hi with rfl | rfl; exact hr i rfl; exact hs' i rfl)
              (by intro y _; simp [orEval, rv])
      · simp at hl
  have norm : ∀ (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (mapIn : ℕ → Bool ⊕ ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ w < 27, ∀ t, mapIn w = Sum.inr t → t < N) →
      ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
        (∀ g ∈ hs, aok g) ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨hs, 0⟩ ∧
        hs.length ≤ C.gates.length ∧
        (∀ w < 27 + C.gates.length, ∀ t, m w = Sum.inr t → t < N + hs.length) ∧
        ∀ (u v : List Bool), u.length = 27 → v.length = N →
          (∀ w < 27, u.getD w false = rv v (mapIn w)) →
          ∀ w < 27 + C.gates.length, (run C.gates u).getD w false = rv (run hs v) (m w) := by
    intro N C mapIn hmono hmapIn
    have key : ∀ k ≤ C.gates.length,
        ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
          (∀ g ∈ hs, aok g) ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨hs, 0⟩ ∧
          hs.length ≤ k ∧
          (∀ w < 27 + k, ∀ t, m w = Sum.inr t → t < N + hs.length) ∧
          ∀ (u v : List Bool), u.length = 27 → v.length = N →
            (∀ w < 27, u.getD w false = rv v (mapIn w)) →
            ∀ w < 27 + k, (run C.gates u).getD w false = rv (run hs v) (m w) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], mapIn, by simp, by intro j hj; exfalso; exact Nat.not_lt_zero j hj, by simp, ?_, ?_⟩
        · intro w hw t ht; simpa using hmapIn w (by omega) t ht
        · intro u v hu _ huv w hw
          rw [run_input C.gates u w (by omega)]
          exact huv w (by omega)
      | succ k ih =>
        intro hk
        obtain ⟨hs, m, h1, hrb, h2, h3, h4⟩ := ih (by omega)
        have hk' : k < C.gates.length := by omega
        let g : PEqualNP.CircuitLowerBounds.Gate := C.gates[k]
        have hg_mem : g ∈ C.gates := List.getElem_mem hk'
        have hg_mono := hmono g hg_mem
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < 27 + k then m i else Sum.inl false
        let rs : List (Bool ⊕ ℕ) := g.inputs.map m'
        have hrs_len : rs.length ≤ 2 := by rw [List.length_map]; exact hg_mono.2
        have hrs_val : ∀ r ∈ rs, ∀ t, r = Sum.inr t → t < N + hs.length := by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          dsimp only [m'] at ht
          split_ifs at ht with hi
          exact h3 i hi t ht
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit N hs g.op hg_mono.1 rs hrs_len hrs_val
        refine ⟨hs ++ e, Function.update m (27 + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with hg' | hg'
          · exact h1 g' hg'
          · exact (e2 g' hg').1
        · intro j hj i hi
          change i ∈ ((hs ++ e).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
          rcases Nat.lt_or_ge j hs.length with hlt | hge
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
            exact hrb j hlt i hi
          · have hjeq : j = hs.length := by rw [List.length_append] at hj; omega
            subst hjeq
            have hmem : (hs ++ e).getD hs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ e := by
              rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right le_rfl]
              exact List.getElem_mem (by rw [List.length_append] at hj; omega)
            exact (e2 _ hmem).2 i hi
        · rw [List.length_append]; omega
        · intro w hw t ht
          rw [List.length_append]
          by_cases hwe : w = 27 + k
          · subst hwe; rw [Function.update_self] at ht; have := e3 t ht; omega
          · rw [Function.update_of_ne hwe] at ht; have := h3 w (by omega) t ht; omega
        · intro u v hu hv huv w hw
          by_cases hwe : w = 27 + k
          · subst hwe; rw [Function.update_self, e4 v hv]
            have rg := run_gate C.gates u k hk'
            rw [hu] at rg
            rw [rg, List.map_map]
            congr 1
            refine List.map_congr_left fun i _ => ?_
            simp only [Function.comp, m']
            split_ifs with h
            · exact h4 u v hu hv huv i h
            · rfl
          · rw [Function.update_of_ne hwe, h4 u v hu hv huv w (by omega)]
            refine (rv_ext hs e v (m w) fun t ht => ?_).symm
            rw [hv]; exact h3 w (by omega) t ht
    exact key C.gates.length le_rfl
  let S : Finset (Fin 13) := {0, 1, 3, 9}
  let flag : Fin 13 → Fin 13 → List Bool := fun p l =>
    (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
  let quad : Finset (Fin 13) → List Bool := fun Q =>
    (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ q ∈ Q, q - i ∉ S)
  let isQuad : Finset (Fin 13) → Prop := fun Q =>
    Q.card = 4 ∧ ∀ l : Fin 13, {q ∈ Q | q - l ∈ S}.card ≤ 2
  have hQ0 : isQuad ({0, 1, 2, 5} : Finset (Fin 13)) := by decide +kernel
  have h00_mem : (0 : Fin 13) - (0 : Fin 13) ∈ S := by decide
  have h11_mem : (1 : Fin 13) - (1 : Fin 13) ∈ S := by decide
  have h22_mem : (2 : Fin 13) - (2 : Fin 13) ∈ S := by decide
  have hflag_len : ∀ p l : Fin 13, (flag p l).length = 26 := fun p l => by simp [flag]
  have hquad_len : ∀ Q : Finset (Fin 13), (quad Q).length = 26 := fun Q => by simp [quad]
  have hflag_pt : ∀ (p l i : Fin 13), (flag p l).getD i.val false = decide (i = p) := by
    intro p l i
    dsimp only [flag]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [i.isLt]), List.getElem?_ofFn]
    simp [i.isLt]
  have hflag_ln : ∀ (p l i : Fin 13), (flag p l).getD (13 + i.val) false = decide (i = l) := by
    intro p l i
    dsimp only [flag]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
        Nat.add_sub_cancel_left, List.getElem?_ofFn]
    simp [i.isLt]
  have hquad_pt : ∀ (Q : Finset (Fin 13)) (i : Fin 13), (quad Q).getD i.val false = decide (i ∈ Q) := by
    intro Q i
    dsimp only [quad]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [i.isLt]), List.getElem?_ofFn]
    simp [i.isLt]
  have hquad_ln : ∀ (Q : Finset (Fin 13)) (i : Fin 13), (quad Q).getD (13 + i.val) false = decide (∀ q ∈ Q, q - i ∉ S) := by
    intro Q i
    dsimp only [quad]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
        Nat.add_sub_cancel_left, List.getElem?_ofFn]
    simp [i.isLt]
  let autP : Fin 24 → Fin 13 → Fin 13 := ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 2, 3, 12, 11, 6, 7, 10, 9, 8, 5, 4, 1],
    ![0, 2, 5, 12, 11, 10, 1, 6, 4, 8, 3, 9, 7],
    ![0, 5, 2, 4, 3, 1, 6, 9, 8, 7, 11, 10, 12],
    ![0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
    ![0, 3, 5, 1, 2, 8, 10, 12, 7, 9, 11, 6, 4],
    ![0, 5, 3, 4, 11, 6, 8, 10, 1, 7, 2, 12, 9],
    ![0, 5, 6, 7, 8, 2, 3, 12, 11, 4, 1, 9, 10],
    ![0, 5, 6, 7, 1, 9, 12, 3, 10, 4, 8, 2, 11],
    ![0, 2, 1, 12, 4, 7, 6, 5, 9, 8, 10, 11, 3],
    ![0, 2, 5, 12, 3, 9, 6, 1, 7, 8, 11, 10, 4],
    ![0, 2, 5, 8, 11, 6, 9, 10, 7, 12, 3, 1, 4],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 1, 5, 3, 6, 11, 12, 10, 7, 9, 8, 2, 4],
    ![0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7],
    ![0, 3, 2, 1, 11, 10, 7, 6, 8, 9, 5, 4, 12],
    ![0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
    ![0, 3, 5, 1, 2, 8, 10, 12, 7, 9, 11, 6, 4],
    ![0, 3, 5, 1, 11, 6, 12, 10, 4, 9, 2, 8, 7],
    ![0, 3, 5, 9, 11, 10, 8, 6, 7, 1, 2, 12, 4],
    ![0, 3, 5, 9, 2, 12, 6, 8, 4, 1, 11, 10, 7],
    ![1, 0, 2, 3, 12, 11, 6, 7, 10, 9, 8, 5, 4],
    ![1, 0, 5, 3, 4, 2, 12, 10, 8, 9, 7, 11, 6],
    ![1, 0, 5, 3, 7, 11, 10, 12, 6, 9, 4, 2, 8]
  ]
  let autL : Fin 24 → Fin 13 → Fin 13 := ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![12, 2, 3, 11, 10, 6, 7, 9, 8, 5, 4, 1, 0],
    ![12, 2, 9, 11, 10, 1, 5, 3, 8, 7, 0, 6, 4],
    ![4, 2, 1, 3, 0, 5, 6, 8, 7, 11, 10, 9, 12],
    ![0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
    ![0, 2, 5, 1, 12, 7, 9, 11, 6, 8, 10, 3, 4],
    ![4, 2, 3, 8, 10, 5, 7, 1, 11, 6, 12, 9, 0],
    ![4, 5, 6, 7, 12, 2, 3, 11, 8, 1, 0, 9, 10],
    ![4, 5, 6, 11, 0, 9, 3, 7, 1, 8, 12, 2, 10],
    ![12, 1, 11, 3, 4, 6, 5, 9, 8, 7, 10, 2, 0],
    ![12, 2, 9, 3, 0, 6, 5, 11, 7, 8, 10, 1, 4],
    ![12, 2, 5, 8, 10, 6, 9, 7, 11, 3, 0, 1, 4],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 5, 2, 3, 10, 11, 9, 7, 6, 8, 12, 1, 4],
    ![0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4],
    ![0, 2, 1, 11, 10, 7, 6, 5, 8, 9, 4, 3, 12],
    ![0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
    ![0, 2, 5, 1, 12, 7, 9, 11, 6, 8, 10, 3, 4],
    ![0, 2, 5, 11, 10, 3, 9, 1, 8, 6, 12, 7, 4],
    ![0, 2, 9, 8, 10, 7, 5, 6, 11, 1, 12, 3, 4],
    ![0, 2, 9, 6, 12, 3, 5, 8, 1, 11, 10, 7, 4],
    ![0, 12, 2, 3, 11, 10, 6, 7, 9, 8, 5, 4, 1],
    ![0, 4, 2, 3, 1, 12, 9, 7, 8, 6, 11, 10, 5],
    ![0, 4, 2, 7, 11, 10, 9, 3, 6, 8, 1, 12, 5]
  ]
  have haut_ok :
      (∀ k : Fin 24, (∀ a b : Fin 13, autP k a = autP k b → a = b) ∧ (∀ a : Fin 13, ∃ b : Fin 13, autP k b = a)) ∧
      (∀ k : Fin 24, (∀ a b : Fin 13, autL k a = autL k b → a = b) ∧ (∀ a : Fin 13, ∃ b : Fin 13, autL k b = a)) ∧
      (∀ (k : Fin 24) (p l : Fin 13), autP k p - autL k l ∈ S ↔ p - l ∈ S) := by
    decide +kernel
  have hcov_pp : ∀ p : Fin 13, p ≠ 0 → ∃ k : Fin 24, (autP k 0 = 0 ∧ autP k p = 1) ∨ (autP k 0 = 1 ∧ autP k p = 0) := by
    decide +kernel
  have hcov_ll : ∀ l : Fin 13, l ≠ 0 → ∃ k : Fin 24, (autL k 0 = 0 ∧ autL k l = 1) ∨ (autL k 0 = 1 ∧ autL k l = 0) := by
    decide +kernel
  have hcov_flag : ∀ l : Fin 13, (0 : Fin 13) - l ∈ S → ∃ k : Fin 24, autP k 0 = 0 ∧ autL k l = 0 := by
    decide +kernel
  have hcov_nonflag : ∀ l : Fin 13, (0 : Fin 13) - l ∉ S → ∃ k : Fin 24, autP k 0 = 0 ∧ autL k l = 1 := by
    decide +kernel
  intro C x2 hx2len hmono _ _ _ _ _ _ hPos hNeg
  let x10 : List Bool → List Bool := fun v => v ++ [x2.any fun i => v.getD i false]
  have hx10_len : ∀ v : List Bool, v.length = 26 → (x10 v).length = 27 := fun v hv => by simp [x10, hv]
  have hx10_lt : ∀ (v : List Bool) (w : ℕ), w < v.length → (x10 v).getD w false = v.getD w false := fun v w hw => getD_lt v _ w hw
  have hx10_26 : ∀ v : List Bool, v.length = 26 → (x10 v).getD 26 false = x2.any (fun i => v.getD i false) := fun v hv => by
    dsimp only [x10]; rw [← hv, getD_at]
  have finishNoExtra : ∀ (hs : List PEqualNP.CircuitLowerBounds.Gate) (out0 : ℕ),
      (∀ g ∈ hs, aok g) →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 ⟨hs, 0⟩ →
      hs.length ≤ C.gates.length →
      out0 < 26 + hs.length →
      (∀ p l : Fin 13, p - l ∈ S → (run hs (flag p l)).getD out0 false = true) →
      (∀ Q : Finset (Fin 13), isQuad Q → (run hs (quad Q)).getD out0 false = false) →
      63 ≤ C.size := by
    intro hs out0 haok hrb hlen hout_lt hP hN
    have hout_ge : 26 ≤ out0 := by
      by_contra hlt
      have hlt26 : out0 < 26 := by omega
      by_cases h13 : out0 < 13
      · let p : Fin 13 := ⟨out0, h13⟩
        by_cases hp0 : p = 0
        · have h1 := hP 1 1 h11_mem
          rw [run_input hs (flag 1 1) out0 (by rw [hflag_len]; exact hlt26)] at h1
          have h2 := hflag_pt 1 1 p
          change (flag 1 1).getD out0 false = decide (p = 1) at h2
          rw [h2, hp0] at h1; simp at h1
        · have h1 := hP 0 0 h00_mem
          rw [run_input hs (flag 0 0) out0 (by rw [hflag_len]; exact hlt26)] at h1
          have h2 := hflag_pt 0 0 p
          change (flag 0 0).getD out0 false = decide (p = 0) at h2
          rw [h2] at h1; simp [hp0] at h1
      · let l : Fin 13 := ⟨out0 - 13, by omega⟩
        have ho : out0 = 13 + l.val := by dsimp only [l]; omega
        by_cases hl0 : l = 0
        · have h1 := hP 1 1 h11_mem
          rw [run_input hs (flag 1 1) out0 (by rw [hflag_len]; exact hlt26), ho, hflag_ln, hl0] at h1
          simp at h1
        · have h1 := hP 0 0 h00_mem
          rw [run_input hs (flag 0 0) out0 (by rw [hflag_len]; exact hlt26), ho, hflag_ln] at h1
          simp [hl0] at h1
    let kCut : ℕ := out0 - 26 + 1
    have hkCut_le : kCut ≤ hs.length := by omega
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨hs.take kCut, out0⟩
    have hDsz : D.size = kCut := List.length_take_of_le hkCut_le
    have hDout : D.output = 26 + (D.size - 1) := by change out0 = 26 + (D.size - 1); omega
    have hDao2 : PEqualNP.TopForm.IsAO2 26 D := by
      refine ⟨fun g hg => (haok g (List.mem_of_mem_take hg)).1, ?_, fun g hg => (haok g (List.mem_of_mem_take hg)).2⟩
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
    have hDeval : ∀ v : List Bool, v.length = 26 → D.eval v = (run hs v).getD out0 false := by
      intro v hv
      have hsp : hs = hs.take kCut ++ hs.drop kCut := (List.take_append_drop kCut hs).symm
      have h1 := run_prefix (hs.take kCut) (hs.drop kCut) v out0
        (by rw [hv, List.length_take_of_le hkCut_le]; omega)
      rw [← hsp] at h1
      exact h1.symm
    have h63 : 63 ≤ D.size := hNoExtra D hDao2 hDout
      (fun p l hpl => (hDeval (flag p l) (hflag_len p l)).trans (hP p l hpl))
      (fun Q hQc hQl => (hDeval (quad Q) (hquad_len Q)).trans (hN Q ⟨hQc, hQl⟩))
    have hCsz : C.size = C.gates.length := rfl
    omega
  have handleNoExtraMap : ∀ (mapIn : ℕ → Bool ⊕ ℕ),
      (∀ w < 27, ∀ t, mapIn w = Sum.inr t → t < 26) →
      (∀ v : List Bool, v.length = 26 → ∀ w < 27, (x10 v).getD w false = rv v (mapIn w)) →
      63 ≤ C.size := by
    intro mapIn hmapLt hmapEq
    obtain ⟨hs, m, haok, hrb, hlen, hmLt, hmEq⟩ := norm 26 C mapIn hmono hmapLt
    have hCout : C.output < 27 + C.gates.length := by
      by_contra hge
      have h1 := hPos 0 0 h00_mem
      change (run C.gates (x10 (flag 0 0))).getD C.output false = true at h1
      rw [List.getD_eq_default _ _ (by rw [run_length, hx10_len _ (hflag_len 0 0)]; omega)] at h1
      cases h1
    rcases hm : m C.output with b | out0
    · cases b
      · have h1 := hPos 0 0 h00_mem
        have h2 := hmEq (x10 (flag 0 0)) (flag 0 0) (hx10_len _ (hflag_len 0 0)) (hflag_len 0 0)
          (hmapEq _ (hflag_len 0 0)) C.output hCout
        rw [hm] at h2; change (run C.gates (x10 (flag 0 0))).getD C.output false = true at h1
        rw [h2] at h1; cases h1
      · have h1 := hNeg {0, 1, 2, 5} hQ0
        have h2 := hmEq (x10 (quad {0, 1, 2, 5})) (quad {0, 1, 2, 5}) (hx10_len _ (hquad_len _)) (hquad_len _)
          (hmapEq _ (hquad_len _)) C.output hCout
        rw [hm] at h2; change (run C.gates (x10 (quad {0, 1, 2, 5}))).getD C.output false = false at h1
        rw [h2] at h1; cases h1
    · refine finishNoExtra hs out0 haok hrb hlen (hmLt C.output hCout out0 hm) ?_ ?_
      · intro p l hpl
        have h1 := hPos p l hpl
        have h2 := hmEq (x10 (flag p l)) (flag p l) (hx10_len _ (hflag_len p l)) (hflag_len p l)
          (hmapEq _ (hflag_len p l)) C.output hCout
        rw [hm] at h2; exact h2.symm.trans h1
      · intro Q hQ
        have h1 := hNeg Q hQ
        have h2 := hmEq (x10 (quad Q)) (quad Q) (hx10_len _ (hquad_len Q)) (hquad_len Q)
          (hmapEq _ (hquad_len Q)) C.output hCout
        rw [hm] at h2; exact h2.symm.trans h1
  have handlePair : ∀ (u v : ℕ), u < 26 → v < 26 → x2 = [u, v] →
      ∀ (σP σL : Fin 13 → Fin 13),
        (∀ a b : Fin 13, σP a = σP b → a = b) →
        (∀ a : Fin 13, ∃ b : Fin 13, σP b = a) →
        (∀ a b : Fin 13, σL a = σL b → a = b) →
        (∀ a : Fin 13, ∃ b : Fin 13, σL b = a) →
        (∀ p l : Fin 13, σP p - σL l ∈ S ↔ p - l ∈ S) →
        ∀ (t0 t1 : ℕ),
          let π : ℕ → ℕ := fun w =>
            if h1 : w < 13 then (σP ⟨w, h1⟩).val
            else if h2 : w < 26 then 13 + (σL ⟨w - 13, by omega⟩).val
            else 26
          ((π u = t0 ∧ π v = t1) ∨ (π u = t1 ∧ π v = t0)) →
          ([t0, t1] ∈ ([[0, 1], [13, 14]] : List (List ℕ)) ∨ [t0, t1] ∈ ([[0, 13], [0, 14]] : List (List ℕ))) →
          63 ≤ C.size := by
    intro u v hu hv hx2eq σP σL hPinj hPsurj hLinj hLsurj hPres t0 t1 π hPairEq hTargetMem
    let t : List ℕ := [t0, t1]
    let ext : List Bool → List Bool := fun w => w ++ [t.any fun i => w.getD i false]
    have hext_len : ∀ w : List Bool, w.length = 26 → (ext w).length = 27 := fun w hw => by simp [ext, hw]
    have hπ_lt : ∀ w < 26, π w < 26 := by
      intro w hw
      dsimp only [π]
      split_ifs with h1 h2
      · have := (σP ⟨w, h1⟩).isLt; omega
      · have := (σL ⟨w - 13, by omega⟩).isLt; omega
    let mapIn : ℕ → Bool ⊕ ℕ := fun w => if w < 26 then Sum.inr (π w) else Sum.inr 26
    have hmapLt : ∀ w < 27, ∀ r, mapIn w = Sum.inr r → r < 27 := by
      intro w hw r hr
      dsimp only [mapIn] at hr
      split_ifs at hr with h26
      · cases hr; have := hπ_lt w h26; omega
      · cases hr; omega
    obtain ⟨hs, m, haok, hrb, hlen, hmLt, hmEq⟩ := norm 27 C mapIn hmono hmapLt
    have hCout : C.output < 27 + C.gates.length := by
      by_contra hge
      have h1 := hPos 0 0 h00_mem
      change (run C.gates (x10 (flag 0 0))).getD C.output false = true at h1
      rw [List.getD_eq_default _ _ (by rw [run_length, hx10_len _ (hflag_len 0 0)]; omega)] at h1
      cases h1
    have hSync : ∀ (w w' : List Bool), w.length = 26 → w'.length = 26 →
        (∀ i < 26, w'.getD i false = w.getD (π i) false) →
        ∀ i < 27, (x10 w').getD i false = rv (ext w) (mapIn i) := by
      intro w w' hw hw' hww' i hi
      by_cases hi26 : i < 26
      · rw [hx10_lt w' i (by omega), hww' i hi26]
        dsimp only [mapIn]
        rw [if_pos hi26]
        dsimp only [rv, Sum.elim]
        rw [getD_lt w _ (π i) (by rw [hw]; exact hπ_lt i hi26)]
      · have hi_eq : i = 26 := by omega
        subst hi_eq
        rw [hx10_26 w' hw', hx2eq]
        dsimp only [mapIn]
        rw [if_neg (by omega)]
        dsimp only [rv, Sum.elim]
        rw [show (ext w).getD 26 false = t.any (fun k => w.getD k false) from by
          dsimp only [ext]; rw [← hw, getD_at]]
        dsimp only [t]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        rw [hww' u hu, hww' v hv]
        rcases hPairEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]; exact Bool.or_comm _ _
    have hP_hs : ∀ p l : Fin 13, p - l ∈ S → rv (run hs (ext (flag p l))) (m C.output) = true := by
      intro p l hpl
      obtain ⟨p0, hp0⟩ := hPsurj p
      obtain ⟨l0, hl0⟩ := hLsurj l
      have hpl0 : p0 - l0 ∈ S := (hPres p0 l0).mp (by rw [hp0, hl0]; exact hpl)
      have hww' : ∀ i < 26, (flag p0 l0).getD i false = (flag p l).getD (π i) false := by
        intro i hi
        dsimp only [π]
        by_cases h13 : i < 13
        · rw [dite_eq_left h13]
          have h1 := hflag_pt p0 l0 ⟨i, h13⟩
          have h2 := hflag_pt p l (σP ⟨i, h13⟩)
          change (flag p0 l0).getD i false = _ at h1
          rw [h1, h2, ← hp0]
          exact decide_eq_decide.mpr ⟨fun heq => by rw [heq], fun heq => hPinj _ _ heq⟩
        · rw [dite_eq_right h13, dite_eq_left hi]
          let j : Fin 13 := ⟨i - 13, by omega⟩
          have hij : i = 13 + j.val := by dsimp only [j]; omega
          have h1 := hflag_ln p0 l0 j
          rw [← hij] at h1
          have h2 := hflag_ln p l (σL j)
          rw [h1, h2, ← hl0]
          exact decide_eq_decide.mpr ⟨fun heq => by rw [heq], fun heq => hLinj _ _ heq⟩
      have h1 := hmEq (x10 (flag p0 l0)) (ext (flag p l))
        (hx10_len _ (hflag_len p0 l0)) (hext_len _ (hflag_len p l))
        (hSync (flag p l) (flag p0 l0) (hflag_len p l) (hflag_len p0 l0) hww') C.output hCout
      exact h1.symm.trans (hPos p0 l0 hpl0)
    have hN_hs : ∀ Q : Finset (Fin 13), isQuad Q → rv (run hs (ext (quad Q))) (m C.output) = false := by
      intro Q hQ
      let Q0 : Finset (Fin 13) := Finset.univ.filter (fun p' => σP p' ∈ Q)
      have hQ0_img : Q0.image σP = Q := by
        ext q; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Q0]
        constructor
        · rintro ⟨p', hp', rfl⟩; exact hp'
        · intro hq; obtain ⟨p', rfl⟩ := hPsurj q; exact ⟨p', hq, rfl⟩
      have hQ0_card : Q0.card = 4 := by
        have h1 := Finset.card_image_of_injective Q0 (fun a b h => hPinj a b h)
        rw [hQ0_img] at h1; rw [← h1, hQ.1]
      have hQ0_line : ∀ l0 : Fin 13, {p' ∈ Q0 | p' - l0 ∈ S}.card ≤ 2 := by
        intro l0
        have himg : ({p' ∈ Q0 | p' - l0 ∈ S}).image σP = {q ∈ Q | q - σL l0 ∈ S} := by
          ext q
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Q0]
          constructor
          · rintro ⟨p', ⟨hp'Q, hp'l⟩, rfl⟩
            exact ⟨hp'Q, (hPres p' l0).mpr hp'l⟩
          · rintro ⟨hqQ, hql⟩
            obtain ⟨p', rfl⟩ := hPsurj q
            exact ⟨p', ⟨hqQ, (hPres p' l0).mp hql⟩, rfl⟩
        have h1 := Finset.card_image_of_injective ({p' ∈ Q0 | p' - l0 ∈ S}) (fun a b h => hPinj a b h)
        rw [himg] at h1; rw [← h1]; exact hQ.2 (σL l0)
      have hww' : ∀ i < 26, (quad Q0).getD i false = (quad Q).getD (π i) false := by
        intro i hi
        dsimp only [π]
        by_cases h13 : i < 13
        · rw [dite_eq_left h13]
          have h1 := hquad_pt Q0 ⟨i, h13⟩
          have h2 := hquad_pt Q (σP ⟨i, h13⟩)
          change (quad Q0).getD i false = _ at h1
          rw [h1, h2]
          exact decide_eq_decide.mpr (by simp [Q0])
        · rw [dite_eq_right h13, dite_eq_left hi]
          let l0 : Fin 13 := ⟨i - 13, by omega⟩
          have hij : i = 13 + l0.val := by dsimp only [l0]; omega
          have h1 := hquad_ln Q0 l0
          rw [← hij] at h1
          have h2 := hquad_ln Q (σL l0)
          rw [h1, h2]
          refine decide_eq_decide.mpr ⟨fun h q hq => ?_, fun h p' hp' => ?_⟩
          · obtain ⟨p', rfl⟩ := hPsurj q
            have hp'0 : p' ∈ Q0 := by simp [Q0, hq]
            intro hm; exact h p' hp'0 ((hPres p' l0).mp hm)
          · have hq : σP p' ∈ Q := (Finset.mem_filter.mp hp').2
            intro hm; exact h (σP p') hq ((hPres p' l0).mpr hm)
      have h1 := hmEq (x10 (quad Q0)) (ext (quad Q))
        (hx10_len _ (hquad_len Q0)) (hext_len _ (hquad_len Q))
        (hSync (quad Q) (quad Q0) (hquad_len Q) (hquad_len Q0) hww') C.output hCout
      exact h1.symm.trans (hNeg Q0 ⟨hQ0_card, hQ0_line⟩)
    rcases hm : m C.output with b | out0
    · cases b
      · have h1 := hP_hs 0 0 h00_mem; rw [hm] at h1; cases h1
      · have h1 := hN_hs {0, 1, 2, 5} hQ0; rw [hm] at h1; cases h1
    have hout0_lt : out0 < 27 + hs.length := hmLt C.output hCout out0 hm
    have hP_out : ∀ p l : Fin 13, p - l ∈ S → (run hs (ext (flag p l))).getD out0 false = true := fun p l hpl => by
      have h1 := hP_hs p l hpl; rw [hm] at h1; exact h1
    have hN_out : ∀ Q : Finset (Fin 13), isQuad Q → (run hs (ext (quad Q))).getD out0 false = false := fun Q hQ => by
      have h1 := hN_hs Q hQ; rw [hm] at h1; exact h1
    have hout0_ge : 27 ≤ out0 := by
      by_contra hlt
      have hlt27 : out0 < 27 := by omega
      by_cases h26 : out0 = 26
      · subst h26
        have h1 := hP_out 2 2 h22_mem
        rw [run_input hs (ext (flag 2 2)) 26 (by rw [hext_len _ (hflag_len 2 2)]; omega)] at h1
        have h2 : (ext (flag 2 2)).getD 26 false = t.any (fun k => (flag 2 2).getD k false) := by
          dsimp only [ext]; rw [← hflag_len 2 2, getD_at]
        rw [h2] at h1
        have ht_false : t.any (fun k => (flag 2 2).getD k false) = false := by
          dsimp only [t]
          rcases hTargetMem with hmem | hmem <;>
            (simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem;
             rcases hmem with hmem | hmem <;> (rw [hmem]; decide +kernel))
        rw [ht_false] at h1; cases h1
      · have hlt26 : out0 < 26 := by omega
        by_cases h13 : out0 < 13
        · let p : Fin 13 := ⟨out0, h13⟩
          by_cases hp0 : p = 0
          · have h1 := hP_out 1 1 h11_mem
            rw [run_input hs (ext (flag 1 1)) out0 (by rw [hext_len _ (hflag_len 1 1)]; omega),
                getD_lt (flag 1 1) _ out0 (by rw [hflag_len]; exact hlt26)] at h1
            have h2 := hflag_pt 1 1 p; change (flag 1 1).getD out0 false = _ at h2
            rw [h2, hp0] at h1; simp at h1
          · have h1 := hP_out 0 0 h00_mem
            rw [run_input hs (ext (flag 0 0)) out0 (by rw [hext_len _ (hflag_len 0 0)]; omega),
                getD_lt (flag 0 0) _ out0 (by rw [hflag_len]; exact hlt26)] at h1
            have h2 := hflag_pt 0 0 p; change (flag 0 0).getD out0 false = _ at h2
            rw [h2] at h1; simp [hp0] at h1
        · let l : Fin 13 := ⟨out0 - 13, by omega⟩
          have ho : out0 = 13 + l.val := by dsimp only [l]; omega
          by_cases hl0 : l = 0
          · have h1 := hP_out 1 1 h11_mem
            rw [run_input hs (ext (flag 1 1)) out0 (by rw [hext_len _ (hflag_len 1 1)]; omega),
                getD_lt (flag 1 1) _ out0 (by rw [hflag_len]; exact hlt26), ho, hflag_ln, hl0] at h1
            simp at h1
          · have h1 := hP_out 0 0 h00_mem
            rw [run_input hs (ext (flag 0 0)) out0 (by rw [hext_len _ (hflag_len 0 0)]; omega),
                getD_lt (flag 0 0) _ out0 (by rw [hflag_len]; exact hlt26), ho, hflag_ln] at h1
            simp [hl0] at h1
    let kCut : ℕ := out0 - 27 + 1
    have hkCut_le : kCut ≤ hs.length := by omega
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨hs.take kCut, out0⟩
    have hDsz : D.size = kCut := List.length_take_of_le hkCut_le
    have hDout : D.output = 27 + (D.size - 1) := by change out0 = 27 + (D.size - 1); omega
    have hDrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 D := by
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
    have hDao2 : PEqualNP.TopForm.IsAO2 27 D :=
      ⟨fun g hg => (haok g (List.mem_of_mem_take hg)).1, hDrb, fun g hg => (haok g (List.mem_of_mem_take hg)).2⟩
    have hDeval : ∀ w : List Bool, w.length = 26 → D.eval (ext w) = (run hs (ext w)).getD out0 false := by
      intro w hw
      have hsp : hs = hs.take kCut ++ hs.drop kCut := (List.take_append_drop kCut hs).symm
      have h1 := run_prefix (hs.take kCut) (hs.drop kCut) (ext w) out0
        (by rw [hext_len w hw, List.length_take_of_le hkCut_le]; omega)
      rw [← hsp] at h1
      exact h1.symm
    have hCsz : C.size = C.gates.length := rfl
    by_cases hUses26 : ∃ j : Fin D.gates.length, 26 ∈ (D.gates.get j).inputs
    · have h63 : 63 ≤ D.size := by
        rcases hTargetMem with hmem | hmem
        · exact hSameSide D t hmem hDao2 hDout hUses26
            (fun p l hpl => (hDeval (flag p l) (hflag_len p l)).trans (hP_out p l hpl))
            (fun Q hQc hQl => (hDeval (quad Q) (hquad_len Q)).trans (hN_out Q ⟨hQc, hQl⟩))
        · exact hCross D t hmem hDao2 hDout hUses26
            (fun p l hpl => (hDeval (flag p l) (hflag_len p l)).trans (hP_out p l hpl))
            (fun Q hQc hQl => (hDeval (quad Q) (hquad_len Q)).trans (hN_out Q ⟨hQc, hQl⟩))
      omega
    · let sh (w : ℕ) : ℕ := if w < 26 then w else w - 1
      let shGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate := ⟨g.op, g.inputs.map sh⟩
      let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨D.gates.map shGate, out0 - 1⟩
      have hEsz : E.size = D.size := List.length_map shGate
      have hErb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 E := by
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
        have hwne26 : w ≠ 26 := by
          intro h26; subst h26
          apply hUses26
          refine ⟨⟨j, hj'⟩, ?_⟩
          rw [List.getD_eq_getElem _ _ hj'] at hw
          exact hw
        dsimp only [sh]; split_ifs <;> omega
      have hEao2 : PEqualNP.TopForm.IsAO2 26 E := by
        refine ⟨?_, hErb, ?_⟩
        · intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg; exact hDao2.1 g' hg'
        · intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
          change (g'.inputs.map sh).length = 2; rw [List.length_map]; exact hDao2.2.2 g' hg'
      have hEwires : ∀ (w : List Bool), w.length = 26 → ∀ i < 27 + D.gates.length, i ≠ 26 →
          (run E.gates w).getD (sh i) false = (run D.gates (ext w)).getD i false := by
        intro w hw i
        induction i using Nat.strong_induction_on with
        | ind i ih =>
          intro hilt hine26
          by_cases hi26 : i < 26
          · have hsh : sh i = i := by simp [sh, hi26]
            rw [hsh, run_input E.gates w i (by omega), run_input D.gates (ext w) i (by rw [hext_len w hw]; omega),
                getD_lt w _ i (by omega)]
          · let j : ℕ := i - 27
            have hij : i = 27 + j := by omega
            have hjD : j < D.gates.length := by omega
            have hjE : j < E.gates.length := by change j < E.size; rw [hEsz]; exact hjD
            have hsh : sh i = 26 + j := by simp [sh, show ¬ i < 26 by omega]; omega
            rw [hsh, hij]
            have rgE := run_gate E.gates w j hjE
            have rgD := run_gate D.gates (ext w) j hjD
            rw [hw] at rgE; rw [hext_len w hw] at rgD
            rw [rgE, rgD]
            have hEg : E.gates[j] = shGate D.gates[j] := List.getElem_map _
            rw [hEg]; dsimp only [shGate]; rw [List.map_map]
            congr 1
            refine List.map_congr_left fun u hu => ?_
            have hu' : u ∈ (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs := by
              rw [List.getD_eq_getElem _ _ hjD]; exact hu
            have hult := hDrb j hjD u hu'
            have hune26 : u ≠ 26 := fun h26 => hUses26 ⟨⟨j, hjD⟩, by subst h26; exact hu⟩
            have hsh_lt : sh u < 26 + j := by dsimp only [sh]; split_ifs <;> omega
            simp only [Function.comp, ite_eq_left hsh_lt, ite_eq_left hult]
            exact ih u (by omega) (by omega) hune26
      have hEeval : ∀ w : List Bool, w.length = 26 → E.eval w = D.eval (ext w) := by
        intro w hw
        have hsh_out : sh out0 = out0 - 1 := by simp [sh, show ¬ out0 < 26 by omega]
        have h1 := hEwires w hw out0 (by change out0 < 27 + D.size; omega) (by omega)
        rw [hsh_out] at h1; exact h1
      have h63 : 63 ≤ E.size := hNoExtra E hEao2 (by change out0 - 1 = 26 + (E.size - 1); omega)
        (fun p l hpl => (hEeval (flag p l) (hflag_len p l)).trans ((hDeval (flag p l) (hflag_len p l)).trans (hP_out p l hpl)))
        (fun Q hQc hQl => (hEeval (quad Q) (hquad_len Q)).trans ((hDeval (quad Q) (hquad_len Q)).trans (hN_out Q ⟨hQc, hQl⟩)))
      omega
  have subInj : ∀ c : Fin 13, ∀ a b : Fin 13, a - c = b - c → a = b := fun c a b h => by
    calc a = (a - c) + c := (sub_add_cancel a c).symm
      _ = (b - c) + c := by rw [h]
      _ = b := sub_add_cancel b c
  rcases hx2 : x2 with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inl false)
      (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht; subst ht; exact h) ?_
    intro w hw i hi
    by_cases h26 : i < 26
    · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
    · have hi26 : i = 26 := by omega
      subst hi26; rw [hx10_26 w hw, hx2]; simp [rv]
  · by_cases hu : u < 26
    · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inr u)
        (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht <;> subst ht <;> assumption) ?_
      intro w hw i hi
      by_cases h26 : i < 26
      · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
      · have hi26 : i = 26 := by omega
        subst hi26; rw [hx10_26 w hw, hx2]; simp [rv]
    · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inl false)
        (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht; subst ht; exact h) ?_
      intro w hw i hi
      by_cases h26 : i < 26
      · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
      · have hi26 : i = 26 := by omega
        subst hi26; rw [hx10_26 w hw, hx2]
        simp only [List.any_cons, List.any_nil, Bool.or_false, rv, show ¬(26 < 26) by omega, ↓reduceIte, Sum.elim_inl]
        exact List.getD_eq_default w false (by omega)
  · by_cases hu : u < 26
    · by_cases hv : v < 26
      · by_cases huv : u = v
        · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inr u)
            (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht <;> subst ht <;> assumption) ?_
          intro w hw i hi
          by_cases h26 : i < 26
          · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
          · have hi26 : i = 26 := by omega
            subst hi26; rw [hx10_26 w hw, hx2, huv]; simp [rv]
        · by_cases hu13 : u < 13
          · by_cases hv13 : v < 13
            · let p1 : Fin 13 := ⟨u, hu13⟩
              let p2 : Fin 13 := ⟨v, hv13⟩
              have hne : p2 - p1 ≠ 0 := by
                intro h0; apply huv
                have h1 : p2 = p1 := sub_eq_zero.mp h0
                exact (congrArg Fin.val h1).symm
              obtain ⟨k, hk⟩ := hcov_pp (p2 - p1) hne
              let σP : Fin 13 → Fin 13 := fun x => autP k (x - p1)
              let σL : Fin 13 → Fin 13 := fun x => autL k (x - p1)
              refine handlePair u v hu hv hx2 σP σL
                (fun a b h => subInj p1 a b ((haut_ok.1 k).1 _ _ h))
                (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                (fun a b h => subInj p1 a b ((haut_ok.2.1 k).1 _ _ h))
                (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                0 1 ?_ (Or.inl (by simp))
              dsimp only [σP]
              simp only [hu13, hv13, ↓reduceDIte, show (⟨u, hu13⟩ : Fin 13) - p1 = 0 from sub_self p1]
              rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
              · exact Or.inr ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
            · let p1 : Fin 13 := ⟨u, hu13⟩
              let l2 : Fin 13 := ⟨v - 13, by omega⟩
              by_cases hfl : (0 : Fin 13) - (l2 - p1) ∈ S
              · obtain ⟨k, hk1, hk2⟩ := hcov_flag (l2 - p1) hfl
                let σP : Fin 13 → Fin 13 := fun x => autP k (x - p1)
                let σL : Fin 13 → Fin 13 := fun x => autL k (x - p1)
                refine handlePair u v hu hv hx2 σP σL
                  (fun a b h => subInj p1 a b ((haut_ok.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun a b h => subInj p1 a b ((haut_ok.2.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                  0 13 ?_ (Or.inr (by simp))
                dsimp only [σP, σL]
                simp only [hu13, hv13, hv, ↓reduceDIte, show (⟨u, hu13⟩ : Fin 13) - p1 = 0 from sub_self p1]
                exact Or.inl ⟨congrArg Fin.val hk1, by rw [show (⟨v - 13, _⟩ : Fin 13) = l2 from rfl, hk2]; rfl⟩
              · obtain ⟨k, hk1, hk2⟩ := hcov_nonflag (l2 - p1) hfl
                let σP : Fin 13 → Fin 13 := fun x => autP k (x - p1)
                let σL : Fin 13 → Fin 13 := fun x => autL k (x - p1)
                refine handlePair u v hu hv hx2 σP σL
                  (fun a b h => subInj p1 a b ((haut_ok.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun a b h => subInj p1 a b ((haut_ok.2.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + p1, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                  0 14 ?_ (Or.inr (by simp))
                dsimp only [σP, σL]
                simp only [hu13, hv13, hv, ↓reduceDIte, show (⟨u, hu13⟩ : Fin 13) - p1 = 0 from sub_self p1]
                exact Or.inl ⟨congrArg Fin.val hk1, by rw [show (⟨v - 13, _⟩ : Fin 13) = l2 from rfl, hk2]; rfl⟩
          · by_cases hv13 : v < 13
            · let l1 : Fin 13 := ⟨u - 13, by omega⟩
              let p2 : Fin 13 := ⟨v, hv13⟩
              by_cases hfl : (0 : Fin 13) - (l1 - p2) ∈ S
              · obtain ⟨k, hk1, hk2⟩ := hcov_flag (l1 - p2) hfl
                let σP : Fin 13 → Fin 13 := fun x => autP k (x - p2)
                let σL : Fin 13 → Fin 13 := fun x => autL k (x - p2)
                refine handlePair u v hu hv hx2 σP σL
                  (fun a b h => subInj p2 a b ((haut_ok.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + p2, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun a b h => subInj p2 a b ((haut_ok.2.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + p2, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                  0 13 ?_ (Or.inr (by simp))
                dsimp only [σP, σL]
                simp only [hu13, hu, hv13, ↓reduceDIte, show (⟨v, hv13⟩ : Fin 13) - p2 = 0 from sub_self p2]
                exact Or.inr ⟨by rw [show (⟨u - 13, _⟩ : Fin 13) = l1 from rfl, hk2]; rfl, congrArg Fin.val hk1⟩
              · obtain ⟨k, hk1, hk2⟩ := hcov_nonflag (l1 - p2) hfl
                let σP : Fin 13 → Fin 13 := fun x => autP k (x - p2)
                let σL : Fin 13 → Fin 13 := fun x => autL k (x - p2)
                refine handlePair u v hu hv hx2 σP σL
                  (fun a b h => subInj p2 a b ((haut_ok.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + p2, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun a b h => subInj p2 a b ((haut_ok.2.1 k).1 _ _ h))
                  (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + p2, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                  (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                  0 14 ?_ (Or.inr (by simp))
                dsimp only [σP, σL]
                simp only [hu13, hu, hv13, ↓reduceDIte, show (⟨v, hv13⟩ : Fin 13) - p2 = 0 from sub_self p2]
                exact Or.inr ⟨by rw [show (⟨u - 13, _⟩ : Fin 13) = l1 from rfl, hk2]; rfl, congrArg Fin.val hk1⟩
            · let l1 : Fin 13 := ⟨u - 13, by omega⟩
              let l2 : Fin 13 := ⟨v - 13, by omega⟩
              have hne : l2 - l1 ≠ 0 := by
                intro h0; apply huv
                have h1 : l2 = l1 := sub_eq_zero.mp h0
                have h2 := congrArg Fin.val h1
                dsimp only [l1, l2] at h2; omega
              obtain ⟨k, hk⟩ := hcov_ll (l2 - l1) hne
              let σP : Fin 13 → Fin 13 := fun x => autP k (x - l1)
              let σL : Fin 13 → Fin 13 := fun x => autL k (x - l1)
              refine handlePair u v hu hv hx2 σP σL
                (fun a b h => subInj l1 a b ((haut_ok.1 k).1 _ _ h))
                (fun a => Exists.elim ((haut_ok.1 k).2 a) fun b hb => ⟨b + l1, by dsimp only [σP]; rw [add_sub_cancel_right]; exact hb⟩)
                (fun a b h => subInj l1 a b ((haut_ok.2.1 k).1 _ _ h))
                (fun a => Exists.elim ((haut_ok.2.1 k).2 a) fun b hb => ⟨b + l1, by dsimp only [σL]; rw [add_sub_cancel_right]; exact hb⟩)
                (fun p l => by dsimp only [σP, σL]; rw [haut_ok.2.2 k, sub_sub_sub_cancel_right])
                13 14 ?_ (Or.inl (by simp))
              dsimp only [σL]
              simp only [hu13, hu, hv13, hv, ↓reduceDIte]
              rw [show (⟨u - 13, _⟩ : Fin 13) - l1 = 0 from sub_self l1,
                  show (⟨v - 13, _⟩ : Fin 13) = l2 from rfl]
              rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
              · exact Or.inr ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
      · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inr u)
          (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht <;> subst ht <;> assumption) ?_
        intro w hw i hi
        by_cases h26 : i < 26
        · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
        · have hi26 : i = 26 := by omega
          subst hi26; rw [hx10_26 w hw, hx2]
          simp only [List.any_cons, List.any_nil, Bool.or_false, rv, show ¬(26 < 26) by omega, ↓reduceIte, Sum.elim_inr]
          rw [show w.getD v false = false from List.getD_eq_default w false (by omega), Bool.or_false]
    · by_cases hv : v < 26
      · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inr v)
          (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht <;> subst ht <;> assumption) ?_
        intro w hw i hi
        by_cases h26 : i < 26
        · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
        · have hi26 : i = 26 := by omega
          subst hi26; rw [hx10_26 w hw, hx2]
          simp only [List.any_cons, List.any_nil, Bool.or_false, rv, show ¬(26 < 26) by omega, ↓reduceIte, Sum.elim_inr]
          rw [show w.getD u false = false from List.getD_eq_default w false (by omega), Bool.false_or]
      · refine handleNoExtraMap (fun i => if i < 26 then Sum.inr i else Sum.inl false)
          (fun i _ t ht => by by_cases h : i < 26 <;> simp [h] at ht; subst ht; exact h) ?_
        intro w hw i hi
        by_cases h26 : i < 26
        · rw [hx10_lt w i (by omega)]; dsimp only [rv, Sum.elim]; rw [if_pos h26]
        · have hi26 : i = 26 := by omega
          subst hi26; rw [hx10_26 w hw, hx2]
          simp only [List.any_cons, List.any_nil, Bool.or_false, rv, show ¬(26 < 26) by omega, ↓reduceIte, Sum.elim_inl]
          rw [show w.getD u false = false from List.getD_eq_default w false (by omega),
              show w.getD v false = false from List.getD_eq_default w false (by omega), Bool.or_false]; rfl
  · simp [hx2] at hx2len
