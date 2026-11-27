import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_650_43 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 28 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 34 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C1, hm1, hs1, he1⟩ ⟨C2, hm2, hs2, he2⟩
  let shiftIdx : ℕ → ℕ → ℕ → ℕ := fun n off i => if i < n then i else i + off
  let shiftGate : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun n off g => ⟨g.op, g.inputs.map (shiftIdx n off)⟩
  let off := C1.gates.length
  let out1 := if C1.output < 26 + off then C1.output else 26 + off + C2.gates.length
  let out2 := shiftIdx 26 off C2.output
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C1.gates ++ C2.gates.map (shiftGate 26 off) ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out1, out2]⟩]
      output := 26 + off + C2.gates.length }
  have wires_len : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (inp : List Bool),
      (D.wires inp).length = inp.length + D.gates.length := by
    intro D inp
    change (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp).length =
      inp.length + D.gates.length
    have h : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
          acc.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro acc; simp
      | cons g t ih =>
        intro acc
        simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
        omega
    exact h D.gates inp
  have getD_append_lt : ∀ (l r : List Bool) (i : ℕ), i < l.length → (l ++ r).getD i false = l.getD i false := by
    intro l r i h; simp [List.getD, List.getElem?_append_left h]
  have getD_append_ge : ∀ (l r : List Bool) (i : ℕ), l.length ≤ i → (l ++ r).getD i false = r.getD (i - l.length) false := by
    intro l r i h; simp [List.getD, List.getElem?_append_right h]
  have foldl_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      ∃ ext : List Bool,
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc = acc ++ ext := by
    intro gs
    induction gs with
    | nil => intro acc; exact ⟨[], by simp⟩
    | cons g t ih =>
      intro acc
      obtain ⟨ext, hext⟩ := ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
      refine ⟨[g.op.eval (g.inputs.map fun i => acc.getD i false)] ++ ext, ?_⟩
      simpa [List.foldl_cons, List.append_assoc] using hext
  have foldl_shift : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (inp : List Bool), inp.length = 26 →
      ∀ (w1 : List Bool), w1.length = 26 + off →
      (∀ i < 26, w1.getD i false = inp.getD i false) →
      ∀ (ext : List Bool),
        (gs.map (shiftGate 26 off)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w1 ++ ext) =
          w1 ++ (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (inp ++ ext)).drop 26 := by
    intro gs
    induction gs with
    | nil =>
      intro inp hn w1 _ _ ext
      simp [List.drop_append_of_le_length (le_of_eq hn.symm), hn]
    | cons g t ih =>
      intro inp hn w1 hw1 hpref ext
      simp only [List.map_cons, List.foldl_cons]
      have harg : ((shiftGate 26 off g).inputs.map fun i => (w1 ++ ext).getD i false) =
          (g.inputs.map fun i => (inp ++ ext).getD i false) := by
        simp only [shiftGate, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply, shiftIdx]
        split_ifs with hi
        · rw [getD_append_lt w1 ext i (by omega), getD_append_lt inp ext i (by omega)]
          exact hpref i hi
        · rw [getD_append_ge w1 ext (i + off) (by omega), getD_append_ge inp ext i (by omega)]
          congr 1; omega
      have hstep := ih inp hn w1 hw1 hpref (ext ++ [g.op.eval (g.inputs.map fun i => (inp ++ ext).getD i false)])
      simpa only [shiftGate, harg, List.append_assoc] using hstep
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (h | ⟨g', hg', rfl⟩) | rfl
    · exact hm1 g h
    · obtain ⟨hop, hlen⟩ := hm2 g' hg'
      exact ⟨hop, by simpa [shiftGate] using hlen⟩
    · exact ⟨by simp, by simp⟩
  · have : C.gates.length = C1.gates.length + C2.gates.length + 1 := by
      simp [C, List.length_append, List.length_map]; omega
    change C.gates.length ≤ 63
    change C1.gates.length ≤ 28 at hs1
    change C2.gates.length ≤ 34 at hs2
    omega
  · intro x
    have heval : C.eval (List.ofFn x) = (C1.eval (List.ofFn x) || C2.eval (List.ofFn x)) := by
      change (C.wires (List.ofFn x)).getD C.output false =
        ((C1.wires (List.ofFn x)).getD C1.output false || (C2.wires (List.ofFn x)).getD C2.output false)
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false =
        ((C1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C1.output false ||
         (C2.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C2.output false)
      dsimp only [C]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      set inp := List.ofFn x
      have hn : inp.length = 26 := by simp [inp]
      set w1 := C1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp
      have hw1_len : w1.length = 26 + off := by
        have := wires_len C1 inp; rw [hn] at this; exact this
      have hpref : ∀ i < 26, w1.getD i false = inp.getD i false := by
        obtain ⟨ext, hext⟩ := foldl_prefix C1.gates inp
        intro i hi
        have hw1eq : w1 = inp ++ ext := hext
        rw [hw1eq, getD_append_lt inp ext i (by omega)]
      have h2 := foldl_shift C2.gates inp hn w1 hw1_len hpref []
      simp only [List.append_nil] at h2
      rw [h2]
      set w2 := C2.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp
      have hw2_len : w2.length = 26 + C2.gates.length := by
        have := wires_len C2 inp; rw [hn] at this; exact this
      have hlen12 : (w1 ++ w2.drop 26).length = 26 + off + C2.gates.length := by
        simp [hw1_len, hw2_len]
      rw [getD_append_ge (w1 ++ w2.drop 26) _ _ (by omega)]
      have hzero : 26 + off + C2.gates.length - (w1 ++ w2.drop 26).length = 0 := by omega
      rw [hzero]
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      change ((w1 ++ w2.drop 26)[out1]?.getD false || ((w1 ++ w2.drop 26)[out2]?.getD false || false)) =
        (w1[C1.output]?.getD false || w2[C2.output]?.getD false)
      have hv1 : (w1 ++ w2.drop 26)[out1]?.getD false = w1[C1.output]?.getD false := by
        dsimp only [out1]
        split_ifs with h
        · exact getD_append_lt w1 (w2.drop 26) C1.output (by omega)
        · simp [List.getElem?_eq_none (by omega : (w1 ++ w2.drop 26).length ≤ 26 + off + C2.gates.length),
            List.getElem?_eq_none (by omega : w1.length ≤ C1.output)]
      have hv2 : (w1 ++ w2.drop 26)[out2]?.getD false = w2[C2.output]?.getD false := by
        dsimp only [out2, shiftIdx]
        split_ifs with h
        · have h1 := getD_append_lt w1 (w2.drop 26) C2.output (by omega)
          have h2' := hpref C2.output h
          obtain ⟨ext2, hext2⟩ := foldl_prefix C2.gates inp
          have hw2eq : w2 = inp ++ ext2 := hext2
          have h3 := getD_append_lt inp ext2 C2.output (by omega)
          simpa only [List.getD, hw2eq] using h1.trans (h2'.trans h3.symm)
        · have h1 := getD_append_ge w1 (w2.drop 26) (C2.output + off) (by omega)
          simp only [List.getD, List.getElem?_drop] at h1
          rw [h1]; congr 2; omega
      rw [hv1, hv2, Bool.or_false]
    rw [heval, Bool.or_eq_true, he1 x, he2 x]
    have hE : ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) =
        [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24)] ++
        [(6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] := rfl
    rw [hE]
    constructor
    · rintro (⟨u, v, hmem, hu, hv⟩ | ⟨u, v, hmem, hu, hv⟩)
      · exact ⟨u, v, List.mem_append_left _ hmem, hu, hv⟩
      · exact ⟨u, v, List.mem_append_right _ hmem, hu, hv⟩
    · rintro ⟨u, v, hmem, hu, hv⟩
      rcases List.mem_append.mp hmem with h1 | h2
      · exact Or.inl ⟨u, v, h1, hu, hv⟩
      · exact Or.inr ⟨u, v, h2, hu, hv⟩
