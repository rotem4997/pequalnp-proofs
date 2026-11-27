import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18729_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def C : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [27, 28]⟩,
  ⟨.and, [15, 29]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [6, 12]⟩,
  ⟨.or, [31, 32]⟩,
  ⟨.and, [16, 33]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [9, 2]⟩,
  ⟨.or, [35, 36]⟩,
  ⟨.and, [19, 37]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [10, 3]⟩,
  ⟨.or, [39, 40]⟩,
  ⟨.and, [20, 41]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.or, [11, 4]⟩,
  ⟨.or, [43, 44]⟩,
  ⟨.and, [21, 45]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [12, 5]⟩,
  ⟨.or, [47, 48]⟩,
  ⟨.and, [22, 49]⟩,
  ⟨.or, [30, 34]⟩,
  ⟨.or, [51, 38]⟩,
  ⟨.or, [52, 42]⟩,
  ⟨.or, [53, 46]⟩,
  ⟨.or, [54, 50]⟩], 55⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem prefixRead (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem stepLength (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem gateRead (gs : List Gate) (w : List Bool) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (h : ∀ k ∈ g.inputs, k < w.length + i) :
    let W := gs.foldl step w
    W.getD (w.length + i) false = g.op.eval (g.inputs.map fun k => W.getD k false) := by
  induction gs generalizing w i with
  | nil => simp at hg
  | cons q qs ih =>
    cases i with
    | zero =>
      simp at hg
      subst q
      simp only [List.foldl_cons, Nat.add_zero] at h ⊢
      rw [prefixRead _ _ _ (by rw [stepLength]; omega)]
      have hx : (step w g).getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
        simp [step]
      rw [hx]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [prefixRead _ _ _ (by rw [stepLength]; specialize h k hk; omega)]
      exact (List.getD_append _ _ _ _ (h k hk)).symm
    | succ i =>
      have H : (step w q).length + i = w.length + (i + 1) := by rw [stepLength]; omega
      simpa only [H, List.foldl_cons] using
        ih (step w q) i (by simpa using hg) (fun k hk => by simpa [H] using h k hk)

set_option maxHeartbeats 2000000 in
theorem eval_eq (x : Fin 26 → Bool) :
    C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔
      ∃ l ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 13)),
        x (Fin.natAdd 13 l) = true ∧
        (x (Fin.castAdd 13 l) = true ∨ x (Fin.castAdd 13 (l + 1)) = true ∨
         x (Fin.castAdd 13 (l + 3)) = true ∨ x (Fin.castAdd 13 (l + 9)) = true) := by
  let bank := List.ofFn x ++ [x 0 || x 1]
  let W (idx : ℕ) := (C.gates.foldl step bank).getD idx false
  have hlen : bank.length = 27 := by simp [bank]
  have orig (k : Fin 26) : W k.val = x k := by
    change (C.gates.foldl step bank).getD k.val false = _
    rw [prefixRead _ _ _ (by rw [hlen]; have := k.isLt; omega)]
    change (List.ofFn x ++ [x 0 || x 1]).getD k.val false = _
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
    simp only [List.getElem_ofFn, Fin.eta]
  have readGate (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g)
      (hb : ∀ i ∈ g.inputs, i < 27 + k) :
      W (27 + k) = g.op.eval (g.inputs.map W) := by
    have r := gateRead C.gates bank k g hg
    have out := r (fun i hi => by rw [hlen]; exact hb i hi)
    change W (bank.length + k) = g.op.eval (g.inputs.map W) at out
    simpa only [hlen] using out
  have v0 : W 27 = (W 2 || W 3) := by
    simpa [GateOp.eval] using readGate 0 ⟨.or, [2, 3]⟩ rfl (by decide)
  have v1 : W 28 = (W 5 || W 11) := by
    simpa [GateOp.eval] using readGate 1 ⟨.or, [5, 11]⟩ rfl (by decide)
  have v2 : W 29 = (W 27 || W 28) := by
    simpa [GateOp.eval] using readGate 2 ⟨.or, [27, 28]⟩ rfl (by decide)
  have v3 : W 30 = (W 15 && W 29) := by
    simpa [GateOp.eval] using readGate 3 ⟨.and, [15, 29]⟩ rfl (by decide)
  have v4 : W 31 = (W 3 || W 4) := by
    simpa [GateOp.eval] using readGate 4 ⟨.or, [3, 4]⟩ rfl (by decide)
  have v5 : W 32 = (W 6 || W 12) := by
    simpa [GateOp.eval] using readGate 5 ⟨.or, [6, 12]⟩ rfl (by decide)
  have v6 : W 33 = (W 31 || W 32) := by
    simpa [GateOp.eval] using readGate 6 ⟨.or, [31, 32]⟩ rfl (by decide)
  have v7 : W 34 = (W 16 && W 33) := by
    simpa [GateOp.eval] using readGate 7 ⟨.and, [16, 33]⟩ rfl (by decide)
  have v8 : W 35 = (W 6 || W 7) := by
    simpa [GateOp.eval] using readGate 8 ⟨.or, [6, 7]⟩ rfl (by decide)
  have v9 : W 36 = (W 9 || W 2) := by
    simpa [GateOp.eval] using readGate 9 ⟨.or, [9, 2]⟩ rfl (by decide)
  have v10 : W 37 = (W 35 || W 36) := by
    simpa [GateOp.eval] using readGate 10 ⟨.or, [35, 36]⟩ rfl (by decide)
  have v11 : W 38 = (W 19 && W 37) := by
    simpa [GateOp.eval] using readGate 11 ⟨.and, [19, 37]⟩ rfl (by decide)
  have v12 : W 39 = (W 7 || W 8) := by
    simpa [GateOp.eval] using readGate 12 ⟨.or, [7, 8]⟩ rfl (by decide)
  have v13 : W 40 = (W 10 || W 3) := by
    simpa [GateOp.eval] using readGate 13 ⟨.or, [10, 3]⟩ rfl (by decide)
  have v14 : W 41 = (W 39 || W 40) := by
    simpa [GateOp.eval] using readGate 14 ⟨.or, [39, 40]⟩ rfl (by decide)
  have v15 : W 42 = (W 20 && W 41) := by
    simpa [GateOp.eval] using readGate 15 ⟨.and, [20, 41]⟩ rfl (by decide)
  have v16 : W 43 = (W 8 || W 9) := by
    simpa [GateOp.eval] using readGate 16 ⟨.or, [8, 9]⟩ rfl (by decide)
  have v17 : W 44 = (W 11 || W 4) := by
    simpa [GateOp.eval] using readGate 17 ⟨.or, [11, 4]⟩ rfl (by decide)
  have v18 : W 45 = (W 43 || W 44) := by
    simpa [GateOp.eval] using readGate 18 ⟨.or, [43, 44]⟩ rfl (by decide)
  have v19 : W 46 = (W 21 && W 45) := by
    simpa [GateOp.eval] using readGate 19 ⟨.and, [21, 45]⟩ rfl (by decide)
  have v20 : W 47 = (W 9 || W 10) := by
    simpa [GateOp.eval] using readGate 20 ⟨.or, [9, 10]⟩ rfl (by decide)
  have v21 : W 48 = (W 12 || W 5) := by
    simpa [GateOp.eval] using readGate 21 ⟨.or, [12, 5]⟩ rfl (by decide)
  have v22 : W 49 = (W 47 || W 48) := by
    simpa [GateOp.eval] using readGate 22 ⟨.or, [47, 48]⟩ rfl (by decide)
  have v23 : W 50 = (W 22 && W 49) := by
    simpa [GateOp.eval] using readGate 23 ⟨.and, [22, 49]⟩ rfl (by decide)
  have v24 : W 51 = (W 30 || W 34) := by
    simpa [GateOp.eval] using readGate 24 ⟨.or, [30, 34]⟩ rfl (by decide)
  have v25 : W 52 = (W 51 || W 38) := by
    simpa [GateOp.eval] using readGate 25 ⟨.or, [51, 38]⟩ rfl (by decide)
  have v26 : W 53 = (W 52 || W 42) := by
    simpa [GateOp.eval] using readGate 26 ⟨.or, [52, 42]⟩ rfl (by decide)
  have v27 : W 54 = (W 53 || W 46) := by
    simpa [GateOp.eval] using readGate 27 ⟨.or, [53, 46]⟩ rfl (by decide)
  have v28 : W 55 = (W 54 || W 50) := by
    simpa [GateOp.eval] using readGate 28 ⟨.or, [54, 50]⟩ rfl (by decide)
  have x0 : W 0 = x 0 := orig 0
  have x1 : W 1 = x 1 := orig 1
  have x2 : W 2 = x 2 := orig 2
  have x3 : W 3 = x 3 := orig 3
  have x4 : W 4 = x 4 := orig 4
  have x5 : W 5 = x 5 := orig 5
  have x6 : W 6 = x 6 := orig 6
  have x7 : W 7 = x 7 := orig 7
  have x8 : W 8 = x 8 := orig 8
  have x9 : W 9 = x 9 := orig 9
  have x10 : W 10 = x 10 := orig 10
  have x11 : W 11 = x 11 := orig 11
  have x12 : W 12 = x 12 := orig 12
  have x13 : W 13 = x 13 := orig 13
  have x14 : W 14 = x 14 := orig 14
  have x15 : W 15 = x 15 := orig 15
  have x16 : W 16 = x 16 := orig 16
  have x17 : W 17 = x 17 := orig 17
  have x18 : W 18 = x 18 := orig 18
  have x19 : W 19 = x 19 := orig 19
  have x20 : W 20 = x 20 := orig 20
  have x21 : W 21 = x 21 := orig 21
  have x22 : W 22 = x 22 := orig 22
  have x23 : W 23 = x 23 := orig 23
  have x24 : W 24 = x 24 := orig 24
  have x25 : W 25 = x 25 := orig 25
  change W 55 = true ↔ _
  rw [v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0]
  simp only [x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x15, x16, x19, x20, x21, x22]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h)
    · exact ⟨2, Or.inl rfl, h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
    · exact ⟨3, Or.inr (Or.inl rfl), h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
    · exact ⟨6, Or.inr (Or.inr (Or.inl rfl)), h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
    · exact ⟨8, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), h.1, by rcases h.2 with (h1|h1)|(h1|h1) <;> simp [h1]⟩
  · rintro ⟨l, hl, hxl, hxp⟩
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩))
    · exact Or.inl (Or.inr ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩)
    · exact Or.inr ⟨hxl, by rcases hxp with a|b|c|d <;> [exact Or.inl (Or.inl a); exact Or.inl (Or.inr b); exact Or.inr (Or.inl c); exact Or.inr (Or.inr d)]⟩

theorem main_proof :
    let inc (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let row (p l : Fin 13) : Fin 26 → Bool := fun i =>
      decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    let input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
    ∃ D : Circuit, D.size ≤ 29 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
      IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      (∀ p l : Fin 13, l ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 13)) → inc p l →
        D.eval (input (row p l)) = true) ∧
      ∀ x : Fin 26 → Bool, D.eval (input x) = true →
        ∃ p l : Fin 13, inc p l ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  refine ⟨C, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro p l hl hinc
    rw [eval_eq]
    refine ⟨l, hl, by simp, ?_⟩
    rcases hinc with rfl | rfl | rfl | rfl <;> simp
  · intro x hx
    rw [eval_eq] at hx
    obtain ⟨l, _, hxl, hxp⟩ := hx
    rcases hxp with h | h | h | h
    · exact ⟨l, l, Or.inl rfl, h, hxl⟩
    · exact ⟨l + 1, l, Or.inr (Or.inl rfl), h, hxl⟩
    · exact ⟨l + 3, l, Or.inr (Or.inr (Or.inl rfl)), h, hxl⟩
    · exact ⟨l + 9, l, Or.inr (Or.inr (Or.inr rfl)), h, hxl⟩

end PEqualNP.Outside.L_meta_18729_aux

theorem PEqualNP.Outside.L_meta_18729 : (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (29 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) := by
  exact PEqualNP.Outside.L_meta_18729_aux.main_proof
