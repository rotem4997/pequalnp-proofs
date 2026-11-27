import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def natStep (u : List ℕ) (g : Gate) : List ℕ :=
  u ++ [if g.op.eval [false, true] = true then
    (u.getD (g.inputs.getD 0 0) 0) ||| (u.getD (g.inputs.getD 1 0) 0) else
    (u.getD (g.inputs.getD 0 0) 0) &&& (u.getD (g.inputs.getD 1 0) 0)]

theorem foldl_natStep_length (gs : List Gate) (u : List ℕ) :
    (gs.foldl natStep u).length = u.length + gs.length := by
  induction gs generalizing u with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, natStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem build_gates (W : List ℕ) (t : ℕ → ℕ) (ht0 : ∀ i < W.length, t i = W.getD i 0) :
    ∀ m : ℕ,
      (∀ j < m, ∃ a < W.length + j, ∃ b < W.length + j,
        t (W.length + j) = t a ||| t b ∨ t (W.length + j) = t a &&& t b) →
      ∃ gs : List Gate, gs.length = m ∧ IsAO2 W.length ⟨gs, 0⟩ ∧
        ∀ k < W.length + m, (gs.foldl natStep W).getD k 0 = t k := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], rfl, ⟨(by intro g hg; cases hg), (by intro j hj; simp at hj), (by intro g hg; cases hg)⟩, ?_⟩
    intro k hk
    exact (ht0 k (by omega)).symm
  | succ m ih =>
    intro hstep
    obtain ⟨gs, hlen, hao, hev⟩ := ih (fun j hj => hstep j (by omega))
    rcases hstep m (Nat.lt_succ_self m) with ⟨a, ha, b, hb, hval⟩
    let op : GateOp := if t (W.length + m) = t a ||| t b then GateOp.or else GateOp.and
    let g : Gate := ⟨op, [a, b]⟩
    have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      dsimp only [g, op]; split_ifs <;> simp
    have hao' : IsAO2 W.length ⟨gs ++ [g], 0⟩ := by
      rcases hao with ⟨hAO, hRB, hL⟩
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hAO q hq
        · exact hgop
      · intro j hj i hi
        change j < (gs ++ [g]).length at hj
        by_cases hjlt : j < gs.length
        · have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
          rw [hga] at hi
          exact hRB j hjlt i hi
        · have hjeq : j = gs.length := by simp at hj; omega
          subst hjeq
          have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
            simp [gateAt, List.getD_eq_getElem?_getD]
          rw [hga] at hi
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
      · intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hL q hq
        · rfl
    refine ⟨gs ++ [g], by simp [hlen], hao', ?_⟩
    intro k hk
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set u := gs.foldl natStep W
    have hulen : u.length = W.length + m := by rw [foldl_natStep_length, hlen]
    by_cases hklt : k < W.length + m
    · dsimp only [natStep]
      rw [List.getD_append u _ 0 k (by omega)]
      exact hev k hklt
    · have hkeq : k = W.length + m := by omega
      subst hkeq
      dsimp only [natStep]
      have hlast : (u ++ [if g.op.eval [false, true] = true then
          (u.getD (g.inputs.getD 0 0) 0) ||| (u.getD (g.inputs.getD 1 0) 0) else
          (u.getD (g.inputs.getD 0 0) 0) &&& (u.getD (g.inputs.getD 1 0) 0)]).getD u.length 0 =
          if g.op.eval [false, true] = true then
            (u.getD (g.inputs.getD 0 0) 0) ||| (u.getD (g.inputs.getD 1 0) 0) else
            (u.getD (g.inputs.getD 0 0) 0) &&& (u.getD (g.inputs.getD 1 0) 0) := by
        simp [List.getD_eq_getElem?_getD]
      rw [← hulen, hlast, hulen]
      have hg0 : g.inputs.getD 0 0 = a := rfl
      have hg1 : g.inputs.getD 1 0 = b := rfl
      rw [hg0, hg1, hev a ha, hev b hb]
      by_cases h1 : t (W.length + m) = t a ||| t b
      · have hop : g.op.eval [false, true] = true := by simp [g, op, h1, GateOp.eval]
        rw [hop]; simp [h1]
      · have hop : g.op.eval [false, true] = false := by simp [g, op, h1, GateOp.eval]
        rw [hop]
        rcases hval with h | h
        · exact absurd h h1
        · simp [h]

theorem main_proof :
    ∀ (W : List ℕ) (m : ℕ) (t : ℕ → ℕ),
      (∀ i < W.length, t i = W.getD i 0) →
      (∀ j < m, ∃ a < W.length + j, ∃ b < W.length + j,
        t (W.length + j) = t a ||| t b ∨ t (W.length + j) = t a &&& t b) →
      ∀ o < W.length + m, ∃ C : Circuit, C.size ≤ m ∧ IsAO2 W.length C ∧
        (C.gates.foldl (fun u g => u ++ [if g.op.eval [false, true] = true then
          (u.getD (g.inputs.getD 0 0) 0) ||| (u.getD (g.inputs.getD 1 0) 0) else
          (u.getD (g.inputs.getD 0 0) 0) &&& (u.getD (g.inputs.getD 1 0) 0)]) W).getD C.output 0 = t o := by
  intro W m t ht0 hstep o ho
  obtain ⟨gs, hlen, hao, hev⟩ := build_gates W t ht0 m hstep
  refine ⟨⟨gs, o⟩, by simp [Circuit.size, hlen], hao, hev o ho⟩

end PEqualNP.Outside.L_meta_18904_aux

theorem PEqualNP.Outside.L_meta_18904 : (∀ (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ), (∀ x4 < x1.length, x3 x4 = x1.getD x4 (0 : ℕ)) → (∀ x5 < x2, ∃ x7 < x1.length + x5, ∃ x8 < x1.length + x5, x3 (x1.length + x5) = x3 x7 ||| x3 x8 ∨ x3 (x1.length + x5) = x3 x7 &&& x3 x8) → ∀ x6 < x1.length + x2, ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size ≤ x2 ∧ PEqualNP.TopForm.IsAO2 x1.length x8 ∧ (List.foldl (fun (x9 : List ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) => x9 ++ [if x10.op.eval [Bool.false, Bool.true] = Bool.true then x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]) x1 x8.gates).getD x8.output (0 : ℕ) = x3 x6)  := by
  exact PEqualNP.Outside.L_meta_18904_aux.main_proof
