import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3083_1
    (firstNotAt1 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 = (1 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size)
    (firstNotAt2 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 = (2 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size)
    (firstNotAt3 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 = (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 ≤ (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size := by
  intro x1 C hFan hNot hFirst hFun hRead
  obtain ⟨a, b, hab, ha3, hna, hnb, hall⟩ := hNot
  have ha0 : (a : ℕ) ≠ 0 := by
    intro ha0
    have hlen : C.gates ≠ [] := List.ne_nil_of_length_pos (lt_of_le_of_lt (Nat.zero_le _) a.isLt)
    obtain ⟨g, gs, hgs⟩ := List.exists_cons_of_ne_nil hlen
    have hg : g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      have e1 : C.gates[(a : ℕ)]? = some (C.gates.get a) := List.getElem?_eq_getElem a.isLt
      rw [ha0] at e1
      have e3 : C.gates[0]? = some g := by rw [hgs]; rfl
      have e2 : g = C.gates.get a := Option.some.inj (e3.symm.trans e1)
      rw [e2]
      exact hna
    let F : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hpre : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        ∃ t, List.foldl F w l = w ++ t := by
      intro l
      induction l with
      | nil => intro w; exact ⟨[], (List.append_nil w).symm⟩
      | cons h l ih =>
        intro w
        obtain ⟨t, ht⟩ := ih (F w h)
        refine ⟨[h.op.eval (h.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
        rw [List.foldl_cons, ht]
        exact List.append_assoc _ _ _
    let x : List Bool := List.ofFn (fun _ : Fin 9 => false)
    have hx : ∀ i : ℕ, x.getD i false = false := by
      intro i
      rw [List.getD_eq_getElem?_getD]
      rcases h : x[i]? with _ | c
      · rfl
      · have hm : c ∈ x := List.mem_of_getElem? h
        have : c = false := by
          rw [List.mem_ofFn] at hm
          obtain ⟨_, hy⟩ := hm
          exact hy.symm
        rw [this]
        rfl
    have hv : g.op.eval (g.inputs.map fun i => x.getD i false) = true := by
      rw [hg]
      rcases g.inputs with _ | ⟨c, l⟩
      · rfl
      · show (!(x.getD c false)) = true
        rw [hx c]
        rfl
    have hw : C.wires x = List.foldl F x C.gates := rfl
    have h9 := hFirst (fun _ => false)
    change (C.wires x).getD 9 false = false at h9
    rw [hw, hgs, List.foldl_cons] at h9
    obtain ⟨t, ht⟩ := hpre gs (F x g)
    rw [ht] at h9
    have hxl : x.length = 9 := List.length_ofFn
    have : ((x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) ++ t).getD 9 false
        = g.op.eval (g.inputs.map fun i => x.getD i false) := by
      rw [List.getD_append _ _ _ _ (by rw [List.length_append, hxl]; exact Nat.lt_succ_self 9)]
      rw [List.getD_append_right _ _ _ _ (by rw [hxl])]
      rw [hxl]
      rfl
    change ((x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) ++ t).getD 9 false = false at h9
    rw [this, hv] at h9
    exact Bool.noConfusion h9
  have hcase : (a : ℕ) = 1 ∨ (a : ℕ) = 2 ∨ (a : ℕ) = 3 := by omega
  rcases hcase with h | h | h
  · exact firstNotAt1 C hFan ⟨a, b, hab, h, hna, hnb, hall⟩ hFirst hFun hRead
  · exact firstNotAt2 C hFan ⟨a, b, hab, h, hna, hnb, hall⟩ hFirst hFun hRead
  · exact firstNotAt3 C hFan ⟨a, b, hab, h, hna, hnb, hall⟩ hFirst hFun hRead
