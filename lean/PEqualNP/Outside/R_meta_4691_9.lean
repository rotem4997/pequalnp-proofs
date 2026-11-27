import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4691_9 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 → C.output + 1 = 14 + C.size →
      PEqualNP.TopForm.IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let w07 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 7)
      let w00 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 0)
      let w77 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 7 7)
      let op : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd C
      let c : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 14 C
      let p (g : ℕ) : Prop :=
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        w07 (14 + g) = true ∧ w00 (14 + g) = false ∧ w77 (14 + g) = false
      let s (g : ℕ) : Prop := p g ∧ ∀ b : Fin 2, w00 (op g b) = true ∨ w77 (op g b) = true
      ∀ i j : ℕ, i < j → ¬c i j → ¬c j i → c i (C.size - 1) → c j (C.size - 1) → p i → p j →
        (∀ b : Fin 2, w00 (op i b) = false) → (∀ b : Fin 2, w77 (op j b) = false) →
        (∃ k : ℕ, s k ∧ c k i ∧ c k j ∧ (∃ b : Fin 2, w77 (op i b) = true) ∧ (∃ b : Fin 2, w00 (op j b) = true)) → False) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 → C.output + 1 = 14 + C.size →
      PEqualNP.TopForm.IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let w07 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 7)
      let w00 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 0)
      let w77 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 7 7)
      let op : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd C
      let c : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 14 C
      let p (g : ℕ) : Prop :=
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        w07 (14 + g) = true ∧ w00 (14 + g) = false ∧ w77 (14 + g) = false
      let s (g : ℕ) : Prop := p g ∧ ∀ b : Fin 2, w00 (op g b) = true ∨ w77 (op g b) = true
      ∀ i j : ℕ, i < j → ¬c i j → ¬c j i → c i (C.size - 1) → c j (C.size - 1) → p i → p j →
        (∀ b : Fin 2, w00 (op i b) = false) → (∀ b : Fin 2, w77 (op j b) = false) →
        (∃ k : ℕ, s k ∧ c k i ∧ c k j ∧ ((∀ b : Fin 2, w77 (op i b) = false) ∨ (∀ b : Fin 2, w00 (op j b) = false))) → False) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 → C.output + 1 = 14 + C.size →
      PEqualNP.TopForm.IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let w07 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 7)
      let w00 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 0 0)
      let w77 (u : ℕ) : Bool := PEqualNP.CleanedNonEdge.wireVal 14 C u (PEqualNP.EdgeOwnership.pairInput 7 7)
      let op : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd C
      let c : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 14 C
      let p (g : ℕ) : Prop :=
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        w07 (14 + g) = true ∧ w00 (14 + g) = false ∧ w77 (14 + g) = false
      let s (g : ℕ) : Prop := p g ∧ ∀ b : Fin 2, w00 (op g b) = true ∨ w77 (op g b) = true
      ∀ i j : ℕ, i < j → ¬c i j → ¬c j i → c i (C.size - 1) → c j (C.size - 1) → p i → p j →
        (∀ b : Fin 2, w00 (op i b) = false) → (∀ b : Fin 2, w77 (op j b) = false) →
        (∃ k m : ℕ, k ≠ m ∧ ¬c k m ∧ ¬c m k ∧ s k ∧ s m ∧ c k i ∧ c m j) → False) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →           have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);           have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;           have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;           have x9 : Fin (14 : ℕ) → ℕ → Prop := fun (x9 : Fin (14 : ℕ)) (x10 : ℕ) => x7 x10 ∧ ((14 : ℕ) + x10 = x1.output ∨ x8 x10 (x1.output - (14 : ℕ))) ∧ x6 x10 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x11) (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.false;           ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬x8 x10 x11 → ¬x8 x11 x10 → x9 (0 : Fin (14 : ℕ)) x10 → x9 (7 : Fin (14 : ℕ)) x11 → (∃ (x17 : ℕ) (x18 : ℕ), x7 x17 ∧ x7 x18 ∧ x8 x17 x10 ∧ x8 x18 x11 ∧ x6 x10 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ x6 x11 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x6 x17 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x6 x18 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x6 x17 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ x6 x18 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x6 x18 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → False := by
  intro hSharedReread hSharedPure hDisjoint
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun idx => ws.getD idx false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have wireVal_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      wireVal 14 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hlt : r < (List.ofFn x).length := by omega
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_ge : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ),
      14 + D.gates.length ≤ r → wireVal 14 D r x = false := by
    intro D x r hr
    have hlen : (D.wires (List.ofFn x)).length = 14 + D.gates.length := by
      change (D.gates.foldl wstep (List.ofFn x)).length = _
      rw [wfold_len, List.length_ofFn]
    exact List.getD_eq_default _ _ (by omega)
  have wireVal_gate : ∀ (D : Circuit) (x : Fin 14 → Bool) (k : ℕ) (g : Gate),
      D.gates[k]? = some g → (∀ idx ∈ g.inputs, idx < 14 + k) →
      wireVal 14 D (14 + k) x = g.op.eval (g.inputs.map fun idx => wireVal 14 D idx x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hg_eq : D.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hgk)
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (D.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + k := by
      dsimp only [pref]
      rw [wfold_len, List.length_ofFn, List.length_take]
      omega
    have hwires_eq : D.wires (List.ofFn x) = (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ idx < 14 + k, pref.getD idx false = wireVal 14 D idx x := by
      intro idx hidx
      change pref.getD idx false = (D.wires (List.ofFn x)).getD idx false
      rw [hwires_eq]
      have hi1 : idx < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ idx hi1]
      have hi0 : idx < pref.length := by omega
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    change (D.wires (List.ofFn x)).getD (14 + k) false = _
    rw [hwires_eq]
    have hidx : 14 + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref g).getD (14 + k) false =
        g.op.eval (g.inputs.map fun idx => pref.getD idx false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun idx hi => hpref_get idx (hlt idx hi)
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      dsimp only [coneStep]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (r : ℕ),
      r < cs.length → (gs.foldl (coneStep 14) cs).getD r [] = cs.getD r [] := by
    intro gs
    induction gs with
    | nil => intro cs r _; rfl
    | cons g gs ih =>
      intro cs r hr
      rw [List.foldl_cons]
      have hr' : r < (coneStep 14 cs g).length := by
        dsimp only [coneStep]; simp only [List.length_append, List.length_singleton]; omega
      rw [ih _ r hr']
      dsimp only [coneStep]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have cones_char : ∀ (gs : List Gate) (a b : ℕ),
      a ∈ (gs.foldl (coneStep 14) []).getD b [] ↔
        b < gs.length ∧ ∃ w ∈ (gs.getD b ⟨GateOp.or, []⟩).inputs,
          14 ≤ w ∧ w < 14 + b ∧
          (a = w - 14 ∨ a ∈ (gs.foldl (coneStep 14) []).getD (w - 14) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro a b; simp
    | append_singleton gs g ih =>
      intro a b
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 14) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep 14 (gs.foldl (coneStep 14) []) g).getD k [] =
            (gs.foldl (coneStep 14) []).getD k [] := by
        intro k hk
        dsimp only [coneStep]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < (gs.foldl (coneStep 14) []).length)]
      rcases Nat.lt_trichotomy b gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD b ⟨GateOp.or, []⟩ = gs.getD b ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key b h, ih a b, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 14) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 14) (by omega)] at h3; exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep 14 (gs.foldl (coneStep 14) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
              (fun w => (w - 14) :: (gs.foldl (coneStep 14) []).getD (w - 14) []) := by
          dsimp only [coneStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e1, e2, List.mem_flatMap]
        constructor
        · rintro ⟨w, hw, hmem⟩
          rw [List.mem_filter, decide_eq_true_eq] at hw
          refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
          rw [key (w - 14) (by omega)]
          simpa using hmem
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 14) (by omega)] at h3
          exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, by simpa using h3⟩
      · have e3 : (coneStep 14 (gs.foldl (coneStep 14) []) g).getD b [] = [] := by
          apply List.getD_eq_default
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton, hlen]
          omega
        rw [e3]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hlt
        simp only [List.length_append, List.length_singleton] at hlt
        omega
  have inCone_iff : ∀ (D : Circuit) (a b : ℕ),
      InCone 14 D a b ↔
        b < D.gates.length ∧ ∃ w ∈ (gateAt D b).inputs,
          14 ≤ w ∧ w < 14 + b ∧ (a = w - 14 ∨ InCone 14 D a (w - 14)) :=
    fun D a b => cones_char D.gates a b
  have inCone_lt : ∀ (D : Circuit) (a b : ℕ), InCone 14 D a b → a < b := by
    intro D a b
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro h
      obtain ⟨_, w, _, hw1, hw2, hr⟩ := (inCone_iff D a b).1 h
      rcases hr with rfl | hc
      · omega
      · have := ih (w - 14) (by omega) hc
        omega
  have inCone_trans : ∀ (D : Circuit) (a b d : ℕ),
      InCone 14 D a b → InCone 14 D b d → InCone 14 D a d := by
    intro D a b d hab
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro hbd
      obtain ⟨hd, w, hw, hw1, hw2, hr⟩ := (inCone_iff D b d).1 hbd
      refine (inCone_iff D a d).2 ⟨hd, w, hw, hw1, hw2, ?_⟩
      rcases hr with rfl | hc
      · exact Or.inr hab
      · exact Or.inr (ih (w - 14) (by omega) hc)
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have ao_gate_info : ∀ (D : Circuit), IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
      ∀ k < D.gates.length,
        ((gateAt D k).op = .and ∨ (gateAt D k).op = .or) ∧
        ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + k ∧ b < 14 + k ∧
          ∀ z, wireVal 14 D (14 + k) z = (gateAt D k).op.eval [wireVal 14 D a z, wireVal 14 D b z] := by
    intro D hao hnd k hk
    have hg : D.gates[k]? = some (gateAt D k) := by
      change D.gates[k]? = some (D.gates.getD k ⟨.or, []⟩)
      rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    have hmem : gateAt D k ∈ D.gates := List.mem_of_getElem? hg
    have hop := hao.1 _ hmem
    have hback := hao.2.1 k hk
    have hlen := hao.2.2 _ hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
    have hne : a ≠ b := by
      have := hnd _ hmem
      rw [hab, List.nodup_cons, List.mem_singleton] at this
      exact this.1
    have ha : a < 14 + k := hback a (by rw [hab]; simp)
    have hb : b < 14 + k := hback b (by rw [hab]; simp)
    refine ⟨hop, a, b, hab, hne, ha, hb, fun z => ?_⟩
    rw [wireVal_gate D z k _ hg hback, hab]
    rfl
  have and_lt_len : ∀ (D : Circuit) (g : ℕ), (gateAt D g).op = .and → g < D.gates.length := by
    intro D g hand
    by_contra! h
    change (D.gates.getD g ⟨.or, []⟩).op = .and at hand
    rw [List.getD_eq_default _ _ h] at hand
    cases hand
  have origin : ∀ (D : Circuit), IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
      ∀ w : ℕ,
        wireVal 14 D w (pairInput (0 : Fin 14) 7) = true →
        wireVal 14 D w (pairInput (0 : Fin 14) 0) = false →
        wireVal 14 D w (pairInput (7 : Fin 14) 7) = false →
        ∃ q, (gateAt D q).op = .and ∧
          gateVal 14 D q (pairInput (0 : Fin 14) 7) = true ∧
          gateVal 14 D q (pairInput (0 : Fin 14) 0) = false ∧
          gateVal 14 D q (pairInput (7 : Fin 14) 7) = false ∧
          (w = 14 + q ∨ InCone 14 D q (w - 14)) := by
    intro D hao hnd w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hp hs ht
      by_cases hin : w < 14
      · rw [wireVal_input D _ w hin] at hp hs ht
        let v : Fin 14 := ⟨w, hin⟩
        change decide (v = 0 ∨ v = 7) = true at hp
        change decide (v = 0 ∨ v = 0) = false at hs
        change decide (v = 7 ∨ v = 7) = false at ht
        simp at hp hs ht
        tauto
      have hw : w < 14 + D.gates.length := by
        by_contra! bad
        rw [wireVal_ge D _ w bad] at hp
        cases hp
      let k := w - 14
      have hwk : 14 + k = w := by dsimp [k]; omega
      have hk : k < D.gates.length := by omega
      obtain ⟨hop, a, b, hab, _, ha, hb, heval⟩ := ao_gate_info D hao hnd k hk
      rcases hop with hand | hor
      · refine ⟨k, hand, ?_, ?_, ?_, Or.inl hwk.symm⟩
        all_goals change wireVal 14 D (14 + k) _ = _; rwa [hwk]
      · have horEval : ∀ z, wireVal 14 D w z = (wireVal 14 D a z || wireVal 14 D b z) := by
          intro z; rw [← hwk, heval, hor, eval_or]
        rw [horEval, Bool.or_eq_true] at hp
        rw [horEval, Bool.or_eq_false_iff] at hs ht
        have lift (u : ℕ) (humem : u ∈ (gateAt D k).inputs) (hu : u < 14 + k)
            (htrue : wireVal 14 D u (pairInput 0 7) = true)
            (hsp : wireVal 14 D u (pairInput 0 0) = false)
            (hsl : wireVal 14 D u (pairInput 7 7) = false) :
            ∃ q, (gateAt D q).op = .and ∧
              gateVal 14 D q (pairInput 0 7) = true ∧
              gateVal 14 D q (pairInput 0 0) = false ∧
              gateVal 14 D q (pairInput 7 7) = false ∧
              (w = 14 + q ∨ InCone 14 D q (w - 14)) := by
          obtain ⟨q, hq, hqp, hqs, hqt, hreach⟩ := ih u (by omega) htrue hsp hsl
          refine ⟨q, hq, hqp, hqs, hqt, Or.inr ((inCone_iff D q k).2 ⟨hk, u, humem, ?_, hu, ?_⟩)⟩
          · rcases hreach with heq | hc
            · omega
            · have := inCone_lt D q (u - 14) hc; omega
          · exact hreach.imp_left (by omega)
        exact hp.elim
          (fun hh => lift a (by simp [hab]) ha hh hs.1 ht.1)
          (fun hh => lift b (by simp [hab]) hb hh hs.2 ht.2)
  let τN (n : ℕ) : ℕ := if n < 7 then 7 + (7 - n) % 7 else (14 - n) % 7
  have hτN_lt : ∀ n < 14, τN n < 14 := by
    intro n hn; dsimp only [τN]; split_ifs <;> omega
  have hτN_inv : ∀ n < 14, τN (τN n) = n := by
    intro n hn; dsimp only [τN]; split_ifs <;> omega
  let τ (v : Fin 14) : Fin 14 := ⟨τN v.val, hτN_lt v.val v.isLt⟩
  have hτ_inv : ∀ v : Fin 14, τ (τ v) = v := by
    intro v; ext; exact hτN_inv v.val v.isLt
  have hτ_00 : ∀ v : Fin 14, decide (τ v = 0 ∨ τ v = 0) = decide (v = 7 ∨ v = 7) := by
    intro v
    have hv := v.isLt
    have h7 : ((7 : Fin 14) : ℕ) = 7 := rfl
    rw [decide_eq_decide]
    simp only [or_self, Fin.ext_iff, Fin.val_zero, h7]
    change τN v.val = 0 ↔ v.val = 7
    dsimp only [τN]; split_ifs <;> omega
  have hτ_77 : ∀ v : Fin 14, decide (τ v = 7 ∨ τ v = 7) = decide (v = 0 ∨ v = 0) := by
    intro v
    have hv := v.isLt
    have h7 : ((7 : Fin 14) : ℕ) = 7 := rfl
    rw [decide_eq_decide]
    simp only [or_self, Fin.ext_iff, Fin.val_zero, h7]
    change τN v.val = 7 ↔ v.val = 0
    dsimp only [τN]; split_ifs <;> omega
  have hτ_07 : ∀ v : Fin 14, decide (τ v = 0 ∨ τ v = 7) = decide (v = 0 ∨ v = 7) := by
    intro v
    have hv := v.isLt
    have h7 : ((7 : Fin 14) : ℕ) = 7 := rfl
    rw [decide_eq_decide]
    simp only [Fin.ext_iff, Fin.val_zero, h7]
    change (τN v.val = 0 ∨ τN v.val = 7) ↔ (v.val = 0 ∨ v.val = 7)
    dsimp only [τN]; split_ifs <;> omega
  have hτ_fano : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
      ∃ p' l' : Fin 7, (p' = l' ∨ p' = l' + 1 ∨ p' = l' + 3) ∧
        τ (Fin.castAdd 7 p') = Fin.natAdd 7 l ∧ τ (Fin.natAdd 7 l') = Fin.castAdd 7 p := by
    intro p l hpl
    have hp := p.isLt
    have hl := l.isLt
    refine ⟨⟨(7 - l.val) % 7, by omega⟩, ⟨(7 - p.val) % 7, by omega⟩, ?_, ?_, ?_⟩
    · have h1 : ((1 : Fin 7) : ℕ) = 1 := rfl
      have h3 : ((3 : Fin 7) : ℕ) = 3 := rfl
      simp only [Fin.ext_iff, Fin.val_add, h1, h3] at hpl ⊢
      omega
    · ext
      change τN ((7 - l.val) % 7) = 7 + l.val
      dsimp only [τN]; split_ifs <;> omega
    · ext
      change τN (7 + (7 - p.val) % 7) = p.val
      dsimp only [τN]; split_ifs <;> omega
  have hp00 : (pairInput (0 : Fin 14) 0 ∘ τ) = pairInput (7 : Fin 14) 7 :=
    funext fun v => hτ_00 v
  have hp77 : (pairInput (7 : Fin 14) 7 ∘ τ) = pairInput (0 : Fin 14) 0 :=
    funext fun v => hτ_77 v
  have hp07 : (pairInput (0 : Fin 14) 7 ∘ τ) = pairInput (0 : Fin 14) 7 :=
    funext fun v => hτ_07 v
  let renW (w : ℕ) : ℕ := if w < 14 then τN w else w
  have renW_inv : ∀ w : ℕ, renW (renW w) = w := by
    intro w
    by_cases hw : w < 14
    · have hrw : τN w < 14 := hτN_lt w hw
      have e1 : renW w = τN w := by dsimp only [renW]; split_ifs; rfl
      have e2 : renW (τN w) = τN (τN w) := by dsimp only [renW]; split_ifs; rfl
      rw [e1, e2]
      exact hτN_inv w hw
    · have e1 : renW w = w := by dsimp only [renW]; split_ifs; rfl
      rw [e1, e1]
  have renW_inj : Function.Injective renW := by
    intro u v h
    rw [← renW_inv u, ← renW_inv v, h]
  have renW_lt_iff : ∀ w k : ℕ, renW w < 14 + k ↔ w < 14 + k := by
    intro w k
    dsimp only [renW]
    split_ifs with hw
    · have := hτN_lt w hw; omega
    · rfl
  have renW_ge14 : ∀ w : ℕ, 14 ≤ w → renW w = w := by
    intro w hw
    dsimp only [renW]
    split_ifs with h
    · omega
    · rfl
  let flipG (g : Gate) : Gate := ⟨g.op, g.inputs.map renW⟩
  let flipC (D : Circuit) : Circuit := ⟨D.gates.map flipG, D.output⟩
  have filter_renW : ∀ (l : List ℕ) (m : ℕ),
      (l.map renW).filter (fun w => decide (14 ≤ w ∧ w < 14 + m)) =
        l.filter (fun w => decide (14 ≤ w ∧ w < 14 + m)) := by
    intro l m
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons]
      by_cases ha : a < 14
      · have hra : renW a < 14 := by dsimp only [renW]; split_ifs; exact hτN_lt a ha
        have f1 : decide (14 ≤ renW a ∧ renW a < 14 + m) = false :=
          decide_eq_false (by omega)
        have f2 : decide (14 ≤ a ∧ a < 14 + m) = false :=
          decide_eq_false (by omega)
        rw [List.filter_cons, List.filter_cons, f1, f2]
        simp only [Bool.false_eq_true, ite_false, ih]
      · rw [renW_ge14 a (by omega)]
        simp only [List.filter_cons, ih]
  have cones_flip : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.map flipG).foldl (coneStep 14) cs = gs.foldl (coneStep 14) cs := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih =>
      intro cs
      simp only [List.map_cons, List.foldl_cons]
      have hstep : coneStep 14 cs (flipG g) = coneStep 14 cs g := by
        dsimp only [coneStep, flipG]
        rw [filter_renW]
      rw [hstep, ih]
  have inCone_flip : ∀ (D : Circuit) (a b : ℕ), InCone 14 (flipC D) a b ↔ InCone 14 D a b := by
    intro D a b
    change a ∈ ((D.gates.map flipG).foldl (coneStep 14) []).getD b [] ↔
      a ∈ (D.gates.foldl (coneStep 14) []).getD b []
    rw [cones_flip]
  have wires_flip : ∀ (D : Circuit), IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
      ∀ (x : Fin 14 → Bool) (w : ℕ),
        wireVal 14 (flipC D) w x = wireVal 14 D (renW w) (x ∘ τ) := by
    intro D hao hnd x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w < 14
      · have hrw : renW w < 14 := by dsimp only [renW]; split_ifs; exact hτN_lt w hw
        rw [wireVal_input (flipC D) x w hw, wireVal_input D (x ∘ τ) (renW w) hrw]
        change x ⟨w, hw⟩ = x (τ ⟨renW w, hrw⟩)
        have heq : (⟨renW w, hrw⟩ : Fin 14) = τ ⟨w, hw⟩ := by
          ext; dsimp only [renW]; split_ifs; rfl
        rw [heq, hτ_inv]
      by_cases hge : 14 + D.gates.length ≤ w
      · have hge' : 14 + (flipC D).gates.length ≤ w := by simpa [flipC] using hge
        rw [wireVal_ge (flipC D) x w hge', renW_ge14 w (by omega), wireVal_ge D (x ∘ τ) w hge]
      let k := w - 14
      have hwk : 14 + k = w := by dsimp [k]; omega
      have hk : k < D.gates.length := by omega
      obtain ⟨hop, a, b, hab, _, ha, hb, heval⟩ := ao_gate_info D hao hnd k hk
      have hgk : D.gates[k]? = some (gateAt D k) := by
        change D.gates[k]? = some (D.gates.getD k ⟨.or, []⟩)
        rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
      have hgk' : (flipC D).gates[k]? = some (flipG (gateAt D k)) := by
        dsimp only [flipC]
        rw [List.getElem?_map, hgk]; rfl
      have hlt' : ∀ idx ∈ (flipG (gateAt D k)).inputs, idx < 14 + k := by
        intro idx hidx
        dsimp only [flipG] at hidx
        rw [hab] at hidx
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hidx
        rcases hidx with rfl | rfl
        · exact (renW_lt_iff a k).2 ha
        · exact (renW_lt_iff b k).2 hb
      rw [← hwk, renW_ge14 (14 + k) (by omega), wireVal_gate (flipC D) x k _ hgk' hlt', heval (x ∘ τ)]
      dsimp only [flipG]
      rw [hab]
      simp only [List.map_cons, List.map_nil]
      rw [ih (renW a) (by have := (renW_lt_iff a k).2 ha; omega),
          ih (renW b) (by have := (renW_lt_iff b k).2 hb; omega),
          renW_inv a, renW_inv b]
  have core : ∀ (D : Circuit) (i j k m : ℕ),
      D.size ≤ 27 →
      IsAO2 14 D →
      (∀ g ∈ D.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      i < j →
      ¬InCone 14 D i j →
      ¬InCone 14 D j i →
      (gateAt D i).op = .and →
      (14 + i = D.output ∨ InCone 14 D i (D.output - 14)) →
      gateVal 14 D i (pairInput 0 7) = true →
      (∀ b : Fin 2, wireVal 14 D (opnd D i b) (pairInput 0 0) = false) →
      (gateAt D j).op = .and →
      (14 + j = D.output ∨ InCone 14 D j (D.output - 14)) →
      gateVal 14 D j (pairInput 0 7) = true →
      (∀ b : Fin 2, wireVal 14 D (opnd D j b) (pairInput 7 7) = false) →
      (gateAt D k).op = .and →
      (gateAt D m).op = .and →
      InCone 14 D k i →
      InCone 14 D m j →
      gateVal 14 D i (pairInput 7 7) = false →
      gateVal 14 D j (pairInput 0 0) = false →
      gateVal 14 D k (pairInput 0 7) = true →
      gateVal 14 D m (pairInput 0 7) = true →
      gateVal 14 D k (pairInput 0 0) = false →
      gateVal 14 D k (pairInput 7 7) = false →
      gateVal 14 D m (pairInput 0 0) = false →
      gateVal 14 D m (pairInput 7 7) = false →
      False := by
    intro D i j k m hsize hao hnd heval hij hnij hnji hai hilive hi07 hi00
      haj hjlive hj07 hj77 hak ham hcki hcmj hi77 hj00 hk07 hm07 hk00 hk77 hm00 hm77
    have hout_lt : D.output < 14 + D.gates.length := by
      by_contra! bad
      have pos := (heval (fun _ => true)).2 ⟨0, 0, Or.inl rfl, rfl, rfl⟩
      have hf := wireVal_ge D (fun _ => true) D.output bad
      change D.eval (List.ofFn (fun _ => true)) = false at hf
      rw [pos] at hf; cases hf
    have hout_ge : 14 ≤ D.output := by
      by_contra! low
      let v : Fin 14 := ⟨D.output, low⟩
      let x : Fin 14 → Bool := fun u => decide (u = v)
      have lit : D.eval (List.ofFn x) = true := (wireVal_input D x _ low).trans (by simp [x, v])
      obtain ⟨p, l, _, hp, hl⟩ := (heval x).1 lit
      have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
      change p.val = 7 + l.val at bad; omega
    let o := D.output - 14
    have ho_len : o < D.gates.length := by dsimp [o]; omega
    have ho_eq : 14 + o = D.output := by dsimp [o]; omega
    have hcio : InCone 14 D i o := by
      rcases hilive with heq | hc
      · exfalso
        have hio : i = o := by omega
        subst hio
        rcases hjlive with heqj | hcj
        · omega
        · exact hnji hcj
      · exact hc
    have hcjo : InCone 14 D j o := by
      rcases hjlive with heq | hc
      · exfalso
        have hjo : j = o := by omega
        subst hjo
        exact hnij hcio
      · exact hc
    have hio_lt : i < o := inCone_lt D i o hcio
    have hjo_lt : j < o := inCone_lt D j o hcjo
    have hko_lt : k < i := inCone_lt D k i hcki
    have hmo_lt : m < j := inCone_lt D m j hcmj
    let T : Circuit := ⟨D.gates.take (o + 1), 14 + o⟩
    have hT_len : T.gates.length = o + 1 := by dsimp [T]; rw [List.length_take]; omega
    have hT_size : T.size ≤ 27 := by
      change T.gates.length ≤ 27
      have : D.gates.length ≤ 27 := hsize
      omega
    have hT_out : T.output + 1 = 14 + T.size := by
      change (14 + o) + 1 = 14 + T.gates.length
      omega
    have hT_gateAt : ∀ g < o + 1, gateAt T g = gateAt D g := by
      intro g hg
      change (D.gates.take (o + 1)).getD g ⟨.or, []⟩ = D.gates.getD g ⟨.or, []⟩
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_take]
    have hT_opnd : ∀ g < o + 1, ∀ b : Fin 2, opnd T g b = opnd D g b := by
      intro g hg b
      change (gateAt T g).inputs.getD b 0 = (gateAt D g).inputs.getD b 0
      rw [hT_gateAt g hg]
    have hT_ao : IsAO2 14 T := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact hao.1 g (List.take_subset _ _ hg)
      · intro g hg w hw
        rw [hT_len] at hg
        rw [hT_gateAt g hg] at hw
        exact hao.2.1 g (by omega) w hw
      · intro g hg
        exact hao.2.2 g (List.take_subset _ _ hg)
    have hT_nd : ∀ g ∈ T.gates, g.inputs.Nodup := fun g hg => hnd g (List.take_subset _ _ hg)
    have hT_wv : ∀ w < 14 + (o + 1), ∀ x : Fin 14 → Bool, wireVal 14 T w x = wireVal 14 D w x := by
      intro w hw x
      have hsplit : D.gates = D.gates.take (o + 1) ++ D.gates.drop (o + 1) := (List.take_append_drop _ _).symm
      change (T.gates.foldl wstep (List.ofFn x)).getD w false = (D.gates.foldl wstep (List.ofFn x)).getD w false
      conv_rhs => rw [hsplit, List.foldl_append]
      symm
      apply wfold_getD_lt
      rw [wfold_len, List.length_ofFn, hT_len]
      omega
    have hT_eval : ∀ x : Fin 14 → Bool, T.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      intro x
      have heq : T.eval (List.ofFn x) = D.eval (List.ofFn x) := by
        change wireVal 14 T (14 + o) x = wireVal 14 D D.output x
        rw [hT_wv (14 + o) (by omega) x, ho_eq]
      rw [heq]; exact heval x
    have hT_cone : ∀ b < o + 1, ∀ a : ℕ, InCone 14 T a b ↔ InCone 14 D a b := by
      intro b hb a
      have hsplit : D.gates = D.gates.take (o + 1) ++ D.gates.drop (o + 1) := (List.take_append_drop _ _).symm
      change a ∈ ((D.gates.take (o + 1)).foldl (coneStep 14) []).getD b [] ↔
        a ∈ (D.gates.foldl (coneStep 14) []).getD b []
      conv_rhs => rw [hsplit, List.foldl_append]
      have hget := cones_getD_lt (D.gates.drop (o + 1)) ((D.gates.take (o + 1)).foldl (coneStep 14) []) b
        (by rw [cones_len]; simp; omega)
      rw [hget]
    let wT (u : ℕ) (x y : Fin 14) : Bool := wireVal 14 T u (pairInput x y)
    let pT (g : ℕ) : Prop :=
      (gateAt T g).op = GateOp.and ∧
      wT (14 + g) 0 7 = true ∧ wT (14 + g) 0 0 = false ∧ wT (14 + g) 7 7 = false
    let sT (g : ℕ) : Prop :=
      pT g ∧ ∀ b : Fin 2, wT (opnd T g b) 0 0 = true ∨ wT (opnd T g b) 7 7 = true
    have hi00_gate : gateVal 14 D i (pairInput 0 0) = false := by
      obtain ⟨_, a, b, hab, _, _, _, hev⟩ := ao_gate_info D hao hnd i (by omega)
      change wireVal 14 D (14 + i) (pairInput 0 0) = false
      rw [hev, hai, eval_and]
      have h0 : wireVal 14 D a (pairInput 0 0) = false := by
        have := hi00 0
        change wireVal 14 D ((gateAt D i).inputs.getD 0 0) (pairInput 0 0) = false at this
        rwa [hab] at this
      rw [h0]; rfl
    have hj77_gate : gateVal 14 D j (pairInput 7 7) = false := by
      obtain ⟨_, a, b, hab, _, _, _, hev⟩ := ao_gate_info D hao hnd j (by omega)
      change wireVal 14 D (14 + j) (pairInput 7 7) = false
      rw [hev, haj, eval_and]
      have h0 : wireVal 14 D a (pairInput 7 7) = false := by
        have := hj77 0
        change wireVal 14 D ((gateAt D j).inputs.getD 0 0) (pairInput 7 7) = false at this
        rwa [hab] at this
      rw [h0]; rfl
    have hp_i : pT i := by
      refine ⟨by rw [hT_gateAt i (by omega)]; exact hai, ?_, ?_, ?_⟩
      · dsimp [wT]; rw [hT_wv (14 + i) (by omega)]; exact hi07
      · dsimp [wT]; rw [hT_wv (14 + i) (by omega)]; exact hi00_gate
      · dsimp [wT]; rw [hT_wv (14 + i) (by omega)]; exact hi77
    have hp_j : pT j := by
      refine ⟨by rw [hT_gateAt j (by omega)]; exact haj, ?_, ?_, ?_⟩
      · dsimp [wT]; rw [hT_wv (14 + j) (by omega)]; exact hj07
      · dsimp [wT]; rw [hT_wv (14 + j) (by omega)]; exact hj00
      · dsimp [wT]; rw [hT_wv (14 + j) (by omega)]; exact hj77_gate
    have hp_k : pT k := by
      refine ⟨by rw [hT_gateAt k (by omega)]; exact hak, ?_, ?_, ?_⟩
      · dsimp [wT]; rw [hT_wv (14 + k) (by omega)]; exact hk07
      · dsimp [wT]; rw [hT_wv (14 + k) (by omega)]; exact hk00
      · dsimp [wT]; rw [hT_wv (14 + k) (by omega)]; exact hk77
    have hp_m : pT m := by
      refine ⟨by rw [hT_gateAt m (by omega)]; exact ham, ?_, ?_, ?_⟩
      · dsimp [wT]; rw [hT_wv (14 + m) (by omega)]; exact hm07
      · dsimp [wT]; rw [hT_wv (14 + m) (by omega)]; exact hm00
      · dsimp [wT]; rw [hT_wv (14 + m) (by omega)]; exact hm77
    have find_min : ∀ (g tgt : ℕ), pT g → InCone 14 T g tgt →
        ∃ g', sT g' ∧ InCone 14 T g' tgt ∧ ∀ q, InCone 14 T q g' → ¬pT q := by
      intro g tgt
      induction g using Nat.strong_induction_on with
      | ind g ih =>
        intro hpg hgt
        by_cases hex : ∃ q, InCone 14 T q g ∧ pT q
        · obtain ⟨q, hqg, hpq⟩ := hex
          exact ih q (inCone_lt T q g hqg) hpq (inCone_trans T q g tgt hqg hgt)
        · refine ⟨g, ⟨hpg, fun b => ?_⟩, hgt, fun q hqg hpq => hex ⟨q, hqg, hpq⟩⟩
          by_contra! hboth
          have hg_lt : g < T.gates.length := and_lt_len T g hpg.1
          obtain ⟨_, a, d, had, _, ha, hd, hev⟩ := ao_gate_info T hT_ao hT_nd g hg_lt
          have h07_true : wT (opnd T g b) 0 7 = true := by
            have hg07 := hpg.2.1
            dsimp [wT] at hg07 ⊢
            rw [hev, hpg.1, eval_and, Bool.and_eq_true] at hg07
            fin_cases b
            · change wireVal 14 T ((gateAt T g).inputs.getD 0 0) _ = true
              rw [had]; exact hg07.1
            · change wireVal 14 T ((gateAt T g).inputs.getD 1 0) _ = true
              rw [had]; exact hg07.2
          have hu_mem : opnd T g b ∈ (gateAt T g).inputs := by
            fin_cases b <;> (change (gateAt T g).inputs.getD _ 0 ∈ _; rw [had]; simp)
          have hu_lt : opnd T g b < 14 + g := hT_ao.2.1 g hg_lt _ hu_mem
          have hf0 : wireVal 14 T (opnd T g b) (pairInput 0 0) = false :=
            Bool.eq_false_iff.2 hboth.1
          have hf7 : wireVal 14 T (opnd T g b) (pairInput 7 7) = false :=
            Bool.eq_false_iff.2 hboth.2
          obtain ⟨q, hqa, hq07, hq00, hq77, hreach⟩ := origin T hT_ao hT_nd (opnd T g b) h07_true hf0 hf7
          have hqg : InCone 14 T q g := by
            refine (inCone_iff T q g).2 ⟨hg_lt, opnd T g b, hu_mem, ?_, hu_lt, ?_⟩
            · rcases hreach with heq | hc
              · omega
              · have := inCone_lt T q (opnd T g b - 14) hc; omega
            · exact hreach.imp_left (by omega)
          exact hex ⟨q, hqg, hqa, hq07, hq00, hq77⟩
    have hcki_T : InCone 14 T k i := (hT_cone i (by omega) k).2 hcki
    have hcmj_T : InCone 14 T m j := (hT_cone j (by omega) m).2 hcmj
    obtain ⟨ks, hsk, hcksi, hmink⟩ := find_min k i hp_k hcki_T
    obtain ⟨ms, hsm, hcmsj, hminm⟩ := find_min m j hp_m hcmj_T
    have hnij_T : ¬InCone 14 T i j := fun h => hnij ((hT_cone j (by omega) i).1 h)
    have hnji_T : ¬InCone 14 T j i := fun h => hnji ((hT_cone i (by omega) j).1 h)
    have hcio_T : InCone 14 T i (T.size - 1) := by
      have he : T.size - 1 = o := by change T.gates.length - 1 = o; omega
      rw [he]; exact (hT_cone o (by omega) i).2 hcio
    have hcjo_T : InCone 14 T j (T.size - 1) := by
      have he : T.size - 1 = o := by change T.gates.length - 1 = o; omega
      rw [he]; exact (hT_cone o (by omega) j).2 hcjo
    have hi00_T : ∀ b : Fin 2, wT (opnd T i b) 0 0 = false := by
      intro b
      have hop_lt : opnd D i b < 14 + i := by
        obtain ⟨_, a, d, had, _, ha, hd, _⟩ := ao_gate_info D hao hnd i (by omega)
        fin_cases b <;> (change (gateAt D i).inputs.getD _ 0 < _; rw [had]; simp [ha, hd])
      dsimp [wT]
      rw [hT_opnd i (by omega) b, hT_wv _ (by omega)]
      exact hi00 b
    have hj77_T : ∀ b : Fin 2, wT (opnd T j b) 7 7 = false := by
      intro b
      have hop_lt : opnd D j b < 14 + j := by
        obtain ⟨_, a, d, had, _, ha, hd, _⟩ := ao_gate_info D hao hnd j (by omega)
        fin_cases b <;> (change (gateAt D j).inputs.getD _ 0 < _; rw [had]; simp [ha, hd])
      dsimp [wT]
      rw [hT_opnd j (by omega) b, hT_wv _ (by omega)]
      exact hj77 b
    by_cases hkm : ks = ms
    · subst hkm
      by_cases hrr : (∃ b : Fin 2, wT (opnd T i b) 7 7 = true) ∧ (∃ b : Fin 2, wT (opnd T j b) 0 0 = true)
      · exact hSharedReread T hT_size hT_out hT_ao hT_nd hT_eval i j hij hnij_T hnji_T hcio_T hcjo_T
          hp_i hp_j hi00_T hj77_T ⟨ks, hsk, hcksi, hcmsj, hrr.1, hrr.2⟩
      · have hpure : (∀ b : Fin 2, wT (opnd T i b) 7 7 = false) ∨ (∀ b : Fin 2, wT (opnd T j b) 0 0 = false) := by
          by_cases h1 : ∃ b : Fin 2, wT (opnd T i b) 7 7 = true
          · right
            intro b
            apply Bool.eq_false_iff.2
            intro ht
            exact hrr ⟨h1, b, ht⟩
          · left
            intro b
            apply Bool.eq_false_iff.2
            intro ht
            exact h1 ⟨b, ht⟩
        exact hSharedPure T hT_size hT_out hT_ao hT_nd hT_eval i j hij hnij_T hnji_T hcio_T hcjo_T
          hp_i hp_j hi00_T hj77_T ⟨ks, hsk, hcksi, hcmsj, hpure⟩
    · have hnkm : ¬InCone 14 T ks ms := fun hc => hminm ks hc hsk.1
      have hnmk : ¬InCone 14 T ms ks := fun hc => hmink ms hc hsm.1
      exact hDisjoint T hT_size hT_out hT_ao hT_nd hT_eval i j hij hnij_T hnji_T hcio_T hcjo_T
        hp_i hp_j hi00_T hj77_T ⟨ks, ms, hkm, hnkm, hnmk, hsk, hsm, hcksi, hcmsj⟩
  intro C hsize hao hnd heval
  dsimp only
  intro i j hne hnij hnji hi hj hex
  obtain ⟨k, m, hak, ham, hcki, hcmj, hi77, hj00, hk07, hm07, hk00, hk77, hm00, hm77⟩ := hex
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact core C i j k m hsize hao hnd heval hij hnij hnji
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
      hak ham hcki hcmj hi77 hj00 hk07 hm07 hk00 hk77 hm00 hm77
  · let F := flipC C
    have hout_ge : 14 ≤ C.output := by
      by_contra! low
      let v : Fin 14 := ⟨C.output, low⟩
      let x : Fin 14 → Bool := fun u => decide (u = v)
      have lit : C.eval (List.ofFn x) = true := (wireVal_input C x _ low).trans (by simp [x, v])
      obtain ⟨p, l, _, hp, hl⟩ := (heval x).1 lit
      have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
      change p.val = 7 + l.val at bad; omega
    have hF_size : F.size ≤ 27 := by
      change (C.gates.map flipG).length ≤ 27
      rw [List.length_map]
      exact hsize
    have hF_ao : IsAO2 14 F := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        dsimp [F, flipC] at hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        exact hao.1 g0 hg0
      · intro g hg w hw
        have hg0 : g < C.gates.length := by simpa [F, flipC] using hg
        have hgeq : gateAt F g = flipG (gateAt C g) := by
          change (C.gates.map flipG).getD g ⟨.or, []⟩ = flipG (C.gates.getD g ⟨.or, []⟩)
          rw [List.getD_eq_getElem _ _ hg, List.getD_eq_getElem _ _ hg0, List.getElem_map]
        rw [hgeq] at hw
        dsimp [flipG] at hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
        exact (renW_lt_iff w0 g).2 (hao.2.1 g hg0 w0 hw0)
      · intro g hg
        dsimp [F, flipC] at hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        dsimp [flipG]
        rw [List.length_map]
        exact hao.2.2 g0 hg0
    have hF_nd : ∀ g ∈ F.gates, g.inputs.Nodup := by
      intro g hg
      dsimp [F, flipC] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact (hnd g0 hg0).map renW_inj
    have hF_eval : ∀ x : Fin 14 → Bool, F.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      intro x
      have hev : F.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ τ)) := by
        change wireVal 14 F C.output x = wireVal 14 C C.output (x ∘ τ)
        rw [wires_flip C hao hnd x C.output, renW_ge14 C.output hout_ge]
      rw [hev, heval (x ∘ τ)]
      constructor
      · rintro ⟨p, l, hpl, hp, hl⟩
        obtain ⟨p', l', hpl', ep, el⟩ := hτ_fano p l hpl
        refine ⟨p', l', hpl', ?_, ?_⟩
        · have : x (τ (τ (Fin.castAdd 7 p'))) = true := by rw [ep]; exact hl
          rwa [hτ_inv] at this
        · have : x (τ (τ (Fin.natAdd 7 l'))) = true := by rw [el]; exact hp
          rwa [hτ_inv] at this
      · rintro ⟨p, l, hpl, hp, hl⟩
        obtain ⟨p', l', hpl', ep, el⟩ := hτ_fano p l hpl
        exact ⟨p', l', hpl', by change x (τ _) = true; rw [ep]; exact hl,
          by change x (τ _) = true; rw [el]; exact hp⟩
    have hF_op : ∀ g : ℕ, (gateAt F g).op = (gateAt C g).op := by
      intro g
      by_cases hg : g < C.gates.length
      · change ((C.gates.map flipG).getD g ⟨.or, []⟩).op = (C.gates.getD g ⟨.or, []⟩).op
        rw [List.getD_eq_getElem _ _ (by simp [hg]), List.getD_eq_getElem _ _ hg, List.getElem_map]
      · change ((C.gates.map flipG).getD g ⟨.or, []⟩).op = (C.gates.getD g ⟨.or, []⟩).op
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have hF_gv : ∀ g : ℕ, ∀ x : Fin 14 → Bool, gateVal 14 F g x = gateVal 14 C g (x ∘ τ) := by
      intro g x
      change wireVal 14 F (14 + g) x = wireVal 14 C (14 + g) (x ∘ τ)
      rw [wires_flip C hao hnd x (14 + g), renW_ge14 (14 + g) (by omega)]
    have hF_opnd : ∀ g < C.gates.length, ∀ b : Fin 2, ∀ x : Fin 14 → Bool,
        wireVal 14 F (opnd F g b) x = wireVal 14 C (opnd C g b) (x ∘ τ) := by
      intro g hg b x
      have hgeq : gateAt F g = flipG (gateAt C g) := by
        change (C.gates.map flipG).getD g ⟨.or, []⟩ = flipG (C.gates.getD g ⟨.or, []⟩)
        rw [List.getD_eq_getElem _ _ (by simp [hg]), List.getD_eq_getElem _ _ hg, List.getElem_map]
      obtain ⟨_, a, d, had, _, _, _, _⟩ := ao_gate_info C hao hnd g hg
      have hop_eq : opnd F g b = renW (opnd C g b) := by
        fin_cases b
        · change (gateAt F g).inputs.getD 0 0 = renW ((gateAt C g).inputs.getD 0 0)
          rw [hgeq]; dsimp [flipG]; rw [had]; rfl
        · change (gateAt F g).inputs.getD 1 0 = renW ((gateAt C g).inputs.getD 1 0)
          rw [hgeq]; dsimp [flipG]; rw [had]; rfl
      rw [hop_eq, wires_flip C hao hnd x, renW_inv]
    have hi_lt : i < C.gates.length := and_lt_len C i hi.1
    have hj_lt : j < C.gates.length := and_lt_len C j hj.1
    exact core F j i m k hF_size hF_ao hF_nd hF_eval hji
      (fun h => hnji ((inCone_flip C j i).1 h))
      (fun h => hnij ((inCone_flip C i j).1 h))
      (by rw [hF_op]; exact hj.1)
      (hj.2.1.imp_right fun h => (inCone_flip C j (C.output - 14)).2 h)
      (by rw [hF_gv, hp07]; exact hj.2.2.1)
      (fun b => by rw [hF_opnd j hj_lt b, hp00]; exact hj.2.2.2 b)
      (by rw [hF_op]; exact hi.1)
      (hi.2.1.imp_right fun h => (inCone_flip C i (C.output - 14)).2 h)
      (by rw [hF_gv, hp07]; exact hi.2.2.1)
      (fun b => by rw [hF_opnd i hi_lt b, hp77]; exact hi.2.2.2 b)
      (by rw [hF_op]; exact ham)
      (by rw [hF_op]; exact hak)
      ((inCone_flip C m j).2 hcmj)
      ((inCone_flip C k i).2 hcki)
      (by rw [hF_gv, hp77]; exact hj00)
      (by rw [hF_gv, hp00]; exact hi77)
      (by rw [hF_gv, hp07]; exact hm07)
      (by rw [hF_gv, hp07]; exact hk07)
      (by rw [hF_gv, hp00]; exact hm77)
      (by rw [hF_gv, hp77]; exact hm00)
      (by rw [hF_gv, hp00]; exact hk77)
      (by rw [hF_gv, hp77]; exact hk00)
