import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4752_1
    (evalGate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (k : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
      PEqualNP.CleanedNonEdge.wireVal 14 D (14 + k) x =
        g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 14 D i x))
    (count : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => x2 x3 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x2 x3 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 x3 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x5 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x6 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), x7 ∈ PEqualNP.CircuitLowerBounds.fanoLines x8 ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true)) → ∀ (x7 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x7 (x1.output - (14 : ℕ)) → (∃ (x10 : ℕ) (x11 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x7 (0 : Fin (2 : ℕ))) x10 ∧ x3 (PEqualNP.TopForm.opnd x1 x7 (1 : Fin (2 : ℕ))) x11) → (28 : ℕ) ≤ x1.size) :
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ)) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  have trace : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => x2 x3 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x2 x3 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 x3 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((14 : ℕ) + x5) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x8 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x5 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x5 x8) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ∀ (x9 : Fin (2 : ℕ)), ∃ (x10 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x5 x9) x10 := by
    let wstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have wfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool),
        (gs.foldl wstep xs).length = xs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro xs; simp
      | cons g rest ih =>
        intro xs
        simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
        omega
    have wfold_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) (r : ℕ),
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
    have wireVal_input : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (r : ℕ)
        (hr : r < 14), PEqualNP.CleanedNonEdge.wireVal 14 D r x = x ⟨r, hr⟩ := by
      intro D x r hr
      have hlen : (List.ofFn x).length = 14 := List.length_ofFn
      have hlt : r < (List.ofFn x).length := by omega
      change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
      rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hr]
    have wireVal_ge : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (r : ℕ),
        14 + D.gates.length ≤ r → PEqualNP.CleanedNonEdge.wireVal 14 D r x = false := by
      intro D x r hr
      have hlen : (D.wires (List.ofFn x)).length = 14 + D.gates.length := by
        change (D.gates.foldl wstep (List.ofFn x)).length = _
        rw [wfold_len, List.length_ofFn]
      exact List.getD_eq_default _ _ (by omega)
    have wireVal_gate := evalGate
    have cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
        (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih]
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have cones_char : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ),
        i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
            14 ≤ w ∧ w < 14 + j ∧
            (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
          rw [cones_len]; simp
        have key : ∀ k, k < gs.length →
            (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD k [] =
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
          intro k hk
          dsimp only [PEqualNP.EdgeOwnership.coneStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
              gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
            rw [key (w - 14) (by omega)]; exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨h, w, hw, h1, h2, ?_⟩
            rw [key (w - 14) (by omega)] at h3; exact h3
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD]
          have e2 : (PEqualNP.EdgeOwnership.coneStep 14
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
                (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
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
        · have e3 : (PEqualNP.EdgeOwnership.coneStep 14
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD j [] = [] := by
            apply List.getD_eq_default
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
            simp only [List.length_append, List.length_singleton, hlen]
            omega
          rw [e3]
          simp only [List.not_mem_nil, false_iff, not_and]
          intro hlt
          simp only [List.length_append, List.length_singleton] at hlt
          omega
    have inCone_iff : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
        PEqualNP.EdgeOwnership.InCone 14 D i j ↔
          j < D.gates.length ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
            14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 D i (w - 14)) :=
      fun D i j => cones_char D.gates i j
    intro C V Birth hao g hg hp hs b
    have shape (j : ℕ) (hj : j < C.gates.length) :
        ∃ u v, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [u,v] ∧ u < 14+j ∧ v < 14+j ∧
          ∀ x : Fin 14 → Bool, PEqualNP.CleanedNonEdge.wireVal 14 C (14+j) x =
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [PEqualNP.CleanedNonEdge.wireVal 14 C u x, PEqualNP.CleanedNonEdge.wireVal 14 C v x] := by
      have mem : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
        rw [show PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      obtain ⟨u,v,hin⟩ := List.length_eq_two.mp (hao.2.2 _ mem)
      have hu := hao.2.1 j hj u (by simp [hin])
      have hv := hao.2.1 j hj v (by simp [hin])
      refine ⟨u,v,hin,hu,hv,?_⟩
      intro x
      have he := wireVal_gate C x j (PEqualNP.MetaComplexity.NestedCover.gateAt C j)
        (by
          rw [show PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
          exact List.getElem?_eq_getElem hj)
        (hao.2.1 j hj)
      simpa only [hin,List.map_cons,List.map_nil] using he
    have inputImpossible (w : ℕ) (hw : w < 14) :
        V w 0 7 = true → V w 0 0 = false → V w 7 7 = false → False := by
      dsimp [V]
      rw [wireVal_input C _ w hw,wireVal_input C _ w hw,wireVal_input C _ w hw]
      have check : ∀ i : Fin 14,
          PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 i = true → PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 i = false →
            PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 i = false → False := by decide
      exact check ⟨w,hw⟩
    have trace : ∀ w : ℕ, V w 0 7 = true → V w 0 0 = false → V w 7 7 = false →
        14 ≤ w ∧ ∃ a, Birth w a := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw h0 h7
        have wn : 14 ≤ w := by
          by_contra h
          exact inputImpossible w (by omega) hw h0 h7
        refine ⟨wn,?_⟩
        let j := w-14
        have wj : 14+j=w := by dsimp [j]; omega
        have hj : j<C.gates.length := by
          by_contra h
          have bad := wireVal_ge C (PEqualNP.EdgeOwnership.pairInput 0 7) w (by dsimp [j] at h; omega)
          change PEqualNP.CleanedNonEdge.wireVal 14 C w (PEqualNP.EdgeOwnership.pairInput 0 7) = true at hw
          rw [bad] at hw
          cases hw
        obtain ⟨u,v,hin,hu,hv,he⟩ := shape j hj
        have descend (z : ℕ) (hz : z ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) (hlt : z<w)
            (hpz : V z 0 7=true) (h0z : V z 0 0=false) (h7z : V z 7 7=false) :
            ∃ a, Birth w a := by
          obtain ⟨zn,a,ha⟩ := ih z hlt hpz h0z h7z
          refine ⟨a,?_⟩
          rcases ha with ⟨_,_,_,hcone,hand,hs0,hs7,hcross⟩
          refine ⟨hw,h0,h7,Or.inr ?_,hand,hs0,hs7,hcross⟩
          rw [← wj, Nat.add_sub_cancel_left]
          apply (inCone_iff C a j).mpr
          refine ⟨hj,z,hz,zn,by omega,?_⟩
          rcases hcone with hsame | hbelow
          · left; omega
          · exact Or.inr hbelow
        have mem : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
          rw [show PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        rcases hao.1 _ mem with hand | hor
        · have eval (p q : Fin 14) : V w p q = (V u p q && V v p q) := by
            have eq := he (PEqualNP.EdgeOwnership.pairInput p q)
            rw [hand] at eq
            change V (14+j) p q = (V u p q && (V v p q && true)) at eq
            simpa only [Bool.and_true,wj] using eq
          have pair : V u 0 7=true ∧ V v 0 7=true := by simpa only [eval,Bool.and_eq_true] using hw
          by_cases u0 : V u 0 0=false
          · by_cases u7 : V u 7 7=false
            · exact descend u (by simp [hin]) (by omega) pair.1 u0 u7
            · have ut : V u 7 7=true := by cases h : V u 7 7 <;> first | exact (u7 h).elim | rfl
              have v7 : V v 7 7=false := by simpa only [eval,ut,Bool.true_and] using h7
              by_cases v0 : V v 0 0=false
              · exact descend v (by simp [hin]) (by omega) pair.2 v0 v7
              · have vt : V v 0 0=true := by cases h : V v 0 0 <;> first | exact (v0 h).elim | rfl
                refine ⟨j,hw,h0,h7,Or.inl wj,hand,?_,?_,1,?_,?_⟩
                · simpa only [wj] using h0
                · simpa only [wj] using h7
                · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) 0 0 = true
                  rw [hin]
                  exact vt
                · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) 7 7 = true
                  rw [hin]
                  exact ut
          · have ut : V u 0 0=true := by cases h : V u 0 0 <;> first | exact (u0 h).elim | rfl
            have v0 : V v 0 0=false := by simpa only [eval,ut,Bool.true_and] using h0
            by_cases v7 : V v 7 7=false
            · exact descend v (by simp [hin]) (by omega) pair.2 v0 v7
            · have vt : V v 7 7=true := by cases h : V v 7 7 <;> first | exact (v7 h).elim | rfl
              refine ⟨j,hw,h0,h7,Or.inl wj,hand,?_,?_,0,?_,?_⟩
              · simpa only [wj] using h0
              · simpa only [wj] using h7
              · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) 0 0 = true
                rw [hin]
                exact ut
              · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) 7 7 = true
                rw [hin]
                exact vt
        · have eval (p q : Fin 14) : V w p q = (V u p q || V v p q) := by
            have eq := he (PEqualNP.EdgeOwnership.pairInput p q)
            rw [hor] at eq
            change V (14+j) p q = (V u p q || (V v p q || false)) at eq
            simpa only [Bool.or_false,wj] using eq
          have all0 : V u 0 0=false ∧ V v 0 0=false := by simpa only [eval,Bool.or_eq_false_iff] using h0
          have all7 : V u 7 7=false ∧ V v 7 7=false := by simpa only [eval,Bool.or_eq_false_iff] using h7
          have pair : V u 0 7=true ∨ V v 0 7=true := by simpa only [eval,Bool.or_eq_true] using hw
          rcases pair with hup | hvp
          · exact descend u (by simp [hin]) (by omega) hup all0.1 all7.1
          · exact descend v (by simp [hin]) (by omega) hvp all0.2 all7.2
    have gj : g<C.gates.length := by
      by_contra h
      have bad : PEqualNP.MetaComplexity.NestedCover.gateAt C g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[]⟩ := List.getD_eq_default _ _ (by omega)
      rw [bad] at hg
      cases hg
    obtain ⟨u,v,hin,hu,hv,he⟩ := shape g gj
    have both : V u 0 7=true ∧ V v 0 7=true := by
      have eq := he (PEqualNP.EdgeOwnership.pairInput 0 7)
      rw [hg] at eq
      change V (14+g) 0 7 = (V u 0 7 && (V v 0 7 && true)) at eq
      have hw : V (14+g) 0 7= (V u 0 7 && V v 0 7) := by simpa only [Bool.and_true] using eq
      simpa only [hw,Bool.and_eq_true] using hp
    apply (trace (PEqualNP.TopForm.opnd C g b) ?_ (hs b).1 (hs b).2).2
    fin_cases b
    · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) 0 7 = true
      rw [hin]
      exact both.1
    · change V ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) 0 7 = true
      rw [hin]
      exact both.2
  intro h
  obtain ⟨C,hSize,hGate,hEval,g,hAnd,hOut,hPair,hSingles⟩ := h
  have get (j : ℕ) (hj : j < C.gates.length) : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj
  have facts (j : ℕ) (hj : j < C.gates.length) :=
    hGate j (C.gates[j]'hj) (List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩)
  have hAO : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g' hg'
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg'
      exact (facts j hj).1
    · intro j hj w hw
      obtain ⟨a,b,he,_,ha,hb⟩ := (facts j hj).2
      rw [get j hj,he] at hw
      rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
    · intro g' hg'
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg'
      obtain ⟨a,b,he,_,_,_⟩ := (facts j hj).2
      simp [he]
  have hDistinct (j : ℕ) (hj : j < C.gates.length) : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup := by
    obtain ⟨a,b,he,hn,_,_⟩ := (facts j hj).2
    rw [get j hj,he]
    simpa using hn
  have geometry : ∀ p l : Fin 7, p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by
    decide +kernel
  have hTarget : PEqualNP.MetaComplexity.circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
      p ∈ PEqualNP.CircuitLowerBounds.fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
    funext x
    exact Bool.eq_iff_iff.mpr ((hEval x).trans (by simp only [decide_eq_true_eq,geometry]))
  obtain ⟨a,ha⟩ := trace C hAO g hAnd hPair hSingles 0
  obtain ⟨b,hb⟩ := trace C hAO g hAnd hPair hSingles 1
  have lower := count C hAO hDistinct hTarget g hAnd hOut ⟨a,b,ha,hb⟩
  omega
