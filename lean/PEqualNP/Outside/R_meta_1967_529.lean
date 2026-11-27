import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- The inputs of each marked AND both depend on the missing endpoint.
-- Adding at each gate counts leaves when every shared wire is expanded into a tree.
-- The finite comparison uses the boundary rows of L_meta_4647.
-- The degree recurrence adapts L_meta_2676.
-- The wire relabeling and cone recurrence are adapted from R_meta_1967_1.
theorem PEqualNP.Outside.R_meta_1967_529
    (rankBound : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
        (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} → 29 ≤ (C.gates.foldl (fun (ws : List ℕ) g => ws ++ [(g.inputs.map fun i => ws.getD i 0).sum]) (List.replicate 14 1)).getD C.output 0)
    (finiteCase : ∀ C : Circuit,
      let rows : List ℕ := [16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
      let mark := fun (j : ℕ) (v : Fin 14) => (gateAt C j).op = .and ∧
        gateVal 14 C j (pairInput 0 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v) = false
      C.size ≤ 27 → IsAO2 14 C → (∀ j < C.size,(gateAt C j).inputs.Nodup) →
      29 ≤ (C.gates.foldl (fun (ws : List ℕ) g => ws ++ [(g.inputs.map fun i => ws.getD i 0).sum]) (List.replicate 14 1)).getD C.output 0 →
      (∀ k : Fin 58, C.eval (List.ofFn (fun i : Fin 14 => (rows.getD i.val 0).testBit k.val)) = decide (k.val < 21)) →
      ∀ a b, InCone 14 C a b → (14+b=C.output ∨ InCone 14 C b (C.output-14)) →
        mark a 0 → mark b 7 → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
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
  have wireVal_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (k : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
      PEqualNP.CleanedNonEdge.wireVal 14 D (14 + k) x =
        g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 14 D i x) := by
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
    have hwires_eq : D.wires (List.ofFn x) =
        (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + k, pref.getD i false = PEqualNP.CleanedNonEdge.wireVal 14 D i x := by
      intro i hi
      change pref.getD i false = (D.wires (List.ofFn x)).getD i false
      rw [hwires_eq]
      have hi1 : i < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ i hi1]
      have hi0 : i < pref.length := by omega
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    change (D.wires (List.ofFn x)).getD (14 + k) false = _
    rw [hwires_eq]
    have hidx : 14 + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref g).getD (14 + k) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
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
  have oriented : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (k1 k2 : ℕ),
      D.size ≤ 27 →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      PEqualNP.EdgeOwnership.InCone 14 D k1 k2 →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k1).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      PEqualNP.EdgeOwnership.gateVal 14 D k1 (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 D (PEqualNP.TopForm.opnd D k1 b)
        (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) = false) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k2).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (14 + k2 = D.output ∨ PEqualNP.EdgeOwnership.InCone 14 D k2 (D.output - 14)) →
      PEqualNP.EdgeOwnership.gateVal 14 D k2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 D (PEqualNP.TopForm.opnd D k2 b)
        (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = false) →
      False := by
    intro D k1 k2 hSize hGates hFano hCone12 hk1And hk1_07 hk1_00 hk2And hk2Live hk2_07 hk2_77
    have transCone (u v : ℕ) (uv : InCone 14 D u v) : ∀ w, InCone 14 D v w → InCone 14 D u w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro vw
        obtain ⟨hw,z,mem,lo,hi,eq|old⟩ := (inCone_iff D v w).mp vw
        · exact (inCone_iff D u w).mpr ⟨hw,z,mem,lo,hi,Or.inr (eq ▸ uv)⟩
        · exact (inCone_iff D u w).mpr ⟨hw,z,mem,lo,hi,Or.inr (ih (z-14) (by omega) old)⟩
    have firstLive : 14+k1=D.output ∨ InCone 14 D k1 (D.output-14) := by
      rcases hk2Live with eq|con
      · right
        rw [←eq]
        simpa using hCone12
      · exact Or.inr (transCone _ _ hCone12 _ con)
    have row (j) (hj : j<D.gates.length) := hGates j D.gates[j] (List.getElem?_eq_getElem hj)
    have ao : IsAO2 14 D := by
      refine ⟨?_,?_,?_⟩
      · intro g hg
        obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
        exact (row j hj).1
      · intro j hj a ha
        obtain ⟨p,q,op,_,hp,hq⟩ := (row j hj).2
        change a ∈ (D.gates.getD j _).inputs at ha
        rw [List.getD_eq_getElem _ _ hj,op] at ha
        rcases (show a=p ∨ a=q by simpa using ha) with rfl|rfl <;> assumption
      · intro g hg
        obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
        obtain ⟨p,q,op,_⟩ := (row j hj).2
        simp [op]
    have distinct (j) (hj : j<D.size) : (gateAt D j).inputs.Nodup := by
      obtain ⟨p,q,op,ne,_⟩ := (row j hj).2
      change (D.gates.getD j _).inputs.Nodup
      rw [List.getD_eq_getElem _ _ hj,op]
      simpa using ne
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    have gateAt_eq {C : Circuit} {j : ℕ} (hj : j<C.gates.length) : gateAt C j=C.gates[j] := by
      change C.gates.getD j _=C.gates[j]
      exact List.getD_eq_getElem _ _ hj
    have gateAt_mem {C : Circuit} {j : ℕ} (hj : j<C.gates.length) : gateAt C j∈C.gates := by
      rw [gateAt_eq hj]
      exact List.getElem_mem hj
    let stepR {β : Type} (F : Gate → List β → β) (d : β) (R : List β) (g : Gate) : List β :=
      R ++ [F g (g.inputs.map fun i => R.getD i d)]

    have R_getD_lt {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
        (i : ℕ) (hi : i < w.length) :
        (gs.foldl (stepR F d) w).getD i d = w.getD i d := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hlt : i < (stepR F d w g).length := by simp [stepR]; omega
        rw [ih (stepR F d w g) hlt]
        simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have R_getD_ge {β : Type} (d : β) (w : List β) (i : ℕ) (hi : w.length ≤ i) :
        w.getD i d = d := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

    have R_getD_gate {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
        (j : ℕ) (hj : j < gs.length) :
        (gs.foldl (stepR F d) w).getD (w.length + j) d =
          F (gs[j]) ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl (stepR F d) w).getD i d else d) := by
      induction gs generalizing w j with
      | nil => simp at hj
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepR F d w g).length := by simp [stepR]
          rw [Nat.add_zero, R_getD_lt F d gs (stepR F d w g) w.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (stepR F d w g).getD w.length d =
              F g (g.inputs.map fun i => w.getD i d) := by
            simp [stepR, List.getD_eq_getElem?_getD]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [if_pos hi, R_getD_lt F d gs (stepR F d w g) i (by simp [stepR]; omega)]
            simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]; exact R_getD_ge d w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simpa using hj
          have key := ih (stepR F d w g) j hj'
          have hl : (stepR F d w g).length = w.length + 1 := by simp [stepR]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key

    let weight (g : Gate) (d : List ℕ) := if g.op=.and then d.sum else d.foldr max 0
    let degree {n} (C : Circuit) (t : Fin n) (w : ℕ) := (C.lineDegrees n {t.val}).getD w 0
    let seeds {n} (t : Fin n) := (List.range n).map fun i => if i∈({t.val} : Finset ℕ) then 1 else 0

    have degInput {n} (C : Circuit) (t : Fin n) (w : ℕ) (hw : w<n) :
        degree C t w = if w=t.val then 1 else 0 := by
      change (C.gates.foldl (stepR weight 0) (seeds t)).getD w 0=_
      have len : (seeds t).length=n := by simp [seeds]
      rw [R_getD_lt _ _ _ _ w (by omega)]
      simp [seeds,List.getD_eq_getElem?_getD,hw]

    have operands {n} (C : Circuit) (ao : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length) :
        ∃ a b,(gateAt C j).inputs=[a,b] ∧ a<n+j ∧ b<n+j := by
      obtain ⟨a,b,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
      exact ⟨a,b,eq,ao.2.1 j hj a (by simp [eq]),ao.2.1 j hj b (by simp [eq])⟩

    have degGate {n} (C : Circuit) (t : Fin n) {j a b : ℕ} (hj : j<C.gates.length)
        (row : (gateAt C j).inputs=[a,b]) (ha : a<n+j) (hb : b<n+j) :
        degree C t (n+j)=if (gateAt C j).op=.and then degree C t a+degree C t b else max (degree C t a) (degree C t b) := by
      have step := R_getD_gate weight 0 C.gates (seeds t) j hj
      have length : (seeds t).length=n := by simp [seeds]
      rw [length,← gateAt_eq hj,row] at step
      have read (w) : (C.gates.foldl (stepR weight 0) (seeds t)).getD w 0=degree C t w := rfl
      simp only [read] at step
      simpa [weight,ha,hb] using step

    have degChild {n} (C : Circuit) (ao : IsAO2 n C) (t : Fin n) {j a : ℕ}
        (hj : j<C.gates.length) (ha : a∈(gateAt C j).inputs) : degree C t a ≤ degree C t (n+j) := by
      obtain ⟨p,q,row,lp,lq⟩ := operands C ao j hj
      have one : a=p ∨ a=q := by simpa [row] using ha
      rw [degGate C t hj row lp lq]
      rcases one with rfl|rfl <;> split <;> omega

    have boolAt (x : Fin 14→Bool) {j a b : ℕ} (hj : j<D.gates.length)
        (eq : (gateAt D j).inputs=[a,b]) : wireVal 14 D (14+j) x =
          (gateAt D j).op.eval [wireVal 14 D a x,wireVal 14 D b x] := by
      have atJ : D.gates[j]?=some (gateAt D j) := by rw [gateAt_eq hj]; exact List.getElem?_eq_getElem hj
      have one := wireVal_gate D x j (gateAt D j) atJ (ao.2.1 j hj)
      simpa only [eq,List.map_cons,List.map_nil] using one
    have countMark (s t : Fin 14) (j : ℕ) (hand : (gateAt D j).op=.and)
        (live : 14+j=D.output ∨ InCone 14 D j (D.output-14))
        (on : gateVal 14 D j (pairInput s t)=true)
        (off : ∀ i : Fin 2,wireVal 14 D (opnd D j i) (pairInput s s)=false) : 2≤D.lineDeg 14 {t.val} := by
      have hj : j<D.gates.length := by
        by_contra! bad
        change (D.gates.getD j _).op=.and at hand
        rw [List.getD_eq_default _ _ bad] at hand
        cases hand
      have sensitive (w : ℕ) (hw : w<14+D.gates.length) : degree D t w=0 →
          wireVal 14 D w (pairInput s t)=wireVal 14 D w (pairInput s s) := by
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro zero
          by_cases raw : w<14
          · rw [degInput D t w raw] at zero
            have ne : (⟨w,raw⟩ : Fin 14)≠t := by
              intro eq
              have h : w=t.val := congrArg Fin.val eq
              rw [if_pos h] at zero
              omega
            rw [wireVal_input D _ w raw,wireVal_input D _ w raw]
            change decide ((⟨w,raw⟩ : Fin 14)=s ∨ (⟨w,raw⟩ : Fin 14)=t)=decide ((⟨w,raw⟩ : Fin 14)=s ∨ (⟨w,raw⟩ : Fin 14)=s)
            simp [ne]
          obtain ⟨k,rfl⟩ : ∃ k,w=14+k := ⟨w-14,by omega⟩
          have hk : k<D.gates.length := by omega
          obtain ⟨a,b,ab,ha,hb⟩ := operands D ao k hk
          have da := degChild D ao t hk (a:=a) (by simp [ab])
          have db := degChild D ao t hk (a:=b) (by simp [ab])
          rw [boolAt _ hk ab,boolAt _ hk ab,ih a ha (by omega) (by omega),ih b hb (by omega) (by omega)]
      obtain ⟨a,b,ab,ha,hb⟩ := operands D ao j hj
      change wireVal 14 D (14+j) (pairInput s t)=true at on
      rw [boolAt _ hj ab,hand] at on
      have both : wireVal 14 D a (pairInput s t)=true ∧ wireVal 14 D b (pairInput s t)=true := by
        have evaluate : ∀ x y : Bool, GateOp.and.eval [x,y]=(x && y) := by decide +kernel
        simpa only [evaluate,Bool.and_eq_true] using on
      have needs (w : ℕ) (hw : w<14+j) (yes : wireVal 14 D w (pairInput s t)=true)
          (no : wireVal 14 D w (pairInput s s)=false) : 1≤degree D t w := by
        by_contra! small
        have eq := sensitive w (by omega) (by omega)
        rw [yes,no] at eq
        cases eq
      have fa := off 0
      have fb := off 1
      change wireVal 14 D ((gateAt D j).inputs.getD 0 0) (pairInput s s)=false at fa
      change wireVal 14 D ((gateAt D j).inputs.getD 1 0) (pairInput s s)=false at fb
      rw [ab] at fa fb
      have da := needs a ha both.1 fa
      have db := needs b hb both.2 fb
      have high : 2≤degree D t (14+j) := by
        rw [degGate D t hj ab ha hb,hand]
        simp only [ite_true]
        omega
      change 2≤degree D t D.output
      rcases live with eq|con
      · simpa [←eq] using high
      have path (k : ℕ) (jk : InCone 14 D j k) : degree D t (14+j)≤degree D t (14+k) := by
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          obtain ⟨hk,w,mem,lo,hi,eq|prev⟩ := (inCone_iff D j k).mp jk
          · have step := degChild D ao t hk mem
            have e : 14+j=w := by omega
            rwa [e]
          · have step := degChild D ao t hk mem
            have prior := ih (w-14) (by omega) prev
            have e : 14+(w-14)=w := by omega
            rw [e] at prior
            exact prior.trans step
      obtain ⟨_,w,_,lo,hi,_⟩ := (inCone_iff D j _).mp con
      have e : 14+(D.output-14)=D.output := by omega
      simpa only [e] using high.trans (path _ con)
    have swap : pairInput (7 : Fin 14) 0=pairInput 0 7 := by
      funext i
      revert i
      decide +kernel
    have high7 := countMark 0 7 k1 hk1And firstLive hk1_07 hk1_00
    have high0 := countMark 7 0 k2 hk2And hk2Live (by rw [swap]; exact hk2_07) hk2_77
    have leaves := rankBound D ao hFano high0 high7
    let rows : List ℕ := [16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
    let sample := fun (k : Fin 58) (i : Fin 14) => (rows.getD i.val 0).testBit k.val
    have labels : ∀ k : Fin 58,
        (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
          sample k (Fin.castAdd 7 p)=true ∧ sample k (Fin.natAdd 7 l)=true) ↔ k.val<21 := by
      dsimp only [sample,rows]
      decide +kernel
    have truth (k : Fin 58) : D.eval (List.ofFn (sample k))=decide (k.val<21) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff,hFano]
      exact labels k
    exact finiteCase D hSize ao distinct leaves truth k1 k2 hCone12 hk2Live
      ⟨hk1And,hk1_07,hk1_00⟩ ⟨hk2And,hk2_07,hk2_77⟩
  rintro ⟨C, hSize, hGates, hFano, k1, k2, hConeOr, hk1And, hk1Live, hk1_07, hk1_00,
    hk2And, hk2Live, hk2_07, hk2_77⟩
  rcases hConeOr with h12 | h21
  · exact oriented C k1 k2 hSize hGates hFano h12 hk1And hk1_07 hk1_00 hk2And hk2Live hk2_07 hk2_77
  · let pol : Fin 14 → Fin 14 := fun i =>
      Fin.ofNat 14 (if i.val < 7 then 7 + (7 - i.val) % 7 else (14 - i.val) % 7)
    have hpol_inv : ∀ i : Fin 14, pol (pol i) = i := by dsimp only [pol]; decide
    have hpol_cast : ∀ u : Fin 7, pol (Fin.castAdd 7 u) = Fin.natAdd 7 (-u) := by
      dsimp only [pol]; decide
    have hpol_nat : ∀ t : Fin 7, pol (Fin.natAdd 7 t) = Fin.castAdd 7 (-t) := by
      dsimp only [pol]; decide
    have hpol_inc : ∀ u t : Fin 7,
        ((-t) = (-u) ∨ (-t) = (-u) + 1 ∨ (-t) = (-u) + 3) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3) := by decide
    let mapW : ℕ → ℕ := fun r => if h : r < 14 then (pol ⟨r, h⟩).val else r
    have hmapW_inj : ∀ a b : ℕ, mapW a = mapW b → a = b := by
      intro a b hab
      by_cases ha : a < 14 <;> by_cases hb : b < 14
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have h2 := congrArg pol (Fin.ext hab)
        rw [hpol_inv, hpol_inv] at h2
        exact congrArg Fin.val h2
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have := (pol ⟨a, ha⟩).isLt; omega
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab
        have := (pol ⟨b, hb⟩).isLt; omega
      · simp only [mapW, ha, hb, ↓reduceDIte] at hab; exact hab
    have hmapW_lt : ∀ a j : ℕ, a < 14 + j → mapW a < 14 + j := by
      intro a j haj
      by_cases ha : a < 14
      · simp only [mapW, ha, ↓reduceDIte]
        have := (pol ⟨a, ha⟩).isLt; omega
      · simp only [mapW, ha, ↓reduceDIte]; exact haj
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩, mapW C.output⟩
    have hSize' : C'.size ≤ 27 := by
      change (C.gates.map _).length ≤ 27
      rw [List.length_map]; exact hSize
    have hGates' : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C'.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
      intro j g hgj
      simp only [C', List.getElem?_map] at hgj
      rcases hCgj : C.gates[j]? with _ | g0
      · rw [hCgj] at hgj; simp at hgj
      · rw [hCgj] at hgj
        have hge := Option.some.inj hgj
        subst hge
        obtain ⟨hop, a, b, hinp, hne, ha, hb⟩ := hGates j g0 hCgj
        exact ⟨hop, mapW a, mapW b, by simp [hinp], fun heq => hne (hmapW_inj a b heq),
          hmapW_lt a j ha, hmapW_lt b j hb⟩
    have hWireMap : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.gates.length →
        PEqualNP.CleanedNonEdge.wireVal 14 C' (mapW r) x =
          PEqualNP.CleanedNonEdge.wireVal 14 C r (fun i => x (pol i)) := by
      intro x r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr
        by_cases hr14 : r < 14
        · simp only [mapW, hr14, ↓reduceDIte]
          rw [wireVal_input C' x _ (pol ⟨r, hr14⟩).isLt, wireVal_input C _ r hr14]
        · have hmap_eq : mapW r = r := by simp [mapW, hr14]
          rw [hmap_eq]
          let k := r - 14
          have hk : k < C.gates.length := by omega
          have hrk : r = 14 + k := by omega
          rw [hrk]
          have hCgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
          have hC'gk : C'.gates[k]? = some ⟨C.gates[k].op, C.gates[k].inputs.map mapW⟩ := by
            simp [C', List.getElem?_map, hCgk]
          obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates k C.gates[k] hCgk
          have hltC : ∀ i ∈ C.gates[k].inputs, i < 14 + k := by
            intro i hi; rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
          have hltC' : ∀ i ∈ (C.gates[k].inputs.map mapW), i < 14 + k := by
            intro i hi
            obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
            exact hmapW_lt i0 k (hltC i0 hi0)
          rw [wireVal_gate C' x k _ hC'gk hltC', wireVal_gate C _ k _ hCgk hltC, List.map_map]
          congr 1
          exact List.map_congr_left fun i hi =>
            ih i (by have := hltC i hi; omega) (by have := hltC i hi; omega)
    have hEvalMap : ∀ x : Fin 14 → Bool,
        C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (pol i))) := by
      intro x
      by_cases ho : C.output < 14 + C.gates.length
      · exact hWireMap x C.output ho
      · have ho' : 14 + C'.gates.length ≤ C'.output := by
          have h14 : ¬ C.output < 14 := by omega
          simp [C', mapW, h14]; omega
        change PEqualNP.CleanedNonEdge.wireVal 14 C' C'.output x =
          PEqualNP.CleanedNonEdge.wireVal 14 C C.output (fun i => x (pol i))
        rw [wireVal_ge C' x C'.output ho', wireVal_ge C _ C.output (by omega)]
    have hFano' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
      intro x
      rw [hEvalMap x, hFano (fun i => x (pol i))]
      constructor
      · rintro ⟨u, t, hinc, hu, ht⟩
        rw [hpol_cast] at hu
        rw [hpol_nat] at ht
        exact ⟨-t, -u, (hpol_inc u t).mpr hinc, ht, hu⟩
      · rintro ⟨u, t, hinc, hu, ht⟩
        refine ⟨-t, -u, ?_, ?_, ?_⟩
        · have h := (hpol_inc (-t) (-u)).mp
          simp only [neg_neg] at h
          exact h hinc
        · rw [hpol_cast, neg_neg]; exact ht
        · rw [hpol_nat, neg_neg]; exact hu
    have hfilt_mapW : ∀ (l : List ℕ) (m : ℕ),
        (l.map mapW).filter (fun w => decide (14 ≤ w ∧ w < m)) =
          l.filter (fun w => decide (14 ≤ w ∧ w < m)) := by
      intro l m
      induction l with
      | nil => rfl
      | cons a as ih =>
        simp only [List.map_cons]
        by_cases ha : a < 14
        · have hm : mapW a < 14 := by simp only [mapW, ha, ↓reduceDIte]; exact (pol ⟨a, ha⟩).isLt
          have d1 : decide (14 ≤ mapW a ∧ mapW a < m) = false := decide_eq_false (by omega)
          have d2 : decide (14 ≤ a ∧ a < m) = false := decide_eq_false (by omega)
          rw [List.filter_cons, List.filter_cons, d1, d2]
          exact ih
        · have hm : mapW a = a := by simp [mapW, ha]
          rw [hm, List.filter_cons, List.filter_cons, ih]
    have hcones_eq : PEqualNP.EdgeOwnership.cones 14 C' = PEqualNP.EdgeOwnership.cones 14 C := by
      change (C.gates.map fun g => (⟨g.op, g.inputs.map mapW⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
          (PEqualNP.EdgeOwnership.coneStep 14) [] =
        C.gates.foldl (PEqualNP.EdgeOwnership.coneStep 14) []
      have gen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
          (gs.map fun g => (⟨g.op, g.inputs.map mapW⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
            (PEqualNP.EdgeOwnership.coneStep 14) cs =
          gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs := by
        intro gs
        induction gs with
        | nil => intro cs; rfl
        | cons g gs ih =>
          intro cs
          simp only [List.map_cons, List.foldl_cons]
          have hcs : PEqualNP.EdgeOwnership.coneStep 14 cs ⟨g.op, g.inputs.map mapW⟩ =
              PEqualNP.EdgeOwnership.coneStep 14 cs g := by
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
            rw [hfilt_mapW]
          rw [hcs, ih]
      exact gen C.gates []
    have hInCone_eq : ∀ i j : ℕ,
        PEqualNP.EdgeOwnership.InCone 14 C' i j ↔ PEqualNP.EdgeOwnership.InCone 14 C i j := by
      intro i j
      unfold PEqualNP.EdgeOwnership.InCone
      rw [hcones_eq]
    have hgateAt_op : ∀ j : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op =
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op := by
      intro j
      by_cases hj : j < C.gates.length
      · have h1 : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
        have h2 : C'.gates[j]? = some ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
          simp [C', List.getElem?_map, h1]
        change (C'.gates.getD j _).op = (C.gates.getD j _).op
        simp [List.getD_eq_getElem?_getD, h1, h2]
      · have h1 : C.gates[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : C'.gates[j]? = none := List.getElem?_eq_none (by simp [C']; omega)
        change (C'.gates.getD j _).op = (C.gates.getD j _).op
        simp [List.getD_eq_getElem?_getD, h1, h2]
    have hopnd_eq : ∀ j < C.gates.length, ∀ b : Fin 2,
        PEqualNP.TopForm.opnd C' j b = mapW (PEqualNP.TopForm.opnd C j b) ∧
        PEqualNP.TopForm.opnd C j b < 14 + C.gates.length := by
      intro j hj b
      have h1 : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have h2 : C'.gates[j]? = some ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
        simp [C', List.getElem?_map, h1]
      obtain ⟨_, a0, b0, hinp, _, ha0, hb0⟩ := hGates j C.gates[j] h1
      have ga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j _ = _; simp [List.getD_eq_getElem?_getD, h1]
      have ga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          ⟨C.gates[j].op, C.gates[j].inputs.map mapW⟩ := by
        change C'.gates.getD j _ = _; simp [List.getD_eq_getElem?_getD, h2]
      fin_cases b <;> dsimp only [PEqualNP.TopForm.opnd] <;> simp [ga1, ga2, hinp] <;> omega
    have hk1_lt : k1 < C.gates.length := (inCone_iff C k2 k1).mp h21 |>.1
    have hk2_lt : k2 < C.gates.length := by
      by_contra h
      have hf := wireVal_ge C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k2) (by omega)
      change PEqualNP.EdgeOwnership.gateVal 14 C k2 _ = false at hf
      rw [hk2_07] at hf; cases hf
    have hp07_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 := by
      funext i; dsimp only [pol]; revert i; decide
    have hp00_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 := by
      funext i; dsimp only [pol]; revert i; decide
    have hp77_pol : (fun i : Fin 14 => PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (pol i)) =
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 := by
      funext i; dsimp only [pol]; revert i; decide
    have hout_eq : C'.output = C.output := by
      by_cases ho14 : C.output < 14
      · exfalso
        have h07_t : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = true :=
          (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
        have h00_f : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0)) = false := by
          cases h : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0))
          · rfl
          · obtain ⟨u, t, _, hu, ht⟩ := (hFano _).mp h
            have habs : ∀ u t : Fin 7, ¬ (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (Fin.castAdd 7 u) = true ∧
              PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 (Fin.natAdd 7 t) = true) := by decide
            exact False.elim (habs u t ⟨hu, ht⟩)
        have h77_f : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7)) = false := by
          cases h : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7))
          · rfl
          · obtain ⟨u, t, _, hu, ht⟩ := (hFano _).mp h
            have habs : ∀ u t : Fin 7, ¬ (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (Fin.castAdd 7 u) = true ∧
              PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 (Fin.natAdd 7 t) = true) := by decide
            exact False.elim (habs u t ⟨hu, ht⟩)
        have e1 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 ⟨C.output, ho14⟩ = true := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) C.output ho14]
          exact h07_t
        have e2 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 ⟨C.output, ho14⟩ = false := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) C.output ho14]
          exact h00_f
        have e3 : PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 ⟨C.output, ho14⟩ = false := by
          rw [← wireVal_input C (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) C.output ho14]
          exact h77_f
        have habs : ∀ i : Fin 14, ¬ (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 i = true ∧
          PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 i = false ∧
          PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 i = false) := by decide
        exact habs ⟨C.output, ho14⟩ ⟨e1, e2, e3⟩
      · simp [C', mapW, ho14]
    refine oriented C' k2 k1 hSize' hGates' hFano' ((hInCone_eq k2 k1).mpr h21)
      (by rw [hgateAt_op]; exact hk2And) ?_ ?_ (by rw [hgateAt_op]; exact hk1And) ?_ ?_ ?_
    · have hw := hWireMap (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k2) (by omega)
      have hm : mapW (14 + k2) = 14 + k2 := by simp [mapW]
      rw [hm, hp07_pol] at hw
      exact hw.trans hk2_07
    · intro b
      obtain ⟨heq, hlt⟩ := hopnd_eq k2 hk2_lt b
      rw [heq, hWireMap _ _ hlt, hp00_pol]
      exact hk2_77 b
    · rw [hout_eq]
      rcases hk1Live with heq | hc
      · exact Or.inl heq
      · exact Or.inr ((hInCone_eq k1 (C.output - 14)).mpr hc)
    · have hw := hWireMap (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) (14 + k1) (by omega)
      have hm : mapW (14 + k1) = 14 + k1 := by simp [mapW]
      rw [hm, hp07_pol] at hw
      exact hw.trans hk1_07
    · intro b
      obtain ⟨heq, hlt⟩ := hopnd_eq k1 hk1_lt b
      rw [heq, hWireMap _ _ hlt, hp77_pol]
      exact hk1_00 b
