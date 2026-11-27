import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_5962_1
    (dirty : ∀ C : Circuit, C.size ≤ 27 →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) →
    2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
    ∃ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j ∧ u ≠ v ∧
      gateVal 14 C j (pairInput u v)=true ∧ C.eval (List.ofFn (pairInput u v))=false)
    (finite : ∀ C : Circuit,
    let rows : List ℕ := [16771220242439,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,182572334459126281,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916]
    let mark := fun (j : ℕ) (v : Fin 14) =>
      (gateAt C j).op=.and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7)=true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v)=false
    C.size ≤ 27 → IsAO2 14 C →
    (∀ k : Fin 58, C.eval (List.ofFn (fun i : Fin 14 => (rows.getD i.val 0).testBit k.val)) = decide (k.val<21)) →
    (∃ w : ℕ, 14 ≤ w ∧ 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count w) →
    ∀ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j → u≠v →
      gateVal 14 C j (pairInput u v)=true → C.eval (List.ofFn (pairInput u v))=false →
      ∀ a b, (InCone 14 C a b ∨ InCone 14 C b a) → mark a 0 → ¬mark b 7) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) →       (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) →         (∃ (x5 : ℕ), (14 : ℕ) ≤ x5 ∧ (2 : ℕ) ≤ List.count x5 (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ∧ ∀ (x6 : Fin (16 : ℕ)), ∃ (x7 : Fin (14 : ℕ) → Bool), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x5 x7 = x1.eval (List.ofFn x7) ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x5 x7 ≠ if x8 : ↑x6 < (14 : ℕ) then x7 (⟨↑x6, x8⟩ : Fin (14 : ℕ)) else Decidable.decide (↑x6 = (15 : ℕ))) →           have x6 : ℕ → Fin (14 : ℕ) → Prop := fun (x6 : ℕ) (x7 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x6 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x6 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x8 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x6 x8) (PEqualNP.EdgeOwnership.pairInput x7 x7) = Bool.false;           ∀ (x7 x8 : ℕ), PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 x7 → x6 x7 (0 : Fin (14 : ℕ)) → ¬x6 x8 (7 : Fin (14 : ℕ))) := by
  have degree_of_mark (D : Circuit) (hGates : ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j)
      (s t : Fin 14) (j : ℕ) (hand : (gateAt D j).op=.and)
      (live : 14+j=D.output ∨ InCone 14 D j (D.output-14))
      (on : gateVal 14 D j (pairInput s t)=true)
      (off : ∀ i : Fin 2, wireVal 14 D (opnd D j i) (pairInput s s)=false) :
      2 ≤ D.lineDeg 14 {t.val} := by
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

  intro C sz legal correct obstruction Mark a b comparison ha hb
  have swap : pairInput (7 : Fin 14) 0=pairInput 0 7 := by
    funext i
    revert i
    decide +kernel
  have d7 := degree_of_mark C legal 0 7 a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  have d0 := degree_of_mark C legal 7 0 b hb.1 hb.2.1 (swap ▸ hb.2.2.1) hb.2.2.2
  obtain ⟨j,u,v,hand,distinct,on,off⟩ := dirty C sz legal correct d0 d7
  obtain ⟨w,internal,reused,_⟩ := obstruction
  have row (j) (hj : j<C.gates.length) := legal j C.gates[j] (List.getElem?_eq_getElem hj)
  have ao : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      exact (row j hj).1
    · intro j hj a ha
      obtain ⟨p,q,op,_,hp,hq⟩ := (row j hj).2
      change a ∈ (C.gates.getD j _).inputs at ha
      rw [List.getD_eq_getElem _ _ hj,op] at ha
      rcases (show a=p ∨ a=q by simpa using ha) with rfl|rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨p,q,op,_⟩ := (row j hj).2
      simp [op]
  let rows : List ℕ := [16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
  let sample := fun (k : Fin 58) (i : Fin 14) => (rows.getD i.val 0).testBit k.val
  have labels : ∀ k : Fin 58,
      (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
        sample k (Fin.castAdd 7 p)=true ∧ sample k (Fin.natAdd 7 l)=true) ↔ k.val<21 := by
    dsimp only [sample,rows]
    decide +kernel
  have truth (k : Fin 58) : C.eval (List.ofFn (sample k))=decide (k.val<21) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff,correct]
    exact labels k
  exact finite C sz ao truth ⟨w,internal,reused⟩ j u v hand distinct on off a b comparison ha hb
