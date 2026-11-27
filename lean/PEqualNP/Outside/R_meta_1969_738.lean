import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Trace each witness either back to an earlier AND that requires both endpoints,
-- or forward to the AND that prevents a true singleton from reaching the output.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1969_738
    (hClean : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let v (j : ℕ) (x y : Fin 14) := gateVal 14 C j (pairInput x y)
      let a (j : ℕ) := (gateAt C j).op = GateOp.and
      let c := InCone 14 C
      let r (x : Fin 14) (j : ℕ) :=
        a j ∧ (14 + j = C.output ∨ c j (C.output - 14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput x x) = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j →
      (∃ k m, a k ∧ a m ∧ c k i ∧ c m j ∧
        v i 7 7 = false ∧ v j 0 0 = false ∧ v k 0 7 = true ∧ v m 0 7 = true ∧
        v k 0 0 = false ∧ v k 7 7 = false ∧ v m 0 0 = false ∧ v m 7 7 = false) → False)
    (hDirty : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let v (j : ℕ) (x y : Fin 14) := gateVal 14 C j (pairInput x y)
      let a (j : ℕ) := (gateAt C j).op = GateOp.and
      let c := InCone 14 C
      let r (x : Fin 14) (j : ℕ) :=
        a j ∧ (14 + j = C.output ∨ c j (C.output - 14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput x x) = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j →
      (∃ k, a k ∧
        ((c i k ∧ v i 7 7 = true ∧ v k 7 7 = false) ∨
         (c j k ∧ v j 0 0 = true ∧ v k 0 0 = false))) → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  have repeat_has_partner (C : Circuit) (p l : Fin 14) (j : ℕ)
      (hwf : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
        (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14 + k ∧ b < 14 + k)
      (hand : (gateAt C j).op = .and)
      (hlive : 14 + j = C.output ∨ InCone 14 C j (C.output - 14))
      (hpair : gateVal 14 C j (pairInput p l) = true)
      (hsingle : ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput p p) = false)
      (houtl : C.eval (List.ofFn (pairInput l l)) = false) :
      ∃ m, (gateAt C m).op = .and ∧
        ((gateVal 14 C j (pairInput l l) = false ∧ InCone 14 C m j ∧ gateVal 14 C m (pairInput p l) = true ∧
          gateVal 14 C m (pairInput p p) = false ∧ gateVal 14 C m (pairInput l l) = false) ∨
         (gateVal 14 C j (pairInput l l) = true ∧ InCone 14 C j m ∧ gateVal 14 C m (pairInput l l) = false)) := by
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
    have eval_and : ∀ b1 b2 : Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
    have eval_or : ∀ b1 b2 : Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
    let wv := wireVal 14 C
    let pos := pairInput p l
    let sp := pairInput p p
    let sl := pairInput l l
    have gate_info (k : ℕ) (hk : k < C.gates.length) :
        ∃ a b, (gateAt C k).inputs = [a,b] ∧ a < 14 + k ∧ b < 14 + k ∧
          ((gateAt C k).op = .and ∨ (gateAt C k).op = .or) ∧
          ∀ z, wv (14+k) z = (gateAt C k).op.eval [wv a z, wv b z] := by
      have hg : C.gates[k]? = some (gateAt C k) := by
        change C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩)
        rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
      obtain ⟨hop, a, b, hargs, _, ha, hb⟩ := hwf k _ hg
      refine ⟨a, b, hargs, ha, hb, hop, fun z => ?_⟩
      dsimp only [wv]
      rw [wireVal_gate C z k _ hg, hargs]
      · rfl
      · simp [hargs, ha, hb]
    have origin :
        ∀ w, wv w pos = true → wv w sp = false → wv w sl = false →
          ∃ m, (gateAt C m).op = .and ∧ gateVal 14 C m pos = true ∧
            gateVal 14 C m sp = false ∧ gateVal 14 C m sl = false ∧
            (w = 14 + m ∨ InCone 14 C m (w - 14)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hp hs ht
        by_cases hin : w < 14
        · change wireVal 14 C w pos = true at hp
          change wireVal 14 C w sp = false at hs
          change wireVal 14 C w sl = false at ht
          rw [wireVal_input C pos w hin] at hp
          rw [wireVal_input C sp w hin] at hs
          rw [wireVal_input C sl w hin] at ht
          let v : Fin 14 := ⟨w, hin⟩
          change decide (v = p ∨ v = l) = true at hp
          change decide (v = p ∨ v = p) = false at hs
          change decide (v = l ∨ v = l) = false at ht
          simp at hp hs ht
          tauto
        have hw : w < 14 + C.gates.length := by
          by_contra! bad
          have hf : wv w pos = false := wireVal_ge C pos w bad
          rw [hf] at hp
          cases hp
        let k := w - 14
        have hwk : 14 + k = w := by dsimp [k]; omega
        have hk : k < C.gates.length := by omega
        obtain ⟨a,b,hab,ha,hb,hop,heval⟩ := gate_info k hk
        rcases hop with hand' | hor
        · refine ⟨k, hand', ?_, ?_, ?_, Or.inl hwk.symm⟩
          all_goals change wv (14+k) _ = _; rwa [hwk]
        · have horEval (z) : wv w z = (wv a z || wv b z) := by
            rw [← hwk, heval, hor, eval_or]
          rw [horEval, Bool.or_eq_true] at hp
          rw [horEval, Bool.or_eq_false_iff] at hs ht
          have lift (u : ℕ) (humem : u ∈ (gateAt C k).inputs) (hu : u < 14+k)
              (htrue : wv u pos = true) (hsp : wv u sp = false) (hsl : wv u sl = false) :
              ∃ m, (gateAt C m).op = .and ∧ gateVal 14 C m pos = true ∧
                gateVal 14 C m sp = false ∧ gateVal 14 C m sl = false ∧
                (w = 14 + m ∨ InCone 14 C m (w-14)) := by
            obtain ⟨m, hm, hmp, hms, hmt, hreach⟩ := ih u (by omega) htrue hsp hsl
            refine ⟨m, hm, hmp, hms, hmt, Or.inr ((inCone_iff C m k).2
              ⟨hk, u, humem, ?_, hu, ?_⟩)⟩
            · rcases hreach with heq | hc
              · omega
              · obtain ⟨_, v, _, hvl, hvh, _⟩ := (inCone_iff C m (u-14)).1 hc
                omega
            · exact hreach.imp_left (by omega)
          exact hp.elim
            (fun hh => lift a (by simp [hab]) ha hh hs.1 ht.1)
            (fun hh => lift b (by simp [hab]) hb hh hs.2 ht.2)
    have blocked :
        ∀ k, InCone 14 C j k → wv (14+k) sl = false → wv (14+j) sl = true →
          ∃ m, (gateAt C m).op = .and ∧ InCone 14 C j m ∧ wv (14+m) sl = false := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hc hv hj
        obtain ⟨hk, a, ha, hal, hah, har⟩ := (inCone_iff C j k).1 hc
        obtain ⟨b,c,hbc,hb,hc',hop,heval⟩ := gate_info k hk
        rcases hop with hAnd | hOr
        · exact ⟨k, hAnd, hc, hv⟩
        · rw [heval, hOr, eval_or, Bool.or_eq_false_iff] at hv
          have haft : wv a sl = false := by
            rw [hbc] at ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with hab | hac
            · simpa [hab] using hv.1
            · simpa [hac] using hv.2
          have ea : 14 + (a-14) = a := by omega
          rcases har with heq | hcone
          · have eq : 14+j = a := by omega
            rw [eq, haft] at hj
            cases hj
          · exact ih (a-14) (by omega) hcone (by simpa only [ea] using haft) hj
    have hj : j < C.gates.length := by
      by_contra! h
      change (C.gates.getD j ⟨.or, []⟩).op = .and at hand
      rw [List.getD_eq_default _ _ h] at hand
      cases hand
    obtain ⟨a,b,hab,ha,hb,_,heval⟩ := gate_info j hj
    have heval' (z) : wv (14+j) z = (wv a z && wv b z) := by
      rw [heval, hand, eval_and]
    have hpos : wv a pos = true ∧ wv b pos = true := by
      change wv (14+j) pos = true at hpair
      rwa [heval', Bool.and_eq_true] at hpair
    have hspa : wv a sp = false := by
      have h := hsingle 0
      change wv ((gateAt C j).inputs.getD 0 0) sp = false at h
      rw [hab] at h
      exact h
    have hspb : wv b sp = false := by
      have h := hsingle 1
      change wv ((gateAt C j).inputs.getD 1 0) sp = false at h
      rw [hab] at h
      exact h
    cases hsl : wv (14+j) sl with
    | true =>
      have ho : wv C.output sl = false := houtl
      rcases hlive with hEq | hCone
      · rw [← hEq, hsl] at ho
        cases ho
      · obtain ⟨hvalid, u, _, hu, hu', _⟩ := (inCone_iff C j (C.output-14)).1 hCone
        have ho' : wv (14+(C.output-14)) sl = false := by
          rwa [show 14+(C.output-14) = C.output by omega]
        obtain ⟨m, hm, hjm, hml⟩ := blocked (C.output-14) hCone ho' hsl
        exact ⟨m, hm, Or.inr ⟨hsl, hjm, hml⟩⟩
    | false =>
      have hs := hsl
      rw [heval', Bool.and_eq_false_iff] at hsl
      have finish (u : ℕ) (huMem : u ∈ (gateAt C j).inputs) (hu : u < 14 + j)
          (hup : wv u pos = true) (husp : wv u sp = false) (husl : wv u sl = false) :
          ∃ m, (gateAt C m).op = .and ∧
            ((gateVal 14 C j sl = false ∧ InCone 14 C m j ∧ gateVal 14 C m pos = true ∧
              gateVal 14 C m sp = false ∧ gateVal 14 C m sl = false) ∨
             (gateVal 14 C j sl = true ∧ InCone 14 C j m ∧ gateVal 14 C m sl = false)) := by
        obtain ⟨m, hm, hmp, hms, hmt, hreach⟩ := origin u hup husp husl
        refine ⟨m, hm, Or.inl ⟨hs, (inCone_iff C m j).2 ⟨hj, u, huMem, ?_, hu, ?_⟩, hmp, hms, hmt⟩⟩
        · rcases hreach with heq | hcone
          · omega
          · obtain ⟨_, v, _, hv, hv', _⟩ := (inCone_iff C m (u-14)).1 hcone
            omega
        · exact hreach.imp_left (by omega)
      exact hsl.elim
        (fun hh => finish a (by simp [hab]) ha hpos.1 hspa hh)
        (fun hh => finish b (by simp [hab]) hb hpos.2 hspb hh)
  rintro ⟨C, hsize, hwf, heval, i, j, hne, hij, hji, hi, hilive, hipair, hi0,
    hj, hjlive, hjpair, hj7⟩
  have hcfg (k : ℕ) (hk : k < C.gates.length) :
      ((gateAt C k).op = .and ∨ (gateAt C k).op = .or) ∧
      ∃ a b : ℕ, (gateAt C k).inputs = [a,b] ∧ a ≠ b ∧ a < 14+k ∧ b < 14+k := by
    apply hwf k
    change C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  have hao : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
      have h := (hcfg k hk).1
      change (C.gates.getD k ⟨.or, []⟩).op = .and ∨
        (C.gates.getD k ⟨.or, []⟩).op = .or at h
      rwa [List.getD_eq_getElem _ _ hk] at h
    · intro k hk w hw
      obtain ⟨a,b,hab,_,ha,hb⟩ := (hcfg k hk).2
      change w ∈ (gateAt C k).inputs at hw
      rw [hab] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
      obtain ⟨a,b,hab,_,_,_⟩ := (hcfg k hk).2
      rw [← List.getD_eq_getElem _ ⟨GateOp.or, []⟩ hk]
      change (gateAt C k).inputs.length = 2
      simp [hab]
  have hdistinct : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨a,b,hab,hab',_,_⟩ := (hcfg k hk).2
    rw [← List.getD_eq_getElem _ ⟨GateOp.or, []⟩ hk]
    change (gateAt C k).inputs.Nodup
    simpa [hab] using hab'
  have no0 : C.eval (List.ofFn (pairInput (0 : Fin 14) 0)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have no (l : Fin 7) : pairInput (0 : Fin 14) 0 (Fin.natAdd 7 l) = false := by decide +revert
    obtain ⟨p,l,_,_,hl⟩ := (heval _).1 h
    rw [no l] at hl
    cases hl
  have no7 : C.eval (List.ofFn (pairInput (7 : Fin 14) 7)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have no (p : Fin 7) : pairInput (7 : Fin 14) 7 (Fin.castAdd 7 p) = false := by decide +revert
    obtain ⟨p,l,_,hp,_⟩ := (heval _).1 h
    rw [no p] at hp
    cases hp
  have flip : pairInput (7 : Fin 14) 0 = pairInput 0 7 := by
    funext x
    change decide (x = 7 ∨ x = 0) = decide (x = 0 ∨ x = 7)
    simp only [or_comm]
  obtain ⟨k, hk, hki | hik⟩ := repeat_has_partner C 0 7 i hwf hi hilive hipair hi0 no7
  · have hp : gateVal 14 C j (pairInput (7 : Fin 14) 0) = true := flip.symm ▸ hjpair
    obtain ⟨m, hm, hmj | hjm⟩ := repeat_has_partner C 7 0 j hwf hj hjlive hp hj7 no0
    · rw [flip] at hmj
      exact hClean C hsize hao hdistinct heval i j hne hij hji
        ⟨hi, hilive, hipair, hi0⟩ ⟨hj, hjlive, hjpair, hj7⟩
        ⟨k, m, hk, hm, hki.2.1, hmj.2.1, hki.1, hmj.1, hki.2.2.1, hmj.2.2.1,
          hki.2.2.2.1, hki.2.2.2.2, hmj.2.2.2.2, hmj.2.2.2.1⟩
    · exact hDirty C hsize hao hdistinct heval i j hne hij hji
        ⟨hi, hilive, hipair, hi0⟩ ⟨hj, hjlive, hjpair, hj7⟩
        ⟨m, hm, Or.inr ⟨hjm.2.1, hjm.1, hjm.2.2⟩⟩
  · exact hDirty C hsize hao hdistinct heval i j hne hij hji
      ⟨hi, hilive, hipair, hi0⟩ ⟨hj, hjlive, hjpair, hj7⟩
      ⟨k, hk, Or.inl ⟨hik.2.1, hik.1, hik.2.2⟩⟩
