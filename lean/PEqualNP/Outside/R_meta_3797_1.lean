import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves
open PEqualNP.TopForm PEqualNP.HeptadCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3797_1
    (hOut :
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size < 64 →
        2 ≤ andPairs 26 C →
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ 26 + j = C.output) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
          (∀ p l : Fin 13, p ∈ singerLines3 l → D.eval
            (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
              List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
          (∀ Q ∈ quadrangles singerLines3, D.eval (N Q) = false) ∧
          D.size < C.size)
    (hOneReader :
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size < 64 →
        2 ≤ andPairs 26 C →
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
          (readers 26 C j).card = 1 ∧ 26 + j ≠ C.output) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
          (∀ p l : Fin 13, p ∈ singerLines3 l → D.eval
            (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
              List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
          (∀ Q ∈ quadrangles singerLines3, D.eval (N Q) = false) ∧
          D.size < C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x12 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.TopForm.readers (26 : ℕ) x4 x12).card ≤ (1 : ℕ)) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x13 ∧ x2 x13 ∧ x13.size < x4.size := by
  intro D_set Correct Nested C hMono hBack hC hSize _hNested hStrict hPairs hWit
  change (∀ p l : Fin 13, p - l ∈ D_set → C.eval
    (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧ _ at hC
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
  let N' (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D_set))
  have hInc : ∀ p l : Fin 13, p - l ∈ D_set ↔ p ∈ singerLines3 l := by decide
  have hGood (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D_set)).card ≤ 2 := by
    have heq (k : Fin 13) : Q ∩ singerLines3 k = Q.filter (fun u => u - k ∈ D_set) := by
      ext u
      simp [hInc u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
        (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, heq]
  have hInputs (Q : Finset (Fin 13)) : N Q = N' Q := by
    have hTail : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D_set)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← hInc]
      constructor
      · intro h r hr hi
        exact h hi hr
      · intro h r hi hr
        exact h r hr hi
    exact congrArg (fun tail : List Bool => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail) hTail
  have hPos : ∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
      (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))) = true :=
    fun p l h => hC.1 p l ((hInc p l).mpr h)
  have hNeg (Q : Finset (Fin 13)) (hQ : Q ∈ quadrangles singerLines3) :
      C.eval (N Q) = false := by
    rw [hInputs]
    exact hC.2 Q ((hGood Q).mp hQ).1 ((hGood Q).mp hQ).2
  have hAO : IsAO2 26 C := by
    refine ⟨?_, hBack, fun g hg => (hStrict g hg).1⟩
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono g hg).1
  have hBridgeBack : ∀ E : Circuit,
      (∀ p l : Fin 13, p ∈ singerLines3 l → E.eval
        (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
          List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
      (∀ Q ∈ quadrangles singerLines3, E.eval (N Q) = false) →
      (∀ u v : Fin 13, u - v ∈ D_set → E.eval
        (List.ofFn (fun x6 : Fin 13 => decide (x6 = u)) ++
          List.ofFn (fun x6 : Fin 13 => decide (x6 = v))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ k : Fin 13, {x6 ∈ Q | x6 - k ∈ D_set}.card ≤ 2) →
        E.eval (List.ofFn (fun x6 : Fin 13 => decide (x6 ∈ Q)) ++
          List.ofFn (fun x6 : Fin 13 => decide (∀ x7 ∈ Q, x7 - x6 ∉ D_set))) = false) := by
    intro E hEP hEN
    refine ⟨fun u v huv => hEP u v ((hInc u v).mp huv), fun Q hCard hInt => ?_⟩
    change E.eval (N' Q) = false
    rw [← hInputs]
    exact hEN Q ((hGood Q).mpr ⟨hCard, hInt⟩)
  obtain ⟨m, hm, hmOp, hmCards⟩ := hWit
  by_cases hOutEq : 26 + m = C.output
  · obtain ⟨E, hEM, hEB, hEP, hEN, hES⟩ :=
      hOut C hAO (fun g hg => (hStrict g hg).2) hSize hPairs hPos hNeg ⟨m, hm, hmOp, hOutEq⟩
    exact ⟨E, hEM, hEB, hBridgeBack E hEP hEN, hES⟩
  · by_cases hOne : (readers 26 C m).card = 1
    · obtain ⟨E, hEM, hEB, hEP, hEN, hES⟩ :=
        hOneReader C hAO (fun g hg => (hStrict g hg).2) hSize hPairs hPos hNeg
          ⟨m, hm, hmOp, hOne, hOutEq⟩
      exact ⟨E, hEM, hEB, hBridgeBack E hEP hEN, hES⟩
    · have hZero : (readers 26 C m).card = 0 := by omega
      have hNoRead : ∀ k < C.gates.length, 26 + m ∉ (gateAt C k).inputs := by
        intro k hk hmem
        have hEmpty : readers 26 C m = ∅ := Finset.card_eq_zero.mp hZero
        have hIn : k ∈ readers 26 C m :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hmem⟩
        rw [hEmpty] at hIn
        exact (Finset.notMem_empty k) hIn
      let pre := C.gates.take m
      let post := C.gates.drop (m + 1)
      let gj := C.gates[m]
      have hSplit : C.gates = pre ++ gj :: post := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      have hPreLen : pre.length = m := by
        simp [pre, Nat.le_of_lt hm]
      have hPostNoRead : ∀ h ∈ post, 26 + m ∉ h.inputs := by
        intro h hh
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hh
        have hk : m + 1 + idx < C.gates.length := by
          have : C.gates.length = pre.length + (1 + post.length) := by
            rw [hSplit]; simp [List.length_append, List.length_cons]; omega
          omega
        have hgat : gateAt C (m + 1 + idx) = post[idx] := by
          dsimp [gateAt]
          simp [List.getD_eq_getElem?_getD, hSplit,
            List.getElem?_append_right (show pre.length ≤ m + 1 + idx by omega),
            show m + 1 + idx - pre.length = idx + 1 by omega, hidx]
        rw [← hgat]
        exact hNoRead (m + 1 + idx) hk
      let red := eraseRedirect 26 m 0
      let T : Gate → Gate := fun g => ⟨g.op, g.inputs.map red⟩
      let E := eraseGate 26 C m 0
      have hE : E = ⟨pre ++ post.map T, red C.output⟩ := by
        dsimp [E, eraseGate]
        rw [if_pos hm]
      have hEM : Monotone2 E := by
        intro g' hg'
        rw [hE] at hg'
        rcases List.mem_append.mp hg' with hp | hp
        · exact hMono g' (by rw [hSplit]; exact List.mem_append.mpr (Or.inl hp))
        · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
          have hmem : h ∈ C.gates := by
            rw [hSplit]
            exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))
          have hm1 := hMono h hmem
          exact ⟨hm1.1, by simpa [T] using hm1.2⟩
      have hEB : ReadsBack 26 E := by
        intro k hk i hi
        rw [hE] at hk hi
        have hk' : k < pre.length + post.length := by simpa using hk
        by_cases hkp : k < pre.length
        · have heq : gateAt ⟨pre ++ post.map T, red C.output⟩ k = gateAt C k := by
            dsimp [gateAt]
            simp only [hSplit, List.getD_eq_getElem?_getD, List.getElem?_append_left hkp]
          rw [heq] at hi
          exact hBack k (by rw [hSplit]; simp only [List.length_append, List.length_cons]; omega) i hi
        · have hidx : k - pre.length < post.length := by omega
          have heq1 : gateAt ⟨pre ++ post.map T, red C.output⟩ k = T (post[k - pre.length]) := by
            dsimp [gateAt]
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (Nat.le_of_not_lt hkp), hidx]
          have heq2 : gateAt C (k + 1) = post[k - pre.length] := by
            have hsub : k + 1 - pre.length = (k - pre.length) + 1 := by omega
            dsimp [gateAt]
            simp [hSplit, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (show pre.length ≤ k + 1 by omega), hsub, hidx]
          rw [heq1] at hi
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
          have hjLt : j < 26 + (k + 1) := by
            have hkC : k + 1 < C.gates.length := by
              rw [hSplit]; simp only [List.length_append, List.length_cons]; omega
            exact hBack (k + 1) hkC j (by rw [heq2]; exact hj)
          have hjNe : j ≠ 26 + m := fun heq =>
            hPostNoRead (post[k - pre.length]) (List.getElem_mem hidx) (heq ▸ hj)
          dsimp [red, eraseRedirect]
          split_ifs <;> omega
      have hES : E.size < C.size := by
        change E.gates.length < C.gates.length
        rw [hE, hSplit]
        simp [List.length_append, List.length_cons, List.length_map]
      have hEvalEq : ∀ x : List Bool, x.length = 26 → E.eval x = C.eval x := by
        intro x hx
        let wf : List Gate → List Bool → List Bool := fun gs w =>
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        have wf_cons : ∀ (g : Gate) (gs : List Gate) (w : List Bool),
            wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
          fun _ _ _ => rfl
        have wf_append : ∀ (gs1 gs2 : List Gate) (w : List Bool),
            wf (gs1 ++ gs2) w = wf gs2 (wf gs1 w) := by
          intro gs1 gs2 w
          simp [wf, List.foldl_append]
        have wf_len : ∀ (gs : List Gate) (w : List Bool), (wf gs w).length = w.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro w; simp [wf]
          | cons g gs ih =>
            intro w
            have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            simp only [wf, List.foldl_cons] at h1 ⊢
            rw [h1]
            simp
            omega
        have getD_red : ∀ (A E' : List Bool) (b : Bool), A.length = 26 + m →
            ∀ i : ℕ, i ≠ 26 + m → (A ++ E').getD (red i) false = (A ++ b :: E').getD i false := by
          intro A E' b hAL i hi
          dsimp [red, eraseRedirect]
          rw [if_neg hi]
          by_cases hlt : 26 + m < i
          · rw [if_pos hlt]
            have h1 : A.length ≤ i - 1 := by omega
            have h2 : A.length ≤ i := by omega
            have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
              List.getElem?_append_right h2]
            rw [h3, List.getElem?_cons_succ]
          · rw [if_neg hlt]
            have h1 : i < A.length := by omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
        have surg : ∀ (gs : List Gate) (A E' : List Bool) (b : Bool),
            A.length = 26 + m → (∀ h ∈ gs, 26 + m ∉ h.inputs) →
            ∃ E2 : List Bool, wf gs (A ++ b :: E') = A ++ b :: E2 ∧
              wf (gs.map T) (A ++ E') = A ++ E2 := by
          intro gs
          induction gs with
          | nil => intro A E' b _ _; exact ⟨E', rfl, rfl⟩
          | cons h gs ih =>
            intro A E' b hAL hgs
            have hh : 26 + m ∉ h.inputs := hgs h (List.mem_cons.mpr (Or.inl rfl))
            have heval : (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false) =
                h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false) := by
              have hmap : (h.inputs.map red).map (fun i => (A ++ E').getD i false) =
                  h.inputs.map fun i => (A ++ b :: E').getD i false := by
                rw [List.map_map]
                apply List.map_congr_left
                intro i hi
                exact getD_red A E' b hAL i (fun heq => hh (heq ▸ hi))
              change h.op.eval ((h.inputs.map red).map fun i => (A ++ E').getD i false) = _
              rw [hmap]
            let v := h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
            obtain ⟨E2, h1, h2⟩ := ih A (E' ++ [v]) b hAL
              (fun h' hh' => hgs h' (List.mem_cons.mpr (Or.inr hh')))
            refine ⟨E2, ?_, ?_⟩
            · rw [wf_cons, List.append_assoc, List.cons_append]
              exact h1
            · rw [List.map_cons, wf_cons, heval, List.append_assoc]
              exact h2
        have hWLen : (wf pre x).length = 26 + m := by
          rw [wf_len, hx, hPreLen]
        let b := gj.op.eval (gj.inputs.map fun i => (wf pre x).getD i false)
        obtain ⟨E2, hW1, hW2⟩ := surg post (wf pre x) [] b hWLen hPostNoRead
        rw [List.append_nil] at hW2
        have hCwires : C.wires x = wf pre x ++ b :: E2 := by
          change wf C.gates x = _
          rw [hSplit, wf_append, wf_cons]
          exact hW1
        have hEwires : E.wires x = wf pre x ++ E2 := by
          change wf E.gates x = _
          rw [hE, wf_append]
          exact hW2
        change (E.wires x).getD E.output false = (C.wires x).getD C.output false
        have hEOut : E.output = red C.output := by rw [hE]
        rw [hEOut, hEwires, hCwires]
        exact getD_red (wf pre x) E2 b hWLen C.output (fun heq => hOutEq heq.symm)
      refine ⟨E, hEM, hEB, ?_, hES⟩
      constructor
      · intro u v huv
        rw [hEvalEq _ (by simp [List.length_append, List.length_ofFn])]
        exact hC.1 u v huv
      · intro Q hCard hInt
        rw [hEvalEq _ (by simp [List.length_append, List.length_ofFn])]
        exact hC.2 Q hCard hInt
