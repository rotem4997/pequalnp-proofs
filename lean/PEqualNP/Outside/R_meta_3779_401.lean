import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3779_401
    (hTopAnd :
      let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
      let row : Bool → List Bool → Prop := fun b x =>
        if b then ∃ l : Fin 13, ∃ p ∈ S l, x = PEqualNP.GenericRejection.incidenceInput {p} {l}
        else ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S, x = PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      let ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧ ∀ b x, row b x → C.eval x = b
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        let wv : List Bool → ℕ → Bool := fun x w => (C.wires x).getD w false
        let isA : ℕ → Prop := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and
        ok C →
        C.size < 64 →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        (∀ j < C.size, PEqualNP.Core.InOutputCone 26 C j) →
        (∀ j < C.size, ∀ b : Bool, ∃ x, row b x ∧ wv x (26 + j) = b) →
        (∀ j < C.size, ∀ w < 26 + j, ∃ b x, row b x ∧ wv x (26 + j) = b ∧ wv x w = !b) →
        (∀ a b : ℕ, isA a → isA b → PEqualNP.EdgeOwnership.InCone 26 C a b → ∃ x, row false x ∧ wv x (26 + a) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        isA (C.output - 26) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, ok C' ∧ C'.size < C.size)
    (hOneJunk :
      let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
      let row : Bool → List Bool → Prop := fun b x =>
        if b then ∃ l : Fin 13, ∃ p ∈ S l, x = PEqualNP.GenericRejection.incidenceInput {p} {l}
        else ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S, x = PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      let ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧ ∀ b x, row b x → C.eval x = b
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        let wv : List Bool → ℕ → Bool := fun x w => (C.wires x).getD w false
        let isA : ℕ → Prop := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and
        ok C →
        C.size < 64 →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        (∀ j < C.size, PEqualNP.Core.InOutputCone 26 C j) →
        (∀ j < C.size, ∀ b : Bool, ∃ x, row b x ∧ wv x (26 + j) = b) →
        (∀ j < C.size, ∀ w < 26 + j, ∃ b x, row b x ∧ wv x (26 + j) = b ∧ wv x w = !b) →
        (∀ a b : ℕ, isA a → isA b → PEqualNP.EdgeOwnership.InCone 26 C a b → ∃ x, row false x ∧ wv x (26 + a) = true) →
        PEqualNP.TopForm.andPairs 26 C = 1 →
        ¬ isA (C.output - 26) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, ok C' ∧ C'.size < C.size)
    (hMultiJunk :
      let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
      let row : Bool → List Bool → Prop := fun b x =>
        if b then ∃ l : Fin 13, ∃ p ∈ S l, x = PEqualNP.GenericRejection.incidenceInput {p} {l}
        else ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S, x = PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      let ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧ ∀ b x, row b x → C.eval x = b
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        let wv : List Bool → ℕ → Bool := fun x w => (C.wires x).getD w false
        let isA : ℕ → Prop := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and
        ok C →
        C.size < 64 →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        (∀ j < C.size, PEqualNP.Core.InOutputCone 26 C j) →
        (∀ j < C.size, ∀ b : Bool, ∃ x, row b x ∧ wv x (26 + j) = b) →
        (∀ j < C.size, ∀ w < 26 + j, ∃ b x, row b x ∧ wv x (26 + j) = b ∧ wv x w = !b) →
        (∀ a b : ℕ, isA a → isA b → PEqualNP.EdgeOwnership.InCone 26 C a b → ∃ x, row false x ∧ wv x (26 + a) = true) →
        2 ≤ PEqualNP.TopForm.andPairs 26 C →
        ¬ isA (C.output - 26) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, ok C' ∧ C'.size < C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 → x5.size < (64 : ℕ) → (∀ (x8 x9 : ℕ), x4 x5 x8 x9 → ∃ (x11 : List Bool), x2 Bool.false x11 ∧ (x5.wires x11).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (∃ (x9 : ℕ) (x10 : ℕ), x4 x5 x9 x10) → (∀ x10 ∈ x5.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x3 x11 ∧ x11.size < x5.size := by
  intro x1 x2 x3 x4 C hCx3 hCsz hCdirty hCnest hCstrict
  let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
  let row : Bool → List Bool → Prop := fun b x =>
    if b then ∃ l : Fin 13, ∃ p ∈ S l, x = PEqualNP.GenericRejection.incidenceInput {p} {l}
    else ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S, x = PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
  let ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
    PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D ∧ ∀ b x, row b x → D.eval x = b
  have heval_and : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have htest_and : PEqualNP.CircuitLowerBounds.GateOp.and.eval [true, false] = false := rfl
  have htest_or : PEqualNP.CircuitLowerBounds.GateOp.or.eval [true, false] = true := rfl
  have hinc_def : ∀ (X Y : Finset (Fin 13)),
      PEqualNP.GenericRejection.incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have hgateAt_def : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
      PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :=
    fun _ _ => rfl
  have hconeStep_def : ∀ (cs : List (List ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate),
      PEqualNP.EdgeOwnership.coneStep 26 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] :=
    fun _ _ => rfl
  have herase_gates : ∀ (m p : ℕ), m < C.gates.length →
      (PEqualNP.CircuitMoves.eraseGate 26 C m p).gates =
      C.gates.take m ++ (C.gates.drop (m + 1)).map
        (fun g => ⟨g.op, g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 m p)⟩) := by
    intro m p hm
    delta PEqualNP.CircuitMoves.eraseGate
    simp [hm]
  have herase_out : ∀ (m p : ℕ), m < C.gates.length →
      (PEqualNP.CircuitMoves.eraseGate 26 C m p).output = PEqualNP.CircuitMoves.eraseRedirect 26 m p C.output := by
    intro m p hm
    delta PEqualNP.CircuitMoves.eraseGate
    simp [hm]
  have hS_iff : ∀ p l : Fin 13, p ∈ S l ↔ p - l ∈ x1 := by
    intro p l
    change p ∈ PEqualNP.HeptadCover.singerLines3 l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
    revert p l
    decide
  have hInc_eq : ∀ p l : Fin 13,
      PEqualNP.GenericRejection.incidenceInput {p} {l} =
      (List.ofFn fun u : Fin 13 => Decidable.decide (u = p)) ++
      List.ofFn fun v : Fin 13 => Decidable.decide (v = l) := by
    intro p l
    rw [hinc_def]
    simp
  have hQuad_iff : ∀ Q : Finset (Fin 13),
      Q ∈ PEqualNP.HeptadCover.quadrangles S ↔
      Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | p - l ∈ x1}.card ≤ 2 := by
    intro Q
    delta PEqualNP.HeptadCover.quadrangles
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro l
    have hEq : Q ∩ S l = {p ∈ Q | p - l ∈ x1} := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact and_congr_right fun _ => hS_iff p l
    rw [hEq]
  have hMiss_eq : ∀ Q : Finset (Fin 13),
      PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q) =
      (List.ofFn fun u : Fin 13 => Decidable.decide (u ∈ Q)) ++
      List.ofFn fun l : Fin 13 => Decidable.decide (∀ p ∈ Q, p - l ∉ x1) := by
    intro Q
    rw [hinc_def]
    apply congrArg (List.append _)
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    delta PEqualNP.HeptadCover.missLines
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
    exact forall₂_congr fun p _ => not_congr (hS_iff p l)
  have hrow_iff : ∀ b x, x2 b x ↔ row b x := by
    intro b x
    cases b
    · change (∃ Q : Finset (Fin 13), Q.card = 4 ∧ (∀ l : Fin 13, {p ∈ Q | p - l ∈ x1}.card ≤ 2) ∧
          x = (List.ofFn fun u : Fin 13 => Decidable.decide (u ∈ Q)) ++
            List.ofFn fun l : Fin 13 => Decidable.decide (∀ p ∈ Q, p - l ∉ x1)) ↔
        ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S,
          x = PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      constructor
      · rintro ⟨Q, hQ1, hQ2, rfl⟩
        exact ⟨Q, (hQuad_iff Q).mpr ⟨hQ1, hQ2⟩, (hMiss_eq Q).symm⟩
      · rintro ⟨Q, hQ, rfl⟩
        obtain ⟨hQ1, hQ2⟩ := (hQuad_iff Q).mp hQ
        exact ⟨Q, hQ1, hQ2, hMiss_eq Q⟩
    · change (∃ p l : Fin 13, p - l ∈ x1 ∧
          x = (List.ofFn fun u : Fin 13 => Decidable.decide (u = p)) ++
            List.ofFn fun v : Fin 13 => Decidable.decide (v = l)) ↔
        ∃ l : Fin 13, ∃ p ∈ S l, x = PEqualNP.GenericRejection.incidenceInput {p} {l}
      constructor
      · rintro ⟨p, l, hpl, rfl⟩
        exact ⟨l, p, (hS_iff p l).mpr hpl, (hInc_eq p l).symm⟩
      · rintro ⟨l, p, hpl, rfl⟩
        exact ⟨p, l, (hS_iff p l).mp hpl, hInc_eq p l⟩
  have hok_iff : ∀ D, x3 D ↔ ok D := by
    intro D
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · intro h b x hx; exact h b x ((hrow_iff b x).mpr hx)
    · intro h b x hx; exact h b x ((hrow_iff b x).mp hx)
  have hrow_len : ∀ b x, row b x → x.length = 26 := by
    intro b x hx
    cases b
    · rcases hx with ⟨Q, _, rfl⟩
      rw [hinc_def]; simp
    · rcases hx with ⟨l, p, _, rfl⟩
      rw [hinc_def]; simp
  have hCok : ok C := (hok_iff C).mp hCx3
  have hCmono : PEqualNP.MetaComplexity.Monotone2 C := hCok.1
  have hCmono_or : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hCmono g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hCrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C := hCok.2.1
  have hCeval : ∀ b x, row b x → C.eval x = b := hCok.2.2
  have hPosWit : row true (PEqualNP.GenericRejection.incidenceInput {(0 : Fin 13)} {(0 : Fin 13)}) := by
    refine ⟨0, 0, ?_, rfl⟩
    rw [hS_iff]
    change (0 : Fin 13) - 0 ∈ ({0, 1, 3, 9} : Finset (Fin 13))
    decide
  have hNegWit : row false (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 5} : Finset (Fin 13))
      (PEqualNP.HeptadCover.missLines S ({0, 1, 2, 5} : Finset (Fin 13)))) := by
    refine ⟨{0, 1, 2, 5}, ?_, rfl⟩
    rw [hQuad_iff]
    change ({0, 1, 2, 5} : Finset (Fin 13)).card = 4 ∧
      ∀ l : Fin 13, {p ∈ ({0, 1, 2, 5} : Finset (Fin 13)) | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2
    decide
  let wf : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have hwf_append : ∀ pre post w, wf (pre ++ post) w = wf post (wf pre w) := by
    intro pre post w
    exact List.foldl_append
  have hwf_len : ∀ gs w, (wf gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wf]
    | cons g gs ih =>
      intro w
      change (wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp
      omega
  have hwf_prefix : ∀ gs w i, i < w.length → (wf gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      let w' := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
      have hi' : i < w'.length := by simp [w']; omega
      have h1 : (wf gs w').getD i false = w'.getD i false := ih w' i hi'
      change (wf gs w').getD i false = w.getD i false
      rw [h1]
      simp [w', List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hwires_prefix : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (i : ℕ),
      i < x.length → (D.wires x).getD i false = x.getD i false :=
    fun D x i hi => hwf_prefix D.gates x i hi
  have hgateAt_eq : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (hk : k < D.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt D k = D.gates[k]'hk := by
    intro D k hk
    rw [hgateAt_def]
    simp [List.getD_eq_getElem?_getD, hk]
  have hwf_gate_rb : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (j : ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length D → j < D.gates.length →
      (D.wires x).getD (x.length + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs.map fun i => (D.wires x).getD i false) := by
    intro D x j hrb hj
    have hsplit : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hlen_pre : (wf (D.gates.take j) x).length = x.length + j := by
      rw [hwf_len, List.length_take_of_le (Nat.le_of_lt hj)]
    have hW : D.wires x = wf (D.gates.drop (j + 1))
        (wf (D.gates.take j) x ++ [D.gates[j].op.eval (D.gates[j].inputs.map fun i => (wf (D.gates.take j) x).getD i false)]) := by
      change wf D.gates x = _
      conv_lhs => rw [hsplit, hwf_append]
      rfl
    have hidx : x.length + j < (wf (D.gates.take j) x ++
        [D.gates[j].op.eval (D.gates[j].inputs.map fun i => (wf (D.gates.take j) x).getD i false)]).length := by
      rw [List.length_append, hlen_pre]
      simp
    have hval1 : (D.wires x).getD (x.length + j) false =
        D.gates[j].op.eval (D.gates[j].inputs.map fun i => (wf (D.gates.take j) x).getD i false) := by
      rw [hW, hwf_prefix _ _ _ hidx]
      simp [List.getD_eq_getElem?_getD, hlen_pre]
    rw [hval1, hgateAt_eq D j hj]
    apply congrArg D.gates[j].op.eval
    apply List.map_congr_left
    intro i hi
    have hilt : i < x.length + j := by
      have := hrb j hj i
      rw [hgateAt_eq D j hj] at this
      exact this hi
    have hW2 : D.wires x = wf (D.gates[j] :: D.gates.drop (j + 1)) (wf (D.gates.take j) x) := by
      change wf D.gates x = _
      conv_lhs => rw [hsplit, hwf_append]
    rw [hW2, hwf_prefix (D.gates[j] :: D.gates.drop (j + 1)) (wf (D.gates.take j) x) i (by omega)]
  have hop_mono : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp),
      op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) →
      ∀ (ins : List ℕ) (f1 f2 : ℕ → Bool),
      (∀ i ∈ ins, f1 i = true → f2 i = true) →
      op.eval (ins.map f1) = true → op.eval (ins.map f2) = true := by
    intro op hop ins f1 f2 hf h1
    rcases hop with rfl | rfl
    · rw [heval_and] at h1 ⊢
      simp only [List.all_eq_true, id_eq, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h1 ⊢
      intro i hi
      exact hf i hi (h1 i hi)
    · rw [heval_or] at h1 ⊢
      simp only [List.any_eq_true, id_eq, List.mem_map] at h1 ⊢
      rcases h1 with ⟨_, ⟨i, hi, rfl⟩, hfi⟩
      exact ⟨f2 i, ⟨i, hi, rfl⟩, hf i hi hfi⟩
  have hcones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      simp only [List.foldl_cons]
      rw [ih, hconeStep_def]
      simp
      omega
  have hcones_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (k : ℕ),
      k < cs.length →
      (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      let cs' := PEqualNP.EdgeOwnership.coneStep 26 cs g
      have hk' : k < cs'.length := by simp only [cs', hconeStep_def, List.length_append, List.length_singleton]; omega
      simp only [List.foldl_cons]
      rw [ih cs' k hk']
      simp only [cs', hconeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have hcone_rec : ∀ k < C.gates.length, ∀ i,
      PEqualNP.EdgeOwnership.InCone 26 C i k ↔
      ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
        26 ≤ w ∧ w < 26 + k ∧ (i = w - 26 ∨ PEqualNP.EdgeOwnership.InCone 26 C i (w - 26)) := by
    intro k hk i
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    let pre := (C.gates.take k).foldl (PEqualNP.EdgeOwnership.coneStep 26) []
    have hpre_len : pre.length = k := by
      simp [pre, hcones_len, List.length_take_of_le (Nat.le_of_lt hk)]
    have hCcones : PEqualNP.EdgeOwnership.cones 26 C =
        (C.gates.drop (k + 1)).foldl (PEqualNP.EdgeOwnership.coneStep 26)
          (PEqualNP.EdgeOwnership.coneStep 26 pre C.gates[k]) := by
      unfold PEqualNP.EdgeOwnership.cones
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    have hEntry : (PEqualNP.EdgeOwnership.cones 26 C).getD k [] =
        (C.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
          (fun w => (w - 26) :: pre.getD (w - 26) []) := by
      rw [hCcones]
      have hk' : k < (PEqualNP.EdgeOwnership.coneStep 26 pre C.gates[k]).length := by
        rw [hconeStep_def]
        simp [hpre_len]
      rw [hcones_prefix _ _ k hk', hconeStep_def]
      simp [hpre_len, List.getD_eq_getElem?_getD]
    have hPreEq : ∀ m < k, (PEqualNP.EdgeOwnership.cones 26 C).getD m [] = pre.getD m [] := by
      intro m hm
      have hCcones2 : PEqualNP.EdgeOwnership.cones 26 C =
          (C.gates[k] :: C.gates.drop (k + 1)).foldl (PEqualNP.EdgeOwnership.coneStep 26) pre := by
        unfold PEqualNP.EdgeOwnership.cones
        conv_lhs => rw [hsplit, List.foldl_append]
      rw [hCcones2, hcones_prefix _ _ m (by omega)]
    unfold PEqualNP.EdgeOwnership.InCone
    rw [hEntry, hgateAt_eq C k hk]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hlo, hhi⟩, hmem⟩
      refine ⟨w, hw, hlo, hhi, ?_⟩
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [hPreEq (w - 26) (by omega)]
        exact hmem
    · rintro ⟨w, hw, hlo, hhi, hmem⟩
      refine ⟨w, ⟨hw, hlo, hhi⟩, ?_⟩
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [← hPreEq (w - 26) (by omega)]
        exact hmem
  have hcone_lt : ∀ j i, PEqualNP.EdgeOwnership.InCone 26 C i j → i < j ∧ j < C.gates.length := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro i hij
      by_cases hj : j < C.gates.length
      · obtain ⟨w, _, hlo, hhi, hcase⟩ := (hcone_rec j hj i).mp hij
        refine ⟨?_, hj⟩
        rcases hcase with rfl | hsub
        · omega
        · have hsublt := (ih (w - 26) (by omega) i hsub).1
          omega
      · exfalso
        unfold PEqualNP.EdgeOwnership.InCone at hij
        have hlen : (PEqualNP.EdgeOwnership.cones 26 C).length = C.gates.length := by
          unfold PEqualNP.EdgeOwnership.cones
          rw [hcones_len]
          simp
        have hget : (PEqualNP.EdgeOwnership.cones 26 C).getD j [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (PEqualNP.EdgeOwnership.cones 26 C).length ≤ j by omega)]
        rw [hget] at hij
        exact List.not_mem_nil hij
  have hcone_trans : ∀ k i j, PEqualNP.EdgeOwnership.InCone 26 C i j →
      PEqualNP.EdgeOwnership.InCone 26 C j k → PEqualNP.EdgeOwnership.InCone 26 C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i j hij hjk
      have hk : k < C.gates.length := (hcone_lt k j hjk).2
      obtain ⟨w, hw, hlo, hhi, hcase⟩ := (hcone_rec k hk j).mp hjk
      apply (hcone_rec k hk i).mpr
      refine ⟨w, hw, hlo, hhi, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 26) (by omega) i j hij hsub
  have hOutLt : C.output < 26 + C.gates.length := by
    by_contra hge
    have hge' : 26 + C.gates.length ≤ C.output := Nat.le_of_not_lt hge
    have hx := hCeval true _ hPosWit
    have hlen : (C.wires (PEqualNP.GenericRejection.incidenceInput {(0 : Fin 13)} {(0 : Fin 13)})).length =
        26 + C.gates.length := by
      change (wf C.gates _).length = _
      rw [hwf_len, hrow_len true _ hPosWit]
    have hf : C.eval (PEqualNP.GenericRejection.incidenceInput {(0 : Fin 13)} {(0 : Fin 13)}) = false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge')]
      rfl
    rw [hf] at hx
    exact Bool.noConfusion hx
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 26 := Nat.lt_of_not_ge hlt
    have hne13 : ∀ u : Fin 13, u ≠ u + 1 := by decide
    by_cases h13 : C.output < 13
    · let p : Fin 13 := ⟨C.output, h13⟩
      let q : Fin 13 := p + 1
      have hqrow : row true (PEqualNP.GenericRejection.incidenceInput {q} {q}) := by
        refine ⟨q, q, ?_, rfl⟩
        rw [hS_iff]
        change q - q ∈ ({0, 1, 3, 9} : Finset (Fin 13))
        simp
      have hev := hCeval true _ hqrow
      have hpre : C.eval (PEqualNP.GenericRejection.incidenceInput {q} {q}) =
          (PEqualNP.GenericRejection.incidenceInput {q} {q}).getD C.output false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        exact hwires_prefix C _ C.output (by rw [hrow_len true _ hqrow]; omega)
      rw [hpre, hInc_eq q q] at hev
      have hget : ((List.ofFn fun u : Fin 13 => Decidable.decide (u = q)) ++
          List.ofFn fun v : Fin 13 => Decidable.decide (v = q)).getD C.output false =
          Decidable.decide (p = q) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [h13]), List.getElem?_ofFn]
        simp [h13, p]
      rw [hget] at hev
      exact hne13 p (of_decide_eq_true hev)
    · let l : Fin 13 := ⟨C.output - 13, by omega⟩
      let q : Fin 13 := l + 1
      have hqrow : row true (PEqualNP.GenericRejection.incidenceInput {q} {q}) := by
        refine ⟨q, q, ?_, rfl⟩
        rw [hS_iff]
        change q - q ∈ ({0, 1, 3, 9} : Finset (Fin 13))
        simp
      have hev := hCeval true _ hqrow
      have hpre : C.eval (PEqualNP.GenericRejection.incidenceInput {q} {q}) =
          (PEqualNP.GenericRejection.incidenceInput {q} {q}).getD C.output false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        exact hwires_prefix C _ C.output (by rw [hrow_len true _ hqrow]; omega)
      rw [hpre, hInc_eq q q] at hev
      have hget : ((List.ofFn fun u : Fin 13 => Decidable.decide (u = q)) ++
          List.ofFn fun v : Fin 13 => Decidable.decide (v = q)).getD C.output false =
          Decidable.decide (l = q) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega), List.length_ofFn,
          List.getElem?_ofFn]
        simp [show C.output - 13 < 13 by omega, l]
      rw [hget] at hev
      exact hne13 l (of_decide_eq_true hev)
  have herase_basic : ∀ (m p : ℕ), m < C.gates.length → p < 26 + m →
      let D := PEqualNP.CircuitMoves.eraseGate 26 C m p
      D.gates.length = C.gates.length - 1 ∧
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D ∧
      (∀ k < m, PEqualNP.MetaComplexity.NestedCover.gateAt D k = PEqualNP.MetaComplexity.NestedCover.gateAt C k) ∧
      (∀ k, m ≤ k → k < C.gates.length - 1 →
        PEqualNP.MetaComplexity.NestedCover.gateAt D k =
          ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)).op,
           (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)).inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 m p)⟩) := by
    intro m p hm hp
    let D := PEqualNP.CircuitMoves.eraseGate 26 C m p
    have hDgates : D.gates = C.gates.take m ++ (C.gates.drop (m + 1)).map
        (fun g => ⟨g.op, g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 m p)⟩) :=
      herase_gates m p hm
    have hDlen : D.gates.length = C.gates.length - 1 := by
      rw [hDgates, List.length_append, List.length_take_of_le (Nat.le_of_lt hm), List.length_map, List.length_drop]
      omega
    have hDlt : ∀ k < m, PEqualNP.MetaComplexity.NestedCover.gateAt D k = PEqualNP.MetaComplexity.NestedCover.gateAt C k := by
      intro k hk
      rw [hgateAt_eq D k (by omega), hgateAt_eq C k (by omega)]
      simp only [hDgates]
      rw [List.getElem_append_left (by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hk)]
      exact List.getElem_take
    have hDge : ∀ k, m ≤ k → k < C.gates.length - 1 →
        PEqualNP.MetaComplexity.NestedCover.gateAt D k =
          ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)).op,
           (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)).inputs.map (PEqualNP.CircuitMoves.eraseRedirect 26 m p)⟩ := by
      intro k hkm hklt
      have htle : (C.gates.take m).length ≤ k := by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hkm
      have hidx : m + 1 + (k - (C.gates.take m).length) = k + 1 := by
        rw [List.length_take_of_le (Nat.le_of_lt hm)]
        omega
      simp only [hgateAt_def, List.getD_eq_getElem?_getD, hDgates,
        List.getElem?_append_right htle, List.getElem?_map, List.getElem?_drop, hidx,
        List.getElem?_eq_getElem (show k + 1 < C.gates.length by omega)]
      rfl
    refine ⟨hDlen, ?_, ?_, hDlt, hDge⟩
    · intro g hg
      rw [hDgates, List.mem_append] at hg
      rcases hg with hg | hg
      · exact hCmono g (List.mem_of_mem_take hg)
      · rw [List.mem_map] at hg
        rcases hg with ⟨g0, hg0, rfl⟩
        have h0 := hCmono g0 (List.mem_of_mem_drop hg0)
        exact ⟨h0.1, by simp [h0.2]⟩
    · intro k hk i hi
      have hk' : k < C.gates.length - 1 := by
        change k < D.gates.length at hk
        omega
      by_cases hkm : k < m
      · rw [hDlt k hkm] at hi
        exact hCrb k (by omega) i hi
      · rw [hDge k (by omega) hk'] at hi
        simp only [List.mem_map] at hi
        rcases hi with ⟨i0, hi0, rfl⟩
        have hi0lt : i0 < 26 + (k + 1) := hCrb (k + 1) (by omega) i0 hi0
        unfold PEqualNP.CircuitMoves.eraseRedirect
        split_ifs <;> omega
  by_cases hLive : ∀ j < C.size, PEqualNP.Core.InOutputCone 26 C j
  · by_cases hNonConst : ∀ j < C.size, ∀ b : Bool, ∃ x, row b x ∧ (C.wires x).getD (26 + j) false = b
    · by_cases hIrred : ∀ j < C.size, ∀ w < 26 + j, ∃ b x, row b x ∧ (C.wires x).getD (26 + j) false = b ∧ (C.wires x).getD w false = !b
      · have hDirty' : ∀ a b : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.InCone 26 C a b →
            ∃ x, row false x ∧ (C.wires x).getD (26 + a) false = true := by
          intro a b ha hb hab
          obtain ⟨x, hx, hval⟩ := hCdirty a b ⟨ha, hb, hab⟩
          exact ⟨x, (hrow_iff false x).mp hx, hval⟩
        have hAPPos : 0 < PEqualNP.TopForm.andPairs 26 C := by
          obtain ⟨a, b, ha, hb, hab⟩ := hCnest
          obtain ⟨hlt, hblt⟩ := hcone_lt b a hab
          unfold PEqualNP.TopForm.andPairs
          refine Finset.card_pos.mpr ⟨(a, b), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨by omega, hblt⟩, ha, hb, hab⟩
        by_cases hOutA : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and
        · obtain ⟨C', hok', hlt⟩ := hTopAnd C hCok hCsz hCstrict hLive hNonConst hIrred hDirty' hAPPos hOutA
          exact ⟨C', (hok_iff C').mpr hok', hlt⟩
        · by_cases hOne : PEqualNP.TopForm.andPairs 26 C = 1
          · obtain ⟨C', hok', hlt⟩ := hOneJunk C hCok hCsz hCstrict hLive hNonConst hIrred hDirty' hOne hOutA
            exact ⟨C', (hok_iff C').mpr hok', hlt⟩
          · obtain ⟨C', hok', hlt⟩ := hMultiJunk C hCok hCsz hCstrict hLive hNonConst hIrred hDirty' (by omega) hOutA
            exact ⟨C', (hok_iff C').mpr hok', hlt⟩
      · push Not at hIrred
        obtain ⟨m, hm, p, hp, hdom⟩ := hIrred
        change m < C.gates.length at hm
        let D := PEqualNP.CircuitMoves.eraseGate 26 C m p
        obtain ⟨hDsz, hDmono, hDrb, hDlt, hDge⟩ := herase_basic m p hm hp
        change D.gates.length = C.gates.length - 1 at hDsz
        have hDout : D.output = PEqualNP.CircuitMoves.eraseRedirect 26 m p C.output :=
          herase_out m p hm
        have hPreEq : ∀ (x : List Bool), x.length = 26 → ∀ w < 26 + m,
            (D.wires x).getD w false = (C.wires x).getD w false := by
          intro x hx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hw26 : w < 26
            · rw [hwires_prefix D x w (by omega), hwires_prefix C x w (by omega)]
            · let k := w - 26
              have hklt : k < m := by omega
              have hkw : w = 26 + k := by omega
              rw [hkw]
              have h1 := hwf_gate_rb D x k (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) (by omega)
              rw [hx] at h1 h2
              rw [h1, h2, hDlt k hklt]
              apply congrArg (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
              apply List.map_congr_left
              intro i hi
              have hilt : i < 26 + k := hCrb k (by omega) i hi
              exact ih i (by omega) (by omega)
        have hUp : ∀ (x : List Bool), x.length = 26 →
            ((C.wires x).getD (26 + m) false = true → (C.wires x).getD p false = true) →
            ∀ w < 26 + C.gates.length,
            (C.wires x).getD w false = true →
            (D.wires x).getD (PEqualNP.CircuitMoves.eraseRedirect 26 m p w) false = true := by
          intro x hx hmp w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hCw
            by_cases hwm : w < 26 + m
            · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = w := by
                unfold PEqualNP.CircuitMoves.eraseRedirect
                split_ifs <;> omega
              rw [hr, hPreEq x hx w hwm]
              exact hCw
            · by_cases hweq : w = 26 + m
              · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = p := by
                  unfold PEqualNP.CircuitMoves.eraseRedirect
                  split_ifs; rfl
                rw [hr, hPreEq x hx p hp]
                exact hmp (hweq ▸ hCw)
              · let k := w - 26
                have hkm : m < k := by omega
                have hklt : k < C.gates.length := by omega
                have hkw : w = 26 + k := by omega
                have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = 26 + (k - 1) := by
                  unfold PEqualNP.CircuitMoves.eraseRedirect
                  split_ifs <;> omega
                rw [hr]
                have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
                have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
                rw [hx] at h1 h2
                rw [hkw] at hCw
                rw [h2] at hCw
                rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega]
                simp only [List.map_map]
                have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                  rw [hgateAt_eq C k hklt]
                  exact List.getElem_mem hklt
                exact hop_mono (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op (hCmono _ hgkmem).1
                  (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs _ _
                  (fun i hi hCi => ih i (by have := hCrb k hklt i hi; omega) (by have := hCrb k hklt i hi; omega) hCi) hCw
        have hDn : ∀ (x : List Bool), x.length = 26 →
            ((C.wires x).getD p false = true → (C.wires x).getD (26 + m) false = true) →
            ∀ w < 26 + C.gates.length,
            (D.wires x).getD (PEqualNP.CircuitMoves.eraseRedirect 26 m p w) false = true →
            (C.wires x).getD w false = true := by
          intro x hx hpm w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hDw
            by_cases hwm : w < 26 + m
            · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = w := by
                unfold PEqualNP.CircuitMoves.eraseRedirect
                split_ifs <;> omega
              rw [hr, hPreEq x hx w hwm] at hDw
              exact hDw
            · by_cases hweq : w = 26 + m
              · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = p := by
                  unfold PEqualNP.CircuitMoves.eraseRedirect
                  split_ifs; rfl
                rw [hr, hPreEq x hx p hp] at hDw
                rw [hweq]
                exact hpm hDw
              · let k := w - 26
                have hkm : m < k := by omega
                have hklt : k < C.gates.length := by omega
                have hkw : w = 26 + k := by omega
                have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m p w = 26 + (k - 1) := by
                  unfold PEqualNP.CircuitMoves.eraseRedirect
                  split_ifs <;> omega
                rw [hr] at hDw
                have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
                have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
                rw [hx] at h1 h2
                rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega] at hDw
                simp only [List.map_map] at hDw
                rw [hkw, h2]
                have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                  rw [hgateAt_eq C k hklt]
                  exact List.getElem_mem hklt
                exact hop_mono (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op (hCmono _ hgkmem).1
                  (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs _ _
                  (fun i hi hDi => ih i (by have := hCrb k hklt i hi; omega) (by have := hCrb k hklt i hi; omega) hDi) hDw
        have hDok : ok D := by
          refine ⟨hDmono, hDrb, fun b x hx => ?_⟩
          cases b
          · cases hDv : D.eval x
            · rfl
            · exfalso
              have hpm : (C.wires x).getD p false = true → (C.wires x).getD (26 + m) false = true := by
                intro hpx
                cases hmx : (C.wires x).getD (26 + m) false
                · exact absurd hpx (hdom false x hx hmx)
                · rfl
              have hCv : C.eval x = true := by
                unfold PEqualNP.CircuitLowerBounds.Circuit.eval at hDv ⊢
                rw [hDout] at hDv
                exact hDn x (hrow_len false x hx) hpm C.output hOutLt hDv
              have hCf := hCeval false x hx
              rw [hCv] at hCf
              exact Bool.noConfusion hCf
          · have hmp : (C.wires x).getD (26 + m) false = true → (C.wires x).getD p false = true := by
              intro hmx
              cases hpx : (C.wires x).getD p false
              · exfalso
                exact hdom true x hx hmx hpx
              · rfl
            unfold PEqualNP.CircuitLowerBounds.Circuit.eval
            rw [hDout]
            exact hUp x (hrow_len true x hx) hmp C.output hOutLt (hCeval true x hx)
        exact ⟨D, (hok_iff D).mpr hDok, by show D.gates.length < C.gates.length; omega⟩
    · push Not at hNonConst
      obtain ⟨m, hm, b, hb⟩ := hNonConst
      change m < C.gates.length at hm
      let N := 26 + m
      let sk : ℕ → ℕ := fun i => if i < N then i else i - 1
      have hsk_lt : ∀ k i, m ≤ k → i < 26 + (k + 1) → i ≠ N → sk i < 26 + k := by
        intro k i hkm hilt hine
        simp only [sk]
        split_ifs <;> omega
      cases b
      · let Tt : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun h =>
          if h.op.eval [true, false] then
            if N ∈ h.inputs then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ else ⟨h.op, h.inputs.map sk⟩
          else
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map sk⟩
        let D : PEqualNP.CircuitLowerBounds.Circuit :=
          ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map Tt, sk C.output⟩
        have hDlen : D.gates.length = C.gates.length - 1 := by
          simp [D, List.length_take_of_le (Nat.le_of_lt hm)]
          omega
        have hDlt : ∀ k < m, PEqualNP.MetaComplexity.NestedCover.gateAt D k = PEqualNP.MetaComplexity.NestedCover.gateAt C k := by
          intro k hk
          rw [hgateAt_eq D k (by omega), hgateAt_eq C k (by omega)]
          simp only [D]
          rw [List.getElem_append_left (by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hk)]
          exact List.getElem_take
        have hDge : ∀ k, m ≤ k → k < C.gates.length - 1 →
            PEqualNP.MetaComplexity.NestedCover.gateAt D k = Tt (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)) := by
          intro k hkm hklt
          have htle : (C.gates.take m).length ≤ k := by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hkm
          have hidx : m + 1 + (k - (C.gates.take m).length) = k + 1 := by
            rw [List.length_take_of_le (Nat.le_of_lt hm)]
            omega
          simp only [D, hgateAt_def, List.getD_eq_getElem?_getD,
            List.getElem?_append_right htle, List.getElem?_map, List.getElem?_drop, hidx,
            List.getElem?_eq_getElem (show k + 1 < C.gates.length by omega)]
          rfl
        have hDmono : PEqualNP.MetaComplexity.Monotone2 D := by
          intro g hg
          simp only [D, List.mem_append, List.mem_map] at hg
          rcases hg with hg | ⟨g0, hg0, rfl⟩
          · exact hCmono g (List.mem_of_mem_take hg)
          · have h0 := hCmono_or g0 (List.mem_of_mem_drop hg0)
            rcases h0.1 with hop | hop
            · simp only [Tt, hop, htest_and, Bool.false_eq_true, ↓reduceIte]
              refine ⟨Or.inl rfl, ?_⟩
              calc ((g0.inputs.filter (fun i => decide (i ≠ N))).map sk).length
                  = (g0.inputs.filter (fun i => decide (i ≠ N))).length := List.length_map _
                _ ≤ g0.inputs.length := List.length_filter_le _ _
                _ ≤ 2 := h0.2
            · simp only [Tt, hop, htest_or, ↓reduceIte]
              split_ifs
              · exact ⟨Or.inl rfl, by simp⟩
              · exact ⟨Or.inr rfl, by simp [h0.2]⟩
        have hDrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D := by
          intro k hk i hi
          by_cases hkm : k < m
          · rw [hDlt k hkm] at hi
            exact hCrb k (by omega) i hi
          · rw [hDge k (by omega) (by omega)] at hi
            have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1) ∈ C.gates := by
              rw [hgateAt_eq C (k + 1) (by omega)]
              exact List.getElem_mem (by omega)
            rcases (hCmono_or _ hgkmem).1 with hop | hop
            · simp only [Tt, hop, htest_and, Bool.false_eq_true, ↓reduceIte,
                List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
              rcases hi with ⟨i0, ⟨hi0, hine⟩, rfl⟩
              exact hsk_lt k i0 (by omega) (hCrb (k + 1) (by omega) i0 hi0) hine
            · simp only [Tt, hop, htest_or, ↓reduceIte] at hi
              split_ifs at hi with hmem
              · simp at hi
              · simp only [List.mem_map] at hi
                rcases hi with ⟨i0, hi0, rfl⟩
                have hine : i0 ≠ N := fun heq => hmem (heq ▸ hi0)
                exact hsk_lt k i0 (by omega) (hCrb (k + 1) (by omega) i0 hi0) hine
        have hOutNe : C.output ≠ N := by
          intro heq
          have h1 := hCeval false _ hNegWit
          have h2 := hb _ hNegWit
          unfold PEqualNP.CircuitLowerBounds.Circuit.eval at h1
          rw [heq] at h1
          exact h2 h1
        have hPreEq : ∀ (x : List Bool), x.length = 26 → ∀ w < N,
            (D.wires x).getD w false = (C.wires x).getD w false := by
          intro x hx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hw26 : w < 26
            · rw [hwires_prefix D x w (by omega), hwires_prefix C x w (by omega)]
            · let k := w - 26
              have hklt : k < m := by omega
              have hkw : w = 26 + k := by omega
              rw [hkw]
              have h1 := hwf_gate_rb D x k (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) (by omega)
              rw [hx] at h1 h2
              rw [h1, h2, hDlt k hklt]
              apply congrArg (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
              apply List.map_congr_left
              intro i hi
              have hilt : i < 26 + k := hCrb k (by omega) i hi
              exact ih i (by omega) (by omega)
        have hUp : ∀ (x : List Bool), x.length = 26 →
            ∀ w < 26 + C.gates.length, w ≠ N →
            (C.wires x).getD w false = true →
            (D.wires x).getD (sk w) false = true := by
          intro x hx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hwne hCw
            by_cases hwN : w < N
            · have hskw : sk w = w := by simp [sk, hwN]
              rw [hskw, hPreEq x hx w hwN]
              exact hCw
            · let k := w - 26
              have hkm : m < k := by omega
              have hklt : k < C.gates.length := by omega
              have hkw : w = 26 + k := by omega
              have hskw : sk w = 26 + (k - 1) := by simp only [sk]; split_ifs; omega
              rw [hskw]
              have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
              rw [hx] at h1 h2
              rw [hkw, h2] at hCw
              rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega]
              have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                rw [hgateAt_eq C k hklt]
                exact List.getElem_mem hklt
              rcases (hCmono_or _ hgkmem).1 with hop | hop
              · simp only [Tt, hop, htest_and, Bool.false_eq_true, ↓reduceIte, heval_and, List.all_eq_true, id_eq] at hCw ⊢
                intro y hy
                simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hy
                rcases hy with ⟨_, ⟨i, ⟨hi, hine⟩, rfl⟩, rfl⟩
                have hilt : i < 26 + k := hCrb k hklt i hi
                have hCi : (C.wires x).getD i false = true := hCw _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
                exact ih i (by omega) (by omega) hine hCi
              · simp only [Tt, hop, htest_or, ↓reduceIte]
                split_ifs with hmem
                · rfl
                · simp only [hop, heval_or, List.any_eq_true, id_eq, List.mem_map] at hCw ⊢
                  rcases hCw with ⟨_, ⟨i, hi, rfl⟩, hCi⟩
                  have hilt : i < 26 + k := hCrb k hklt i hi
                  have hine : i ≠ N := fun heq => hmem (heq ▸ hi)
                  exact ⟨(D.wires x).getD (sk i) false, ⟨sk i, ⟨i, hi, rfl⟩, rfl⟩, ih i (by omega) (by omega) hine hCi⟩
        have hDn : ∀ (x : List Bool), x.length = 26 → (C.wires x).getD N false = true →
            ∀ w < 26 + C.gates.length, w ≠ N →
            (D.wires x).getD (sk w) false = true →
            (C.wires x).getD w false = true := by
          intro x hx hNt w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hwne hDw
            by_cases hwN : w < N
            · have hskw : sk w = w := by simp [sk, hwN]
              rw [hskw, hPreEq x hx w hwN] at hDw
              exact hDw
            · let k := w - 26
              have hkm : m < k := by omega
              have hklt : k < C.gates.length := by omega
              have hkw : w = 26 + k := by omega
              have hskw : sk w = 26 + (k - 1) := by simp only [sk]; split_ifs; omega
              rw [hskw] at hDw
              have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
              rw [hx] at h1 h2
              rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega] at hDw
              rw [hkw, h2]
              have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                rw [hgateAt_eq C k hklt]
                exact List.getElem_mem hklt
              rcases (hCmono_or _ hgkmem).1 with hop | hop
              · simp only [Tt, hop, htest_and, Bool.false_eq_true, ↓reduceIte, heval_and, List.all_eq_true, id_eq] at hDw ⊢
                intro y hy
                simp only [List.mem_map] at hy
                rcases hy with ⟨i, hi, rfl⟩
                by_cases hine : i = N
                · exact hine ▸ hNt
                · have hilt : i < 26 + k := hCrb k hklt i hi
                  have hDi : (D.wires x).getD (sk i) false = true :=
                    hDw _ (List.mem_map.mpr ⟨sk i, List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hine]⟩, rfl⟩, rfl⟩)
                  exact ih i (by omega) (by omega) hine hDi
              · simp only [Tt, hop, htest_or, ↓reduceIte] at hDw
                split_ifs at hDw with hmem
                · simp only [hop, heval_or, List.any_eq_true, id_eq, List.mem_map]
                  exact ⟨(C.wires x).getD N false, ⟨N, hmem, rfl⟩, hNt⟩
                · simp only [hop, heval_or, List.any_eq_true, id_eq, List.mem_map] at hDw ⊢
                  rcases hDw with ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, hDi⟩
                  have hilt : i < 26 + k := hCrb k hklt i hi
                  have hine : i ≠ N := fun heq => hmem (heq ▸ hi)
                  exact ⟨(C.wires x).getD i false, ⟨i, hi, rfl⟩, ih i (by omega) (by omega) hine hDi⟩
        have hDok : ok D := by
          refine ⟨hDmono, hDrb, fun b' x hx => ?_⟩
          cases b'
          · cases hDv : D.eval x
            · rfl
            · exfalso
              have hNt : (C.wires x).getD N false = true := by
                cases hNx : (C.wires x).getD N false
                · exact absurd hNx (hb x hx)
                · rfl
              have hCv : C.eval x = true := hDn x (hrow_len false x hx) hNt C.output hOutLt hOutNe hDv
              have hCf := hCeval false x hx
              rw [hCv] at hCf
              exact Bool.noConfusion hCf
          · exact hUp x (hrow_len true x hx) C.output hOutLt hOutNe (hCeval true x hx)
        exact ⟨D, (hok_iff D).mpr hDok, by show D.gates.length < C.gates.length; omega⟩
      · let Tf : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun h =>
          if h.op.eval [true, false] then
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map sk⟩
          else
            if N ∈ h.inputs then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ else ⟨h.op, h.inputs.map sk⟩
        let D : PEqualNP.CircuitLowerBounds.Circuit :=
          ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map Tf, sk C.output⟩
        have hDlen : D.gates.length = C.gates.length - 1 := by
          simp [D, List.length_take_of_le (Nat.le_of_lt hm)]
          omega
        have hDlt : ∀ k < m, PEqualNP.MetaComplexity.NestedCover.gateAt D k = PEqualNP.MetaComplexity.NestedCover.gateAt C k := by
          intro k hk
          rw [hgateAt_eq D k (by omega), hgateAt_eq C k (by omega)]
          simp only [D]
          rw [List.getElem_append_left (by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hk)]
          exact List.getElem_take
        have hDge : ∀ k, m ≤ k → k < C.gates.length - 1 →
            PEqualNP.MetaComplexity.NestedCover.gateAt D k = Tf (PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1)) := by
          intro k hkm hklt
          have htle : (C.gates.take m).length ≤ k := by rw [List.length_take_of_le (Nat.le_of_lt hm)]; exact hkm
          have hidx : m + 1 + (k - (C.gates.take m).length) = k + 1 := by
            rw [List.length_take_of_le (Nat.le_of_lt hm)]
            omega
          simp only [D, hgateAt_def, List.getD_eq_getElem?_getD,
            List.getElem?_append_right htle, List.getElem?_map, List.getElem?_drop, hidx,
            List.getElem?_eq_getElem (show k + 1 < C.gates.length by omega)]
          rfl
        have hDmono : PEqualNP.MetaComplexity.Monotone2 D := by
          intro g hg
          simp only [D, List.mem_append, List.mem_map] at hg
          rcases hg with hg | ⟨g0, hg0, rfl⟩
          · exact hCmono g (List.mem_of_mem_take hg)
          · have h0 := hCmono_or g0 (List.mem_of_mem_drop hg0)
            rcases h0.1 with hop | hop
            · simp only [Tf, hop, htest_and, Bool.false_eq_true, ↓reduceIte]
              split_ifs
              · exact ⟨Or.inr rfl, by simp⟩
              · exact ⟨Or.inl rfl, by simp [h0.2]⟩
            · simp only [Tf, hop, htest_or, ↓reduceIte]
              refine ⟨Or.inr rfl, ?_⟩
              calc ((g0.inputs.filter (fun i => decide (i ≠ N))).map sk).length
                  = (g0.inputs.filter (fun i => decide (i ≠ N))).length := List.length_map _
                _ ≤ g0.inputs.length := List.length_filter_le _ _
                _ ≤ 2 := h0.2
        have hDrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D := by
          intro k hk i hi
          by_cases hkm : k < m
          · rw [hDlt k hkm] at hi
            exact hCrb k (by omega) i hi
          · rw [hDge k (by omega) (by omega)] at hi
            have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C (k + 1) ∈ C.gates := by
              rw [hgateAt_eq C (k + 1) (by omega)]
              exact List.getElem_mem (by omega)
            rcases (hCmono_or _ hgkmem).1 with hop | hop
            · simp only [Tf, hop, htest_and, Bool.false_eq_true, ↓reduceIte] at hi
              split_ifs at hi with hmem
              · simp at hi
              · simp only [List.mem_map] at hi
                rcases hi with ⟨i0, hi0, rfl⟩
                have hine : i0 ≠ N := fun heq => hmem (heq ▸ hi0)
                exact hsk_lt k i0 (by omega) (hCrb (k + 1) (by omega) i0 hi0) hine
            · simp only [Tf, hop, htest_or, ↓reduceIte,
                List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
              rcases hi with ⟨i0, ⟨hi0, hine⟩, rfl⟩
              exact hsk_lt k i0 (by omega) (hCrb (k + 1) (by omega) i0 hi0) hine
        have hOutNe : C.output ≠ N := by
          intro heq
          have h1 := hCeval true _ hPosWit
          have h2 := hb _ hPosWit
          unfold PEqualNP.CircuitLowerBounds.Circuit.eval at h1
          rw [heq] at h1
          exact h2 h1
        have hPreEq : ∀ (x : List Bool), x.length = 26 → ∀ w < N,
            (D.wires x).getD w false = (C.wires x).getD w false := by
          intro x hx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hw26 : w < 26
            · rw [hwires_prefix D x w (by omega), hwires_prefix C x w (by omega)]
            · let k := w - 26
              have hklt : k < m := by omega
              have hkw : w = 26 + k := by omega
              rw [hkw]
              have h1 := hwf_gate_rb D x k (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) (by omega)
              rw [hx] at h1 h2
              rw [h1, h2, hDlt k hklt]
              apply congrArg (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
              apply List.map_congr_left
              intro i hi
              have hilt : i < 26 + k := hCrb k (by omega) i hi
              exact ih i (by omega) (by omega)
        have hDn : ∀ (x : List Bool), x.length = 26 →
            ∀ w < 26 + C.gates.length, w ≠ N →
            (D.wires x).getD (sk w) false = true →
            (C.wires x).getD w false = true := by
          intro x hx w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hwne hDw
            by_cases hwN : w < N
            · have hskw : sk w = w := by simp [sk, hwN]
              rw [hskw, hPreEq x hx w hwN] at hDw
              exact hDw
            · let k := w - 26
              have hkm : m < k := by omega
              have hklt : k < C.gates.length := by omega
              have hkw : w = 26 + k := by omega
              have hskw : sk w = 26 + (k - 1) := by simp only [sk]; split_ifs; omega
              rw [hskw] at hDw
              have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
              rw [hx] at h1 h2
              rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega] at hDw
              rw [hkw, h2]
              have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                rw [hgateAt_eq C k hklt]
                exact List.getElem_mem hklt
              rcases (hCmono_or _ hgkmem).1 with hop | hop
              · simp only [Tf, hop, htest_and, Bool.false_eq_true, ↓reduceIte] at hDw
                split_ifs at hDw with hmem
                · rw [heval_or] at hDw
                  simp at hDw
                · simp only [hop, heval_and, List.all_eq_true, id_eq] at hDw ⊢
                  intro y hy
                  simp only [List.mem_map] at hy
                  rcases hy with ⟨i, hi, rfl⟩
                  have hilt : i < 26 + k := hCrb k hklt i hi
                  have hine : i ≠ N := fun heq => hmem (heq ▸ hi)
                  have hDi : (D.wires x).getD (sk i) false = true :=
                    hDw _ (List.mem_map.mpr ⟨sk i, List.mem_map.mpr ⟨i, hi, rfl⟩, rfl⟩)
                  exact ih i (by omega) (by omega) hine hDi
              · simp only [Tf, hop, htest_or, ↓reduceIte, heval_or, List.any_eq_true, id_eq,
                  List.mem_map, List.mem_filter, decide_eq_true_eq] at hDw ⊢
                rcases hDw with ⟨_, ⟨_, ⟨i, ⟨hi, hine⟩, rfl⟩, rfl⟩, hDi⟩
                have hilt : i < 26 + k := hCrb k hklt i hi
                exact ⟨(C.wires x).getD i false, ⟨i, hi, rfl⟩, ih i (by omega) (by omega) hine hDi⟩
        have hUp : ∀ (x : List Bool), x.length = 26 → (C.wires x).getD N false = false →
            ∀ w < 26 + C.gates.length, w ≠ N →
            (C.wires x).getD w false = true →
            (D.wires x).getD (sk w) false = true := by
          intro x hx hNf w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hwne hCw
            by_cases hwN : w < N
            · have hskw : sk w = w := by simp [sk, hwN]
              rw [hskw, hPreEq x hx w hwN]
              exact hCw
            · let k := w - 26
              have hkm : m < k := by omega
              have hklt : k < C.gates.length := by omega
              have hkw : w = 26 + k := by omega
              have hskw : sk w = 26 + (k - 1) := by simp only [sk]; split_ifs; omega
              rw [hskw]
              have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
              have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
              rw [hx] at h1 h2
              rw [hkw, h2] at hCw
              rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega]
              have hgkmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
                rw [hgateAt_eq C k hklt]
                exact List.getElem_mem hklt
              rcases (hCmono_or _ hgkmem).1 with hop | hop
              · simp only [Tf, hop, htest_and, Bool.false_eq_true, ↓reduceIte]
                have hNnot : N ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs := by
                  intro hmem
                  simp only [hop, heval_and, List.all_eq_true, id_eq] at hCw
                  have hNt := hCw _ (List.mem_map.mpr ⟨N, hmem, rfl⟩)
                  rw [hNf] at hNt
                  exact Bool.noConfusion hNt
                rw [ite_eq_right_iff.mpr (fun h => False.elim (hNnot h))]
                simp only [hop, heval_and, List.all_eq_true, id_eq] at hCw ⊢
                intro y hy
                simp only [List.mem_map] at hy
                rcases hy with ⟨_, ⟨i, hi, rfl⟩, rfl⟩
                have hilt : i < 26 + k := hCrb k hklt i hi
                have hine : i ≠ N := fun heq => hNnot (heq ▸ hi)
                have hCi : (C.wires x).getD i false = true := hCw _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
                exact ih i (by omega) (by omega) hine hCi
              · simp only [Tf, hop, htest_or, ↓reduceIte, heval_or, List.any_eq_true, id_eq,
                  List.mem_map, List.mem_filter, decide_eq_true_eq] at hCw ⊢
                rcases hCw with ⟨_, ⟨i, hi, rfl⟩, hCi⟩
                have hine : i ≠ N := by
                  intro heq
                  rw [heq, hNf] at hCi
                  exact Bool.noConfusion hCi
                have hilt : i < 26 + k := hCrb k hklt i hi
                exact ⟨(D.wires x).getD (sk i) false, ⟨sk i, ⟨i, ⟨hi, hine⟩, rfl⟩, rfl⟩,
                  ih i (by omega) (by omega) hine hCi⟩
        have hDok : ok D := by
          refine ⟨hDmono, hDrb, fun b' x hx => ?_⟩
          cases b'
          · cases hDv : D.eval x
            · rfl
            · exfalso
              have hCv : C.eval x = true := hDn x (hrow_len false x hx) C.output hOutLt hOutNe hDv
              have hCf := hCeval false x hx
              rw [hCv] at hCf
              exact Bool.noConfusion hCf
          · have hNf : (C.wires x).getD N false = false := by
              cases hNx : (C.wires x).getD N false
              · rfl
              · exact absurd hNx (hb x hx)
            exact hUp x (hrow_len true x hx) hNf C.output hOutLt hOutNe (hCeval true x hx)
        exact ⟨D, (hok_iff D).mpr hDok, by show D.gates.length < C.gates.length; omega⟩
  · push Not at hLive
    obtain ⟨m, hm, hndead⟩ := hLive
    change m < C.gates.length at hm
    let D := PEqualNP.CircuitMoves.eraseGate 26 C m 0
    obtain ⟨hDsz, hDmono, hDrb, hDlt, hDge⟩ := herase_basic m 0 hm (by omega)
    change D.gates.length = C.gates.length - 1 at hDsz
    have hDout : D.output = PEqualNP.CircuitMoves.eraseRedirect 26 m 0 C.output :=
      herase_out m 0 hm
    have hEqLive : ∀ (x : List Bool), x.length = 26 →
        ∀ w < 26 + C.gates.length,
        (w < 26 ∨ (26 ≤ w ∧ PEqualNP.Core.InOutputCone 26 C (w - 26))) →
        (D.wires x).getD (PEqualNP.CircuitMoves.eraseRedirect 26 m 0 w) false = (C.wires x).getD w false := by
      intro x hx w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hlive
        by_cases hw26 : w < 26
        · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m 0 w = w := by
            unfold PEqualNP.CircuitMoves.eraseRedirect
            split_ifs <;> omega
          rw [hr, hwires_prefix D x w (by omega), hwires_prefix C x w (by omega)]
        · have hwge : 26 ≤ w := Nat.le_of_not_lt hw26
          have hlivek : PEqualNP.Core.InOutputCone 26 C (w - 26) := by
            rcases hlive with h | h
            · omega
            · exact h.2
          let k := w - 26
          have hklt : k < C.gates.length := by omega
          have hkw : w = 26 + k := by omega
          have hkm_ne : k ≠ m := fun heq => hndead (heq ▸ hlivek)
          have hstep : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
              (D.wires x).getD (PEqualNP.CircuitMoves.eraseRedirect 26 m 0 i) false = (C.wires x).getD i false := by
            intro i hi
            have hilt : i < 26 + k := hCrb k hklt i hi
            apply ih i (by omega) (by omega)
            by_cases hi26 : i < 26
            · exact Or.inl hi26
            · right
              refine ⟨by omega, by omega, ?_⟩
              have hic : PEqualNP.EdgeOwnership.InCone 26 C (i - 26) k := by
                apply (hcone_rec k hklt (i - 26)).mpr
                exact ⟨i, hi, by omega, hilt, Or.inl rfl⟩
              rcases hlivek.2 with houtk | ⟨h26o, hko⟩
              · right
                refine ⟨hOutGe, ?_⟩
                have hk_eq : k = C.output - 26 := by omega
                rwa [← hk_eq]
              · right
                exact ⟨h26o, hcone_trans (C.output - 26) (i - 26) k hic hko⟩
          by_cases hkm : k < m
          · have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m 0 w = 26 + k := by
              unfold PEqualNP.CircuitMoves.eraseRedirect
              split_ifs <;> omega
            rw [hr, hkw]
            have h1 := hwf_gate_rb D x k (by rw [hx]; exact hDrb) (by omega)
            have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
            rw [hx] at h1 h2
            rw [h1, h2, hDlt k hkm]
            apply congrArg (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
            apply List.map_congr_left
            intro i hi
            have hilt : i < 26 + k := hCrb k hklt i hi
            have hri : PEqualNP.CircuitMoves.eraseRedirect 26 m 0 i = i := by
              unfold PEqualNP.CircuitMoves.eraseRedirect
              split_ifs <;> omega
            conv_lhs => rw [← hri]
            exact hstep i hi
          · have hkmgt : m < k := by omega
            have hr : PEqualNP.CircuitMoves.eraseRedirect 26 m 0 w = 26 + (k - 1) := by
              unfold PEqualNP.CircuitMoves.eraseRedirect
              split_ifs <;> omega
            rw [hr, hkw]
            have h1 := hwf_gate_rb D x (k - 1) (by rw [hx]; exact hDrb) (by omega)
            have h2 := hwf_gate_rb C x k (by rw [hx]; exact hCrb) hklt
            rw [hx] at h1 h2
            rw [h1, hDge (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega]
            simp only [List.map_map]
            rw [h2]
            apply congrArg (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
            apply List.map_congr_left
            intro i hi
            exact hstep i hi
    have hDok : ok D := by
      refine ⟨hDmono, hDrb, fun b x hx => ?_⟩
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [hDout, hEqLive x (hrow_len b x hx) C.output hOutLt (Or.inr ⟨hOutGe, by omega, Or.inl (by omega)⟩)]
      exact hCeval b x hx
    exact ⟨D, (hok_iff D).mpr hDok, by show D.gates.length < C.gates.length; omega⟩
