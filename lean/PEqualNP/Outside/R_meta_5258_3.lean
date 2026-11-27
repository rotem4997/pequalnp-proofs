import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.SharedOr

-- Clean away dead gates, wire aliases, degenerate fan-in/duplicate gates, and constant gates,
-- then choose a maximal nested AND gate j (so only OR gates lie above j).
-- Either j feeds both outputs (hence rejects every quadrangle) or j is private to one output.
set_option maxHeartbeats 2800000 in
theorem PEqualNP.Outside.R_meta_5258_3
    (sharedTopAnd :
      let T := Circuit
      let n := 26
      let S := singerLines3
      let H := fun (C : T) => (quadrangles S).filter fun Q =>
        C.eval (incidenceInput Q (missLines S Q)) = true
      let ok := fun (C D : T) => C.gates = D.gates ∧ Monotone2 C ∧ ReadsBack n C ∧
        Disjoint (H C) (H D) ∧ ∀ E ∈ [C, D], RightOnIncidentPairs S E ∧ (H E).Nonempty
      ∀ (C D : T) (j : ℕ),
        let g := gateAt C
        let ic := InOutCone n C
        ok C D → C.size < 63 → j < C.size →
        (∀ k < C.size, (g k).inputs.length = 2 ∧ (g k).inputs.Nodup ∧
          (ic (n + k) C.output ∨ ic (n + k) D.output) ∧
          ∀ p < n + k, ∃ x : List Bool, x.length = n ∧
            (C.wires x).getD (n + k) false ≠ (C.wires x).getD p false) →
        (g j).op = .and →
        (∃ i, (g i).op = .and ∧ InCone n C i j) →
        (∀ k, InCone n C j k → (g k).op = .or) →
        ic (n + j) C.output → ic (n + j) D.output →
        ¬ (H ⟨C.gates, n + j⟩).Nonempty →
        ∃ E F : T, ok E F ∧ E.size < C.size)
    (privateTopAnd :
      let T := Circuit
      let n := 26
      let S := singerLines3
      let H := fun (C : T) => (quadrangles S).filter fun Q =>
        C.eval (incidenceInput Q (missLines S Q)) = true
      let ok := fun (C D : T) => C.gates = D.gates ∧ Monotone2 C ∧ ReadsBack n C ∧
        Disjoint (H C) (H D) ∧ ∀ E ∈ [C, D], RightOnIncidentPairs S E ∧ (H E).Nonempty
      ∀ (C D : T) (j : ℕ),
        let g := gateAt C
        let ic := InOutCone n C
        ok C D → C.size < 63 → j < C.size →
        (∀ k < C.size, (g k).inputs.length = 2 ∧ (g k).inputs.Nodup ∧
          (ic (n + k) C.output ∨ ic (n + k) D.output) ∧
          ∀ p < n + k, ∃ x : List Bool, x.length = n ∧
            (C.wires x).getD (n + k) false ≠ (C.wires x).getD p false) →
        (g j).op = .and →
        (∃ i, (g i).op = .and ∧ InCone n C i j) →
        (∀ k, InCone n C j k → (g k).op = .or) →
        ic (n + j) C.output → ¬ ic (n + j) D.output →
        ∃ E F : T, ok E F ∧ E.size < C.size) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) =>   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), x5 x6 x7 x8 → x6.size < (63 : ℕ) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x5 x12 x13 x14 ∧ x12.size < x6.size := by
  intro dif posRaw negRaw quad Form C u v hForm hSmall hNested
  classical
  let Qs := quadrangles singerLines3
  let sample (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  let hit (D : Circuit) (w : ℕ) := Qs.filter
    (fun Q => (Circuit.mk D.gates w).eval (sample Q) = true)
  let val (D : Circuit) (w : ℕ) (xs : List Bool) := (D.wires xs).getD w false
  let valid (D : Circuit) (a b : ℕ) :=
    Monotone2 D ∧ ReadsBack 26 D ∧
    RightOnIncidentPairs singerLines3 ⟨D.gates, a⟩ ∧ RightOnIncidentPairs singerLines3 ⟨D.gates, b⟩ ∧
    Disjoint (hit D a) (hit D b) ∧ (hit D a).Nonempty ∧ (hit D b).Nonempty
  have incidence (p l : Fin 13) : p - l ∈ dif ↔ p ∈ singerLines3 l := by
    change p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l
    revert p l
    decide +kernel
  have incidenceRow (p l : Fin 13) : incidenceInput {p} {l} = posRaw p l := by
    change (List.ofFn (fun x : Fin 13 => decide (x ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun x : Fin 13 => decide (x ∈ ({l} : Finset (Fin 13))))) = _
    simp only [Finset.mem_singleton]
    rfl
  have quadrangle (Q : Finset (Fin 13)) : Q ∈ Qs ↔ quad Q := by
    have cross (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun x => x - l ∈ dif) := by
      ext x
      simp [incidence x l]
    change Q ∈ (Finset.univ.powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, cross]
    rfl
  have quadrangleRow (Q : Finset (Fin 13)) : sample Q = negRaw Q := by
    have tail : List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ dif)) := by
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      change l ∈ Finset.univ.filter (fun k => Disjoint (singerLines3 k) Q) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← incidence]
      exact ⟨fun h p hp hi => h hi hp, fun h p hp hi => h p hi hp⟩
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ Q))) ++ _ = _
    rw [tail]
  have inputLength (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ L))).length = 26
    simp
  have memHit (D : Circuit) (a : ℕ) (Q : Finset (Fin 13)) :
      Q ∈ hit D a ↔ Q ∈ Qs ∧ val D a (sample Q) = true := by
    change Q ∈ Qs.filter (fun X => val D a (sample X) = true) ↔ _
    exact Finset.mem_filter
  have strict : ∀ a b : Bool, a < b ↔ a = false ∧ b = true := by decide
  have compact (D : Circuit) (a b : ℕ) : Form D a b ↔ valid D a b := by
    constructor
    · rintro ⟨hm, hb, hpos, hneg, hab, hba⟩
      refine ⟨hm, hb, ?_, ?_, ?_, ?_, ?_⟩
      · intro l p hinc
        have h := Bool.and_eq_true_iff.mp (hpos p l ((incidence p l).mpr hinc))
        change val D a (incidenceInput {p} {l}) = true
        rw [incidenceRow]
        exact h.1
      · intro l p hinc
        have h := Bool.and_eq_true_iff.mp (hpos p l ((incidence p l).mpr hinc))
        change val D b (incidenceInput {p} {l}) = true
        rw [incidenceRow]
        exact h.2
      · apply Finset.disjoint_left.mpr
        intro Q ha hb
        obtain ⟨hq, ha⟩ := (memHit D a Q).mp ha
        have hb := ((memHit D b Q).mp hb).2
        rw [quadrangleRow] at ha hb
        have imp := hneg Q ((quadrangle Q).mp hq)
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false at imp
        simp [ha, hb] at imp
      · obtain ⟨B, hB, hBA⟩ := hba
        exact ⟨B, (memHit D a B).mpr ⟨(quadrangle B).mpr hB, by
          rw [quadrangleRow]; exact ((strict _ _).mp hBA).2⟩⟩
      · obtain ⟨A, hA, hAB⟩ := hab
        exact ⟨A, (memHit D b A).mpr ⟨(quadrangle A).mpr hA, by
          rw [quadrangleRow]; exact ((strict _ _).mp hAB).2⟩⟩
    · rintro ⟨hm, hb, pa, pb, hdisj, liveA, liveB⟩
      refine ⟨hm, hb, ?_, ?_, ?_, ?_⟩
      · intro p l hinc
        apply Bool.and_eq_true_iff.mpr
        have h1 := pa l p ((incidence p l).mp hinc)
        have h2 := pb l p ((incidence p l).mp hinc)
        change val D a (incidenceInput {p} {l}) = true at h1
        change val D b (incidenceInput {p} {l}) = true at h2
        rw [incidenceRow] at h1 h2
        exact ⟨h1, h2⟩
      · intro Q hQ
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false
        rw [← quadrangleRow]
        cases h : (val D a (sample Q) && val D b (sample Q)) with
        | false => rfl
        | true =>
          have bits := Bool.and_eq_true_iff.mp h
          have hq := (quadrangle Q).mpr hQ
          exact (Finset.disjoint_left.mp hdisj ((memHit D a Q).mpr ⟨hq, bits.1⟩)
            ((memHit D b Q).mpr ⟨hq, bits.2⟩)).elim
      · obtain ⟨Q, hQ⟩ := liveB
        obtain ⟨hq, bt⟩ := (memHit D b Q).mp hQ
        have af : val D a (sample Q) = false := by
          cases h : val D a (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp hdisj ((memHit D a Q).mpr ⟨hq, h⟩) hQ).elim
        refine ⟨Q, (quadrangle Q).mp hq, (strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨af, bt⟩
      · obtain ⟨Q, hQ⟩ := liveA
        obtain ⟨hq, atrue⟩ := (memHit D a Q).mp hQ
        have bf : val D b (sample Q) = false := by
          cases h : val D b (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp hdisj hQ ((memHit D b Q).mpr ⟨hq, h⟩)).elim
        refine ⟨Q, (quadrangle Q).mp hq, (strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨bf, atrue⟩
  -- Basic wire-evaluation helpers
  let wf (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wf_len (gs : List Gate) (w : List Bool) : (wf gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wf]
    | cons g gs ih =>
      show (wf gs (w ++ [_])).length = w.length + (gs.length + 1)
      rw [ih]; simp; omega
  have wf_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (wf gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      show (wf gs (w ++ [_])).getD i false = w.getD i false
      rw [ih _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have wf_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
      (hback : ∀ u ∈ gs[k].inputs, u < x.length + k) :
      (wf gs x).getD (x.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun u => (wf gs x).getD u false) := by
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hpref_len : (wf (gs.take k) x).length = x.length + k := by
      rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have hstep : wf gs x = wf (gs.drop (k + 1))
        (wf (gs.take k) x ++ [gs[k].op.eval (gs[k].inputs.map fun u => (wf (gs.take k) x).getD u false)]) := by
      dsimp only [wf]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      rfl
    have hval : (wf gs x).getD (x.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun u => (wf (gs.take k) x).getD u false) := by
      rw [hstep, wf_getD_lt _ _ (x.length + k) (by simp [hpref_len])]
      rw [← hpref_len]
      simp [List.getD_eq_getElem?_getD]
    rw [hval]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hult : u < (wf (gs.take k) x).length := by rw [hpref_len]; exact hback u hu
    have hult' : u < (wf (gs.take k) x ++
        [gs[k].op.eval (gs[k].inputs.map fun u => (wf (gs.take k) x).getD u false)]).length := by
      simp [Nat.lt_succ_of_lt hult]
    rw [hstep, wf_getD_lt _ _ u hult']
    symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hult, ← List.getD_eq_getElem?_getD]
  have gateAt_eq (D : Circuit) (k : ℕ) (hk : k < D.gates.length) : gateAt D k = D.gates[k] :=
    List.getD_eq_getElem _ _ hk
  have gateAt_mem (D : Circuit) (k : ℕ) (hk : k < D.gates.length) : gateAt D k ∈ D.gates := by
    rw [gateAt_eq D k hk]; exact List.getElem_mem hk
  have val_gate (D : Circuit) (hb : ReadsBack 26 D) (k : ℕ) (hk : k < D.gates.length)
      (x : List Bool) (hx : x.length = 26) :
      val D (26 + k) x = (gateAt D k).op.eval ((gateAt D k).inputs.map fun u => val D u x) := by
    have hg : gateAt D k = D.gates[k] := gateAt_eq D k hk
    have h1 := wf_gate D.gates x k hk (by
      intro u hu
      rw [hx]
      have := hb k hk u
      rw [hg] at this
      exact this hu)
    rw [hx] at h1
    rw [hg]
    exact h1
  have val_in (D : Circuit) (x : List Bool) (hx : x.length = 26) (w : ℕ) (hw : w < 26) :
      val D w x = x.getD w false := by
    exact wf_getD_lt D.gates x w (by omega)
  have val_oob (D : Circuit) (x : List Bool) (hx : x.length = 26) (w : ℕ) (hw : 26 + D.size ≤ w) :
      val D w x = false := by
    apply List.getD_eq_default
    show (wf D.gates x).length ≤ w
    rw [wf_len, hx]
    exact hw
  -- Basic cone helpers (using definitional `change` to avoid generating `.eq_1` lemmas)
  have cones_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_getD_lt (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (hk : k < cs.length) :
      (gs.foldl (coneStep 26) cs).getD k [] = cs.getD k [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hk' : k < (coneStep 26 cs g).length := by
        change k < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih _ hk']
      change (cs ++ [_]).getD k [] = cs.getD k []
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
  have inCone_lt_len (D : Circuit) (i k : ℕ) (h : InCone 26 D i k) : k < D.gates.length := by
    by_contra hge
    have hlen : (cones 26 D).length = D.gates.length := by
      change (D.gates.foldl (coneStep 26) []).length = D.gates.length
      rw [cones_len]
      simp
    have hdef : (cones 26 D).getD k [] = [] := List.getD_eq_default _ _ (by omega)
    change i ∈ (cones 26 D).getD k [] at h
    rw [hdef] at h
    exact List.not_mem_nil h
  have inCone_iff (D : Circuit) (i k : ℕ) (hk : k < D.gates.length) :
      InCone 26 D i k ↔
        ∃ w ∈ (gateAt D k).inputs, 26 ≤ w ∧ w < 26 + k ∧ (i = w - 26 ∨ InCone 26 D i (w - 26)) := by
    have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by
      have h1 := (List.take_append_drop k D.gates).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    let pref := (D.gates.take k).foldl (coneStep 26) []
    have hplen : pref.length = k := by
      have := cones_len (D.gates.take k) []
      simp [pref, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this ⊢
      exact this
    have hstep : cones 26 D = (D.gates.drop (k + 1)).foldl (coneStep 26) (coneStep 26 pref D.gates[k]) := by
      change D.gates.foldl (coneStep 26) [] = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      rfl
    have hpref_eq (t : ℕ) (ht : t < k) : pref.getD t [] = (cones 26 D).getD t [] := by
      have ht' : t < (coneStep 26 pref D.gates[k]).length := by
        change t < (pref ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil, hplen]
        omega
      rw [hstep, cones_getD_lt _ _ t ht']
      change pref.getD t [] = (pref ++ [_]).getD t []
      symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : t < pref.length),
        ← List.getD_eq_getElem?_getD]
    have hget : (cones 26 D).getD k [] =
        (D.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
          (fun w => (w - 26) :: pref.getD (w - 26) []) := by
      have hk' : k < (coneStep 26 pref D.gates[k]).length := by
        change k < (pref ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil, hplen]
        omega
      rw [hstep, cones_getD_lt _ _ k hk']
      change (pref ++ [(D.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + pref.length))).flatMap
          (fun w => (w - 26) :: pref.getD (w - 26) [])]).getD k [] = _
      have hsnoc : (pref ++ [(D.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + pref.length))).flatMap
          (fun w => (w - 26) :: pref.getD (w - 26) [])]).getD pref.length [] =
          (D.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + pref.length))).flatMap
          (fun w => (w - 26) :: pref.getD (w - 26) []) := by
        simp [List.getD_eq_getElem?_getD]
      simpa only [hplen] using hsnoc
    have hg : gateAt D k = D.gates[k] := gateAt_eq D k hk
    change i ∈ (cones 26 D).getD k [] ↔ _
    rw [hget, hg, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hmem⟩
      rw [List.mem_filter] at hw
      have hbd : 26 ≤ w ∧ w < 26 + k := of_decide_eq_true hw.2
      rw [List.mem_cons] at hmem
      refine ⟨w, hw.1, hbd.1, hbd.2, ?_⟩
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 26 D).getD (w - 26) []
        rw [← hpref_eq (w - 26) (by omega)]
        exact hmem
    · rintro ⟨w, hw, hlo, hhi, hcase⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨hlo, hhi⟩⟩, List.mem_cons.mpr ?_⟩
      rcases hcase with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 26 D).getD (w - 26) [] at hmem
        rw [hpref_eq (w - 26) (by omega)]
        exact hmem
  have inCone_lt (D : Circuit) : ∀ k i, InCone 26 D i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik
      have hk := inCone_lt_len D i k hik
      obtain ⟨w, _, hlo, hhi, hcase⟩ := (inCone_iff D i k hk).mp hik
      rcases hcase with rfl | hsub
      · omega
      · have := ih (w - 26) (by omega) i hsub
        omega
  have inCone_trans (D : Circuit) : ∀ k i j, InCone 26 D i j → InCone 26 D j k → InCone 26 D i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i j hij hjk
      have hk := inCone_lt_len D j k hjk
      obtain ⟨w, hw, hlo, hhi, hcase⟩ := (inCone_iff D j k hk).mp hjk
      apply (inCone_iff D i k hk).mpr
      refine ⟨w, hw, hlo, hhi, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 26) (by omega) i j hij hsub
  have inOutCone_step (D : Circuit) (hb : ReadsBack 26 D) (k u a : ℕ)
      (hk : k < D.size) (hu : u ∈ (gateAt D k).inputs) (h26 : 26 ≤ u)
      (hka : InOutCone 26 D (26 + k) a) : InOutCone 26 D u a := by
    have hult : u < 26 + k := hb k hk u hu
    have hu_in_k : InCone 26 D (u - 26) k :=
      (inCone_iff D (u - 26) k hk).mpr ⟨u, hu, h26, hult, Or.inl rfl⟩
    rcases hka with rfl | ⟨_, ha26, hcone⟩
    · right
      refine ⟨h26, by omega, ?_⟩
      simpa using hu_in_k
    · right
      refine ⟨h26, ha26, inCone_trans D (a - 26) (u - 26) k hu_in_k ?_⟩
      simpa using hcone
  -- Unified eraseGate lemmas
  have erase_meta (D : Circuit) (hm : Monotone2 D) (hb : ReadsBack 26 D) (m p : ℕ)
      (hm_lt : m < D.size) (hp : p < 26 + m) :
      Monotone2 (eraseGate 26 D m p) ∧ ReadsBack 26 (eraseGate 26 D m p) ∧
        (eraseGate 26 D m p).size + 1 = D.size := by
    change m < D.gates.length at hm_lt
    let E := eraseGate 26 D m p
    have hEg : E.gates = D.gates.take m ++
        (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 m p)⟩) := by
      dsimp only [E, eraseGate]
      rw [ite_eq_left hm_lt]
    have hszLen : E.gates.length + 1 = D.gates.length := by
      rw [hEg, List.length_append, List.length_take, List.length_map, List.length_drop,
        Nat.min_eq_left (Nat.le_of_lt hm_lt)]
      omega
    have hmE : Monotone2 E := by
      intro g hg
      rw [hEg, List.mem_append, List.mem_map] at hg
      rcases hg with h1 | ⟨g0, hg0, rfl⟩
      · exact hm g (List.mem_of_mem_take h1)
      · obtain ⟨hop, hlen⟩ := hm g0 (List.mem_of_mem_drop hg0)
        exact ⟨hop, by simpa using hlen⟩
    have hbE : ReadsBack 26 E := by
      intro k hk u hu
      have hgE : gateAt E k = E.gates[k] := gateAt_eq E k hk
      rw [hgE] at hu
      by_cases hkm : k < m
      · have htk : k < (D.gates.take m).length := by rw [List.length_take]; omega
        have hEk : E.gates[k] = D.gates[k] := by
          simp only [hEg]
          rw [List.getElem_append_left htk, List.getElem_take]
        rw [hEk] at hu
        have hkD : k < D.gates.length := by omega
        have := hb k hkD u
        rw [gateAt_eq D k hkD] at this
        exact this hu
      · have htk : (D.gates.take m).length = m := by rw [List.length_take]; omega
        have hk1D : k + 1 < D.gates.length := by omega
        have hEk : E.gates[k] = ⟨D.gates[k + 1].op, D.gates[k + 1].inputs.map (eraseRedirect 26 m p)⟩ := by
          have hge : (D.gates.take m).length ≤ k := by omega
          have h1 : E.gates[k] = ((D.gates.drop (m + 1)).map
              (fun g => ⟨g.op, g.inputs.map (eraseRedirect 26 m p)⟩))[k - m]'(by
                rw [List.length_map, List.length_drop]; omega) := by
            simp only [hEg]
            rw [List.getElem_append_right hge]
            congr 1
            omega
          rw [h1, List.getElem_map, List.getElem_drop]
          have hidx : m + 1 + (k - m) = k + 1 := by omega
          simp [hidx]
        rw [hEk] at hu
        rcases List.mem_map.mp hu with ⟨u0, hu0, rfl⟩
        have hu0_lt : u0 < 26 + (k + 1) := by
          have := hb (k + 1) hk1D u0
          rw [gateAt_eq D (k + 1) hk1D] at this
          exact this hu0
        unfold eraseRedirect
        split_ifs <;> omega
    exact ⟨hmE, hbE, hszLen⟩
  have erase_eval (D : Circuit) (hm : Monotone2 D) (hb : ReadsBack 26 D) (m p : ℕ)
      (hm_lt : m < D.size) (hp : p < 26 + m) (P : ℕ → Prop)
      (hDown : ∀ k < D.size, P (26 + k) → ∀ u ∈ (gateAt D k).inputs, P u)
      (hElim : ¬ P (26 + m) ∨ ((∀ x : List Bool, x.length = 26 → val D (26 + m) x = val D p x) ∧ P p))
      (x : List Bool) (hx : x.length = 26) :
      ∀ w, P w → val (eraseGate 26 D m p) (eraseRedirect 26 m p w) x = val D w x := by
    change m < D.gates.length at hm_lt
    let E := eraseGate 26 D m p
    let f := eraseRedirect 26 m p
    obtain ⟨_, hbE, hszE⟩ := erase_meta D hm hb m p hm_lt hp
    change E.gates.length + 1 = D.gates.length at hszE
    have hEg : E.gates = D.gates.take m ++
        (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map f⟩) := by
      dsimp only [E, f, eraseGate]
      rw [ite_eq_left hm_lt]
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hPw
      change val E (f w) x = val D w x
      by_cases hw26 : w < 26
      · have hfw : f w = w := by unfold f eraseRedirect; split_ifs <;> omega
        rw [hfw, val_in E x hx w hw26, val_in D x hx w hw26]
      · by_cases hwHi : 26 + D.gates.length ≤ w
        · have hfw : f w = w - 1 := by unfold f eraseRedirect; split_ifs <;> omega
          rw [hfw, val_oob E x hx (w - 1) (by change 26 + E.gates.length ≤ w - 1; omega),
            val_oob D x hx w hwHi]
        · let k := w - 26
          have hwk : w = 26 + k := by omega
          have hk_lt : k < D.gates.length := by omega
          rw [hwk] at hPw ⊢
          rcases Nat.lt_trichotomy k m with hkm | rfl | hmk
          · have hfw : f (26 + k) = 26 + k := by unfold f eraseRedirect; split_ifs <;> omega
            rw [hfw, val_gate E hbE k (by omega) x hx, val_gate D hb k hk_lt x hx]
            have htk : k < (D.gates.take m).length := by rw [List.length_take]; omega
            have hEk : gateAt E k = gateAt D k := by
              rw [gateAt_eq E k (by omega), gateAt_eq D k hk_lt]
              simp only [hEg]
              rw [List.getElem_append_left htk, List.getElem_take]
            rw [hEk]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult : u < 26 + k := hb k hk_lt u hu
            have hfu : f u = u := by unfold f eraseRedirect; split_ifs <;> omega
            have hPu : P u := hDown k hk_lt hPw u hu
            have h1 : val E (f u) x = val D u x := ih u (by omega) hPu
            rwa [hfu] at h1
          · rcases hElim with hnot | ⟨heq, hPp⟩
            · exact (hnot hPw).elim
            · have hfm : f (26 + k) = p := by unfold f eraseRedirect; simp
              have hfp : f p = p := by unfold f eraseRedirect; split_ifs <;> omega
              rw [hfm, ← hfp, ih p (by omega) hPp, heq x hx]
          · have hfw : f (26 + k) = 26 + (k - 1) := by unfold f eraseRedirect; split_ifs <;> omega
            have hk1 : k - 1 < E.gates.length := by omega
            rw [hfw, val_gate E hbE (k - 1) hk1 x hx, val_gate D hb k hk_lt x hx]
            have hEk : gateAt E (k - 1) = ⟨(gateAt D k).op, (gateAt D k).inputs.map f⟩ := by
              rw [gateAt_eq E (k - 1) hk1, gateAt_eq D k hk_lt]
              have hge : (D.gates.take m).length ≤ k - 1 := by rw [List.length_take]; omega
              have h1 : E.gates[k - 1] = ((D.gates.drop (m + 1)).map
                  (fun g => ⟨g.op, g.inputs.map f⟩))[k - 1 - m]'(by
                    rw [List.length_map, List.length_drop]; omega) := by
                simp only [hEg]
                rw [List.getElem_append_right hge]
                congr 1
                rw [List.length_take]
                omega
              rw [h1, List.getElem_map, List.getElem_drop]
              have hidx : m + 1 + (k - 1 - m) = k := by omega
              simp [hidx]
            rw [hEk, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult : u < 26 + k := hb k hk_lt u hu
            have hPu : P u := hDown k hk_lt hPw u hu
            exact ih u (by omega) hPu
  -- Extract valid C u v
  obtain ⟨hmC, hbC, hpaC, hpbC, hdisjC, hliveA, hliveB⟩ := (compact C u v).mp hForm
  have hValid : valid C u v := ⟨hmC, hbC, hpaC, hpbC, hdisjC, hliveA, hliveB⟩
  -- Helper: shrink from semantic agreement on u and v
  have shrink_of_eq (E : Circuit) (a' b' : ℕ) (hmE : Monotone2 E) (hbE : ReadsBack 26 E)
      (hszE : E.size < C.size)
      (heqA : ∀ x : List Bool, x.length = 26 → val E a' x = val C u x)
      (heqB : ∀ x : List Bool, x.length = 26 → val E b' x = val C v x) :
      ∃ (D : Circuit) (c d : ℕ), Form D c d ∧ D.size < C.size := by
    have hhitA : hit E a' = hit C u := by
      ext Q
      rw [memHit, memHit, heqA _ (inputLength Q (missLines singerLines3 Q))]
    have hhitB : hit E b' = hit C v := by
      ext Q
      rw [memHit, memHit, heqB _ (inputLength Q (missLines singerLines3 Q))]
    have hpaE : RightOnIncidentPairs singerLines3 ⟨E.gates, a'⟩ := by
      intro l p hinc
      change val E a' (incidenceInput {p} {l}) = true
      rw [heqA _ (inputLength {p} {l})]
      exact hpaC l p hinc
    have hpbE : RightOnIncidentPairs singerLines3 ⟨E.gates, b'⟩ := by
      intro l p hinc
      change val E b' (incidenceInput {p} {l}) = true
      rw [heqB _ (inputLength {p} {l})]
      exact hpbC l p hinc
    refine ⟨E, a', b', (compact E a' b').mpr ⟨hmE, hbE, hpaE, hpbE, ?_, ?_, ?_⟩, hszE⟩
    · rw [hhitA, hhitB]; exact hdisjC
    · rw [hhitA]; exact hliveA
    · rw [hhitB]; exact hliveB
  -- Step 1: eliminate any dead gate outside cone(u) ∪ cone(v)
  by_cases hDead : ∃ k < C.size, ¬ InOutCone 26 C (26 + k) u ∧ ¬ InOutCone 26 C (26 + k) v
  · obtain ⟨k, hk, hnu, hnv⟩ := hDead
    obtain ⟨hmE, hbE, hszE⟩ := erase_meta C hmC hbC k 0 hk (by omega)
    let P' (w : ℕ) : Prop := w < 26 ∨ InOutCone 26 C w u ∨ InOutCone 26 C w v
    have hDown' : ∀ m < C.size, P' (26 + m) → ∀ w ∈ (gateAt C m).inputs, P' w := by
      intro m hm hPm w hw
      by_cases hw26 : 26 ≤ w
      · rcases hPm with hlt | h1 | h2
        · omega
        · exact Or.inr (Or.inl (inOutCone_step C hbC m w u hm hw hw26 h1))
        · exact Or.inr (Or.inr (inOutCone_step C hbC m w v hm hw hw26 h2))
      · exact Or.inl (by omega)
    have hNotP : ¬ P' (26 + k) := by
      rintro (hlt | h1 | h2)
      · omega
      · exact hnu h1
      · exact hnv h2
    have hEv := erase_eval C hmC hbC k 0 hk (by omega) P' hDown' (Or.inl hNotP)
    exact shrink_of_eq (eraseGate 26 C k 0) (eraseRedirect 26 k 0 u) (eraseRedirect 26 k 0 v)
      hmE hbE (by omega)
      (fun x hx => hEv x hx u (Or.inr (Or.inl (Or.inl rfl))))
      (fun x hx => hEv x hx v (Or.inr (Or.inr (Or.inl rfl))))
  have hNoDead : ∀ k < C.size, InOutCone 26 C (26 + k) u ∨ InOutCone 26 C (26 + k) v := by
    intro k hk
    by_contra h
    push Not at h
    exact hDead ⟨k, hk, h⟩
  -- Step 2: eliminate any gate that equals an earlier wire on all length-26 inputs
  by_cases hSameWire : ∃ k < C.size, ∃ p < 26 + k,
      ∀ x : List Bool, x.length = 26 → val C (26 + k) x = val C p x
  · obtain ⟨k, hk, p, hp, heq⟩ := hSameWire
    obtain ⟨hmE, hbE, hszE⟩ := erase_meta C hmC hbC k p hk hp
    have hEv := erase_eval C hmC hbC k p hk hp (fun _ => True)
      (fun _ _ _ _ _ => trivial) (Or.inr ⟨heq, trivial⟩)
    exact shrink_of_eq (eraseGate 26 C k p) (eraseRedirect 26 k p u) (eraseRedirect 26 k p v)
      hmE hbE (by omega)
      (fun x hx => hEv x hx u trivial)
      (fun x hx => hEv x hx v trivial)
  have hNoSame : ∀ k < C.size, ∀ p < 26 + k,
      ∃ x : List Bool, x.length = 26 ∧ val C (26 + k) x ≠ val C p x := by
    intro k hk p hp
    by_contra h
    push Not at h
    exact hSameWire ⟨k, hk, p, hp, h⟩
  -- Consequences of hNoSame: no fan-in 1 gate and no duplicate-input gate
  have hNotLen1 (k : ℕ) (hk : k < C.size) : (gateAt C k).inputs.length ≠ 1 := by
    intro hlen
    obtain ⟨p, hp_eq⟩ := List.length_eq_one_iff.mp hlen
    have hp_lt : p < 26 + k := hbC k hk p (by rw [hp_eq]; simp)
    have hop : (gateAt C k).op = .and ∨ (gateAt C k).op = .or :=
      (hmC (gateAt C k) (gateAt_mem C k hk)).1
    obtain ⟨x, hx, hne⟩ := hNoSame k hk p hp_lt
    apply hne
    rw [val_gate C hbC k hk x hx, hp_eq]
    rcases hop with h | h
    · rw [h]; change ([val C p x]).all id = val C p x; simp
    · rw [h]; change ([val C p x]).any id = val C p x; simp
  have hDistinctOfLen2 (k : ℕ) (hk : k < C.size) (hlen : (gateAt C k).inputs.length = 2) :
      (gateAt C k).inputs.Nodup := by
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
    rw [hpq]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true]
    intro heq
    subst heq
    have hp_lt : p < 26 + k := hbC k hk p (by rw [hpq]; simp)
    have hop : (gateAt C k).op = .and ∨ (gateAt C k).op = .or :=
      (hmC (gateAt C k) (gateAt_mem C k hk)).1
    obtain ⟨x, hx, hne⟩ := hNoSame k hk p hp_lt
    apply hne
    rw [val_gate C hbC k hk x hx, hpq]
    rcases hop with h | h
    · rw [h]; change ([val C p x, val C p x]).all id = val C p x; simp
    · rw [h]; change ([val C p x, val C p x]).any id = val C p x; simp
  -- Step 3: eliminate any constant-false gate (take maximal index m)
  by_cases hConstF : ∃ k < C.size, ∀ x : List Bool, x.length = 26 → val C (26 + k) x = false
  · let Fs := (Finset.range C.size).filter fun k => ∀ x : List Bool, x.length = 26 → val C (26 + k) x = false
    have hFsNE : Fs.Nonempty := by
      obtain ⟨k, hk, hf⟩ := hConstF
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hf⟩⟩
    let m := Fs.max' hFsNE
    have hmMem := Finset.mem_filter.mp (Finset.max'_mem Fs hFsNE)
    have hmLt : m < C.size := Finset.mem_range.mp hmMem.1
    have hmF : ∀ x : List Bool, x.length = 26 → val C (26 + m) x = false := hmMem.2
    have h0inc : (0 : Fin 13) ∈ singerLines3 0 := by decide
    have hmu : u ≠ 26 + m := by
      intro h
      have h1 : val C u (incidenceInput {0} {0}) = true := hpaC 0 0 h0inc
      rw [h, hmF _ (inputLength {0} {0})] at h1
      exact Bool.false_ne_true h1
    have hmv : v ≠ 26 + m := by
      intro h
      have h1 : val C v (incidenceInput {0} {0}) = true := hpbC 0 0 h0inc
      rw [h, hmF _ (inputLength {0} {0})] at h1
      exact Bool.false_ne_true h1
    have hNoRead : ∀ k < C.size, 26 + m ∉ (gateAt C k).inputs := by
      intro k hk hmem
      have hmk : m < k := by
        have := hbC k hk (26 + m) hmem
        omega
      obtain ⟨hop, hlenLe⟩ := hmC (gateAt C k) (gateAt_mem C k hk)
      rcases hop with hand | hor
      · have hkF : ∀ x : List Bool, x.length = 26 → val C (26 + k) x = false := by
          intro x hx
          rw [val_gate C hbC k hk x hx, hand]
          change ((gateAt C k).inputs.map fun w => val C w x).all id = false
          rw [List.all_eq_false]
          exact ⟨false, List.mem_map.mpr ⟨26 + m, hmem, hmF x hx⟩, by decide⟩
        have hkIn : k ∈ Fs := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkF⟩
        have hle := Finset.le_max' Fs k hkIn
        omega
      · have hlenNe0 : (gateAt C k).inputs.length ≠ 0 := by
          intro h0
          rw [List.length_eq_zero_iff.mp h0] at hmem
          exact List.not_mem_nil hmem
        have hlen2 : (gateAt C k).inputs.length = 2 := by
          have := hNotLen1 k hk; omega
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
        rw [hpq] at hmem
        have hOther : ∃ r < 26 + k, ∀ x : List Bool, x.length = 26 → val C (26 + k) x = val C r x := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · refine ⟨q, hbC k hk q (by rw [hpq]; simp), fun x hx => ?_⟩
            rw [val_gate C hbC k hk x hx, hor, hpq]
            change ([val C (26 + m) x, val C q x]).any id = val C q x
            simp [hmF x hx]
          · refine ⟨p, hbC k hk p (by rw [hpq]; simp), fun x hx => ?_⟩
            rw [val_gate C hbC k hk x hx, hor, hpq]
            change ([val C p x, val C (26 + m) x]).any id = val C p x
            simp [hmF x hx]
        obtain ⟨r, hr, heq⟩ := hOther
        obtain ⟨x, hx, hne⟩ := hNoSame k hk r hr
        exact hne (heq x hx)
    obtain ⟨hmE, hbE, hszE⟩ := erase_meta C hmC hbC m 0 hmLt (by omega)
    have hEv := erase_eval C hmC hbC m 0 hmLt (by omega) (fun w => w ≠ 26 + m)
      (fun k hk _ w hw hEq => hNoRead k hk (hEq ▸ hw))
      (Or.inl (fun h => h rfl))
    exact shrink_of_eq (eraseGate 26 C m 0) (eraseRedirect 26 m 0 u) (eraseRedirect 26 m 0 v)
      hmE hbE (by omega)
      (fun x hx => hEv x hx u hmu)
      (fun x hx => hEv x hx v hmv)
  -- Step 4: eliminate any constant-true gate (take maximal index m)
  by_cases hConstT : ∃ k < C.size, ∀ x : List Bool, x.length = 26 → val C (26 + k) x = true
  · let Ts := (Finset.range C.size).filter fun k => ∀ x : List Bool, x.length = 26 → val C (26 + k) x = true
    have hTsNE : Ts.Nonempty := by
      obtain ⟨k, hk, ht⟩ := hConstT
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ht⟩⟩
    let m := Ts.max' hTsNE
    have hmMem := Finset.mem_filter.mp (Finset.max'_mem Ts hTsNE)
    have hmLt : m < C.size := Finset.mem_range.mp hmMem.1
    have hmT : ∀ x : List Bool, x.length = 26 → val C (26 + m) x = true := hmMem.2
    have hmu : u ≠ 26 + m := by
      intro h
      obtain ⟨Q, hQ⟩ := hliveB
      obtain ⟨hQs, _⟩ := (memHit C v Q).mp hQ
      have huT : val C u (sample Q) = true := by rw [h]; exact hmT _ (inputLength _ _)
      exact Finset.disjoint_left.mp hdisjC ((memHit C u Q).mpr ⟨hQs, huT⟩) hQ
    have hmv : v ≠ 26 + m := by
      intro h
      obtain ⟨Q, hQ⟩ := hliveA
      obtain ⟨hQs, _⟩ := (memHit C u Q).mp hQ
      have hvT : val C v (sample Q) = true := by rw [h]; exact hmT _ (inputLength _ _)
      exact Finset.disjoint_left.mp hdisjC hQ ((memHit C v Q).mpr ⟨hQs, hvT⟩)
    have hNoRead : ∀ k < C.size, 26 + m ∉ (gateAt C k).inputs := by
      intro k hk hmem
      have hmk : m < k := by
        have := hbC k hk (26 + m) hmem
        omega
      obtain ⟨hop, hlenLe⟩ := hmC (gateAt C k) (gateAt_mem C k hk)
      rcases hop with hand | hor
      · have hlenNe0 : (gateAt C k).inputs.length ≠ 0 := by
          intro h0
          rw [List.length_eq_zero_iff.mp h0] at hmem
          exact List.not_mem_nil hmem
        have hlen2 : (gateAt C k).inputs.length = 2 := by
          have := hNotLen1 k hk; omega
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
        rw [hpq] at hmem
        have hOther : ∃ r < 26 + k, ∀ x : List Bool, x.length = 26 → val C (26 + k) x = val C r x := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · refine ⟨q, hbC k hk q (by rw [hpq]; simp), fun x hx => ?_⟩
            rw [val_gate C hbC k hk x hx, hand, hpq]
            change ([val C (26 + m) x, val C q x]).all id = val C q x
            simp [hmT x hx]
          · refine ⟨p, hbC k hk p (by rw [hpq]; simp), fun x hx => ?_⟩
            rw [val_gate C hbC k hk x hx, hand, hpq]
            change ([val C p x, val C (26 + m) x]).all id = val C p x
            simp [hmT x hx]
        obtain ⟨r, hr, heq⟩ := hOther
        obtain ⟨x, hx, hne⟩ := hNoSame k hk r hr
        exact hne (heq x hx)
      · have hkT : ∀ x : List Bool, x.length = 26 → val C (26 + k) x = true := by
          intro x hx
          rw [val_gate C hbC k hk x hx, hor]
          change ((gateAt C k).inputs.map fun w => val C w x).any id = true
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨26 + m, hmem, hmT x hx⟩, rfl⟩
        have hkIn : k ∈ Ts := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkT⟩
        have hle := Finset.le_max' Ts k hkIn
        omega
    obtain ⟨hmE, hbE, hszE⟩ := erase_meta C hmC hbC m 0 hmLt (by omega)
    have hEv := erase_eval C hmC hbC m 0 hmLt (by omega) (fun w => w ≠ 26 + m)
      (fun k hk _ w hw hEq => hNoRead k hk (hEq ▸ hw))
      (Or.inl (fun h => h rfl))
    exact shrink_of_eq (eraseGate 26 C m 0) (eraseRedirect 26 m 0 u) (eraseRedirect 26 m 0 v)
      hmE hbE (by omega)
      (fun x hx => hEv x hx u hmu)
      (fun x hx => hEv x hx v hmv)
  -- Now every gate has inputs.length = 2 and distinct inputs (hence IsAO2 26 C)
  have hLen2 (k : ℕ) (hk : k < C.size) : (gateAt C k).inputs.length = 2 := by
    obtain ⟨hop, hle⟩ := hmC (gateAt C k) (gateAt_mem C k hk)
    have hne1 := hNotLen1 k hk
    have hne0 : (gateAt C k).inputs.length ≠ 0 := by
      intro h0
      have hnil := List.length_eq_zero_iff.mp h0
      rcases hop with hand | hor
      · apply hConstT
        refine ⟨k, hk, fun x hx => ?_⟩
        rw [val_gate C hbC k hk x hx, hand, hnil]
        rfl
      · apply hConstF
        refine ⟨k, hk, fun x hx => ?_⟩
        rw [val_gate C hbC k hk x hx, hor, hnil]
        rfl
    omega
  have hDistinct : ∀ k < C.size, (gateAt C k).inputs.Nodup :=
    fun k hk => hDistinctOfLen2 k hk (hLen2 k hk)
  -- Step 5: choose a maximal nested AND gate j
  let Nest := (Finset.range C.size).filter fun j =>
    (gateAt C j).op = .and ∧ ∃ i, (gateAt C i).op = .and ∧ InCone 26 C i j
  have hNestNE : Nest.Nonempty := by
    obtain ⟨i, j, hi, hj, hcone⟩ := hNested
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (inCone_lt_len C i j hcone), hj, i, hi, hcone⟩⟩
  let j := Nest.max' hNestNE
  have hjMem := Finset.mem_filter.mp (Finset.max'_mem Nest hNestNE)
  have hjLt : j < C.size := Finset.mem_range.mp hjMem.1
  have hjAnd : (gateAt C j).op = .and := hjMem.2.1
  have hjHasI : ∃ i, (gateAt C i).op = .and ∧ InCone 26 C i j := hjMem.2.2
  have hNoAndAbove : ∀ k, InCone 26 C j k → (gateAt C k).op = .or := by
    intro k hjk
    have hkLt := inCone_lt_len C j k hjk
    have hop : (gateAt C k).op = .and ∨ (gateAt C k).op = .or :=
      (hmC (gateAt C k) (gateAt_mem C k hkLt)).1
    rcases hop with hand | hor
    · have hkIn : k ∈ Nest := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hkLt, hand, j, hjAnd, hjk⟩
      have hle := Finset.le_max' Nest k hkIn
      have hlt := inCone_lt C k j hjk
      omega
    · exact hor
  have hOrUp : ∀ k, InCone 26 C j k → ∀ x : List Bool, x.length = 26 →
      val C (26 + j) x = true → val C (26 + k) x = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hjk x hx hjT
      have hkLt := inCone_lt_len C j k hjk
      have hkOr := hNoAndAbove k hjk
      obtain ⟨w, hw, h26, hlt, hcase⟩ := (inCone_iff C j k hkLt).mp hjk
      have hwT : val C w x = true := by
        rcases hcase with hEq | hSub
        · have : w = 26 + j := by omega
          rw [this]; exact hjT
        · have : w = 26 + (w - 26) := by omega
          rw [this]
          exact ih (w - 26) (by omega) hSub x hx hjT
      rw [val_gate C hbC k hkLt x hx, hkOr]
      change ((gateAt C k).inputs.map fun u => val C u x).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨w, hw, hwT⟩, rfl⟩
  have hConeImplies (w : ℕ) (hw : InOutCone 26 C (26 + j) w) (x : List Bool) (hx : x.length = 26)
      (hjT : val C (26 + j) x = true) : val C w x = true := by
    rcases hw with rfl | ⟨_, hw26, hcone⟩
    · exact hjT
    · have hEq : w = 26 + (w - 26) := by omega
      rw [hEq]
      exact hOrUp (w - 26) (by simpa using hcone) x hx hjT
  -- Step 6: split on whether j lies in both cones or is private to one output
  let U : Circuit := ⟨C.gates, u⟩
  let V : Circuit := ⟨C.gates, v⟩
  have hClean : ∀ k < U.size, (gateAt U k).inputs.length = 2 ∧ (gateAt U k).inputs.Nodup ∧
      (InOutCone 26 U (26 + k) U.output ∨ InOutCone 26 U (26 + k) V.output) ∧
      ∀ p < 26 + k, ∃ x : List Bool, x.length = 26 ∧
        (U.wires x).getD (26 + k) false ≠ (U.wires x).getD p false :=
    fun k hk => ⟨hLen2 k hk, hDistinct k hk, hNoDead k hk, hNoSame k hk⟩
  have ofPair (E F : Circuit)
      (h : E.gates = F.gates ∧ Monotone2 E ∧ ReadsBack 26 E ∧
        Disjoint (hit E E.output) (hit F F.output) ∧
        ∀ G ∈ [E, F], RightOnIncidentPairs singerLines3 G ∧ (hit G G.output).Nonempty)
      (hsz : E.size < C.size) :
      ∃ (D : Circuit) (a' b' : ℕ), Form D a' b' ∧ D.size < C.size := by
    obtain ⟨heq, hmE, hbE, hd, hboth⟩ := h
    obtain ⟨hpE, hneE⟩ := hboth E (by simp)
    obtain ⟨hpF, hneF⟩ := hboth F (by simp)
    refine ⟨E, E.output, F.output, (compact E E.output F.output).mpr ?_, hsz⟩
    have hF1 : (Circuit.mk E.gates F.output) = F := by cases F; simp [heq]
    have hE1 : (Circuit.mk E.gates E.output) = E := by cases E; rfl
    refine ⟨hmE, hbE, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [hE1]
    · rwa [hF1]
    · change Disjoint (hit E E.output) (hit E F.output)
      have hhitF : hit E F.output = hit F F.output := by
        ext Q; simp only [hit, Finset.mem_filter, heq]
      rwa [hhitF]
    · exact hneE
    · have hhitF : hit E F.output = hit F F.output := by
        ext Q; simp only [hit, Finset.mem_filter, heq]
      rwa [hhitF]
  have hBothUV : ∀ G ∈ [U, V], RightOnIncidentPairs singerLines3 G ∧ (hit G G.output).Nonempty := by
    intro G hG
    rcases (show G = U ∨ G = V by simpa using hG) with rfl | rfl
    · exact ⟨hpaC, hliveA⟩
    · exact ⟨hpbC, hliveB⟩
  by_cases hInU : InOutCone 26 C (26 + j) u
  · by_cases hInV : InOutCone 26 C (26 + j) v
    · have hRej : ¬ (hit C (26 + j)).Nonempty := by
        rintro ⟨Q, hQ⟩
        obtain ⟨hQs, hval⟩ := (memHit C (26 + j) Q).mp hQ
        have huT := hConeImplies u hInU (sample Q) (inputLength _ _) hval
        have hvT := hConeImplies v hInV (sample Q) (inputLength _ _) hval
        exact Finset.disjoint_left.mp hdisjC
          ((memHit C u Q).mpr ⟨hQs, huT⟩) ((memHit C v Q).mpr ⟨hQs, hvT⟩)
      obtain ⟨E, F, hEF, hEsz⟩ := sharedTopAnd U V j
        ⟨rfl, hmC, hbC, hdisjC, hBothUV⟩
        hSmall hjLt hClean hjAnd hjHasI hNoAndAbove hInU hInV hRej
      exact ofPair E F hEF hEsz
    · obtain ⟨E, F, hEF, hEsz⟩ := privateTopAnd U V j
        ⟨rfl, hmC, hbC, hdisjC, hBothUV⟩
        hSmall hjLt hClean hjAnd hjHasI hNoAndAbove hInU hInV
      exact ofPair E F hEF hEsz
  · have hInV : InOutCone 26 C (26 + j) v :=
      (hNoDead j hjLt).resolve_left hInU
    have hBothVU : ∀ G ∈ [V, U], RightOnIncidentPairs singerLines3 G ∧ (hit G G.output).Nonempty := by
      intro G hG
      rcases (show G = V ∨ G = U by simpa using hG) with rfl | rfl
      · exact ⟨hpbC, hliveB⟩
      · exact ⟨hpaC, hliveA⟩
    have hCleanSwap : ∀ k < V.size, (gateAt V k).inputs.length = 2 ∧ (gateAt V k).inputs.Nodup ∧
        (InOutCone 26 V (26 + k) V.output ∨ InOutCone 26 V (26 + k) U.output) ∧
        ∀ p < 26 + k, ∃ x : List Bool, x.length = 26 ∧
          (V.wires x).getD (26 + k) false ≠ (V.wires x).getD p false :=
      fun k hk => ⟨hLen2 k hk, hDistinct k hk, (hNoDead k hk).symm, hNoSame k hk⟩
    obtain ⟨E, F, hEF, hEsz⟩ := privateTopAnd V U j
      ⟨rfl, hmC, hbC, hdisjC.symm, hBothVU⟩
      hSmall hjLt hCleanSwap hjAnd hjHasI hNoAndAbove hInV hInU
    exact ofPair E F hEF hEsz
