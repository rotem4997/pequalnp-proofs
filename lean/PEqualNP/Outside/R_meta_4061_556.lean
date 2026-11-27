import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4061_556
    (sameSide :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
        (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
          (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨
            b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) →
        ∀ C : Circuit, IsLeastAO G C →
          ∀ j ∈ junk G C, ¬ OrReaches 26 C C.output j →
            (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ InCone 26 C j k) →
            gateVal 26 C j (pairInput 0 1) = false)
    (nonIncident :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
        (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
          (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨
            b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) →
        ∀ C : Circuit, IsLeastAO G C →
          ∀ j ∈ junk G C, ¬ OrReaches 26 C C.output j →
            (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ InCone 26 C j k) →
            gateVal 26 C j (pairInput 0 14) = false) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x9 : Fin (26 : ℕ)), x9 = (0 : Fin (26 : ℕ)) ∨ x9 = (1 : Fin (26 : ℕ)) ∨ x9 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x9) = Bool.false) := by
  classical
  intro G hdec hadj C hleast j hj hja v hv
  let _ : DecidableEq GateOp := gateOpDecEq
  have gateAt_def : ∀ (D : Circuit) (k : ℕ), gateAt D k = D.gates.getD k ⟨GateOp.or, []⟩ :=
    fun _ _ => rfl
  have evA : ∀ l : List Bool, GateOp.eval GateOp.and l = l.all id := fun _ => rfl
  have evO : ∀ l : List Bool, GateOp.eval GateOp.or l = l.any id := fun _ => rfl
  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 26 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate), orStep 26 cs g =
      cs ++ [cs.length :: @ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
        ((g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
          (fun w => cs.getD (w - 26) [])) []] := fun _ _ => rfl
  have pairInput_def : ∀ a b : Fin 26, pairInput a b = fun w => decide (w = a ∨ w = b) :=
    fun _ _ => rfl
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stepW]; omega
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stepW w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < w.length + k then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w k hk; simp at hk
    | cons g gs ih =>
      intro w k hk
      rw [List.foldl_cons]
      cases k with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length (by simp [stepW])]
        simp only [List.getElem_cons_zero]
        have h2 : (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          exact getD_ge w i (by omega)
      | succ k =>
        have hk' : k < gs.length := by simpa using hk
        have key := ih (stepW w g) k hk'
        have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
        rw [hl] at key
        simp only [List.getElem_cons_succ]
        rw [show w.length + (k + 1) = w.length + 1 + k by omega]
        exact key
  have foldl_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl stepW w1).getD i false = true → (gs.foldl stepW w2).getD i false = true := by
    intro gs hgs
    induction gs with
    | nil => intro w1 w2 _ hle i hi; exact hle i hi
    | cons g gs ih =>
      intro w1 w2 hlen hle i hi
      rw [List.foldl_cons] at hi ⊢
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepW w1 g) (stepW w2 g)
        (by simp [stepW, hlen]) _ i hi
      intro u hu
      by_cases hlt : u < w1.length
      · have h1 : (stepW w1 g).getD u false = w1.getD u false := by
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        have h2 : (stepW w2 g).getD u false = w2.getD u false := by
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < w2.length)]
        rw [h1] at hu; rw [h2]; exact hle u hu
      · by_cases heq : u = w1.length
        · subst heq
          have h1 : (stepW w1 g).getD w1.length false = g.op.eval (g.inputs.map fun k => w1.getD k false) := by
            simp [stepW, List.getD_eq_getElem?_getD]
          have h2 : (stepW w2 g).getD w1.length false = g.op.eval (g.inputs.map fun k => w2.getD k false) := by
            rw [hlen]; simp [stepW, List.getD_eq_getElem?_getD]
          rw [h1] at hu; rw [h2]
          rcases hgs g List.mem_cons_self with hand | hor
          · rw [hand] at hu ⊢
            simp only [evA, List.all_eq_true, List.mem_map, id_eq] at hu ⊢
            rintro _ ⟨k, hk, rfl⟩
            exact hle k (hu _ ⟨k, hk, rfl⟩)
          · rw [hor] at hu ⊢
            simp only [evO, List.any_eq_true, List.mem_map, id_eq] at hu ⊢
            rcases hu with ⟨_, ⟨k, hk, rfl⟩, hwk⟩
            exact ⟨true, ⟨k, hk, hle k hwk⟩, rfl⟩
        · have h1 : (stepW w1 g).getD u false = false := getD_ge (stepW w1 g) u (by simp [stepW]; omega)
          rw [h1] at hu; cases hu
  have hAO := hleast.1
  have hfun := hleast.2.1
  have hmin := hleast.2.2
  have hmono : ∀ (x y : Fin 26 → Bool), (∀ i, x i = true → y i = true) →
      ∀ w, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
    intro x y hxy w hw
    apply foldl_mono C.gates hAO.1 (List.ofFn x) (List.ofFn y) (by simp) _ w hw
    intro i hi
    by_cases hlt : i < 26
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp [hlt] at hi ⊢
      exact hxy ⟨i, hlt⟩ hi
    · rw [getD_ge (List.ofFn x) i (by simp; omega)] at hi; cases hi
  have graphFun_pair : ∀ a b : Fin 26, graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
    intro a b
    delta graphFun
    simp only [pairInput_def, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (G.ne_of_adj hxy rfl).elim
      · exact hxy
      · exact hxy.symm
      · exact (G.ne_of_adj hxy rfl).elim
    · intro hab; exact ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
  have hnotAdj1 : ¬ G.Adj 0 1 := by
    intro h
    obtain ⟨p, l, _, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩ := (hadj 0 1).mp h
    · have := congrArg Fin.val h1; simp at this
    · have := congrArg Fin.val h0; simp at this
  have hnotAdj14 : ¬ G.Adj 0 14 := by
    intro h
    obtain ⟨p, l, hpl, ⟨h0, h14⟩ | ⟨h14, h0⟩⟩ := (hadj 0 14).mp h
    · have hp : p.val = 0 := by have := congrArg Fin.val h0; simp at this; omega
      have hl : l.val = 1 := by have := congrArg Fin.val h14; simp at this; omega
      have hp0 : p = 0 := Fin.ext hp
      have hl1 : l = 1 := Fin.ext hl
      subst hp0; subst hl1
      exact absurd hpl (by decide)
    · have := congrArg Fin.val h0; simp at this
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih]; simp [coneStep_def]; omega
  have cones_char : ∀ (gs : List Gate) (i k : ℕ),
      i ∈ (gs.foldl (coneStep 26) []).getD k [] ↔
        k < gs.length ∧ ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs,
          26 ≤ w ∧ w < 26 + k ∧
          (i = w - 26 ∨ i ∈ (gs.foldl (coneStep 26) []).getD (w - 26) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i k; simp
    | append_singleton gs g ih =>
      intro i k
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 26) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ t, t < gs.length →
          (coneStep 26 (gs.foldl (coneStep 26) []) g).getD t [] =
            (gs.foldl (coneStep 26) []).getD t [] := by
        intro t ht
        simp only [coneStep_def, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy k gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
        rw [key k h, ih i k, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 26) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 26) (by omega)] at h3; exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep 26 (gs.foldl (coneStep 26) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + gs.length))).flatMap
              (fun w => (w - 26) :: (gs.foldl (coneStep 26) []).getD (w - 26) []) := by
          simp only [coneStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]; simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - 26) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 26) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep 26 (gs.foldl (coneStep 26) []) g).getD k [] = [] := by
          simp only [coneStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]; rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have inCone_iff : ∀ i k : ℕ, InCone 26 C i k ↔
      k < C.gates.length ∧ ∃ t, t < k ∧ 26 + t ∈ (gateAt C k).inputs ∧
        (i = t ∨ InCone 26 C i t) := by
    intro i k
    have h := cones_char C.gates i k
    delta InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - 26, by omega, ?_, h3⟩
      rw [show 26 + (w - 26) = w by omega]; exact hw
    · rintro ⟨h0, t, ht, hw, h3⟩
      refine ⟨h0, 26 + t, hw, by omega, by omega, ?_⟩
      rw [show 26 + t - 26 = t by omega]; exact h3
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih]; simp [orStep_def]; omega
  have orSets_char : ∀ (gs : List Gate) (i k : ℕ),
      i ∈ (gs.foldl (orStep 26) []).getD k [] ↔
        k < gs.length ∧ (i = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, 26 ≤ w ∧ w < 26 + k ∧
            i ∈ (gs.foldl (orStep 26) []).getD (w - 26) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i k; simp
    | append_singleton gs g ih =>
      intro i k
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 26) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ t, t < gs.length →
          (orStep 26 (gs.foldl (orStep 26) []) g).getD t [] =
            (gs.foldl (orStep 26) []).getD t [] := by
        intro t ht
        simp only [orStep_def, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy k gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
        rw [key k h, ih i k, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - 26) (by omega)]; exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - 26) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep 26 (gs.foldl (orStep 26) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + gs.length))).flatMap
                (fun w => (gs.foldl (orStep 26) []).getD (w - 26) []) := by
            simp only [orStep_def, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]; simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - 26) (by omega)]; exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - 26) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep 26 (gs.foldl (orStep 26) []) g).getD gs.length [] = [gs.length] := by
            simp only [orStep_def, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]; simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep 26 (gs.foldl (orStep 26) []) g).getD k [] = [] := by
          simp only [orStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]; rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have orReaches_iff : ∀ k g : ℕ, OrReaches 26 C (26 + k) g ↔
      k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < 26 + k ∧ OrReaches 26 C i g)) := by
    intro k g
    have h := orSets_char C.gates g k
    delta OrReaches orSets gateAt
    rw [show 26 + k - 26 = k by omega, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
  have orReaches_val : ∀ (x : Fin 26 → Bool) (w g : ℕ), OrReaches 26 C w g →
      gateVal 26 C g x = true → (C.wires (List.ofFn x)).getD w false = true := by
    intro x w g
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hr hg
      have hge : 26 ≤ w := hr.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp hr
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hri⟩
      · exact hg
      · have hvi := ih i hlt hri hg
        have hval := foldl_getD_gate C.gates (List.ofFn x) k hk
        rw [List.length_ofFn] at hval
        change (C.gates.foldl stepW (List.ofFn x)).getD (26 + k) false = true
        rw [hval]
        have hg_eq : gateAt C k = C.gates[k] := by
          simp [gateAt_def, List.getD_eq_getElem?_getD, hk]
        rw [← hg_eq, hop]
        simp only [evO, List.any_eq_true, List.mem_map, id_eq]
        have hvi' : (C.gates.foldl stepW (List.ofFn x)).getD i false = true := hvi
        exact ⟨true, ⟨i, hi, by rw [ite_eq_left hlt]; exact hvi'⟩, rfl⟩
  have notOr_and_inCone : ∀ (k : ℕ), k < C.gates.length →
      (∀ m < C.gates.length, (gateAt C m).op = GateOp.and → ¬ InCone 26 C j m) →
      (k = j ∨ InCone 26 C j k) → OrReaches 26 C (26 + k) j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hno hjk
      rcases hjk with hkeq | hcone
      · rw [hkeq]; exact (orReaches_iff j j).mpr ⟨hj, Or.inl rfl⟩
      · obtain ⟨_, t, htk, htin, hjt⟩ := (inCone_iff j k).mp hcone
        have hkop : (gateAt C k).op = GateOp.or := by
          have hg_eq : gateAt C k = C.gates[k] := by
            simp [gateAt_def, List.getD_eq_getElem?_getD, hk]
          rcases hAO.1 _ (hg_eq ▸ List.getElem_mem hk) with ha | ho
          · exact (hno k hk ha hcone).elim
          · exact ho
        exact (orReaches_iff k j).mpr ⟨hk, Or.inr ⟨hkop, 26 + t, htin, by omega,
          ih t htk (by omega) hno (hjt.imp Eq.symm id)⟩⟩
  have hasAboveAnd : ¬ OrReaches 26 C C.output j →
      ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ InCone 26 C j k := by
    intro hnor
    by_contra hno0
    have hno : ∀ m < C.gates.length, (gateAt C m).op = GateOp.and → ¬ InCone 26 C j m :=
      fun m hm ha hc => hno0 ⟨m, hm, ha, hc⟩
    have hnotout : ∀ m, C.output = 26 + m → m < C.gates.length → m ≠ j ∧ ¬ InCone 26 C j m := by
      intro m hm hmlt
      constructor
      · intro heq; rw [heq] at hm; exact hnor (hm ▸ (orReaches_iff j j).mpr ⟨hj, Or.inl rfl⟩)
      · intro hc; exact hnor (hm ▸ notOr_and_inCone m hmlt hno (Or.inr hc))
    let r : ℕ → ℕ := fun w => if w < 26 + j then w else if w = 26 + j then 0 else w - 1
    let C' : Circuit := ⟨(C.gates.eraseIdx j).map fun g => ⟨g.op, g.inputs.map r⟩, r C.output⟩
    have hC'len : C'.gates.length = C.gates.length - 1 := by
      simp [C', List.length_eraseIdx_of_lt hj]
    have hC'AO : IsAO2 26 C' := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [C', List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
      · intro k hk w hw
        have hk' : k < (C.gates.eraseIdx j).length := by
          simpa [C'] using hk
        have hgk : gateAt C' k = ⟨((C.gates.eraseIdx j)[k]).op, ((C.gates.eraseIdx j)[k]).inputs.map r⟩ := by
          simp [gateAt_def, C', List.getD_eq_getElem?_getD, hk']
        rw [hgk] at hw
        simp only [List.mem_map] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        by_cases hkj : k < j
        · have heq : (C.gates.eraseIdx j)[k] = C.gates[k] := List.getElem_eraseIdx_of_lt hk' hkj
          rw [heq] at hu
          have hg_eq : gateAt C k = C.gates[k] := by
            simp [gateAt_def, List.getD_eq_getElem?_getD, show k < C.gates.length by omega]
          have hult : u < 26 + k := hAO.2.1 k (by omega) u (hg_eq ▸ hu)
          simp only [r, ite_eq_left (by omega : u < 26 + j)]
          omega
        · have hkj' : j ≤ k := by omega
          have heq : (C.gates.eraseIdx j)[k] = C.gates[k + 1] := List.getElem_eraseIdx_of_ge hk' hkj'
          rw [heq] at hu
          have hk1 : k + 1 < C.gates.length := by
            rw [List.length_eraseIdx_of_lt hj] at hk'; omega
          have hg_eq : gateAt C (k + 1) = C.gates[k + 1] := by
            simp [gateAt_def, List.getD_eq_getElem?_getD, hk1]
          have hult : u < 26 + (k + 1) := hAO.2.1 (k + 1) hk1 u (hg_eq ▸ hu)
          dsimp only [r]
          split_ifs <;> omega
      · intro g hg
        simp only [C', List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        simp [hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)]
    have hwire_eq : ∀ (x : Fin 26 → Bool) (w : ℕ),
        (∀ m, w = 26 + m → m < C.gates.length → m ≠ j ∧ ¬ InCone 26 C j m) →
        (C'.wires (List.ofFn x)).getD (r w) false = (C.wires (List.ofFn x)).getD w false := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hsafe
        by_cases hlt : w < 26
        · have hrw : r w = w := by simp [r, show w < 26 + j by omega]
          rw [hrw]
          change (C'.gates.foldl stepW (List.ofFn x)).getD w false =
            (C.gates.foldl stepW (List.ofFn x)).getD w false
          rw [foldl_getD_lt _ _ w (by simp; omega), foldl_getD_lt _ _ w (by simp; omega)]
        · by_cases hin : w < 26 + C.gates.length
          · obtain ⟨m, rfl⟩ : ∃ m, w = 26 + m := ⟨w - 26, by omega⟩
            have hm : m < C.gates.length := by omega
            obtain ⟨hmnej, hmnic⟩ := hsafe m rfl hm
            have hCval := foldl_getD_gate C.gates (List.ofFn x) m hm
            rw [List.length_ofFn] at hCval
            have hm_inputs : ∀ u ∈ (C.gates[m]).inputs, u < 26 + m ∧
                ∀ t, u = 26 + t → t < C.gates.length → t ≠ j ∧ ¬ InCone 26 C j t := by
              intro u hu
              have hg_eq : gateAt C m = C.gates[m] := by
                simp [gateAt_def, List.getD_eq_getElem?_getD, hm]
              have hult : u < 26 + m := hAO.2.1 m hm u (hg_eq ▸ hu)
              refine ⟨hult, fun t hut ht => ⟨?_, ?_⟩⟩
              · intro heq; rw [heq] at hut; apply hmnic
                exact (inCone_iff j m).mpr ⟨hm, j, by omega, hg_eq ▸ (hut ▸ hu), Or.inl rfl⟩
              · intro hc; apply hmnic
                exact (inCone_iff j m).mpr ⟨hm, t, by omega, hg_eq ▸ (hut ▸ hu), Or.inr hc⟩
            by_cases hmj : m < j
            · have hrm : r (26 + m) = 26 + m := by simp [r, hmj]
              have hm' : m < C'.gates.length := by rw [hC'len]; omega
              have hC'val := foldl_getD_gate C'.gates (List.ofFn x) m hm'
              rw [List.length_ofFn] at hC'val
              change (C'.gates.foldl stepW (List.ofFn x)).getD (r (26 + m)) false =
                (C.gates.foldl stepW (List.ofFn x)).getD (26 + m) false
              rw [hrm, hC'val, hCval]
              have hgm : C'.gates[m] = ⟨(C.gates[m]).op, (C.gates[m]).inputs.map r⟩ := by
                have hm'' : m < (C.gates.eraseIdx j).length := by
                  rw [List.length_eraseIdx_of_lt hj]; omega
                simp [C', List.getElem_eraseIdx_of_lt hm'' hmj]
              rw [hgm, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              obtain ⟨hult, husafe⟩ := hm_inputs u hu
              have hru : r u < 26 + m := by dsimp only [r]; split_ifs <;> omega
              simp only [Function.comp_apply, ite_eq_left hru, ite_eq_left hult]
              exact ih u hult husafe
            · have hmj' : j < m := by omega
              have hrm : r (26 + m) = 26 + (m - 1) := by
                dsimp only [r]
                rw [ite_eq_right (by omega : ¬ 26 + m < 26 + j), ite_eq_right (by omega : 26 + m ≠ 26 + j)]
                omega
              have hm' : m - 1 < C'.gates.length := by rw [hC'len]; omega
              have hC'val := foldl_getD_gate C'.gates (List.ofFn x) (m - 1) hm'
              rw [List.length_ofFn] at hC'val
              change (C'.gates.foldl stepW (List.ofFn x)).getD (r (26 + m)) false =
                (C.gates.foldl stepW (List.ofFn x)).getD (26 + m) false
              rw [hrm, hC'val, hCval]
              have hgm : C'.gates[m - 1] = ⟨(C.gates[m]).op, (C.gates[m]).inputs.map r⟩ := by
                have hm'' : m - 1 < (C.gates.eraseIdx j).length := by
                  rw [List.length_eraseIdx_of_lt hj]; omega
                have hge' : j ≤ m - 1 := by omega
                have heq := List.getElem_eraseIdx_of_ge hm'' hge'
                simp only [C', List.getElem_map]
                rw [heq]
                have hm1 : m - 1 + 1 = m := by omega
                simp [hm1]
              rw [hgm, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              obtain ⟨hult, husafe⟩ := hm_inputs u hu
              have hune : u ≠ 26 + j := by
                intro heq; exact (husafe j heq hj).1 rfl
              have hru : r u < 26 + (m - 1) := by dsimp only [r]; split_ifs <;> omega
              simp only [Function.comp_apply, ite_eq_left hru, ite_eq_left hult]
              exact ih u hult husafe
          · have hge1 : (C.wires (List.ofFn x)).length ≤ w := by
              change (C.gates.foldl stepW (List.ofFn x)).length ≤ w
              rw [foldl_len, List.length_ofFn]; omega
            have hge2 : (C'.wires (List.ofFn x)).length ≤ r w := by
              change (C'.gates.foldl stepW (List.ofFn x)).length ≤ r w
              rw [foldl_len, List.length_ofFn, hC'len]
              dsimp only [r]; split_ifs <;> omega
            rw [getD_ge _ _ hge2, getD_ge _ _ hge1]
    have hC'fun : circuitFun 26 C' = graphFun G ∅ := by
      rw [← hfun]
      funext x
      exact hwire_eq x C.output hnotout
    have hle := hmin C' hC'AO hC'fun
    change C.gates.length ≤ C'.gates.length at hle
    omega
  have checkPair : ∀ (w : Fin 26), ¬ G.Adj 0 w →
      (∀ (hjunk : j ∈ junk G C), ¬ OrReaches 26 C C.output j →
        (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ InCone 26 C j k) →
        gateVal 26 C j (pairInput 0 w) = false) →
      gateVal 26 C j (pairInput 0 w) = false := by
    intro w hna hcase
    cases hval : gateVal 26 C j (pairInput 0 w) with
    | false => rfl
    | true =>
      exfalso
      have hgf : graphFun G ∅ (pairInput 0 w) = false := by
        cases h : graphFun G ∅ (pairInput 0 w)
        · rfl
        · exact (hna ((graphFun_pair 0 w).mp h)).elim
      have hjunk : j ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hja, hj, ⟨pairInput 0 w, hval, hgf⟩⟩
      have hnor : ¬ OrReaches 26 C C.output j := by
        intro hr
        have h1 := orReaches_val (pairInput 0 w) C.output j hr hval
        have h2 : (C.wires (List.ofFn (pairInput 0 w))).getD C.output false = graphFun G ∅ (pairInput 0 w) :=
          congrFun hfun (pairInput 0 w)
        rw [h2, hgf] at h1
        cases h1
      have hres := hcase hjunk hnor (hasAboveAnd hnor)
      rw [hval] at hres
      cases hres
  have h1 : gateVal 26 C j (pairInput 0 1) = false :=
    checkPair 1 hnotAdj1 (fun hjunk hnor hk => sameSide G hadj C hleast j hjunk hnor hk)
  rcases hv with rfl | rfl | rfl
  · cases h0 : gateVal 26 C j (pairInput 0 0) with
    | false => rfl
    | true =>
      have hsub : ∀ i : Fin 26, pairInput (0 : Fin 26) 0 i = true → pairInput (0 : Fin 26) 1 i = true := by
        intro i hi
        simp only [pairInput_def, decide_eq_true_eq] at hi ⊢
        rcases hi with rfl | rfl <;> exact Or.inl rfl
      have h1t : gateVal 26 C j (pairInput 0 1) = true :=
        hmono (pairInput 0 0) (pairInput 0 1) hsub (26 + j) h0
      rw [h1] at h1t
      cases h1t
  · exact h1
  · exact checkPair 14 hnotAdj14 (fun hjunk hnor hk => nonIncident G hadj C hleast j hjunk hnor hk)
