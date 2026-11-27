import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4041_2
    (hClean : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      ¬ PEqualNP.TopForm.IsAO2 42 C →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42,
          (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 42 D ∧ D.size + 1 ≤ C.size ∧
        ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hSize123 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 42 D → D.size ≤ 123 →
      ∃ x : Fin 42 → Bool, ¬(D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42,
          (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true))
    (hAO2One : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 42),
      PEqualNP.TopForm.IsAO2 42 C → C.size ≤ 124 →
      v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) →
      (∃ j g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = true) →
      ∃ x : Fin 42 → Bool, ¬(C.eval (List.ofFn x) = true ↔
        ∃ u w : Fin 42,
          (u.val < 21 ∧ 21 ≤ w.val ∧ (w.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x w = true))
    (hAO2Two : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin 42)),
      PEqualNP.TopForm.IsAO2 42 C → C.size ≤ 124 → Y.card = 2 →
      (∀ v ∈ Y, v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
      (∀ v : Fin 42, v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) →
        ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = false) →
      (∃ j g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn fun i : Fin 42 => decide (i ∈ Y))).getD (42 + j) false = true) →
      ∃ x : Fin 42 → Bool, ¬(C.eval (List.ofFn x) = true ↔
        ∃ u w : Fin 42,
          (u.val < 21 ∧ 21 ≤ w.val ∧ (w.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x w = true)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by
  intro C Y hmono hsize hcard hY hfire
  by_cases hAO : PEqualNP.TopForm.IsAO2 42 C
  · by_cases hzero : Y.card = 0
    · exfalso
      have hYemp : Y = ∅ := Finset.card_eq_zero.mp hzero
      subst hYemp
      obtain ⟨j, g, _, _, htrue⟩ := hfire
      have hallFalse : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
          (∀ h ∈ gs, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ h.inputs.length = 2) →
          ∀ w : List Bool, (∀ b ∈ w, b = false) →
          ∀ b ∈ gs.foldl (fun acc h => acc ++ [h.op.eval (h.inputs.map fun i => acc.getD i false)]) w, b = false := by
        intro gs
        induction gs with
        | nil =>
          intro _ w hw b hb
          exact hw b hb
        | cons h gs ih =>
          intro hgs w hw b hb
          refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem h hg'))
            (w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) ?_ b hb
          intro b' hb'
          rw [List.mem_append, List.mem_singleton] at hb'
          rcases hb' with hbw | rfl
          · exact hw b' hbw
          · obtain ⟨hop, hlen⟩ := hgs h (List.mem_cons_self ..)
            have hgetFalse : ∀ i, w.getD i false = false := by
              intro i
              by_cases hi : i < w.length
              · rw [List.getD_eq_getElem _ _ hi]
                exact hw _ (List.getElem_mem hi)
              · exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)
            rcases hinp : h.inputs with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
            · simp [hinp] at hlen
            · simp [hinp] at hlen
            · simp only [List.map_cons, List.map_nil, hgetFalse]
              rcases hop with hop | hop <;> (rw [hop]; rfl)
            · simp [hinp] at hlen
      have hinit : ∀ b ∈ List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42)))), b = false := by
        intro b hb
        rw [List.mem_ofFn] at hb
        obtain ⟨_, rfl⟩ := hb
        simp
      have hwires : ∀ b ∈ C.wires (List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42))))), b = false :=
        hallFalse C.gates (fun h hh => ⟨hAO.1 h hh, hAO.2.2 h hh⟩) _ hinit
      have hgetF : (C.wires (List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42)))))).getD (42 + j) false = false := by
        by_cases hi : 42 + j < (C.wires (List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42)))))).length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hwires _ (List.getElem_mem hi)
        · exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)
      rw [hgetF] at htrue
      exact Bool.false_ne_true htrue
    · by_cases hone : Y.card = 1
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
        have hv : v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) :=
          hY v (Finset.mem_singleton_self v)
        have hfire' : ∃ j g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = true := by
          simpa only [Finset.mem_singleton] using hfire
        exact hAO2One C v hAO hsize hv hfire'
      · have htwo : Y.card = 2 := by omega
        by_cases hsing : ∃ v : Fin 42, v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) ∧
            ∃ j g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = true
        · obtain ⟨v, hv, hfv⟩ := hsing
          exact hAO2One C v hAO hsize hv hfv
        · push Not at hsing
          have hclean1 : ∀ v : Fin 42, v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) →
              ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = false := by
            intro v hv j g hg hop
            exact Bool.eq_false_iff.mpr (hsing v hv j g hg hop)
          exact hAO2Two C Y hAO hsize htwo hY hclean1 hfire
  · by_contra hcomp
    push Not at hcomp
    obtain ⟨D, hDAO, hDsize, hDeval⟩ := hClean C hmono hAO hcomp
    obtain ⟨x, hx⟩ := hSize123 D hDAO (by omega)
    exact hx (by rw [hDeval x]; exact hcomp x)
