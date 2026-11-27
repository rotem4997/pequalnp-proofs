import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5202_701
    (hAA : let P := PEqualNP.HeptadCover.singerLines3;
      let X := fun T L : Finset (Fin 13) =>
        (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ List.ofFn fun q : Fin 13 => decide (q ∈ L);
      let W := fun (C : PEqualNP.CircuitLowerBounds.Circuit) r x => (C.wires x).getD r false;
      let G := PEqualNP.MetaComplexity.NestedCover.gateAt;
      let A := PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        26 ≤ a → a < 26 + C.size → 26 ≤ b → b < 26 + C.size → a ≠ b →
        (G C (a - 26)).op = A → (G C (b - 26)).op = A →
        (∀ p l, p ∈ P l → W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true) →
        (∀ S, PEqualNP.HeptadCover.IsQuadrangle P S →
          W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧
          W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false) →
        (∃ p l, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) →
        (∃ p l, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) →
        (∃ T : Finset ℕ, T.card = 3 ∧ ∀ j ∈ T, j < C.size ∧
          (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A) →
        63 ≤ C.size)
    (hAO : let P := PEqualNP.HeptadCover.singerLines3;
      let X := fun T L : Finset (Fin 13) =>
        (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ List.ofFn fun q : Fin 13 => decide (q ∈ L);
      let W := fun (C : PEqualNP.CircuitLowerBounds.Circuit) r x => (C.wires x).getD r false;
      let G := PEqualNP.MetaComplexity.NestedCover.gateAt;
      let A := PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        26 ≤ a → a < 26 + C.size → 26 ≤ b → b < 26 + C.size → a ≠ b →
        (G C (a - 26)).op = A → (G C (b - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ p l, p ∈ P l → W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true) →
        (∀ S, PEqualNP.HeptadCover.IsQuadrangle P S →
          W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧
          W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false) →
        (∃ p l, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) →
        (∃ p l, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) →
        (∃ T : Finset ℕ, T.card = 3 ∧ ∀ j ∈ T, j < C.size ∧
          (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A) →
        63 ≤ C.size)
    (hOO : let P := PEqualNP.HeptadCover.singerLines3;
      let X := fun T L : Finset (Fin 13) =>
        (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ List.ofFn fun q : Fin 13 => decide (q ∈ L);
      let W := fun (C : PEqualNP.CircuitLowerBounds.Circuit) r x => (C.wires x).getD r false;
      let G := PEqualNP.MetaComplexity.NestedCover.gateAt;
      let A := PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        26 ≤ a → a < 26 + C.size → 26 ≤ b → b < 26 + C.size → a ≠ b →
        (G C (a - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (G C (b - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ p l, p ∈ P l → W C a (X {p} {l}) = true ∨ W C b (X {p} {l}) = true) →
        (∀ S, PEqualNP.HeptadCover.IsQuadrangle P S →
          W C a (X S (PEqualNP.HeptadCover.missLines P S)) = false ∧
          W C b (X S (PEqualNP.HeptadCover.missLines P S)) = false) →
        (∃ p l, p ∈ P l ∧ W C a (X {p} {l}) = true ∧ W C b (X {p} {l}) = false) →
        (∃ p l, p ∈ P l ∧ W C b (X {p} {l}) = true ∧ W C a (X {p} {l}) = false) →
        (∃ T : Finset ℕ, T.card = 3 ∧ ∀ j ∈ T, j < C.size ∧
          (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A) →
        63 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∃ x18 ∈ Finset.range x7.size, ∃ x19 ∈ Finset.range x7.size, ∃ x20 ∈ Finset.range x7.size, x18 ≠ x19 ∧ x18 ≠ x20 ∧ x19 ≠ x20 ∧ x6 x7 x18 ∧ x6 x7 x19 ∧ x6 x7 x20) → (63 : ℕ) ≤ x7.size := by
  intro P X W G A aa C a b hm hr ha hb hpos hneg hea heb h3
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
      simp only [List.foldl_cons, ht, List.append_assoc, List.singleton_append]
  have hget : ∀ (w : ℕ) (S L : Finset (Fin 13)), w < 26 → W C w (X S L) = (X S L).getD w false := by
    intro w S L hw
    obtain ⟨t, ht⟩ := hpre C.gates (X S L)
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (X S L)).getD w false = _
    rw [ht, List.getD_append _ _ _ _ (by simp [X]; omega)]
  have hQp : ∀ p : Fin 13, PEqualNP.HeptadCover.IsQuadrangle P ({p, p + 1, p + 2, p + 5} : Finset (Fin 13)) := by
    decide
  have hQl : ∀ l : Fin 13, PEqualNP.HeptadCover.IsQuadrangle P ({l - 3, l - 2, l - 1, l + 2} : Finset (Fin 13)) ∧
      l ∈ PEqualNP.HeptadCover.missLines P ({l - 3, l - 2, l - 1, l + 2} : Finset (Fin 13)) := by
    decide
  have hge26 : ∀ w, (∀ S, PEqualNP.HeptadCover.IsQuadrangle P S → W C w (X S (PEqualNP.HeptadCover.missLines P S)) = false) → 26 ≤ w := by
    intro w hw
    by_contra hlt
    push_neg at hlt
    by_cases hp : w < 13
    · let p : Fin 13 := ⟨w, hp⟩
      let S : Finset (Fin 13) := {p, p + 1, p + 2, p + 5}
      have h0 := hw S (hQp p)
      rw [hget w S _ hlt] at h0
      have h1 : (X S (PEqualNP.HeptadCover.missLines P S)).getD w false = true := by
        simp only [X]
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        rw [List.getElem_ofFn]
        exact decide_eq_true (by simp [S, p])
      rw [h1] at h0
      exact Bool.noConfusion h0
    · let l : Fin 13 := ⟨w - 13, by omega⟩
      let S : Finset (Fin 13) := {l - 3, l - 2, l - 1, l + 2}
      have h0 := hw S (hQl l).1
      rw [hget w S _ hlt] at h0
      have h1 : (X S (PEqualNP.HeptadCover.missLines P S)).getD w false = true := by
        simp only [X]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        rw [List.getElem_ofFn]
        have hidx : (⟨w - (List.ofFn fun x4 : Fin 13 => decide (x4 ∈ S)).length, by simp; omega⟩ : Fin 13) = l := by
          ext; simp [l]
        rw [hidx]
        exact decide_eq_true (hQl l).2
      rw [h1] at h0
      exact Bool.noConfusion h0
  have ha26 : 26 ≤ a := hge26 a (fun S hS => (hneg S hS).1)
  have hb26 : 26 ≤ b := hge26 b (fun S hS => (hneg S hS).2)
  have hab : a ≠ b := by
    intro heq
    subst heq
    obtain ⟨p, l, _, h1, h2⟩ := hea
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hcard : ∃ T : Finset ℕ, T.card = 3 ∧ ∀ j ∈ T, j < C.size ∧
      (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A := by
    obtain ⟨j1, hj1, j2, hj2, j3, hj3, h12, h13, h23, ha1, ha2, ha3⟩ := h3
    refine ⟨{j1, j2, j3}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [h12, h13])]
      rw [Finset.card_insert_of_notMem (by simp [h23])]
      simp
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Finset.mem_range.mp hj1, ha1⟩
      · exact ⟨Finset.mem_range.mp hj2, ha2⟩
      · exact ⟨Finset.mem_range.mp hj3, ha3⟩
  have hop_a : (G C (a - 26)).op = A ∨ (G C (a - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    have hidx : a - 26 < C.gates.length := by unfold PEqualNP.CircuitLowerBounds.Circuit.size at ha; omega
    have hmem := (hm _ (List.getElem_mem hidx)).1
    have hg : G C (a - 26) = C.gates[a - 26] := by
      unfold G PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hidx]
    rw [hg]
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, A] using hmem
  have hop_b : (G C (b - 26)).op = A ∨ (G C (b - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    have hidx : b - 26 < C.gates.length := by unfold PEqualNP.CircuitLowerBounds.Circuit.size at hb; omega
    have hmem := (hm _ (List.getElem_mem hidx)).1
    have hg : G C (b - 26) = C.gates[b - 26] := by
      unfold G PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hidx]
    rw [hg]
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, A] using hmem
  rcases hop_a with ha_op | ha_op <;> rcases hop_b with hb_op | hb_op
  · exact hAA C a b hm hr ha26 ha hb26 hb hab ha_op hb_op hpos hneg hea heb hcard
  · exact hAO C a b hm hr ha26 ha hb26 hb hab ha_op hb_op hpos hneg hea heb hcard
  · exact hAO C b a hm hr hb26 hb ha26 ha (Ne.symm hab) hb_op ha_op
      (fun p l hpl => (hpos p l hpl).symm)
      (fun S hS => ⟨(hneg S hS).2, (hneg S hS).1⟩) heb hea hcard
  · exact hOO C a b hm hr ha26 ha hb26 hb hab ha_op hb_op hpos hneg hea heb hcard
