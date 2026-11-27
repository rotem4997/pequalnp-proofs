import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5270_17
    (h_le26 :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → x4.size ≤ (26 : ℕ) → ¬x3 x4 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)})
    (h_27_and :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x2 x4 → x4.size = (27 : ℕ) → ¬x3 x4 → x4.gates[k]? = Option.some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (2 : ℕ) ≤ List.count ((14 : ℕ) + k) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)})
    (h_27_or_leaf :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x2 x4 → x4.size = (27 : ℕ) → ¬x3 x4 → x4.gates[k]? = Option.some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (w : ℕ), w ∈ g.inputs → w < (14 : ℕ)) → (2 : ℕ) ≤ List.count ((14 : ℕ) + k) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)})
    (h_27_or_deep :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x2 x4 → x4.size = (27 : ℕ) → ¬x3 x4 → x4.gates[k]? = Option.some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ (w : ℕ), w ∈ g.inputs ∧ (14 : ℕ) ≤ w) → (2 : ℕ) ≤ List.count ((14 : ℕ) + k) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)} := by
  intro x1 x2 x3 x4 hx2 hnx3 hd0 hd7
  have hsize : x4.size ≤ 27 := hx2.1
  by_cases h26 : x4.size ≤ 26
  · exact h_le26 x4 hx2 h26 hnx3 hd0 hd7
  · have h27 : x4.size = 27 := by omega
    have hnot_le1 : ¬ ∀ w : ℕ, List.count w (List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) ≤ 1 := by
      intro hall
      exact hnx3 (List.nodup_iff_count_le_one.mpr hall)
    obtain ⟨w, hwgt⟩ := Classical.not_forall.mp hnot_le1
    have hw2 : 2 ≤ List.count w (List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) := by omega
    have hwmem : w ∈ List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) :=
      List.count_pos_iff.mp (by omega)
    have hw14 : 14 ≤ w := of_decide_eq_true (List.mem_filter.mp hwmem).2
    have hwcnt : 2 ≤ List.count w (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) :=
      le_trans hw2 (List.Sublist.count_le w List.filter_sublist)
    have hflat_pos : 0 < List.count w (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) := by
      rw [List.count_cons] at hwcnt
      split at hwcnt <;> omega
    have hflat_mem : w ∈ List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates :=
      List.count_pos_iff.mp hflat_pos
    obtain ⟨g', hg'mem, hwg'⟩ := List.mem_flatMap.mp hflat_mem
    obtain ⟨j, hjlt, rfl⟩ := List.getElem_of_mem hg'mem
    obtain ⟨_, a, b, hab, _, ha, hb⟩ := hx2.2.1 j x4.gates[j] (List.getElem?_eq_getElem hjlt)
    rw [hab] at hwg'
    have hwlt : w < 14 + x4.gates.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwg'
      rcases hwg' with rfl | rfl <;> omega
    let k := w - 14
    have hklt : k < x4.gates.length := by omega
    have hwk : 14 + k = w := by omega
    have hgk : x4.gates[k]? = Option.some x4.gates[k] := List.getElem?_eq_getElem hklt
    have hcntk : 2 ≤ List.count (14 + k) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) := by
      rw [hwk]; exact hwcnt
    rcases (hx2.2.1 k x4.gates[k] hgk).1 with hand | hor
    · exact h_27_and x4 k x4.gates[k] hx2 h27 hnx3 hgk hand hcntk hd0 hd7
    · by_cases hleaf : ∀ u : ℕ, u ∈ x4.gates[k].inputs → u < 14
      · exact h_27_or_leaf x4 k x4.gates[k] hx2 h27 hnx3 hgk hor hleaf hcntk hd0 hd7
      · obtain ⟨u, hu⟩ := Classical.not_forall.mp hleaf
        obtain ⟨humem, huge⟩ := Classical.not_imp.mp hu
        exact h_27_or_deep x4 k x4.gates[k] hx2 h27 hnx3 hgk hor ⟨u, humem, by omega⟩ hcntk hd0 hd7
