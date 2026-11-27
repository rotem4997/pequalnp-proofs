import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3791_556
    (majorAnd :
      ∀ (C : Circuit) (w1 w2 : ℕ), Monotone2 C → ReadsBack 26 C →
        26 ≤ w1 ∧ w1 < 26 + C.size ∧ 26 ≤ w2 ∧ w2 < 26 + C.size ∧ w1 ≠ w2 →
        ¬ OrReaches 26 C w2 (w1 - 26) ∧ ¬ OrReaches 26 C w1 (w2 - 26) →
        (gateAt C (w1 - 26)).op = GateOp.and →
        let D : Finset (Fin 13) := {0, 1, 3, 9}
        let pair : Fin 13 → Fin 13 → List Bool := fun p l =>
          (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
        let arc : Finset (Fin 13) → List Bool := fun S =>
          (List.ofFn fun i : Fin 13 => decide (i ∈ S)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ S, p - i ∉ D)
        let ev : ℕ → List Bool → Bool := fun w x => (C.wires x).getD w false
        (∀ p l : Fin 13, p - l ∈ D → ev w1 (pair p l) = true ∨ ev w2 (pair p l) = true) →
        (∀ S : Finset (Fin 13), S.card = 4 → (∀ l : Fin 13, (S.filter fun p => p - l ∈ D).card ≤ 2) →
          ev w1 (arc S) = false ∧ ev w2 (arc S) = false) →
        26 ≤ Fintype.card { pl : Fin 13 × Fin 13 // pl.1 - pl.2 ∈ D ∧ ev w1 (pair pl.1 pl.2) = true } →
        (∃ p l : Fin 13, p - l ∈ D ∧ ev w2 (pair p l) = true ∧ ev w1 (pair p l) = false) →
        63 ≤ C.size)
    (majorOr :
      ∀ (C : Circuit) (w1 w2 : ℕ), Monotone2 C → ReadsBack 26 C →
        26 ≤ w1 ∧ w1 < 26 + C.size ∧ 26 ≤ w2 ∧ w2 < 26 + C.size ∧ w1 ≠ w2 →
        ¬ OrReaches 26 C w2 (w1 - 26) ∧ ¬ OrReaches 26 C w1 (w2 - 26) →
        (gateAt C (w1 - 26)).op = GateOp.or →
        let D : Finset (Fin 13) := {0, 1, 3, 9}
        let pair : Fin 13 → Fin 13 → List Bool := fun p l =>
          (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
        let arc : Finset (Fin 13) → List Bool := fun S =>
          (List.ofFn fun i : Fin 13 => decide (i ∈ S)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ S, p - i ∉ D)
        let ev : ℕ → List Bool → Bool := fun w x => (C.wires x).getD w false
        (∀ p l : Fin 13, p - l ∈ D → ev w1 (pair p l) = true ∨ ev w2 (pair p l) = true) →
        (∀ S : Finset (Fin 13), S.card = 4 → (∀ l : Fin 13, (S.filter fun p => p - l ∈ D).card ≤ 2) →
          ev w1 (arc S) = false ∧ ev w2 (arc S) = false) →
        26 ≤ Fintype.card { pl : Fin 13 × Fin 13 // pl.1 - pl.2 ∈ D ∧ ev w1 (pair pl.1 pl.2) = true } →
        (∃ p l : Fin 13, p - l ∈ D ∧ ev w2 (pair p l) = true ∧ ev w1 (pair p l) = false) →
        63 ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size) := by
  classical
  dsimp only at majorAnd majorOr ⊢
  intro C w1 w2 hmono hrb hw1lt hw2lt hnor1 hnor2 hcov harc hex1 hex2
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let pair : Fin 13 → Fin 13 → List Bool := fun p l =>
    (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
  let arc : Finset (Fin 13) → List Bool := fun S =>
    (List.ofFn fun i : Fin 13 => decide (i ∈ S)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ S, p - i ∉ D)
  let ev : ℕ → List Bool → Bool := fun w x => (C.wires x).getD w false
  let stepWire : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) i hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  have ev_input : ∀ (x : List Bool) (hx : x.length = 26) (w : ℕ), w < 26 →
      ev w x = x.getD w false := by
    intro x hx w hw
    exact foldl_getD_lt C.gates x w (by omega)
  have arc_len : ∀ S : Finset (Fin 13), (arc S).length = 26 := by
    intro S; simp [arc]
  have pair_len : ∀ p l : Fin 13, (pair p l).length = 26 := by
    intro p l; simp [pair]
  have pointArc : ∀ p : Fin 13,
      let S : Finset (Fin 13) := {p, p + 1, p + 2, p + 5}
      S.card = 4 ∧ (∀ l : Fin 13, (S.filter fun q => q - l ∈ D).card ≤ 2) ∧ p ∈ S := by
    decide +kernel
  have lineArc : ∀ l : Fin 13,
      let S : Finset (Fin 13) := {l + 2, l + 4, l + 5, l + 6}
      S.card = 4 ∧ (∀ k : Fin 13, (S.filter fun q => q - k ∈ D).card ≤ 2) ∧ ∀ q ∈ S, q - l ∉ D := by
    decide +kernel
  have wire_ge_26 : ∀ w : ℕ,
      (∀ S : Finset (Fin 13), S.card = 4 → (∀ l : Fin 13, (S.filter fun p => p - l ∈ D).card ≤ 2) →
        ev w (arc S) = false) → 26 ≤ w := by
    intro w hfalse
    by_contra hlt
    by_cases h13 : w < 13
    · let p : Fin 13 := ⟨w, h13⟩
      obtain ⟨hc, ha, hp⟩ := pointArc p
      have hf := hfalse {p, p + 1, p + 2, p + 5} hc ha
      have ht : ev w (arc {p, p + 1, p + 2, p + 5}) = true := by
        rw [ev_input _ (arc_len _) w (by omega)]
        simp only [arc, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp; omega : w < (List.ofFn fun i : Fin 13 => decide (i ∈ ({p, p + 1, p + 2, p + 5} : Finset (Fin 13)))).length),
          List.getElem?_ofFn]
        simp [p, h13, hp]
      rw [ht] at hf
      cases hf
    · have hl13 : w - 13 < 13 := by omega
      let l : Fin 13 := ⟨w - 13, hl13⟩
      obtain ⟨hc, ha, hdisj⟩ := lineArc l
      have hf := hfalse {l + 2, l + 4, l + 5, l + 6} hc ha
      have ht : ev w (arc {l + 2, l + 4, l + 5, l + 6}) = true := by
        rw [ev_input _ (arc_len _) w (by omega)]
        simp only [arc, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega : (List.ofFn fun i : Fin 13 => decide (i ∈ ({l + 2, l + 4, l + 5, l + 6} : Finset (Fin 13)))).length ≤ w),
          List.length_ofFn, List.getElem?_ofFn]
        simp [l, hl13]
        decide
      rw [ht] at hf
      cases hf
  have hw1ge : 26 ≤ w1 := wire_ge_26 w1 (fun S hc ha => (harc S ⟨hc, ha⟩).1)
  have hw2ge : 26 ≤ w2 := wire_ge_26 w2 (fun S hc ha => (harc S ⟨hc, ha⟩).2)
  have hwne : w1 ≠ w2 := by
    intro heq
    obtain ⟨p, l, _, h1, h2⟩ := hex1
    rw [heq] at h1
    rw [h1] at h2
    cases h2
  have nonconst : ∀ w : ℕ, 26 ≤ w → w < 26 + C.size →
      (∃ p l : Fin 13, ev w (pair p l) = true) →
      (∀ S : Finset (Fin 13), S.card = 4 → (∀ l : Fin 13, (S.filter fun p => p - l ∈ D).card ≤ 2) →
        ev w (arc S) = false) →
      1 ≤ (gateAt C (w - 26)).inputs.length := by
    intro w hge hlt htrue hfalse
    by_contra hz
    have hnil : (gateAt C (w - 26)).inputs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hj : w - 26 < C.gates.length := by unfold Circuit.size at hlt; omega
    have hge_eq : gateAt C (w - 26) = C.gates[w - 26] := by
      delta gateAt; simp [List.getD_eq_getElem?_getD, hj]
    have hmem : C.gates[w - 26] ∈ C.gates := List.getElem_mem hj
    have hmon := (hmono _ hmem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmon
    have hweq : 26 + (w - 26) = w := by omega
    rcases hmon with hand | hor
    · obtain ⟨hc, ha, _⟩ := pointArc 0
      have hf := hfalse {0, 1, 2, 5} hc ha
      have hval := foldl_getD_gate C.gates (arc {0, 1, 2, 5}) (w - 26) hj
      rw [arc_len, hweq] at hval
      have hnil' : (C.gates[w - 26]).inputs = [] := by rw [← hge_eq]; exact hnil
      rw [hnil', hand] at hval
      change (C.gates.foldl stepWire (arc {0, 1, 2, 5})).getD w false = false at hf
      rw [hval] at hf
      rw [List.map_nil] at hf
      exact absurd hf (by decide)
    · obtain ⟨p, l, ht⟩ := htrue
      have hval := foldl_getD_gate C.gates (pair p l) (w - 26) hj
      rw [pair_len, hweq] at hval
      have hnil' : (C.gates[w - 26]).inputs = [] := by rw [← hge_eq]; exact hnil
      rw [hnil', hor] at hval
      change (C.gates.foldl stepWire (pair p l)).getD w false = true at ht
      rw [hval] at ht
      rw [List.map_nil] at ht
      exact absurd ht (by decide)
  have hin1 : 1 ≤ (gateAt C (w1 - 26)).inputs.length :=
    nonconst w1 hw1ge hw1lt (by obtain ⟨p, l, _, h1, _⟩ := hex1; exact ⟨p, l, h1⟩)
      (fun S hc ha => (harc S ⟨hc, ha⟩).1)
  have hin2 : 1 ≤ (gateAt C (w2 - 26)).inputs.length :=
    nonconst w2 hw2ge hw2lt (by obtain ⟨p, l, _, h2, _⟩ := hex2; exact ⟨p, l, h2⟩)
      (fun S hc ha => (harc S ⟨hc, ha⟩).2)
  have hflags : (Finset.univ.filter fun pl : Fin 13 × Fin 13 => pl.1 - pl.2 ∈ D).card = 52 := by
    decide +kernel
  let F := Finset.univ.filter fun pl : Fin 13 × Fin 13 => pl.1 - pl.2 ∈ D
  let F1 := Finset.univ.filter fun pl : Fin 13 × Fin 13 => pl.1 - pl.2 ∈ D ∧ ev w1 (pair pl.1 pl.2) = true
  let F2 := Finset.univ.filter fun pl : Fin 13 × Fin 13 => pl.1 - pl.2 ∈ D ∧ ev w2 (pair pl.1 pl.2) = true
  have hsub : F ⊆ F1 ∪ F2 := by
    intro pl hpl
    have hmem : pl.1 - pl.2 ∈ D := (Finset.mem_filter.mp hpl).2
    rcases hcov pl.1 pl.2 hmem with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem, h2⟩)
  have hsum : 52 ≤ F1.card + F2.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le F1 F2
    change F.card = 52 at hflags
    omega
  have finish : ∀ (a b : ℕ), 26 ≤ a → a < 26 + C.size → 26 ≤ b → b < 26 + C.size → a ≠ b →
      ¬ OrReaches 26 C b (a - 26) → ¬ OrReaches 26 C a (b - 26) →
      (∀ p l : Fin 13, p - l ∈ D → ev a (pair p l) = true ∨ ev b (pair p l) = true) →
      (∀ S : Finset (Fin 13), S.card = 4 → (∀ l : Fin 13, (S.filter fun p => p - l ∈ D).card ≤ 2) →
        ev a (arc S) = false ∧ ev b (arc S) = false) →
      26 ≤ (Finset.univ.filter fun pl : Fin 13 × Fin 13 => pl.1 - pl.2 ∈ D ∧ ev a (pair pl.1 pl.2) = true).card →
      (∃ p l : Fin 13, p - l ∈ D ∧ ev b (pair p l) = true ∧ ev a (pair p l) = false) →
      63 ≤ C.size := by
    intro a b hage halt hbge hblt hab hna hnb hcab haab hmaj hexb
    have hj : a - 26 < C.gates.length := by unfold Circuit.size at halt; omega
    have hge_eq : gateAt C (a - 26) = C.gates[a - 26] := by
      delta gateAt; simp [List.getD_eq_getElem?_getD, hj]
    have hmon := (hmono _ (List.getElem_mem hj)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmon
    rw [← hge_eq] at hmon
    have hmaj' : 26 ≤ Fintype.card { pl : Fin 13 × Fin 13 // pl.1 - pl.2 ∈ D ∧ ev a (pair pl.1 pl.2) = true } := by
      rw [Fintype.card_subtype]; exact hmaj
    rcases hmon with hand | hor
    · exact majorAnd C a b hmono hrb ⟨hage, halt, hbge, hblt, hab⟩ ⟨hna, hnb⟩ hand hcab haab hmaj' hexb
    · exact majorOr C a b hmono hrb ⟨hage, halt, hbge, hblt, hab⟩ ⟨hna, hnb⟩ hor hcab haab hmaj' hexb
  by_cases h1ge : 26 ≤ F1.card
  · exact finish w1 w2 hw1ge hw1lt hw2ge hw2lt hwne (hnor1 hw1ge) (hnor2 hw2ge)
      hcov (fun S hc ha => harc S ⟨hc, ha⟩) h1ge hex2
  · have h2ge : 26 ≤ F2.card := by omega
    exact finish w2 w1 hw2ge hw2lt hw1ge hw1lt hwne.symm (hnor2 hw2ge) (hnor1 hw1ge)
      (fun p l hpl => (hcov p l hpl).symm) (fun S hc ha => (harc S ⟨hc, ha⟩).symm) h2ge hex1
