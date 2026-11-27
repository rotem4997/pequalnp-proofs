import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_2613_1
    (hgate :
      let val := fun (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
      ∀ (C : Circuit) (x : Fin 26 → Bool) (j a b : ℕ),
        IsAO2 26 C → C.gates[j]? = some ⟨.and, [a, b]⟩ →
        val C x (26 + j) = (val C x a && val C x b))
    (horigin :
      let val := fun (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
      let arc := fun (C : Circuit) (u v : ℕ) =>
        ∃ j : ℕ, v = 26 + j ∧ (gateAt C j).op = .or ∧ u ∈ (gateAt C j).inputs
      let source := fun (C : Circuit) (x : Fin 26 → Bool) (k w : ℕ) =>
        (gateAt C k).op = .and ∧ val C x (26 + k) = true ∧
          Relation.ReflTransGen (arc C) (26 + k) w
      let both := fun p l : Fin 26 => fun x : Fin 26 => decide (x = p ∨ x = l)
      ∀ (C : Circuit) (p l : Fin 26) (w : ℕ), IsAO2 26 C →
        val C (both p l) w = true →
        val C (fun x => decide (x = p)) w = false →
        val C (fun x => decide (x = l)) w = false →
        ∃ k, source C (both p l) k w)
    (hsame :
      ∀ C : Circuit,
        let gate := gateAt C
        let val := fun (x : Fin 26 → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
        let inc := fun p l : Fin 13 => p - l ∈ ([0, 1, 3, 9] : List (Fin 13))
        C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, val x C.output = true ↔
          ∃ p l : Fin 13, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∀ j, (gate j).op = .and → ∀ x, val x (26 + j) = true → val x C.output = true) →
        ∀ (p l : Fin 13) (j a b i : ℕ),
          let both := fun x : Fin 26 => decide (x = Fin.castAdd 13 p ∨ x = Fin.natAdd 13 l)
          let source := fun n w : ℕ =>
            (gate n).op = .and ∧ val both (26 + n) = true ∧
              Relation.ReflTransGen (fun u v =>
                ∃ m, v = 26 + m ∧ (gate m).op = .or ∧ u ∈ (gate m).inputs) (26 + n) w
          inc p l → gate j = ⟨.and, [a, b]⟩ → val both (26 + j) = true →
          (∀ t : Fin 26, both t = true →
            (val (fun x => decide (x = t)) a || val (fun x => decide (x = t)) b) = false) →
          source i a → source i b → False)
    (hdistinct :
      ∀ C : Circuit,
        let gate := gateAt C
        let val := fun (x : Fin 26 → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
        let inc := fun p l : Fin 13 => p - l ∈ ([0, 1, 3, 9] : List (Fin 13))
        C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, val x C.output = true ↔
          ∃ p l : Fin 13, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∀ j, (gate j).op = .and → ∀ x, val x (26 + j) = true → val x C.output = true) →
        ∀ (p l : Fin 13) (j a b i k : ℕ),
          let both := fun x : Fin 26 => decide (x = Fin.castAdd 13 p ∨ x = Fin.natAdd 13 l)
          let source := fun n w : ℕ =>
            (gate n).op = .and ∧ val both (26 + n) = true ∧
              Relation.ReflTransGen (fun u v =>
                ∃ m, v = 26 + m ∧ (gate m).op = .or ∧ u ∈ (gate m).inputs) (26 + n) w
          inc p l → gate j = ⟨.and, [a, b]⟩ → val both (26 + j) = true →
          (∀ t : Fin 26, both t = true →
            (val (fun x => decide (x = t)) a || val (fun x => decide (x = t)) b) = false) →
          source i a → source k b → i ≠ k → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → x5.inputs.Nodup) →         have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ));         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x1.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x5 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin (26 : ℕ) → Bool), x6 x10 ((26 : ℕ) + x8) = Bool.true → x6 x10 x1.output = Bool.true) →             ∀ (x9 x10 : Fin (13 : ℕ)),               x5 x9 x10 →                 have x12 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.castAdd (13 : ℕ) x9;                 have x13 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.natAdd (13 : ℕ) x10;                 have x14 : ℕ → ℕ → ℕ → Prop := fun (x14 x15 x16 : ℕ) => x1.gates[x14]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x15, x16] : PEqualNP.CircuitLowerBounds.Gate } ∧ x6 (fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x12 ∨ x17 = x13)) ((26 : ℕ) + x14) = Bool.true;                 have x15 : Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x15 : Fin (26 : ℕ)) (x16 x17 : ℕ) => (x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x16 || x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x17) = Bool.true;                 ∀ (x16 x17 x18 : ℕ), x14 x16 x17 x18 → x15 x12 x17 x18 ∨ x15 x13 x17 x18 := by
  dsimp only
  intro C hsize hao hnodup hval hclean p l hinc j a b hactive
  let P : Fin 26 := Fin.castAdd 13 p
  let L : Fin 26 := Fin.natAdd 13 l
  let val := fun (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
  let single := fun t x : Fin 26 => decide (x = t)
  let pair := fun x : Fin 26 => decide (x = P ∨ x = L)
  change (val C (single P) a || val C (single P) b) = true ∨
    (val C (single L) a || val C (single L) b) = true
  by_contra noHit
  have hnone (t : Fin 26) (ht : t = P ∨ t = L) :
      (val C (single t) a || val C (single t) b) = false := by
    cases h : val C (single t) a || val C (single t) b
    · rfl
    · rcases ht with rfl | rfl
      · exact (noHit (Or.inl h)).elim
      · exact (noHit (Or.inr h)).elim
  have hTrue : (val C pair a && val C pair b) = true :=
    (hgate C pair j a b hao hactive.1).symm.trans hactive.2
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hTrue
  obtain ⟨haP, hbP⟩ := Bool.or_eq_false_iff.mp (hnone P (Or.inl rfl))
  obtain ⟨haL, hbL⟩ := Bool.or_eq_false_iff.mp (hnone L (Or.inr rfl))
  obtain ⟨i, hi⟩ := horigin C P L a hao ha haP haL
  obtain ⟨k, hk⟩ := horigin C P L b hao hb hbP hbL
  have hnd (g : Gate) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hg
    exact hnodup m g hm
  have hincList (p l : Fin 13) :
      p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) ↔ p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  have hvalList (x : Fin 26 → Bool) : val C x C.output = true ↔
      ∃ p l : Fin 13, p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    simpa only [hincList] using hval x
  have hgateAt : gateAt C j = ⟨.and, [a, b]⟩ := by
    change C.gates.getD j ⟨.or, []⟩ = _
    rw [List.getD_eq_getElem?_getD, hactive.1] <;> rfl
  have he := (hincList p l).2 hinc
  have hnoPair (t : Fin 26) (ht : pair t = true) :
      (val C (single t) a || val C (single t) b) = false :=
    hnone t (of_decide_eq_true ht)
  by_cases h : i = k
  · subst k
    exact hsame C hsize hao hnd hvalList hclean p l j a b i he hgateAt hactive.2 hnoPair hi hk
  · exact hdistinct C hsize hao hnd hvalList hclean p l j a b i k he hgateAt hactive.2 hnoPair hi hk h
