import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5256_138
    (normalize : ∀ (n : ℕ) (C : Circuit) (T : Bool → List Bool → Prop)
    (lengths : ∀ b xs, T b xs → xs.length = n)
    (positive : ∃ xs, T true xs) (negative : ∃ xs, T false xs)
    (nonempty : 0 < C.size) (mono : Monotone2 C) (back : ReadsBack n C)
    (fit : ∀ b xs, T b xs → C.eval xs = b)
    (witness : ∀ j < C.size, ∀ a ≤ n + j, ∃ b xs, T b xs ∧
        (C.wires xs).getD (n + j) false = b ∧
        (if a = n + j then false else (C.wires xs).getD a false) = !b),
      C.output + 1 = n + C.size ∧ (∀ j < C.size, let g := gateAt C j;
        (∃ a b, a ≠ b ∧ g.inputs = [a, b]) ∨
        (g.inputs = [] ∧ C.output ≠ n + j ∧
          (∀ k < C.size, n + j ∉ (gateAt C k).inputs) ∧
          ∀ k < C.size, (gateAt C k).inputs = [] → k = j)))
    (delete : ∀ (n : ℕ) (C : Circuit) (T : Bool → List Bool → Prop) (cut : ℕ),
      let witness := fun C : Circuit => ∀ j < C.size, ∀ a ≤ n + j, ∃ b xs, T b xs ∧
        (C.wires xs).getD (n + j) false = b ∧
        (if a = n + j then false else (C.wires xs).getD a false) = !b
      let nested := fun C : Circuit => ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone n C i j
      (∀ b xs, T b xs → xs.length = n) → Monotone2 C → ReadsBack n C → cut < C.size →
        C.output ≠ n + cut → (gateAt C cut).inputs = [] →
        (∀ j < C.size, n + cut ∉ (gateAt C j).inputs) →
        (∀ j < C.size, j ≠ cut → ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a, b]) →
        witness C → nested C →
        ∃ D : Circuit, D.size + 1 = C.size ∧ Monotone2 D ∧ ReadsBack n D ∧
          (∀ j < D.size, ∃ a b, a ≠ b ∧ (gateAt D j).inputs = [a, b]) ∧
          (∀ xs : List Bool, xs.length = n → D.eval xs = C.eval xs) ∧
          (∀ marked, D.lineDeg n marked = C.lineDeg n marked) ∧ witness D ∧ nested D)
    (core : let d : Finset (Fin 13) := {0, 1, 3, 9}
      let T := fun (b : Bool) (xs : List Bool) => if b then
        ∃ p l : Fin 13, p - l ∈ d ∧ xs =
          List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
          List.ofFn (fun l' : Fin 13 => decide (l' = l))
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧
          (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ d)).card ≤ 2) ∧ xs =
          List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ d))
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
        (∀ b xs, T b xs → C.eval xs = b) → 2 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        (∀ j < C.size, ∀ a ≤ 26 + j, ∃ b xs, T b xs ∧
        (C.wires xs).getD (26 + j) false = b ∧
        (if a = 26 + j then false else (C.wires xs).getD a false) = !b) →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        C.output + 1 = 26 + C.size →
        (∀ j < C.size, ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a, b]) → 64 ≤ C.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  intro d T C mono back fit degree witness nested
  have hlen : ∀ b xs, T b xs → xs.length = 26 := by
    intro b xs h
    cases b
    · obtain ⟨Q, _, _, rfl⟩ := h
      simp
    · obtain ⟨p, l, _, rfl⟩ := h
      simp
  have positive : ∃ xs, T true xs := by
    refine ⟨_, (0 : Fin 13), (0 : Fin 13), ?_, rfl⟩
    decide
  have negative : ∃ xs, T false xs := by
    refine ⟨_, ({0, 1, 2, 5} : Finset (Fin 13)), by decide, ?_, rfl⟩
    decide
  have hasGates (D : Circuit)
      (h : ∃ i j, (gateAt D i).op = .and ∧ (gateAt D j).op = .and ∧ InCone 26 D i j) :
      0 < D.size := by
    obtain ⟨i, _, hi, _⟩ := h
    by_contra! h
    have empty : D.gates = [] := List.length_eq_zero_iff.mp (by omega : D.size = 0)
    change (D.gates.getD i ⟨.or, []⟩).op = .and at hi
    rw [empty] at hi
    exact GateOp.noConfusion hi
  obtain ⟨last, shape⟩ := normalize 26 C T hlen positive negative (hasGates C nested) mono back fit witness
  by_cases hconst : ∃ j < C.size, (gateAt C j).inputs = []
  · obtain ⟨j, hj, hempty⟩ := hconst
    rcases shape j hj with ⟨a, b, _, hab⟩ | ⟨_, hout, avoid, unique⟩
    · rw [hab] at hempty
      contradiction
    · have binaryRest : ∀ k < C.size, k ≠ j →
          ∃ a b, a ≠ b ∧ (gateAt C k).inputs = [a, b] := by
        intro k hk hkj
        rcases shape k hk with hb | ⟨hkempty, _⟩
        · exact hb
        · exact False.elim (hkj (unique k hk hkempty))
      obtain ⟨D, sizeD, monoD, backD, binaryD, evalD, degreeD, witnessD, nestedD⟩ :=
        delete 26 C T j hlen mono back hj hout hempty avoid binaryRest witness nested
      have fitD : ∀ b xs, T b xs → D.eval xs = b := by
        intro b xs ht
        rw [evalD xs (hlen b xs ht)]
        exact fit b xs ht
      have lastD := (normalize 26 D T hlen positive negative (hasGates D nestedD)
        monoD backD fitD witnessD).1
      rw [← degreeD] at degree
      exact (core D monoD backD fitD degree witnessD nestedD lastD binaryD).trans (by omega)
  · apply core C mono back fit degree witness nested last
    intro j hj
    rcases shape j hj with h | ⟨hempty, _⟩
    · exact h
    · exact False.elim (hconst ⟨j, hj, hempty⟩)
