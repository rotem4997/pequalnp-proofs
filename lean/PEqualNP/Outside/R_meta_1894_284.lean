import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1894_284
    (transfer : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x p = true ∧ x l = true) →
      let ms : List ℕ := [693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,1718003696225,1387274437386,3436007392450,214756769811,412337856832,3436108316976,154640061441,1168315262978]
      let row (m : ℕ) (i : Fin 42) := m.testBit i.val
      let hit (x : Fin 42 → Bool) := ∃ j g, C.gates[j]? = some g ∧ g.op = .and ∧
        (C.wires (List.ofFn x)).getD (42+j) false = true
      let count (m : ℕ) := (Finset.range C.size).filter fun j =>
        (((C.gates[j]?.map fun g => GateOp.rec false true false (fun _ => false) false g.op).getD false) &&
          !(C.wires (List.ofFn (row m))).getD (42+j) false) = true
      hit (fun (i : Fin 42) => decide (i.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))) → ((∃ m ∈ ms, hit (row m)) ∧ ∀ m ∈ ms, 33 ≤ (count m).card))
    (impossible : ∀ C : Circuit, Monotone2 C → C.size ≤ 124 → (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x p = true ∧ x l = true) →
      let ms : List ℕ := [693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,1718003696225,1387274437386,3436007392450,214756769811,412337856832,3436108316976,154640061441,1168315262978]
      let row (m : ℕ) (i : Fin 42) := m.testBit i.val
      let hit (x : Fin 42 → Bool) := ∃ j g, C.gates[j]? = some g ∧ g.op = .and ∧
        (C.wires (List.ofFn x)).getD (42+j) false = true
      let count (m : ℕ) := (Finset.range C.size).filter fun j =>
        (((C.gates[j]?.map fun g => GateOp.rec false true false (fun _ => false) false g.op).getD false) &&
          !(C.wires (List.ofFn (row m))).getD (42+j) false) = true
      hit (fun (i : Fin 42) => decide (i.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))) → ((∃ m ∈ ms, hit (row m)) ∧ ∀ m ∈ ms, 33 ≤ (count m).card) → False) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  classical
  intro C mono small active
  by_contra noMismatch
  have correct : (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x p = true ∧ x l = true) := by
    intro x
    by_contra wrong
    exact noMismatch ⟨x, wrong⟩
  have checks := transfer C mono correct active
  exact impossible C mono small correct active checks
