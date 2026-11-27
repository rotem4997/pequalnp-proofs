import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_3551_642
    (binary : ∀ C : Circuit, FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 13 ≤ C.size - notCount C)
    (boundary : let reads (g : Gate) (w : ℕ) := g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
      ∀ C : Circuit, FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ reads (C.gates.get i) 4 ∧ reads (C.gates.get j) 6 ∧
        (∀ k : Fin C.gates.length, reads (C.gates.get k) 4 → k = i) ∧
        (∀ k : Fin C.gates.length, reads (C.gates.get k) 6 → k = j)) → notCount C = 0 →
      (∀ m ∈ ([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ), let x : Fin 9 → Bool := fun i => m.testBit i.val
        C.eval (List.ofFn x ++ [x 4 || x 6]) = decide (m ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ))) →
      15 ≤ C.size)
    (signed : let reads (g : Gate) (w : ℕ) := g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
      ∀ C : Circuit, FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ reads (C.gates.get i) 4 ∧ reads (C.gates.get j) 6 ∧
        (∀ k : Fin C.gates.length, reads (C.gates.get k) 4 → k = i) ∧
        (∀ k : Fin C.gates.length, reads (C.gates.get k) 6 → k = j)) → 1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6]) =
        ([(1:ℕ),11,21,31,36,5,15,25,35,52,62,77].any fun e =>
          x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) → 15 ≤ C.size) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →     (∀ (x4 : Fin (9 : ℕ) → Bool), { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) x4) →       (∃ (x5 : Fin x1.length) (x6 : Fin x1.length),           x5 < x6 ∧             (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x5;               x7.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x7.inputs) ∧               (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x6;                 x7.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x7.inputs) ∧                 (∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x8.inputs) →                       x7 = x5) ∧                   ∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x8.inputs) →                       x7 = x6) →         (15 : ℕ) ≤ x1.length := by
  intro gs o legal computes readers
  let C : Circuit := ⟨gs,o⟩
  change 15 ≤ C.size
  by_cases none : notCount C = 0
  · apply boundary C legal readers none
    intro m hm
    let x : Fin 9 → Bool := fun i => m.testBit i.val
    apply (computes x).trans
    have table : ∀ m ∈ ([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ),
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        ([(1:ℕ),11,21,31,36,5,15,25,35,52,62,77].any fun e =>
          x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) = decide (m ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ)) := by
      intro m h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact table m hm
  by_cases low : notCount C ≤ 2
  · exact signed C legal readers (by omega) low computes
  let first : Gate := ⟨.or,[4,6]⟩
  let D : Circuit := ⟨first :: gs,o⟩
  have fan : FanInTwo D := by
    intro g hg
    change g ∈ first :: gs at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    · exact legal g hg
  have bound := binary D fan (by
    intro x
    have firstValue : (List.ofFn x ++ [([(List.ofFn x).getD 4 false,
        (List.ofFn x).getD 6 false].any id)]) = List.ofFn x ++ [x 4 || x 6] := by
      simp [List.getD_eq_getElem?_getD]
    change (gs.foldl _ (List.ofFn x ++ [([(List.ofFn x).getD 4 false,
      (List.ofFn x).getD 6 false].any id)])).getD o false = _
    rw [firstValue]
    exact computes x)
  have sz : D.size = C.size + 1 := rfl
  have nc : notCount D = notCount C := by
    change (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))
      (first :: gs)).length = _
    change _ = (List.filter (fun g : Gate => @decide (g.op = GateOp.not)
      (lineDegreeGateOpDecEq _ _)) gs).length
    simp [first]
  rw [sz,nc] at bound
  omega
