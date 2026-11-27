import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2280_728
    (normalize :
      let E (u v : ℕ) : Prop :=
        (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
      let F (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, E u.val v.val ∧ x u = true ∧ x v = true
      let B (x : Fin 14 → Bool) : Prop :=
        (F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
        (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))
      let OK (C : Circuit) (r : Fin 14) : Prop := Monotone2 C ∧
        ∀ x, B x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x)
      let P (C : Circuit) : Prop := ∀ g ∈ C.gates, g.op = .and →
        (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
        ∀ a b, g.inputs = [a,b] → a < 14 → b < 14 → a ≠ b → E a b ∨ E b a
      ∀ (C : Circuit) (r : Fin 14), 7 ≤ r.val → OK C r →
        ∃ D : Circuit, D.size = C.size ∧ OK D r ∧ P D)
    (search :
      let E (u v : ℕ) : Prop :=
        (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
      let F (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, E u.val v.val ∧ x u = true ∧ x v = true
      let B (x : Fin 14 → Bool) : Prop :=
        (F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
        (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))
      let OK (C : Circuit) (r : Fin 14) : Prop := Monotone2 C ∧
        ∀ x, B x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x)
      let P (C : Circuit) : Prop := ∀ g ∈ C.gates, g.op = .and →
        (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
        ∀ a b, g.inputs = [a,b] → a < 14 → b < 14 → a ≠ b → E a b ∨ E b a
      ∀ (C : Circuit) (r : Fin 14), r = 7 ∨ r = 9 → OK C r → P C → 26 ≤ C.size) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  dsimp only
  intro C r hr hC h
  let E (u v : ℕ) : Prop :=
    (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
  let F (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, E u.val v.val ∧ x u = true ∧ x v = true
  let orig (x : Fin 14 → Bool) : Prop :=
    ∃ u v : Fin 14, (u.val,v.val) ∈
      ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
        (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true
  have tab (u v : Fin 14) :
      E u.val v.val ↔ (u.val,v.val) ∈
      ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
        (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) := by
    fin_cases u <;> fin_cases v <;> decide +kernel
  have eq : F = orig := by
    funext x
    apply propext
    simp only [F,orig,tab]
  have nums : 7 ≤ r.val := by rcases hr with rfl | rfl <;> decide
  have correctOld (x : Fin 14 → Bool) (extremal :
      (F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
      (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))) :
      C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x := by
    rw [eq]
    exact h x (by simpa only [eq,orig] using extremal)
  obtain ⟨D,ds,dOK,dP⟩ := normalize C r nums ⟨hC,correctOld⟩
  simpa only [ds] using search D r hr dOK dP
