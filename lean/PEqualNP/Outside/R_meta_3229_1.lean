import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3229_1
    (h_and :
      let T (D : Circuit) :=
        (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false]) = false) ∧
        (∃ m ∈ ([50, 116, 208, 276, 402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true]) = true)
      let v (D : Circuit) (m : ℕ) := D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3])
      ∀ D : Circuit, D.gates.length = 14 → Monotone2 D → D.output = 23 → T D →
        (∃ g gs, D.gates = g :: gs ∧ g.op = GateOp.and) →
        (∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ), v D m = true) →
        ¬∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), v D m = false)
    (h_or_03 :
      let T (D : Circuit) :=
        (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false]) = false) ∧
        (∃ m ∈ ([50, 116, 208, 276, 402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true]) = true)
      let v (D : Circuit) (m : ℕ) := D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3])
      ∀ D : Circuit, D.gates.length = 14 → Monotone2 D → D.output = 23 → T D →
        (∃ g gs, D.gates = g :: gs ∧ g.op = GateOp.or ∧ (0 ∈ g.inputs ∨ 3 ∈ g.inputs)) →
        (∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ), v D m = true) →
        ¬∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), v D m = false)
    (h_or_9 :
      let T (D : Circuit) :=
        (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false]) = false) ∧
        (∃ m ∈ ([50, 116, 208, 276, 402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true]) = true)
      let v (D : Circuit) (m : ℕ) := D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3])
      ∀ D : Circuit, D.gates.length = 14 → Monotone2 D → D.output = 23 → T D →
        (∃ g gs, D.gates = g :: gs ∧ g.op = GateOp.or ∧ 0 ∉ g.inputs ∧ 3 ∉ g.inputs ∧ 9 ∈ g.inputs) →
        (∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ), v D m = true) →
        ¬∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), v D m = false)
    (h_or_rest :
      let T (D : Circuit) :=
        (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false]) = false) ∧
        (∃ m ∈ ([50, 116, 208, 276, 402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true]) = true)
      let v (D : Circuit) (m : ℕ) := D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3])
      ∀ D : Circuit, D.gates.length = 14 → Monotone2 D → D.output = 23 → T D →
        (∃ g gs, D.gates = g :: gs ∧ g.op = GateOp.or ∧ 0 ∉ g.inputs ∧ 3 ∉ g.inputs ∧ 9 ∉ g.inputs) →
        (∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ), v D m = true) →
        ¬∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), v D m = false) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∀ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x8 = Bool.true) → ¬∀ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x9 = Bool.false := by
  dsimp only
  intro D hlen hmono hout hT hpos hneg
  cases hg : D.gates with
  | nil => simp [hg] at hlen
  | cons g gs =>
    have hgmem : g ∈ D.gates := by rw [hg]; exact List.mem_cons_self
    rcases (hmono g hgmem).1 with hand | hor
    · exact h_and D hlen hmono hout hT ⟨g, gs, hg, hand⟩ hpos hneg
    · by_cases h0 : 0 ∈ g.inputs
      · exact h_or_03 D hlen hmono hout hT ⟨g, gs, hg, hor, Or.inl h0⟩ hpos hneg
      · by_cases h3 : 3 ∈ g.inputs
        · exact h_or_03 D hlen hmono hout hT ⟨g, gs, hg, hor, Or.inr h3⟩ hpos hneg
        · by_cases h9 : 9 ∈ g.inputs
          · exact h_or_9 D hlen hmono hout hT ⟨g, gs, hg, hor, h0, h3, h9⟩ hpos hneg
          · exact h_or_rest D hlen hmono hout hT ⟨g, gs, hg, hor, h0, h3, h9⟩ hpos hneg
