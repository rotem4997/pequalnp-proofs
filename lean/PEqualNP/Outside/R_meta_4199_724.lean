import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4199_724
    (extract : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 42 → Bool, C.eval (List.ofFn x)=true ↔ ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x a=true ∧ x b=true) → C.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op true false false (fun _ => false) false) ≤ 20 → ∃ A : PEqualNP.AndCount.AndCountCircuit 42, A.WellFormed ∧ A.Computes G ∧ A.outVars=∅ ∧ (∀ i v, A.gateVal {v} i=false) ∧ (∀ i, Disjoint (A.leftVars i) (A.rightVars i)) ∧ 19 ≤ A.size ∧ A.size ≤ C.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op true false false (fun _ => false) false))
    (cofactor : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
∀ A : PEqualNP.AndCount.AndCountCircuit 42, A.WellFormed → A.Computes G → let live := fun (U : Finset (Fin 42)) => {i : Fin A.size | ((∃ v ∈ A.leftVars i, v ∈ U) ∨ ∃ j ∈ A.leftGates i, A.gateVal U j=true) ∨ ((∃ v ∈ A.rightVars i, v ∈ U) ∨ ∃ j ∈ A.rightGates i, A.gateVal U j=true)}.ncard;
(∀ v : Fin 42, live {v} + 16 ≤ A.size) ∧ (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → live {p,l} + 14 ≤ A.size))
    (nineteen : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
∀ A : PEqualNP.AndCount.AndCountCircuit 42, A.WellFormed → A.Computes G → A.outVars=∅ → (∀ i v, A.gateVal {v} i=false) → (∀ i, Disjoint (A.leftVars i) (A.rightVars i)) → A.size = 19 → let live := fun (U : Finset (Fin 42)) => {i : Fin A.size | ((∃ v ∈ A.leftVars i, v ∈ U) ∨ ∃ j ∈ A.leftGates i, A.gateVal U j=true) ∨ ((∃ v ∈ A.rightVars i, v ∈ U) ∨ ∃ j ∈ A.rightGates i, A.gateVal U j=true)}.ncard;
(∀ v : Fin 42, live {v} ≤ 3) → (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → live {p,l} ≤ 5) → False)
    (twenty : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
∀ A : PEqualNP.AndCount.AndCountCircuit 42, A.WellFormed → A.Computes G → A.outVars=∅ → (∀ i v, A.gateVal {v} i=false) → (∀ i, Disjoint (A.leftVars i) (A.rightVars i)) → A.size = 20 → let live := fun (U : Finset (Fin 42)) => {i : Fin A.size | ((∃ v ∈ A.leftVars i, v ∈ U) ∨ ∃ j ∈ A.leftGates i, A.gateVal U j=true) ∨ ((∃ v ∈ A.rightVars i, v ∈ U) ∨ ∃ j ∈ A.rightGates i, A.gateVal U j=true)}.ncard;
(∀ v : Fin 42, live {v} ≤ 4) → (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → live {p,l} ≤ 6) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.true Bool.false Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x1.gates := by
  intro C mono computes
  by_contra h
  have sm : C.gates.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op true false false (fun _ => false) false) ≤ 20 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  obtain ⟨A,wf,comp,out,clean,disj,low,high⟩ := extract C mono computes sm
  obtain ⟨single,pair⟩ := cofactor A wf comp
  have hcases : A.size = 19 ∨ A.size = 20 := by omega
  rcases hcases with size | size
  · apply nineteen A wf comp out clean disj size
    · intro v
      have t := single v
      omega
    · intro p l hp hl hn
      have t := pair p l hp hl hn
      omega
  · apply twenty A wf comp out clean disj size
    · intro v
      have t := single v
      omega
    · intro p l hp hl hn
      have t := pair p l hp hl hn
      omega
