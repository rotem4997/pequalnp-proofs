import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two OR gates give two extra input signals to the remaining circuit.
-- A mask records the raw input coordinates used by the second OR.
theorem PEqualNP.Outside.R_meta_3348_119 :
    (let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      circuitFun 9 C = f → C.gates[1]?.map (fun g => g.op) = some GateOp.or → C.size ≤ 15 →
      ∃ m ∈ ([0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208] : List ℕ), ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧ (∀ x : Fin 9 → Bool, circuitFun 11 D (Fin.snoc (Fin.snoc x (x 4 || x 6)) (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true))) = f x)) →
    (let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ m ∈ ([0, 1, 4, 16, 128, 80] : List ℕ), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, circuitFun 11 D (Fin.snoc (Fin.snoc x (x 4 || x 6)) (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true))) = f x) → 14 ≤ D.size) →
    (let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ m ∈ ([3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144] : List ℕ), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, circuitFun 11 D (Fin.snoc (Fin.snoc x (x 4 || x 6)) (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true))) = f x) → 14 ≤ D.size) →
    (let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ m ∈ ([81, 84, 208] : List ℕ), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, circuitFun 11 D (Fin.snoc (Fin.snoc x (x 4 || x 6)) (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true))) = f x) → 14 ≤ D.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have same : (fun x4 : Fin 9 → Bool => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) = f := by decide +kernel
  intro normalize aliasCase pairCase tripleCase C ok first target second
  by_contra! small
  obtain ⟨m, mem, D, legal, budget, works⟩ := normalize C ok first (target.trans same) second (by omega)
  have parts : m ∈ ([0, 1, 4, 16, 128, 80] : List ℕ) ∨ m ∈ ([3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144] : List ℕ) ∨ m ∈ ([81, 84, 208] : List ℕ) := by
    have unroll : ([0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208] : List ℕ) = ([0, 1, 4, 16, 128, 80] : List ℕ) ++ (([3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144] : List ℕ) ++ ([81, 84, 208] : List ℕ)) := rfl
    simpa only [unroll,List.mem_append] using mem
  have lower : 14 ≤ D.size := by
    rcases parts with h | h | h
    · exact aliasCase m h D legal works
    · exact pairCase m h D legal works
    · exact tripleCase m h D legal works
  omega
