import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4139_183
    (encode : ∀ (n : Nat) (C : Circuit), FanInTwo C →
      ∃ (program : (i : Fin C.size) → Fin (n + (i : Nat) + 1) ⊕ (Bool × Fin (n + (i : Nat) + 1) × Fin (n + (i : Nat) + 1)))
        (output : Fin (n + C.size + 1)),
        have gs : List Gate := List.ofFn fun i : Fin C.size => (program i).elim
          (fun a : Fin (n + (i : Nat) + 1) => (⟨.not, [(a : Nat)]⟩ : Gate))
          (fun t : Bool × Fin (n + (i : Nat) + 1) × Fin (n + (i : Nat) + 1) => ⟨Bool.rec GateOp.and GateOp.or t.1, [(t.2.1 : Nat), (t.2.2 : Nat)]⟩)
        ∀ xs : List Bool, xs.length = n →
          C.eval xs = (⟨gs, (output : Nat)⟩ : Circuit).eval xs)
    (search : ∀ (k : Fin 19),
      ∀ (program : (i : Fin (k : Nat)) → Fin (11 + (i : Nat) + 1) ⊕ (Bool × Fin (11 + (i : Nat) + 1) × Fin (11 + (i : Nat) + 1)))
        (output : Fin (11 + (k : Nat) + 1)),
        have gs : List Gate := List.ofFn fun i : Fin (k : Nat) => (program i).elim
          (fun a : Fin (11 + (i : Nat) + 1) => (⟨.not, [(a : Nat)]⟩ : Gate))
          (fun t : Bool × Fin (11 + (i : Nat) + 1) × Fin (11 + (i : Nat) + 1) => ⟨Bool.rec GateOp.and GateOp.or t.1, [(t.2.1 : Nat), (t.2.2 : Nat)]⟩)
        ∃ x : Fin 10 → Bool,
          (⟨gs, (output : Nat)⟩ : Circuit).eval (List.ofFn x ++ [x 0 || x 1]) ≠
            ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
              (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hfan hsize
  obtain ⟨p, o, agrees⟩ := encode 11 C hfan
  obtain ⟨x, hx⟩ := search ⟨C.size, by omega⟩ p o
  refine ⟨x, ?_⟩
  rw [agrees _ (by simp)]
  intro heq
  apply hx
  -- List.any associates to the right; the target associates to the left.
  rw [heq]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc,
    Nat.reduceDiv, Nat.reduceMod]
  rfl
