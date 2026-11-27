import PEqualNP.Defs

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_909_927
    (search : ∃ (A B : Fin 6 → ℕ) (O : Finset (Fin 6)),
      (∀ i : Fin 6, A i < 2 ^ (10 + (i : ℕ)) ∧ B i < 2 ^ (10 + (i : ℕ))) ∧
      (∀ v : Fin 10, Fintype.card {i : Fin 6 //
        (A i).testBit (v : ℕ) = true ∨ (B i).testBit (v : ℕ) = true} ≤ 2) ∧
      let run : ℕ → ℕ := fun m : ℕ => (List.finRange 6).foldl (fun w i =>
      if (w &&& A i) ≠ 0 ∧ (w &&& B i) ≠ 0 then w ||| 2 ^ (10 + (i : ℕ)) else w) (m % 1024)
      let accept : ℕ → Bool := fun m => decide (∃ i ∈ O, (run m).testBit (10 + (i : ℕ)) = true)
      ∀ m ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), accept m = false ∧
        ∀ v : Fin 10, m.testBit (v : ℕ) = false → accept (m ||| 2 ^ (0 + (v : ℕ))) = true)
    (compile : ∀ (A B : Fin 6 → ℕ) (O : Finset (Fin 6)),
      (∀ i : Fin 6, A i < 2 ^ (10 + (i : ℕ)) ∧ B i < 2 ^ (10 + (i : ℕ))) →
      let C := ({ size := 6, leftVars := fun i => Finset.univ.filter (fun v : Fin 10 => (A i).testBit (v : ℕ) = true), rightVars := fun i => Finset.univ.filter (fun v : Fin 10 => (B i).testBit (v : ℕ) = true), leftGates := fun i => Finset.univ.filter (fun j : Fin 6 => j < i ∧ (A i).testBit (10 + (j : ℕ)) = true), rightGates := fun i => Finset.univ.filter (fun j : Fin 6 => j < i ∧ (B i).testBit (10 + (j : ℕ)) = true), outVars := ∅, outGates := O } : PEqualNP.AndCount.AndCountCircuit 10)
      let run : ℕ → ℕ := fun m : ℕ => (List.finRange 6).foldl (fun w i =>
      if (w &&& A i) ≠ 0 ∧ (w &&& B i) ≠ 0 then w ||| 2 ^ (10 + (i : ℕ)) else w) (m % 1024)
      ∀ m : ℕ, C.eval (Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)) =
        decide (∃ i ∈ O, (run m).testBit (10 + (i : ℕ)) = true))
    :
    ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  have geometry : ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
      ∀ I : Finset (Fin 10),
      (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      I ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ).map (fun m =>
        Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)) := by
    intro G hG
    subst G
    simp only [SimpleGraph.fromRel_adj, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    decide +kernel
  intro G hG
  obtain ⟨A, B, O, bounds, budget, tests⟩ := search
  let C := ({ size := 6, leftVars := fun i => Finset.univ.filter (fun v : Fin 10 => (A i).testBit (v : ℕ) = true), rightVars := fun i => Finset.univ.filter (fun v : Fin 10 => (B i).testBit (v : ℕ) = true), leftGates := fun i => Finset.univ.filter (fun j : Fin 6 => j < i ∧ (A i).testBit (10 + (j : ℕ)) = true), rightGates := fun i => Finset.univ.filter (fun j : Fin 6 => j < i ∧ (B i).testBit (10 + (j : ℕ)) = true), outVars := ∅, outGates := O } : PEqualNP.AndCount.AndCountCircuit 10)
  let run : ℕ → ℕ := fun m : ℕ => (List.finRange 6).foldl (fun w i =>
      if (w &&& A i) ≠ 0 ∧ (w &&& B i) ≠ 0 then w ||| 2 ^ (10 + (i : ℕ)) else w) (m % 1024)
  let accept : ℕ → Bool := fun m => decide (∃ i ∈ O, (run m).testBit (10 + (i : ℕ)) = true)
  have values (m : ℕ) : C.eval (Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)) = accept m :=
    compile A B O bounds m
  refine ⟨C, ?_, Nat.le_refl 6, ?_, ?_⟩
  · intro i
    constructor
    · intro j hj
      exact (Finset.mem_filter.mp hj).2.1
    · intro j hj
      exact (Finset.mem_filter.mp hj).2.1
  · intro v
    simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.subtype_card] using budget v
  · intro I independent maximal
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (geometry G hG I independent maximal)
    constructor
    · rw [values]
      exact (tests m hm).1
    · intro v hv
      have bitoff : m.testBit (v : ℕ) = false := by
        cases e : m.testBit (v : ℕ)
        · rfl
        · exact False.elim (hv (by simp [e]))
      have insert_bits :
          Finset.univ.filter (fun w : Fin 10 => (m ||| 2 ^ (v : ℕ)).testBit (w : ℕ) = true) =
            insert v (Finset.univ.filter (fun w : Fin 10 => m.testBit (w : ℕ) = true)) := by
        ext w
        simp [Nat.testBit_or, Nat.testBit_two_pow, Fin.ext_iff, or_comm]
        exact or_congr eq_comm Iff.rfl
      rw [← insert_bits, values]
      simpa only [Nat.zero_add] using (tests m hm).2 v bitoff
