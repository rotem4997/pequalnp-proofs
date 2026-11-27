import Mathlib
import PEqualNP.Defs

-- Gate elimination for the Petersen edge function at 18 gates.
-- hElim: fixing input v to false removes every gate that reads v (general, any circuit).
-- hSmall: the function with one vertex fixed to false has no circuit with at most 15 gates,
--   and its complement none with at most 14.
-- hRest: the step for circuits in which no input is read by more than 2 gates
--   (3 when the wire is taken negated).
theorem PEqualNP.Outside.R_meta_2371_418
    (hElim : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (S : Finset ℕ),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ j ∈ S, ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some (v : ℕ))) →
      (∃ c : Bool, ∀ x : Fin n → Bool, x v = false → C.eval (List.ofFn x) = c) ∨
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size + S.card ≤ C.size ∧
        ∀ x : Fin n → Bool, x v = false → C'.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hSmall : ∀ (v : Fin 10) (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.FanInTwo C → C.size + (if b = true then 1 else 0) ≤ 15 →
      ∃ x : Fin 10 → Bool, x v = false ∧
        (if b = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hRest : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →
      (∀ (v : Fin 10) (S : Finset ℕ),
        (∀ j ∈ S, ∃ g : PEqualNP.CircuitLowerBounds.Gate, (x1 :: x2.gates)[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some (v : ℕ))) →
        S.card ≤ if x4 = true then 3 else 2) →
         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  intro g D u b hg hD hsize
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: D.gates, u⟩
  have hC : PEqualNP.MetaComplexity.FanInTwo C := by
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact hg _ (List.mem_singleton_self _)
    · exact hD h hh
  have hCsize : C.size ≤ 18 := by
    have h17 : D.gates.length ≤ 17 := hsize
    show (g :: D.gates).length ≤ 18
    simp only [List.length_cons]
    omega
  have key : ∀ v : Fin 10, (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) (fun i => decide (i ≠ v)) = true := by
    decide
  by_cases hbig : ∃ (v : Fin 10) (S : Finset ℕ),
      (∀ j ∈ S, ∃ g' : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g' ∧ (v : ℕ) ∈ g'.inputs ∧
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → g'.inputs.head? = some (v : ℕ))) ∧
      (if b = true then 3 else 2) < S.card
  · obtain ⟨v, S, hS, hcard⟩ := hbig
    rcases hElim 10 C v S hC hS with ⟨c, hc⟩ | ⟨C', hC', hsz, hagree⟩
    · have h1 : (fun i : Fin 10 => decide (i ≠ v)) v = false := by simp
      by_cases hc0 : (if b = true then !c else c) = false
      · refine ⟨fun i => decide (i ≠ v), ?_⟩
        show (if b = true then !(C.eval (List.ofFn fun i => decide (i ≠ v)))
          else C.eval (List.ofFn fun i => decide (i ≠ v))) ≠
          (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) (fun i => decide (i ≠ v))
        rw [hc _ h1, hc0, key v]
        decide
      · refine ⟨fun _ => false, ?_⟩
        show (if b = true then !(C.eval (List.ofFn fun _ : Fin 10 => false))
          else C.eval (List.ofFn fun _ : Fin 10 => false)) ≠ false
        rw [hc _ rfl]
        exact hc0
    · have hsz' : C'.size + (if b = true then 1 else 0) ≤ 15 := by
        cases b <;> simp at hcard ⊢ <;> omega
      obtain ⟨x, hxv, hne⟩ := hSmall v C' b hC' hsz'
      refine ⟨x, ?_⟩
      rw [hagree x hxv] at hne
      exact hne
  · apply hRest g D u b hg hD hsize
    intro v S hS
    by_contra hlt
    exact hbig ⟨v, S, hS, not_le.1 hlt⟩
