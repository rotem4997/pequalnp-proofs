import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing the distinguished vertex leaves six vertices on a cycle.
-- Each of its three neighbors attaches to opposite vertices of that cycle.
-- The two cofactors share ordinary gates. At a signed-input reader one cofactor
-- can copy an earlier wire while the other takes a constant value.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5369_21
    (compile :
      let gate (b : Bool) (v : Bool × Bool × ℕ) : Gate :=
        if b = v.1 then ⟨if v.2.1 then .and else .or, []⟩ else ⟨.or, [v.2.2]⟩
      let circ (b : Bool) (s : List (Gate ⊕ (Bool × Bool × ℕ))) (o : ℕ) : Circuit :=
        ⟨s.map (Sum.elim id (gate b)), o⟩
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → C.gates.countP (fun (g : Gate) =>
        let pins := GateOp.rec (motive := fun _ => List ℕ) g.inputs g.inputs
          (g.inputs.take 1) (fun _ => g.inputs) g.inputs g.op
        pins.contains 0 || pins.contains 10) ≤ 3 →
        (∀ b : Bool, C.eval ((b :: List.replicate 9 false) ++ [!b]) = false) →
        ∃ (s : List (Gate ⊕ (Bool × Bool × ℕ))) (o : ℕ), s.length ≤ 18 ∧ s.countP Sum.isRight ≤ 3 ∧ FanInTwo (circ false s o) ∧
          ∀ (b : Bool) (x : Fin 9 → Bool), (circ b s o).eval (List.ofFn x) =
            C.eval ((b :: List.ofFn x) ++ [!b]))
    (joint :
      let gate (b : Bool) (v : Bool × Bool × ℕ) : Gate :=
        if b = v.1 then ⟨if v.2.1 then .and else .or, []⟩ else ⟨.or, [v.2.2]⟩
      let circ (b : Bool) (s : List (Gate ⊕ (Bool × Bool × ℕ))) (o : ℕ) : Circuit :=
        ⟨s.map (Sum.elim id (gate b)), o⟩
      ∀ (s : List (Gate ⊕ (Bool × Bool × ℕ))) (o : ℕ), s.length ≤ 18 → s.countP Sum.isRight ≤ 3 → FanInTwo (circ false s o) →
        ∃ x : Fin 9 → Bool,
          let ring := (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1)
          (circ false s o).eval (List.ofFn x) ≠ (ring || ((x 0 && (x 1 || x 5)) || (x 3 && (x 2 || x 8)) || (x 4 && (x 6 || x 7)))) ∨
          (circ true s o).eval (List.ofFn x) ≠ (ring || x 0 || x 3 || x 4)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       List.countP             (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) =>               have x5 : List ℕ := PEqualNP.CircuitLowerBounds.GateOp.rec x4.inputs x4.inputs (List.take (1 : ℕ) x4.inputs) (fun (x5 : ℕ) => x4.inputs) x4.inputs x4.op;               x5.contains (0 : ℕ) || x5.contains (10 : ℕ))             x1.gates ≤           (3 : ℕ) →         ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan cap few
  by_contra! rows
  let edge := fun (x : Fin 10 → Bool) => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let ring := fun (x : Fin 9 → Bool) => (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1)
  let low := fun (x : Fin 9 → Bool) => ring x || ((x 0 && (x 1 || x 5)) || (x 3 && (x 2 || x 8)) || (x 4 && (x 6 || x 7)))
  let high := fun (x : Fin 9 → Bool) => ring x || x 0 || x 3 || x 4
  have matched (b : Bool) (x : Fin 9 → Bool) :
      C.eval ((b :: List.ofFn x) ++ [!b]) = edge (Fin.cons b x) := by
    have h := rows (Fin.cons b x)
    change C.eval (List.ofFn (Fin.cons b x) ++ [!b]) = edge (Fin.cons b x) at h
    simpa using h
  have emptyRows (b : Bool) : C.eval ((b :: List.replicate 9 false) ++ [!b]) = false := by
    have h := matched b (fun _ => false)
    have hz : edge (Fin.cons b (fun _ => false)) = false := by cases b <;> rfl
    simpa [hz] using h
  obtain ⟨s, o, bound, switches, legal, sim⟩ := compile C fan cap few emptyRows
  obtain ⟨x, hx⟩ := joint s o bound switches legal
  have h0 : ∀ x : Fin 9 → Bool, edge (Fin.cons false x) = low x := by decide +kernel
  have h1 : ∀ x : Fin 9 → Bool, edge (Fin.cons true x) = high x := by decide +kernel
  rcases hx with h | h
  · exact h (((sim false x).trans (matched false x)).trans (h0 x))
  · exact h (((sim true x).trans (matched true x)).trans (h1 x))
