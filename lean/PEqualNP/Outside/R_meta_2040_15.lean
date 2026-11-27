import Mathlib
import PEqualNP.Defs

-- The sensitive assignments follow the argument in R_meta_2040_271.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_2040_15
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (normalize : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : (Fin (8 : ℕ) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = !x6 (4 : Fin (9 : ℕ))) → (∀ (x7 : Fin (8 : ℕ) → Bool) (x8 : Bool), x1.eval ((List.ofFn x7).insertIdx (4 : ℕ) x8) = if x8 = Bool.true then x3 x7 else x2 x7) → x2 ≠ x3 → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x2 (12 : ℕ) ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) (x12 : Bool), PEqualNP.MetaComplexity.FanInTwo x9 ∧ PEqualNP.MetaComplexity.FanInTwo x10 ∧ x9.size + x10.size ≤ (13 : ℕ) ∧ x11 < (8 : ℕ) + x9.size ∧ ∀ (x13 : Fin (8 : ℕ) → Bool) (x14 : Bool), have x15 : List Bool := x9.wires (List.ofFn x13); x10.eval (x15 ++ [if x14 = Bool.true then x12 else x15.getD x11 Bool.false]) = if x14 = Bool.true then x3 x13 else x2 x13)
    (positive :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (i : ℕ), FanInTwo p → FanInTwo t →
        p.size + t.size ≤ 13 → i < 8 + p.size →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let u := fun x : Fin 8 → Bool => (w x).getD i false
        (∀ x, t.eval (w x ++ [u x]) = lo x) →
        ∃ x, t.eval (w x ++ [true]) ≠ (lo x || x 0 || x 3))
    (negative :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (i : ℕ), FanInTwo p → FanInTwo t →
        p.size + t.size ≤ 13 → 8 ≤ i → i < 8 + p.size →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let u := fun x : Fin 8 → Bool => (w x).getD i false
        (∀ x, lo x = false → (x 0 || x 3) = true → u x = true) →
        (∀ x, t.eval (w x ++ [u x]) = lo x) →
        ∃ x, t.eval (w x ++ [false]) ≠ (lo x || x 0 || x 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let input := fun (b : Bool) (x : Fin 8 → Bool) =>
    [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
  dsimp only
  intro D fan size _readers low
  by_contra! high
  change ∀ x, D.eval (input false x) = lo x at low
  change ∀ x, D.eval (input true x) = (lo x || x 0 || x 3) at high
  have witnesses (j : Fin 8) (d : Bool) :
      ∃ x : Fin 8 → Bool, lo x = false ∧ (x 0 || x 3) = true ∧ x j = d := by
    dsimp [lo]
    fin_cases j <;> cases d <;> decide +kernel
  let hi := fun x : Fin 8 → Bool => lo x || x 0 || x 3
  have cofactor_ne : lo ≠ hi := by
    intro e
    obtain ⟨x, hx, hz, _⟩ := witnesses 0 true
    have he := congrFun e x
    change lo x = (lo x || x 0 || x 3) at he
    rw [hx, Bool.false_or, hz] at he
    contradiction
  let prep : Circuit := ⟨⟨.not, [4]⟩ :: D.gates, D.output⟩
  have prepFan : FanInTwo prep := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact fan g hg
  have prepSize : prep.size ≤ 15 := by
    change D.gates.length + 1 ≤ 15
    change D.gates.length ≤ 14 at size
    omega
  -- The initial NOT gate appends the tenth wire of the posted input list.
  have keep (i : ℕ) (gs : List Gate) (ys : List Bool) (h : i < ys.length) :
      (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
        ys).getD i false = ys.getD i false := by
    induction gs generalizing ys with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have nth (x : Fin 9 → Bool) : (List.ofFn x).getD 4 false = x 4 := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact congrArg x (Fin.ext rfl)
  have first (x : Fin 9 → Bool) : (prep.wires (List.ofFn x)).getD 9 false = !x 4 := by
    change (D.gates.foldl (fun acc g => acc ++ [g.op.eval
      (g.inputs.map fun k => acc.getD k false)])
      (List.ofFn x ++ [!((List.ofFn x).getD 4 false)])).getD 9 false = !x 4
    rw [keep _ _ _ (by simp), nth]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have slices (x : Fin 8 → Bool) (b : Bool) :
      prep.eval ((List.ofFn x).insertIdx 4 b) = if b = true then hi x else lo x := by
    have he : (List.ofFn x).insertIdx 4 b = [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7] := by
      simp only [List.ofFn_succ, List.ofFn_zero, List.insertIdx_succ_cons, List.insertIdx_zero]
      rfl
    rw [he]
    change D.eval (input b x) = if b = true then hi x else lo x
    cases b
    · simpa using low x
    · simpa [hi] using high x
  rcases normalize prep lo hi prepFan prepSize first slices cofactor_ne with hsmall | split
  · exact cofactor hsmall
  obtain ⟨p, t, i, d, fp, ft, bound, valid, sim⟩ := split
  let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
  let u := fun x : Fin 8 → Bool => (w x).getD i false
  have a (x : Fin 8 → Bool) : t.eval (w x ++ [u x]) = lo x := by
    simpa [w, u] using sim x false
  have b (x : Fin 8 → Bool) : t.eval (w x ++ [d]) = (lo x || x 0 || x 3) := by
    simpa [w, hi] using sim x true
  have sensitive (x : Fin 8 → Bool) (hx : lo x = false) (hz : (x 0 || x 3) = true) :
      u x = !d := by
    have clash : u x ≠ d := by
      intro e
      have eq := a x
      rw [e, b, hx, Bool.false_or, hz] at eq
      exact Bool.noConfusion eq
    cases d <;> cases e : u x <;> first | rfl | exact (clash e).elim
  have generated : 8 ≤ i := by
    by_contra! short
    let j : Fin 8 := ⟨i, short⟩
    obtain ⟨x, hx, hz, bit⟩ := witnesses j d
    have keep (gs : List Gate) (ys : List Bool) (h : i < ys.length) :
        (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
          ys).getD i false = ys.getD i false := by
      induction gs generalizing ys with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have value : u x = x j := by
      change (p.gates.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
        (List.ofFn x)).getD i false = x j
      have lt : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using short
      rw [keep _ _ lt, List.getD_eq_getElem _ _ lt, List.getElem_ofFn]
    have h := sensitive x hx hz
    rw [value, bit] at h
    cases d <;> exact Bool.noConfusion h
  cases d
  · obtain ⟨x, bad⟩ := negative p t i fp ft bound generated valid (fun x hx hz =>
      sensitive x hx hz) a
    exact bad (b x)
  · obtain ⟨x, bad⟩ := positive p t i fp ft bound valid a
    exact bad (b x)
