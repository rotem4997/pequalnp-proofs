import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3024_561
    (paired : ∀ i : Fin 11, (i = 0 ∨ i = 3 ∨ i = 4) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 13 → ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 2]
          D.eval (w ++ [!(w.getD i.val false)]) ≠
            ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
              List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (fixed : ∀ i : Fin 11, (i = 1 ∨ i = 6 ∨ i = 8) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 13 → ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 2]
          D.eval (w ++ [!(w.getD i.val false)]) ≠
            ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
              List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (special : ∀ i : Fin 11, (i = 9 ∨ i = 10) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 13 → ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 2]
          D.eval (w ++ [!(w.getD i.val false)]) ≠
            ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
              List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : List (Fin (11 : ℕ))), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
            (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
             x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
             x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins _ C fan size
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  let inputs (x : Fin 9 → Bool) (i : Fin 11) :=
    seed x ++ [!((seed x).getD i.val false)]
  let target (x : Fin 9 → Bool) :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let symmetry : Fin 9 → Fin 9 := ![2,1,0,5,7,3,6,4,8]
  let wire (i : ℕ) : ℕ := if h : i < 9 then (symmetry ⟨i, h⟩).val else i
  have targetSymmetry : ∀ x, target (x ∘ symmetry) = target x := by
    decide +kernel
  have seedLength (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
  have wireFixed (i : ℕ) (h : 9 ≤ i) : wire i = i := by
    simp [wire, Nat.not_lt.mpr h]
  have seedSymmetry (x : Fin 9 → Bool) (i : ℕ) :
      (seed (x ∘ symmetry)).getD i false = (seed x).getD (wire i) false := by
    by_cases h : i < 10
    · interval_cases i <;> first | rfl | exact Bool.or_comm _ _
    · rw [wireFixed i (by omega)]
      rw [List.getD_eq_default _ _ (by rw [seedLength]; omega),
        List.getD_eq_default _ _ (by rw [seedLength]; omega)]
  have extend {w w' : List Bool} (len : w'.length = w.length) (lower : 9 ≤ w.length)
      (agree : ∀ i, w'.getD i false = w.getD (wire i) false) (b : Bool) (i : ℕ) :
      (w' ++ [b]).getD i false = (w ++ [b]).getD (wire i) false := by
    by_cases hi : i < w.length
    · have hi' : i < w'.length := by omega
      have wi : wire i < w.length := by
        by_cases h : i < 9
        · exact lt_of_lt_of_le (show wire i < 9 from by
            simp [wire, h]) lower
        · rwa [wireFixed i (by omega)]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi',
        List.getElem?_append_left wi] using agree i
    · rw [wireFixed i (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w'.length ≤ i),
        List.getElem?_append_right (by omega : w.length ≤ i), len]
  let mapGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map wire⟩
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have folds (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool)
      (len : w'.length = w.length) (lower : 9 ≤ w.length)
      (agree : ∀ i, w'.getD i false = w.getD (wire i) false) (i : ℕ) :
      (gs.foldl step w').getD i false = ((gs.map mapGate).foldl step w).getD (wire i) false := by
    induction gs generalizing w w' with
    | nil => exact agree i
    | cons g gs ih =>
      have mapValues : g.inputs.map (fun j => w'.getD j false) =
          (mapGate g).inputs.map (fun j => w.getD j false) := by
        simp only [mapGate, List.map_map]
        exact congrArg (fun f => g.inputs.map f) (funext agree)
      simp only [List.foldl_cons, List.map_cons]
      apply ih (step w (mapGate g)) (step w' g)
      · simp [step, len]
      · simp [step]; omega
      · intro j
        simp only [step, mapValues]
        exact extend len lower agree _ j
  let reflected : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map mapGate, wire C.output⟩
  have reflectedFan : PEqualNP.MetaComplexity.FanInTwo reflected := by
    intro g hg
    change g ∈ C.gates.map mapGate at hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using fan k hk
  have reflectedSize : reflected.size ≤ 13 := by
    change (C.gates.map mapGate).length ≤ 13
    change C.gates.length ≤ 13 at size
    simpa only [List.length_map] using size
  have reflect (i j : Fin 11) (hij : wire i.val = j.val)
      (witness : ∃ x, reflected.eval (inputs x j) ≠ target x) :
      ∃ x, C.eval (inputs x i) ≠ target x := by
    obtain ⟨x, hx⟩ := witness
    have notSame : (!((seed (x ∘ symmetry)).getD i.val false)) =
        (!((seed x).getD j.val false)) := by
      rw [seedSymmetry, hij]
    have values : ∀ k, (inputs (x ∘ symmetry) i).getD k false =
        (inputs x j).getD (wire k) false := by
      intro k
      simp only [inputs, notSame]
      exact extend (by simp [seedLength]) (by simp [seedLength]) (seedSymmetry x) _ k
    have lengthInputs (y : Fin 9 → Bool) (k : Fin 11) : (inputs y k).length = 11 := by
      simp [inputs, seedLength]
    have equality := folds C.gates (inputs x j) (inputs (x ∘ symmetry) i)
      (by simp [lengthInputs]) (by simp [lengthInputs]) values C.output
    change C.eval (inputs (x ∘ symmetry) i) = reflected.eval (inputs x j) at equality
    exact ⟨x ∘ symmetry, by rw [equality, targetSymmetry]; exact hx⟩
  have representatives (i : Fin 11) : ∃ x, C.eval (inputs x i) ≠ target x := by
    fin_cases i
    · exact paired 0 (by decide) C fan size
    · exact fixed 1 (by decide) C fan size
    · exact reflect 2 0 rfl (paired 0 (by decide) reflected reflectedFan reflectedSize)
    · exact paired 3 (by decide) C fan size
    · exact paired 4 (by decide) C fan size
    · exact reflect 5 3 rfl (paired 3 (by decide) reflected reflectedFan reflectedSize)
    · exact fixed 6 (by decide) C fan size
    · exact reflect 7 4 rfl (paired 4 (by decide) reflected reflectedFan reflectedSize)
    · exact fixed 8 (by decide) C fan size
    · exact special 9 (by decide) C fan size
    · exact special 10 (by decide) C fan size
  obtain ⟨x, hx⟩ := representatives (pins.headD 10)
  have notHead : PEqualNP.CircuitLowerBounds.GateOp.not.eval
      (pins.map fun i => (seed x).getD i.val false) =
      !((seed x).getD (pins.headD 10).val false) := by
    cases pins with
    | nil =>
      change true = !((seed x).getD 10 false)
      rw [List.getD_eq_default _ _ (by simp [seedLength])]
      rfl
    | cons i rest => rfl
  refine ⟨x, ?_⟩
  simpa only [inputs, target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc, ← notHead] using hx
