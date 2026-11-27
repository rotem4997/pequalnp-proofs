import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Supply the forced first gate as a tenth input and split at the output operation.
-- Thirteen intermediate gates can access wires zero through twenty-two.
-- Wire twenty-three represents every read past the currently available wires.
theorem PEqualNP.Outside.R_meta_1672_1 :
  (∀ (middle : List Gate) (pins : List (Fin 24)), middle.length ≤ 13 →
    FanInTwo ⟨middle, 0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    pins.length ≤ 2 → ∃ x : Fin 9 → Bool,
      let wires := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 4 && x 6])
      GateOp.and.eval (pins.map fun i => wires.getD i.val false) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (middle : List Gate) (pins : List (Fin 24)), middle.length ≤ 13 →
    FanInTwo ⟨middle, 0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    pins.length ≤ 2 → ∃ x : Fin 9 → Bool,
      let wires := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 4 && x 6])
      GateOp.or.eval (pins.map fun i => wires.getD i.val false) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (middle : List Gate) (pins : List (Fin 24)), middle.length ≤ 13 →
    FanInTwo ⟨middle, 0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    pins.length ≤ 2 → ∃ x : Fin 9 → Bool,
      let wires := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 4 && x 6])
      GateOp.not.eval (pins.map fun i => wires.getD i.val false) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) →
    PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    16 ≤ C.size := by
  intro andCase orCase notCase circuit fan first correct
  by_contra insufficient
  have sizeLimit : circuit.size ≤ 15 := by omega
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 && x 6]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g rest ih =>
      obtain ⟨extra, heq, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
      change run rest (step w g) = _
      rw [heq]
      simp [step, List.append_assoc]
  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    obtain ⟨extra, heq, hlen⟩ := extend gs w
    simp [heq, hlen]
  let clip := fun i : ℕ => (⟨min i 23, by omega⟩ : Fin 24)
  have sameRead (w : List Bool) (lengthBound : w.length ≤ 23) (i : ℕ) :
      w.getD (clip i).val false = w.getD i false := by
    by_cases small : i ≤ 23
    · simp [clip, Nat.min_eq_left small]
    · have large : 23 ≤ i := by omega
      change w.getD (min i 23) false = _
      rw [Nat.min_eq_right large, List.getD_eq_default w false lengthBound,
        List.getD_eq_default w false (by omega : w.length ≤ i)]
  let norm := fun g : Gate => Gate.mk g.op (g.inputs.map fun i => (clip i).val)
  have normStep (w : List Bool) (g : Gate) (hw : w.length ≤ 23) :
      step w (norm g) = step w g := by
    simp only [step, norm, List.map_map, Function.comp_def, sameRead w hw]
  have normRun (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 23) :
      run (gs.map norm) w = run gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      change run (rest.map norm) (step w (norm g)) = run rest (step w g)
      have hw' : w.length ≤ 23 := by omega
      rw [normStep w g hw']
      apply ih
      simp only [List.length_cons] at hw
      simp [step]
      omega
  have cut (middle : List Gate) (pins : List ℕ) (op : GateOp)
      (hsize : middle.length ≤ 13) (hfan : FanInTwo ⟨middle, 0⟩)
      (hpin : pins.length ≤ 2) (hop : op = .and ∨ op = .or ∨ op = .not) :
      ∃ x, op.eval (pins.map fun i => (run middle (seed x)).getD i false) ≠ target x := by
    let normalized := middle.map norm
    let inputs := pins.map clip
    have shortPrefix : normalized.length ≤ 13 := by simpa [normalized] using hsize
    have shortPins : inputs.length ≤ 2 := by simpa [inputs] using hpin
    have good : FanInTwo ⟨normalized, 0⟩ := by
      intro g hg
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan old hold).1, by simpa [norm] using (hfan old hold).2⟩
    have bounded : ∀ g ∈ normalized, ∀ i ∈ g.inputs, i ≤ 23 := by
      intro g hg i hi
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact min_le_right _ _
    have error : ∃ x, op.eval (inputs.map fun i =>
        (run normalized (seed x)).getD i.val false) ≠ target x := by
      rcases hop with rfl | rfl | rfl
      · exact andCase normalized inputs shortPrefix good bounded shortPins
      · exact orCase normalized inputs shortPrefix good bounded shortPins
      · exact notCase normalized inputs shortPrefix good bounded shortPins
    obtain ⟨x, hx⟩ := error
    have initial : (seed x).length + middle.length ≤ 23 := by
      simp [seed]
      omega
    rw [show run normalized (seed x) = run middle (seed x) from normRun middle (seed x) initial] at hx
    have nwire : (run middle (seed x)).length ≤ 23 := by rw [runLength]; exact initial
    refine ⟨x, ?_⟩
    simpa only [inputs, List.map_map, Function.comp_def, sameRead _ nwire] using hx
  have tap (middle : List Gate) (out : ℕ) (hs : middle.length ≤ 13)
      (hf : FanInTwo ⟨middle, 0⟩) :
      ∃ x, (run middle (seed x)).getD out false ≠ target x := by
    obtain ⟨x, hx⟩ := cut middle [out] .or hs hf (by simp) (Or.inr (Or.inl rfl))
    have readOne (b : Bool) : GateOp.or.eval [b] = b := by cases b <;> rfl
    change GateOp.or.eval [(run middle (seed x)).getD out false] ≠ target x at hx
    exact ⟨x, by rwa [readOne] at hx⟩
  obtain ⟨gs, out⟩ := circuit
  cases gs with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ false (by simp)] at h
    contradiction
  | cons g rest =>
    have firstValue (x : Fin 9 → Bool) :
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 && x 6) := by
      let w := List.ofFn x
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨extra, heq, _⟩ := extend rest (w ++ [value])
      have h := first x
      change (run rest (w ++ [value])).getD 9 false = _ at h
      rw [heq, List.getD_append _ _ false 9 (by simp [w]),
        List.getD_append_right w [value] false 9 (by simp [w])] at h
      simpa [value, w] using h
    have computes (x : Fin 9 → Bool) : (run rest (seed x)).getD out false = target x := by
      have h := congrFun correct x
      change (run rest (List.ofFn x ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD out false = target x at h
      rw [firstValue] at h
      exact h
    obtain hempty | ⟨middle, last, eqRest⟩ := List.eq_nil_or_concat' rest
    · subst rest
      have emptyFan : FanInTwo ⟨[], 0⟩ := by intro a ha; cases ha
      obtain ⟨x, hx⟩ := tap [] out (by decide) emptyFan
      exact hx (computes x)
    · subst rest
      have hs : middle.length ≤ 13 := by
        change (g :: (middle ++ [last])).length ≤ 15 at sizeLimit
        simp only [List.length_cons, List.length_append] at sizeLimit
        omega
      have hf : FanInTwo ⟨middle, 0⟩ := by
        intro a ha
        exact fan a (by simp [ha])
      have lastOK := fan last (by simp)
      let value := fun x : Fin 9 → Bool =>
        last.op.eval (last.inputs.map fun i => (run middle (seed x)).getD i false)
      have atOut (x : Fin 9 → Bool) :
          (run middle (seed x) ++ [value x]).getD out false = target x := by
        simpa only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, step, value]
          using computes x
      have lengthAt (x : Fin 9 → Bool) : (run middle (seed x)).length = 10 + middle.length := by
        rw [runLength]
        simp [seed]
      by_cases endWire : out = 10 + middle.length
      · have hop : last.op = .and ∨ last.op = .or ∨ last.op = .not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using lastOK.1
        obtain ⟨x, hx⟩ := cut middle last.inputs last.op hs hf lastOK.2 hop
        have h := atOut x
        rw [List.getD_append_right _ _ _ _ (by rw [lengthAt]; omega), lengthAt, endWire] at h
        exact hx (by simpa [value] using h)
      · obtain ⟨x, hx⟩ := tap middle out hs hf
        have h := atOut x
        by_cases early : out < (run middle (seed x)).length
        · rw [List.getD_append _ _ _ _ early] at h
          exact hx h
        · have beyond : (run middle (seed x)).length < out := by rw [lengthAt] at *; omega
          rw [List.getD_eq_default _ false (by simp; omega)] at h
          apply hx
          rw [List.getD_eq_default _ false (by omega)]
          exact h
