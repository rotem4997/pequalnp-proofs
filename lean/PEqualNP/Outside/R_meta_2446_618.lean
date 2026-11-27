import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Refines the suffix reduction in PR 5377 by requiring effective reads of
-- all ten suffix inputs. Out-of-range or ignored operands do not count.
theorem PEqualNP.Outside.R_meta_2446_618
    (minimum : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) 14)
    (binary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) →
      13 ≤ C.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)))
    (residual : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)),
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.output = 23 →
      12 ≤ D.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) →
      (∀ i : Fin 10, ∃ g ∈ D.gates, i.val ∈
        (bif GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op
          then g.inputs.take 1 else g.inputs)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 || x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  have runLength (l : List Gate) (w : List Bool) :
      (l.foldl step w).length = w.length + l.length := by
    induction l generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have keep (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (l.foldl step w).getD i false = w.getD i false := by
    induction l generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  let pairs : List (Fin 9 × Fin 9) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (4, 6)]

  let edgeFun (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let endpoint (p : Fin 9 × Fin 9) (side : Bool) : Fin 9 := if side then p.1 else p.2
  let partner (p : Fin 9 × Fin 9) (side : Bool) : Fin 9 := if side then p.2 else p.1

  let sample (u z : Fin 9) (i : Fin 9) : Bool := decide (i = u ∨ i = z)

  let seed (p : Fin 9 × Fin 9) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [x p.1 || x p.2]

  let agreeOff (u : ℕ) (left right : List Bool) : Prop :=
    left.length = right.length ∧ ∀ i, i ≠ u → left.getD i false = right.getD i false

  let effectiveInputs (gate : Gate) : List ℕ :=
    bif GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false gate.op
      then gate.inputs.take 1 else gate.inputs

  have evalEffective (gate : Gate) (w : List Bool) :
      gate.op.eval (gate.inputs.map fun i => w.getD i false) =
        gate.op.eval ((effectiveInputs gate).map fun i => w.getD i false) := by
    rcases gate with ⟨op, inputs⟩
    cases op <;> try rfl
    cases inputs <;> rfl

  have samplesSeparate : ∀ p ∈ pairs, ∀ b : Bool, ∃ z : Fin 9,
      let x := sample (partner p b) z
      let y := Function.update x (endpoint p b) true
      edgeFun x ≠ edgeFun y ∧ (x p.1 || x p.2) = (y p.1 || y p.2) := by
    decide +kernel

  have samplesSeparateOutside : ∀ p ∈ pairs, ∀ u : Fin 9,
      u ≠ p.1 → u ≠ p.2 → ∃ z : Fin 9,
      let x := fun i : Fin 9 => decide (i = z)
      let y := Function.update x u true
      edgeFun x ≠ edgeFun y ∧ (x p.1 || x p.2) = (y p.1 || y p.2) := by
    decide +kernel

  have agreement_append {u : ℕ} {left right : List Bool}
      (agreement : agreeOff u left right) (value : Bool) :
      agreeOff u (left ++ [value]) (right ++ [value]) := by
    obtain ⟨lengths, same⟩ := agreement
    refine ⟨by simpa using lengths, ?_⟩
    intro i hi
    by_cases h : i < left.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (lengths ▸ h)]
      exact same i hi
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      rw [lengths]

  have foldAgreement (u : ℕ) (gates : List Gate)
      (avoids : ∀ g ∈ gates, u ∉ effectiveInputs g) (left right : List Bool)
      (agreement : agreeOff u left right) :
      agreeOff u ((Circuit.mk gates 0).wires left) ((Circuit.mk gates 0).wires right) := by
    induction gates generalizing left right with
    | nil => exact agreement
    | cons gate rest ih =>
      let eval (w : List Bool) := gate.op.eval (gate.inputs.map fun j => w.getD j false)
      have equal : eval left = eval right := by
        unfold eval
        rw [evalEffective, evalEffective]
        apply congrArg gate.op.eval
        apply List.map_congr_left
        intro j hj
        apply agreement.2 j
        intro same
        exact avoids gate (by simp) (same ▸ hj)
      change agreeOff u ((Circuit.mk rest 0).wires (left ++ [eval left]))
        ((Circuit.mk rest 0).wires (right ++ [eval right]))
      rw [← equal]
      exact ih (fun g hg => avoids g (List.mem_cons_of_mem _ hg)) _ _
        (agreement_append agreement _)

  have seedAgreement {p : Fin 9 × Fin 9} {x y : Fin 9 → Bool} {u : Fin 9}
      (same : ∀ i : Fin 9, i ≠ u → x i = y i)
      (orSame : (x p.1 || x p.2) = (y p.1 || y p.2)) :
      agreeOff u.val (seed p x) (seed p y) := by
    unfold seed
    rw [← orSame]
    refine agreement_append ⟨by simp, ?_⟩ _
    intro i hi
    by_cases input : i < 9
    · rw [List.getD_eq_getElem _ _ (by simpa using input),
        List.getD_eq_getElem _ _ (by simpa using input), List.getElem_ofFn, List.getElem_ofFn]
      exact same ⟨i, input⟩ (fun eq => hi (congrArg Fin.val eq))
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have suffix_reader_of_samples (p : Fin 9 × Fin 9)
      (D : Circuit) (validOutput : 9 ≤ D.output)
      (computes : ∀ x : Fin 9 → Bool, D.eval (seed p x) = edgeFun x)
      (u : Fin 9) (x : Fin 9 → Bool)
      (differs : edgeFun x ≠ edgeFun (Function.update x u true))
      (orSame : (x p.1 || x p.2) =
        (Function.update x u true p.1 || Function.update x u true p.2)) :
      ∃ g ∈ D.gates, u.val ∈ effectiveInputs g := by
    by_contra! avoids
    let y := Function.update x u true
    have same : ∀ i : Fin 9, i ≠ u → x i = y i := by
      intro i distinct
      exact (Function.update_of_ne distinct true x).symm
    have agreement := seedAgreement same orSame
    have after := foldAgreement u.val D.gates avoids (seed p x) (seed p y) agreement
    have outputs := after.2 D.output (by have := u.isLt; omega)
    change D.eval (seed p x) = D.eval (seed p y) at outputs
    exact differs ((computes x).symm.trans (outputs.trans (computes y)))

  have endpoint_has_suffix_reader (p : Fin 9 × Fin 9) (hp : p ∈ pairs)
      (D : Circuit) (validOutput : 9 ≤ D.output)
      (computes : ∀ x : Fin 9 → Bool, D.eval (seed p x) = edgeFun x)
      (side : Bool) : ∃ g ∈ D.gates, (endpoint p side).val ∈ effectiveInputs g := by
    obtain ⟨z, differs, orSame⟩ := samplesSeparate p hp side
    exact suffix_reader_of_samples p D validOutput computes (endpoint p side) (sample (partner p side) z)
      differs orSame

  have every_input_has_suffix_reader (p : Fin 9 × Fin 9) (hp : p ∈ pairs)
      (D : Circuit) (validOutput : 9 ≤ D.output)
      (computes : ∀ x : Fin 9 → Bool, D.eval (seed p x) = edgeFun x)
      (u : Fin 9) : ∃ g ∈ D.gates, u.val ∈ effectiveInputs g := by
    by_cases first : u = p.1
    · simpa [first, endpoint] using endpoint_has_suffix_reader p hp D validOutput computes true
    by_cases second : u = p.2
    · simpa [second, endpoint] using endpoint_has_suffix_reader p hp D validOutput computes false
    obtain ⟨z, differs, orSame⟩ := samplesSeparateOutside p hp u first second
    exact suffix_reader_of_samples p D validOutput computes u (fun i => decide (i = z)) differs orSame

  let lowerWire (i : ℕ) : ℕ := if i < 9 then i else if i = 9 then 0 else i - 1

  let lowerGate (g : Gate) : Gate := ⟨g.op, g.inputs.map lowerWire⟩

  let lowers (long short : List Bool) : Prop :=
    short.length ≥ 9 ∧ long.length = short.length + 1 ∧
    ∀ i, long.getD i false = short.getD (lowerWire i) false

  have lowerWire_inside {n i : ℕ} (nBig : 9 ≤ n) :
      lowerWire i < n ↔ i < n + 1 := by
    unfold lowerWire
    split <;> rename_i h
    · omega
    · split <;> omega

  have lowerWire_outside {n i : ℕ} (nBig : 9 ≤ n) (outside : n + 1 ≤ i) :
      lowerWire i - n = i - (n + 1) := by
    unfold lowerWire
    split <;> rename_i h
    · omega
    · split <;> omega

  have lowers_append {long short : List Bool} (h : lowers long short) (b : Bool) :
      lowers (long ++ [b]) (short ++ [b]) := by
    obtain ⟨big, lengthEq, agrees⟩ := h
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro i
    by_cases iLow : i < long.length
    · have kLow : lowerWire i < short.length := (lowerWire_inside big).2 (lengthEq ▸ iLow)
      rw [List.getD_append _ _ _ _ iLow, List.getD_append _ _ _ _ kLow]
      exact agrees i
    · have kHigh : short.length ≤ lowerWire i := by
        by_contra! h
        exact iLow (lengthEq.symm ▸ (lowerWire_inside big).1 h)
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ kHigh,
        lowerWire_outside big (by omega : short.length + 1 ≤ i), lengthEq]

  have lowers_initial (x : Fin 9 → Bool) :
      lowers (List.ofFn x ++ [x 0]) (List.ofFn x) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    have lengthX : (List.ofFn x).length = 9 := List.length_ofFn
    by_cases inBounds : i < 9
    · rw [show lowerWire i = i by simp [lowerWire, inBounds], List.getD_append _ _ _ _ (by omega)]
    by_cases last : i = 9
    · subst i
      simp [lowerWire]
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by rw [lengthX]; exact Nat.le_of_not_gt (fun h => by
        have := (lowerWire_inside (n := 9) (by omega)).1 h
        omega))]

  have lowers_wires (gates : List Gate) (long short : List Bool)
      (agrees : lowers long short) :
      lowers ((Circuit.mk gates 0).wires long) ((Circuit.mk (gates.map lowerGate) 0).wires short) := by
    induction gates generalizing long short with
    | nil => exact agrees
    | cons g gs ih =>
      let evalIn (gate : Gate) (w : List Bool) := gate.op.eval (gate.inputs.map fun i => w.getD i false)
      have gateEq : evalIn g long = evalIn (lowerGate g) short := by
        unfold evalIn lowerGate
        dsimp only
        rw [List.map_map]
        exact congrArg g.op.eval (List.map_congr_left (fun i _ => agrees.2.2 i))
      change lowers ((Circuit.mk gs 0).wires (long ++ [evalIn g long]))
        ((Circuit.mk (gs.map lowerGate) 0).wires (short ++ [evalIn (lowerGate g) short]))
      rw [← gateEq]
      exact ih _ _ (lowers_append agrees _)

  have first_or_has_suffix_reader (p : Fin 9 × Fin 9) (D : Circuit)
      (validOutput : 10 ≤ D.output) (legal : FanInTwo D) (sizeBound : D.size ≤ 14)
      (computes : ∀ x : Fin 9 → Bool, D.eval (seed p x) = edgeFun x)
      (minimum : ¬ HasCircuitSize 9 edgeFun 14) :
      ∃ g ∈ D.gates, 9 ∈ effectiveInputs g := by
    by_contra! avoids
    let smaller : Circuit := ⟨D.gates.map lowerGate, lowerWire D.output⟩
    apply minimum
    refine ⟨smaller, ?_, ?_, ?_⟩
    · intro g mem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp mem
      simpa only [lowerGate, List.length_map] using legal g' hg'
    · change (D.gates.map lowerGate).length ≤ 14
      rw [List.length_map]
      exact sizeBound
    intro x
    have initial : agreeOff 9 (seed p x) (List.ofFn x ++ [x 0]) := by
      refine ⟨by simp [seed], ?_⟩
      intro i iOff
      by_cases iSmall : i < 9
      · unfold seed
        rw [List.getD_append _ _ _ _ (by simpa using iSmall),
          List.getD_append _ _ _ _ (by simpa using iSmall)]
      · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
    have firstEq := (foldAgreement 9 D.gates avoids _ _ initial).2 D.output (by omega)
    change D.eval (seed p x) = D.eval (List.ofFn x ++ [x 0]) at firstEq
    have lowerEq := (lowers_wires D.gates _ _ (lowers_initial x)).2.2 D.output
    change D.eval (List.ofFn x ++ [x 0]) = smaller.eval (List.ofFn x) at lowerEq
    exact lowerEq.symm.trans (firstEq.symm.trans (computes x))
  intro p hp C fan first computes
  have fEq : f = edgeFun := by
    funext x
    simp only [f, edgeFun, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have minGraph : ¬ HasCircuitSize 9 edgeFun 14 := by simpa only [← fEq] using minimum
  have eqf : circuitFun 9 C = f := by
    rw [computes]
    funext x
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  by_contra! small
  have exactSize : C.gates.length = 15 := by
    have lower : ¬ C.size ≤ 14 := fun h => minimum ⟨C,fan,h,congrFun eqf⟩
    change C.gates.length < 16 at small
    change ¬ C.gates.length ≤ 14 at lower
    omega
  have outputLast : C.output = 23 := by
    have valid : C.output < 24 := by
      by_contra! outside
      let x : Fin 9 → Bool := fun _ => true
      have on : (C.gates.foldl step (List.ofFn x)).getD C.output false = true :=
        (congrFun eqf x).trans (by decide)
      rw [List.getD_eq_default _ _ (by rw [runLength, List.length_ofFn, exactSize]; omega)] at on
      contradiction
    by_contra earlier
    let A : Circuit := ⟨C.gates.take 14, C.output⟩
    apply minimum
    refine ⟨A, fun g hg => fan g (List.mem_of_mem_take hg), ?_, ?_⟩
    · change (C.gates.take 14).length ≤ 14
      simp
    · intro x
      have eq := congrFun eqf x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = f x at eq
      rw [← List.take_append_drop 14 C.gates, List.foldl_append, keep] at eq
      · exact eq
      · rw [runLength, List.length_ofFn, List.length_take, exactSize]
        omega
  cases gates : C.gates with
  | nil => simp [gates] at exactSize
  | cons g gs =>
    let D : Circuit := ⟨gs, C.output⟩
    have fanD : FanInTwo D := fun h hh => fan h (by rw [gates]; exact List.mem_cons_of_mem g hh)
    have sizeD : D.size = 14 := by
      change gs.length = 14
      simp [gates] at exactSize
      omega
    have enough : 12 ≤ D.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) := by
      have bound := binary C fan eqf
      let pred := fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)
      change 13 ≤ C.gates.countP pred at bound
      rw [gates] at bound
      change 12 ≤ gs.countP _
      have inc : (g :: gs).countP pred ≤ gs.countP pred + 1 := by
        rw [List.countP_cons]
        split <;> omega
      change 12 ≤ gs.countP pred
      omega
    have evalD : ∀ x, D.eval (seed p x) = edgeFun x := by
      intro x
      let w := List.ofFn x
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      have atNine : (w ++ [v]).getD 9 false = v := by simp [w]
      have val := first x
      change (C.gates.foldl step w).getD 9 false = _ at val
      rw [gates, List.foldl_cons, keep] at val
      · change (w ++ [v]).getD 9 false = _ at val
        rw [atNine] at val
        have h := congrFun eqf x
        change (C.gates.foldl step w).getD C.output false = f x at h
        rw [gates, List.foldl_cons] at h
        change (gs.foldl step (w ++ [v])).getD C.output false = _ at h
        rw [val] at h
        exact h.trans (congrFun fEq x)
      · simp [step,w]
    have lastD : D.output = 23 := outputLast
    have everyWire (i : Fin 10) : ∃ g ∈ D.gates, i.val ∈ effectiveInputs g := by
      by_cases raw : i.val < 9
      · exact every_input_has_suffix_reader p hp D (by omega) evalD ⟨i.val, raw⟩
      · have nine : i.val = 9 := by omega
        rw [nine]
        exact first_or_has_suffix_reader p D (by omega) fanD (by omega) evalD minGraph
    obtain ⟨x, miss⟩ := residual p hp D fanD sizeD lastD enough everyWire
    exact miss ((evalD x).trans (congrFun fEq x).symm)
