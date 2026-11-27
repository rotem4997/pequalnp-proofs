import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reattach the first two gates before counting effective reads of input four.
-- Its false restriction is the checked eight-input minor.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1868_2 :
  (let readers := fun C : Circuit => C.gates.countP fun g =>
      (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
    ∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) →
  (let readers := fun C : Circuit => C.gates.countP fun g =>
      (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
    let assemble := fun (tail : Circuit) (pins : List (Fin 11)) =>
      (⟨⟨GateOp.and, [0, 3]⟩ :: ⟨GateOp.or, pins.map Fin.val⟩ :: tail.gates, tail.output⟩ : Circuit)
    ∀ (tail : Circuit) (pins : List (Fin 11)), FanInTwo tail → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool,
        let base := List.ofFn x ++ [x 0 && x 3]
        tail.eval (base ++ [GateOp.or.eval (pins.map fun i => base.getD i.val false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      readers (assemble tail pins) ≤ 2 → 14 ≤ tail.size) →
  (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro eliminate sparse minor tail pins legal arity correct
  let readers := fun C : Circuit => C.gates.countP fun g =>
    (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
  let assemble := fun (tail : Circuit) (pins : List (Fin 11)) =>
    (⟨⟨GateOp.and, [0, 3]⟩ :: ⟨GateOp.or, pins.map Fin.val⟩ :: tail.gates, tail.output⟩ : Circuit)
  change (∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) at eliminate
  change (∀ (tail : Circuit) (pins : List (Fin 11)), FanInTwo tail → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool,
        let base := List.ofFn x ++ [x 0 && x 3]
        tail.eval (base ++ [GateOp.or.eval (pins.map fun i => base.getD i.val false)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      readers (assemble tail pins) ≤ 2 → 14 ≤ tail.size) at sparse
  let C := assemble tail pins
  by_cases many : 3 ≤ readers C
  · by_contra tooSmall
    have sizeC : C.size = tail.size + 2 := rfl
    have legalC : FanInTwo C := by
      change ∀ g ∈ (⟨GateOp.and, [0, 3]⟩ : Gate) ::
        ⟨GateOp.or, pins.map Fin.val⟩ :: tail.gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Set.mem_insert _ _, by decide⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · refine ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), ?_⟩
        change (pins.map Fin.val).length ≤ 2
        simpa only [List.length_map] using arity
      · exact legal g hg
    let step (values : List Bool) (gate : Gate) :=
      values ++ [gate.op.eval (gate.inputs.map fun i => values.getD i false)]
    have readInput (x : Fin 9 → Bool) (i : Fin 9) :
        (List.ofFn x).getD i.val false = x i := by
      have bound : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
      simp only [Option.getD_some, List.getElem_ofFn]
    have firstStep (x : Fin 9 → Bool) :
        step (List.ofFn x) ⟨GateOp.and, [0, 3]⟩ = List.ofFn x ++ [x 0 && x 3] := by
      have input0 : (List.ofFn x).getD 0 false = x 0 := readInput x 0
      have input3 : (List.ofFn x).getD 3 false = x 3 := readInput x 3
      change List.ofFn x ++ [GateOp.and.eval [(List.ofFn x).getD 0 false,
        (List.ofFn x).getD 3 false]] = _
      rw [input0, input3]
      change List.ofFn x ++ [x 0 && (x 3 && true)] = _
      rw [Bool.and_true]
    have secondStep (base : List Bool) :
        step base ⟨GateOp.or, pins.map Fin.val⟩ =
          base ++ [GateOp.or.eval (pins.map fun i => base.getD i.val false)] := by
      change base ++ [GateOp.or.eval ((pins.map Fin.val).map fun i => base.getD i false)] = _
      simp only [List.map_map, Function.comp_def]
    have correctC (x : Fin 9 → Bool) : circuitFun 9 C x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      change (List.foldl step (List.ofFn x) ((⟨GateOp.and, [0, 3]⟩ : Gate) ::
        ⟨GateOp.or, pins.map Fin.val⟩ :: tail.gates)).getD tail.output false = _
      simp only [List.foldl_cons]
      rw [firstStep, secondStep]
      exact correct x
    have restriction (x : Fin 8 → Bool) :
        circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) x := by
      let ins : Fin 9 → Bool := Fin.insertNth (4 : Fin 9) false x
      have hi (j : Fin 8) : ins ((4 : Fin 9).succAbove j) = x j :=
        Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x j
      have h0 : ins 0 = x 0 := hi 0
      have h1 : ins 1 = x 1 := hi 1
      have h2 : ins 2 = x 2 := hi 2
      have h3 : ins 3 = x 3 := hi 3
      have h4 : ins 4 = false :=
        Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x
      have h5 : ins 5 = x 4 := hi 4
      have h6 : ins 6 = x 5 := hi 5
      have h7 : ins 7 = x 6 := hi 6
      have h8 : ins 8 = x 7 := hi 7
      calc
        _ = ((ins 0 && ins 1) || (ins 1 && ins 2) || (ins 2 && ins 3) || (ins 3 && ins 4) ||
          (ins 4 && ins 0) || (ins 0 && ins 5) || (ins 1 && ins 6) || (ins 2 && ins 7) ||
          (ins 3 && ins 8) || (ins 5 && ins 7) || (ins 6 && ins 8) || (ins 8 && ins 5)) := correctC ins
        _ = _ := by simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8,
          Bool.false_and, Bool.and_false, Bool.or_false]
    have notTrue : circuitFun 9 C (Fin.insertNth (4 : Fin 9) false (fun _ => false)) = false :=
      restriction (fun _ => false)
    obtain ⟨D, legalD, saving, evalD⟩ := eliminate C legalC many ⟨_, notTrue⟩
    apply minor
    refine ⟨D, legalD, by omega, ?_⟩
    intro x
    exact (congrFun evalD x).trans (restriction x)
  · have few : readers C ≤ 2 := by omega
    exact sparse tail pins legal arity correct few
