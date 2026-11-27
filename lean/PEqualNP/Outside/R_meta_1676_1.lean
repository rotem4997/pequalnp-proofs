import Mathlib
import PEqualNP.Defs

/-- A cut of L-meta-1676 by the operation of the second gate, or its absence. -/
theorem PEqualNP.Outside.R_meta_1676_1
    (hAnd : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.and → 16 ≤ C.size)
    (hOr : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.or → 16 ≤ C.size)
    (hNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.not → 16 ≤ C.size)
    (hNone : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]? = none → 16 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hFan hFirst hFun
  cases h : C.gates[1]? with
  | none =>
    exact hNone C hFan hFirst hFun h
  | some g =>
    have hlen : 1 < C.gates.length := by
      obtain ⟨hlt, _⟩ := (List.getElem?_eq_some_iff).1 h
      exact hlt
    have hg : C.gates[1] = g := by
      obtain ⟨_, heq⟩ := (List.getElem?_eq_some_iff).1 h
      exact heq
    have mem : g ∈ C.gates := by
      rw [← hg]
      exact List.getElem_mem hlen
    have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      have hin := (hFan g mem).1
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hin
      exact hin
    have hmap : C.gates[1]?.map (fun x => x.op) = some g.op := by
      rw [h]; rfl
    rcases hop with han | hor | hn
    · exact hAnd C hFan hFirst hFun (hmap.trans (congrArg some han))
    · exact hOr C hFan hFirst hFun (hmap.trans (congrArg some hor))
    · exact hNot C hFan hFirst hFun (hmap.trans (congrArg some hn))
