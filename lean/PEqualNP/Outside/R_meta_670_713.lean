import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_670_713
    (normalize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
        ((∃ i ∈ ([0,4] : List (Fin 9)), ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = !(x i)) ∨
        (∃ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∃ b : Bool, ∀ x : Fin 9 → Bool,
          (D.wires (List.ofFn x)).getD 9 false = if b then x p.1 && x p.2 else x p.1 || x p.2)))
    (unary : ∀ i ∈ ([0,4] : List (Fin 9)), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = !(x i)) →
      circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ D.size)
    (both : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x p.1 && x p.2)) →
      circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ D.size)
    (either : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x p.1 || x p.2)) →
      circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ D.size) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,legal,small,computes⟩
  have hc : circuitFun 9 C = _ := funext computes
  obtain ⟨D,hd,hle,heq,hfirst⟩ := normalize C legal hc
  have graph := heq.trans hc
  have lower : 16 ≤ D.size := by
    rcases hfirst with ⟨i,hi,h⟩ | ⟨p,hp,b,h⟩
    · exact unary i hi D hd h graph
    · cases b with
      | false => exact either p hp D hd h graph
      | true => exact both p hp D hd h graph
  omega
