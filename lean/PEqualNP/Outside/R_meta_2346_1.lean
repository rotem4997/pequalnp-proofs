import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2346_1
    (traceSound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C →
      ∀ (r : Bool) (v : ℕ → Bool),
      let t : Fin 14 := if r then 0 else 7
      let s : ℕ := if r then 7 else 0
      let z := C.wires (List.ofFn fun k : Fin 14 => decide (k=t))
      (∀ i < 14, v i = decide (i=s)) →
      (∀ j < C.size,
        let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
        let a := PEqualNP.TopForm.opnd C j 0
        let b := PEqualNP.TopForm.opnd C j 1
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          v (14+j) = ((z.getD a false && v b) || (v a && z.getD b false))) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14+j) = (v a || v b))) →
      v C.output = false →
      PEqualNP.ReadK.lineSingle C 14 (fun i => if r then decide (7 ≤ i) else !decide (7 ≤ i)) 0 7 = false)
    (extremalTests : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
      (∀ j < C.size, PEqualNP.TopForm.opnd C j 0 ≠ PEqualNP.TopForm.opnd C j 1) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      let D : Finset (Fin 7) := {0,1,3}
      (∀ p l : Fin 7, p-l ∈ D → C.eval (List.ofFn fun k : Fin 14 =>
        decide (k = Fin.castAdd 7 p ∨ k = Fin.natAdd 7 l)) = true) →
      (∀ P : Finset (Fin 7),
        let L := Finset.univ.filter fun l => ∀ p ∈ P, p-l ∉ D
        (∀ p ∉ P, ∃ l ∈ L, p-l ∈ D) →
        C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)))) = false) →
      PEqualNP.ReadK.IsSingleRead C 14 (fun i => decide (7 ≤ i)) [(0,7)]) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C size ao distinct first spec deriv
  let D : Finset (Fin 7) := {0,1,3}
  have incident : ∀ p l : Fin 7, p-l ∈ D ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide
  have positives (p l : Fin 7) (h : p-l ∈ D) :
      C.eval (List.ofFn fun k : Fin 14 => decide (k = Fin.castAdd 7 p ∨ k = Fin.natAdd 7 l)) = true :=
    (spec _).mpr ⟨p,l,(incident p l).mp h,by simp,by simp⟩
  have negatives (P : Finset (Fin 7)) :
      let L := Finset.univ.filter fun l => ∀ p ∈ P, p-l ∉ D
      (∀ p ∉ P, ∃ l ∈ L, p-l ∈ D) →
      C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)))) = false := by
    intro L _
    cases h : C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)))) with
    | false => rfl
    | true =>
      obtain ⟨p,l,edge,hp,hl⟩ := (spec _).mp h
      have hP : p ∈ P := by simpa only [Fin.addCases_left, decide_eq_true_eq] using hp
      have hL : l ∈ L := by simpa only [Fin.addCases_right, decide_eq_true_eq] using hl
      exact ((Finset.mem_filter.mp hL).2 p hP ((incident p l).mpr edge)).elim
  have single := extremalTests C size ao distinct first positives negatives
  have trace (r : Bool) :
      PEqualNP.ReadK.lineSingle C 14 (fun i => if r then decide (7 ≤ i) else !decide (7 ≤ i)) 0 7 = false := by
    obtain ⟨v,init,step,out⟩ := deriv r
    exact traceSound C ao r v init step out
  have left := trace true
  have right := trace false
  simp only [Bool.false_eq_true, ite_true, ite_false] at left right
  change ([(0,7)] : List (ℕ × ℕ)).filter (fun e =>
    !(PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) e.1 e.2) &&
    !(PEqualNP.ReadK.lineSingle C 14 (fun i => !decide (7 ≤ i)) e.1 e.2)) = [] at single
  simp [left, right] at single
