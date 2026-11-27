import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3382_741
    (dropOrReaders : ∀ (n : ℕ) (C : Circuit) (p : List (Option (Fin n))) (k : ℕ),
      FanInTwo C → p[k]? = some none →
      (∃ x y : Fin n → Bool,
        C.eval (p.map (fun q => q.elim false x)) ≠ C.eval (p.map (fun q => q.elim false y))) →
      ∃ D : Circuit, FanInTwo D ∧
        D.size + (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains k)).length ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (p.map (fun q => q.elim false x)))
    (sixCycleLower : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 0 && x 3) || (x 1 && x 4) ||
          (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5))) → 8 ≤ C.size)
    (twoReaders :
      let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,36] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
      ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → C.size = 11 → circuitFun 7 C = f →
        List.Forall₂ (fun g h : Gate => g.op = h.op ∧
          List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i=a ∨ i=b)) g.inputs h.inputs) C.gates D.gates →
        (∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (f x || x 2)) →
        (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 2 → False)
    (threeReaders :
      let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,36] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
      ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → C.size = 11 → circuitFun 7 C = f →
        List.Forall₂ (fun g h : Gate => g.op = h.op ∧
          List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i=a ∨ i=b)) g.inputs h.inputs) C.gates D.gates →
        (∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (f x || x 2)) →
        (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 3 → False) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fan size base edits modified
  dsimp only at twoReaders threeReaders
  let p : List (Option (Fin 6)) := [some 0,some 1,none,some 2,some 3,some 4,some 5]
  let lift (x : Fin 6 → Bool) : Fin 7 → Bool := ![x 0,x 1,false,x 2,x 3,x 4,x 5]
  let cyc (x : Fin 6 → Bool) := (x 0 && x 1) || (x 0 && x 3) ||
    (x 1 && x 4) || (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5)
  have geometry : ∀ x : Fin 6 → Bool, f (lift x) = cyc x := by
    dsimp only [f,lift,cyc]
    decide +kernel
  have projected (x : Fin 6 → Bool) : C.eval (p.map (fun q => q.elim false x)) = cyc x := by
    have pins : p.map (fun q => q.elim false x) = List.ofFn (lift x) := rfl
    rw [pins]
    exact (congrFun base (lift x)).trans (geometry x)
  have nonconstant : ∃ x y : Fin 6 → Bool,
      C.eval (p.map (fun q => q.elim false x)) ≠ C.eval (p.map (fun q => q.elim false y)) := by
    refine ⟨(fun _ => false), ![true,true,false,false,false,false],?_⟩
    rw [projected,projected]
    decide
  obtain ⟨E,fanE,cost,values⟩ := dropOrReaders 6 C p 2 fan (by decide) nonconstant
  have cycleE : ∀ x : Fin 6 → Bool, E.eval (List.ofFn x) = cyc x := by
    intro x
    exact (values x).trans (projected x)
  have lower := sixCycleLower E fanE cycleE
  have atMostThree :
      (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length ≤ 3 := by
    omega
  by_contra h
  have cases :
      (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 2 ∨
      (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length = 3 := by
    omega
  rcases cases with two | three
  · exact twoReaders C D a b fan size base edits modified two
  · exact threeReaders C D a b fan size base edits modified three
