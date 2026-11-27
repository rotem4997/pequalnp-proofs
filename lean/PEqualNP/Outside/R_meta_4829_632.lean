import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4829_632
    (normalize :
      let codes : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
      let edge := fun (x : Fin 9 → Bool) =>
        codes.any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let reads := fun (C : Circuit) (a : ℕ) (i : Fin C.size) => a ∈ (C.gates.get i).inputs
      let op := fun (C : Circuit) (i : Fin C.size) => (C.gates.get i).op
      ∀ (C : Circuit) (i : Fin C.size), FanInTwo C → C.size ≤ 15 → op C i ≠ .or →
        (∀ j, reads C 4 j ↔ j = i) → circuitFun 9 C = edge →
        ∃ (D : Circuit) (a b : Fin D.size), FanInTwo D ∧ D.size ≤ 15 ∧ a < b ∧
        circuitFun 9 D = edge ∧
        (∀ k, reads D 4 k ↔ k = a) ∧
        (∀ k, reads D (9+a.val) k ↔ k = b) ∧
        ((op D a = .and ∧ op D b = .or) ∨ (op D a = .not ∧ op D b = .and)))
    (paired :
      let codes : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
      let edge := fun (x : Fin 9 → Bool) =>
        codes.any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let reads := fun (C : Circuit) (a : ℕ) (i : Fin C.size) => a ∈ (C.gates.get i).inputs
      let op := fun (C : Circuit) (i : Fin C.size) => (C.gates.get i).op
      ∀ (D : Circuit) (a b : Fin D.size), FanInTwo D → D.size ≤ 15 → a < b →
        (∀ k, reads D 4 k ↔ k = a) →
        (∀ k, reads D (9+a.val) k ↔ k = b) →
        ((op D a = .and ∧ op D b = .or) ∨ (op D a = .not ∧ op D b = .and)) →
        circuitFun 9 D ≠ edge) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) := by
  intro C i fan small nonOr sole exactEval
  have edgeEq : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
      x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
      x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) =
      (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) := by
    funext x
    revert x
    decide +kernel
  obtain ⟨D,a,b,hd,ds,order,shapeEval,raw,feed,kinds⟩ :=
    normalize C i fan small nonOr sole (exactEval.trans edgeEq)
  exact paired D a b hd ds order raw feed kinds shapeEval
