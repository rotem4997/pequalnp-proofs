import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3198_75
    (normalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 →
    (∃ i j : Fin C.gates.length, i<j ∧ i.val=5 ∧ (C.gates.get i).op=PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).op=PEqualNP.CircuitLowerBounds.GateOp.not) →
    (∀ x : Fin 9 → Bool, let a := C.wires (List.ofFn x)
      a.getD 9 false = (x 0 || x 2) ∧ a.getD C.output false = ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
        (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 n))) →
    let w := (List.range 7).map (fun i => BitVec.ofNat 512 (((2^128-1) / (2^(2^i)+1)) * 2^(2^i)))
    let op := fun (u v : Bool) (a b : BitVec 512) =>
      let z := (if u then a else ~~~a) &&& (if v then b else ~~~b)
      if z.getLsbD 0 then ~~~z else z
    ∃ l : List (BitVec 512), l.length ≤ 10 ∧ (∀ i : Fin l.length, let prev := w ++ l.take i.val
        ∃ a ∈ prev, ∃ b ∈ prev, ∃ u v, l.get i = op u v a b) ∧ BitVec.ofNat 512 (18446744060824649720 * 2^64 + 18441958779708426440) ∈ w ++ l)
    (exclude : let w := (List.range 7).map (fun i => BitVec.ofNat 512 (((2^128-1) / (2^(2^i)+1)) * 2^(2^i)))
    let op := fun (u v : Bool) (a b : BitVec 512) =>
      let z := (if u then a else ~~~a) &&& (if v then b else ~~~b)
      if z.getLsbD 0 then ~~~z else z
    ∀ l : List (BitVec 512), l.length ≤ 10 → (∀ i : Fin l.length, let prev := w ++ l.take i.val
        ∃ a ∈ prev, ∃ b ∈ prev, ∃ u v, l.get i = op u v a b) → BitVec.ofNat 512 (18446744060824649720 * 2^64 + 18441958779708426440) ∉ w ++ l) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (5 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C legal nots first correct
  by_contra! small
  obtain ⟨i,j,lt,idx,ni,nj,_⟩ := nots
  have graphEq : ∀ x : Fin 9 → Bool, (([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
        (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 n))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by decide +kernel
  obtain ⟨l,b,valid,out⟩ := normalize C legal (by omega) ⟨i,j,lt,idx,ni,nj⟩ (fun x => ⟨first x, (congrFun correct x).trans (graphEq x).symm⟩)
  exact exclude l b valid out
