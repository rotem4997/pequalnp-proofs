import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4029

namespace Eval

open PEqualNP.CircuitLowerBounds

def fiveGates (b o tap : ℕ) : List Gate :=
  [⟨.or,[o,14]⟩, ⟨.or,[tap,4]⟩, ⟨.or,[b+1,10]⟩, ⟨.or,[o,b+2]⟩,
    ⟨.and,[b,b+3]⟩]

def extend (C : Circuit) (tap : ℕ) : Circuit :=
  ⟨C.gates ++ fiveGates (26+C.size) C.output tap, 26+C.size+4⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step]
      omega

private theorem fold_keeps (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

private theorem primary (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
  rw [fold_keeps _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

private theorem len_wires (C : Circuit) (x : Fin 26 → Bool) :
    (C.wires (List.ofFn x)).length = 26+C.size := by
  change (C.gates.foldl step (List.ofFn x)).length = 26+C.gates.length
  rw [fold_length,List.length_ofFn]

private theorem step_or (w : List Bool) (a b : ℕ) :
    step w ⟨.or,[a,b]⟩ = w ++ [w.getD a false || w.getD b false] := by simp [step,GateOp.eval]

private theorem step_and (w : List Bool) (a b : ℕ) :
    step w ⟨.and,[a,b]⟩ = w ++ [w.getD a false && w.getD b false] := by simp [step,GateOp.eval]

private theorem get_new (w ls : List Bool) (b : ℕ) (len : w.length = b) (i : ℕ) :
    (w ++ ls).getD (b+i) false = ls.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega),len]
  congr 1
  omega

theorem extend_wires (C : Circuit) (tap : ℕ) (ho : C.output < 26+C.size)
    (ht : tap < 26 + C.size) (x : Fin 26 → Bool) :
    let w := C.wires (List.ofFn x)
    let o := C.eval (List.ofFn x)
    let l := o || x 14
    let s := w.getD tap false || x 4
    let t := s || x 10
    let r := o || t
    (extend C tap).wires (List.ofFn x) = w ++ [l,s,t,r,l && r] := by
  intro w o l s t r
  let b := 26+C.size
  have nw : w.length = b := len_wires C x
  have old (ls : List Bool) (j : ℕ) (jlt : j < b) : (w++ls).getD j false = w.getD j false :=
    List.getD_append _ _ _ _ (by omega)
  have new (ls : List Bool) (i : ℕ) : (w++ls).getD (b+i) false = ls.getD i false :=
    get_new _ _ _ nw _
  have hi (i : Fin 26) : w.getD i.val false = x i := primary C x i
  have h14 : w.getD 14 false = x 14 := hi 14
  have h4in : w.getD 4 false = x 4 := hi 4
  have h10 : w.getD 10 false = x 10 := hi 10
  have h0 : step w ⟨.or,[C.output,14]⟩ = w ++ [l] := by
    rw [step_or,h14]
    rfl
  have h1 : step (w++[l]) ⟨.or,[tap,4]⟩ = w ++ [l,s] := by
    rw [step_or,old _ _ ht,old _ 4 (by dsimp [b]; omega),h4in]
    simp only [s,List.append_assoc,List.singleton_append]
  have h2 : step (w++[l,s]) ⟨.or,[b+1,10]⟩ = w ++ [l,s,t] := by
    rw [step_or,new _ 1,old _ 10 (by dsimp [b]; omega),h10]
    simp only [t,List.append_assoc,List.cons_append,List.nil_append,List.getD_cons_succ,List.getD_cons_zero]
  have h3 : step (w++[l,s,t]) ⟨.or,[C.output,b+2]⟩ = w ++ [l,s,t,r] := by
    rw [step_or,old _ _ ho,new _ 2]
    simp only [r,o,Circuit.eval,List.append_assoc,List.cons_append,List.nil_append,
      List.getD_cons_succ,List.getD_cons_zero]
    rfl
  have h4 : step (w++[l,s,t,r]) ⟨.and,[b,b+3]⟩ = w ++ [l,s,t,r,l && r] := by
    rw [step_and,show b = b+0 by omega,new _ 0,new _ 3]
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.getD_cons_succ,List.getD_cons_zero]
  change ((C.gates ++ fiveGates b C.output tap).foldl step (List.ofFn x)) = _
  rw [List.foldl_append]
  change (fiveGates b C.output tap).foldl step w = _
  simp only [fiveGates,List.foldl_cons,List.foldl_nil,h0,h1,h2,h3,h4]

theorem extend_eval (C : Circuit) (tap : ℕ) (ho : C.output < 26+C.size)
    (ht : tap < 26 + C.size)
    (tapValue : ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD tap false = (x 1 || x 2))
    (x : Fin 26 → Bool) :
    let b := 26+C.size
    let W := (extend C tap).wires (List.ofFn x)
    let H := C.eval (List.ofFn x)
    W.getD b false = (H || x 14) ∧
      W.getD (b+3) false = (H || x 1 || x 2 || x 4 || x 10) ∧
      (extend C tap).eval (List.ofFn x) = (W.getD b false && W.getD (b+3) false) := by
  intro b W H
  have wireTable := extend_wires C tap ho ht x
  dsimp only at wireTable
  change W = _ at wireTable
  have len := len_wires C x
  change (C.wires (List.ofFn x)).length = b at len
  change W.getD b false = _ ∧ W.getD (b+3) false = _ ∧
    W.getD (b+4) false = (W.getD b false && W.getD (b+3) false)
  rw [wireTable]
  let w := C.wires (List.ofFn x)
  let s := w.getD tap false || x 4
  let t := s || x 10
  let l := H || x 14
  let r := H || t
  let ls := [l,s,t,r,l && r]
  have at0 : (w++ls).getD b false = l := by
    change (w++ls).getD (b+0) false = l
    rw [get_new _ _ _ len 0]
    rfl
  have at3 : (w++ls).getD (b+3) false = r := by
    rw [get_new _ _ _ len 3]
    rfl
  have at4 : (w++ls).getD (b+4) false = (l && r) := by
    rw [get_new _ _ _ len 4]
    rfl
  change (w++ls).getD b false = _ ∧ (w++ls).getD (b+3) false = _ ∧
    (w++ls).getD (b+4) false = ((w++ls).getD b false && (w++ls).getD (b+3) false)
  refine ⟨at0,?_,?_⟩
  · rw [at3]
    simp only [r,t,s,w,tapValue x,Bool.or_assoc]
  · rw [at0,at3]
    exact at4

end Eval

namespace Shape

open PEqualNP.CircuitLowerBounds

def b (C : Circuit) : ℕ := 26 + C.size

abbrev tail (C : Circuit) (tap : ℕ) : List Gate :=
  PEqualNP.Outside.L_meta_4029.Eval.fiveGates (b C) C.output tap

abbrev extend (C : Circuit) (tap : ℕ) : Circuit :=
  PEqualNP.Outside.L_meta_4029.Eval.extend C tap

def lawful (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 26 + j ∧ v < 26 + j

theorem extend_size (C : Circuit) (tap : ℕ) :
    (extend C tap).size = C.size + 5 := by
  simp [extend, PEqualNP.Outside.L_meta_4029.Eval.extend, PEqualNP.Outside.L_meta_4029.Eval.fiveGates, Circuit.size, b]

theorem extend_lawful (C : Circuit) (tap : ℕ)
    (outLo : 26 ≤ C.output) (outHi : C.output < b C)
    (tapLo : 26 ≤ tap) (tapHi : tap < b C) (old : lawful C) :
    lawful (extend C tap) := by
  intro j g hj
  change (C.gates ++ tail C tap)[j]? = some g at hj
  by_cases oldIndex : j < C.gates.length
  · rw [List.getElem?_append_left oldIndex] at hj
    exact old j g hj
  · have hjLo : C.gates.length ≤ j := Nat.le_of_not_gt oldIndex
    rw [List.getElem?_append_right hjLo] at hj
    have valid : j - C.gates.length < (tail C tap).length := by
      obtain ⟨inRange,_⟩ := List.getElem?_eq_some_iff.mp hj
      exact inRange
    have hsmall : j-C.gates.length < 5 := by simpa [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] using valid
    have hb : b C = 26+C.gates.length := rfl
    have hcases : j-C.gates.length = 0 ∨ j-C.gates.length = 1 ∨
        j-C.gates.length = 2 ∨ j-C.gates.length = 3 ∨ j-C.gates.length = 4 := by omega
    rcases hcases with h | h | h | h | h
    · rw [h] at hj
      simp [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] at hj
      subst g
      exact ⟨Or.inr rfl, C.output, 14, rfl, by omega, by omega, by omega⟩
    · rw [h] at hj
      simp [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] at hj
      subst g
      exact ⟨Or.inr rfl, tap, 4, rfl, by omega, by omega, by omega⟩
    · rw [h] at hj
      simp [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] at hj
      subst g
      exact ⟨Or.inr rfl, b C + 1, 10, rfl, by omega, by omega, by omega⟩
    · rw [h] at hj
      simp [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] at hj
      subst g
      exact ⟨Or.inr rfl, C.output, b C + 2, rfl, by omega, by omega, by omega⟩
    · rw [h] at hj
      simp [tail, PEqualNP.Outside.L_meta_4029.Eval.fiveGates] at hj
      subst g
      exact ⟨Or.inl rfl, b C, b C + 3, rfl, by omega, by omega, by omega⟩

theorem extend_output (C : Circuit) (tap : ℕ) :
    (extend C tap).output = 26 + (C.size+4) := by
  simp [extend, PEqualNP.Outside.L_meta_4029.Eval.extend, b, Nat.add_assoc]

theorem extend_last (C : Circuit) (tap : ℕ) :
    (extend C tap).gates[C.size+4]? = some ⟨.and, [b C,b C+3]⟩ := by
  change (C.gates ++ tail C tap)[C.gates.length + 4]? = _
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rfl


end Shape

end PEqualNP.Outside.L_meta_4029

open PEqualNP.Outside.L_meta_4029.Shape in
theorem PEqualNP.Outside.L_meta_4029 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   (26 : ℕ) ≤ x1.output →     x1.output < (26 : ℕ) + x1.size →       (26 : ℕ) ≤ x2 →         x2 < (26 : ℕ) + x1.size →           (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x7 ∧ x11 < (26 : ℕ) + x7) →             (∀ (x8 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x8)).getD x2 Bool.false = (x8 (1 : Fin (26 : ℕ)) || x8 (2 : Fin (26 : ℕ)))) →               ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ),                 x9.size ≤ x1.size + (5 : ℕ) ∧                   (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x9.gates[x13]? = Option.some x14 → (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 ≠ x17 ∧ x16 < (26 : ℕ) + x13 ∧ x17 < (26 : ℕ) + x13) ∧                     x9.output = (26 : ℕ) + x10 ∧                       x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x11, x12] : PEqualNP.CircuitLowerBounds.Gate } ∧                         ∀ (x13 : Fin (26 : ℕ) → Bool),                           have x14 : List Bool := x9.wires (List.ofFn x13);                           have x15 : Bool := x1.eval (List.ofFn x13);                           x14.getD x11 Bool.false = (x15 || x13 (14 : Fin (26 : ℕ))) ∧ x14.getD x12 Bool.false = (x15 || x13 (1 : Fin (26 : ℕ)) || x13 (2 : Fin (26 : ℕ)) || x13 (4 : Fin (26 : ℕ)) || x13 (10 : Fin (26 : ℕ))) ∧ x9.eval (List.ofFn x13) = (x14.getD x11 Bool.false && x14.getD x12 Bool.false) := by
  intro C tap outLo outHi tapLo tapHi valid validTap
  refine ⟨extend C tap, C.size+4, b C, b C+3,
    (extend_size C tap).le, extend_lawful C tap outLo outHi tapLo tapHi valid,
    extend_output C tap, extend_last C tap, ?_⟩
  intro x
  exact PEqualNP.Outside.L_meta_4029.Eval.extend_eval C tap outHi tapHi validTap x
