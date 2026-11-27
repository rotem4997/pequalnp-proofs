import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18502_aux
open PEqualNP.CircuitLowerBounds

private def gate (t : Bool × ℕ × ℕ) : Gate :=
  ⟨if t.1 then .and else .or,[t.2.1,t.2.2]⟩

private def step {α : Type} (w : List (Set α)) (t : Bool × ℕ × ℕ) :=
  w.concat (if t.1 then w.getD t.2.1 ∅ ∩ w.getD t.2.2 ∅ else w.getD t.2.1 ∅ ∪ w.getD t.2.2 ∅)

private def evalG (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem sim {α : Type} (a : α) (ts : List (Bool × ℕ × ℕ))
    (b : List Bool) (S : List (Set α)) (len : b.length = S.length)
    (h : ∀ i, b.getD i false = true ↔ a ∈ S.getD i ∅) :
    ∀ i, ((ts.map gate).foldl evalG b).getD i false = true ↔ a ∈ (ts.foldl step S).getD i ∅ := by
  induction ts generalizing b S with
  | nil => exact h
  | cons t ts ih =>
    apply ih (evalG b (gate t)) (step S t) (by simp [evalG,step,len])
    intro i
    by_cases lt : i < b.length
    · simpa only [evalG,step,List.concat_eq_append,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_append_left (show i < S.length by omega)] using h i
    by_cases eq : i = b.length
    · subst i
      rcases t with ⟨op,j,k⟩
      cases op <;> simp [evalG,step,gate,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_append_right,len,List.concat_eq_append] <;> first | exact and_congr (h j) (h k) | exact or_congr (h j) (h k)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (evalG b (gate t)).length ≤ i by simp [evalG]; omega),List.getElem?_eq_none (show (step S t).length ≤ i by simp [step]; omega)]

private theorem compile : have x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); ∀ (x2 : Fin (25 : ℕ) → Set x1) (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.length ∧ x5.output = x4 ∧ ∀ (x6 : x1) (x7 : Fin (25 : ℕ) → Bool), (∀ (x8 : Fin (25 : ℕ)), x7 x8 = Bool.true ↔ x6 ∈ x2 x8) → ∀ (x9 : ℕ), (x5.wires (List.ofFn x7)).getD x9 Bool.false = Bool.true ↔ x6 ∈ (List.foldl (fun (x10 : List (Set x1)) (x11 : Bool × ℕ × ℕ) => x10.concat (if x11.1 = Bool.true then x10.getD x11.2.1 ∅ ∩ x10.getD x11.2.2 ∅ else x10.getD x11.2.1 ∅ ∪ x10.getD x11.2.2 ∅)) (List.ofFn x2) x3).getD x9 ∅ := by
  dsimp only
  intro f ts out
  refine ⟨⟨ts.map gate,out⟩,?_,by simp [Circuit.size],rfl,?_⟩
  · intro g hg
    obtain ⟨⟨op,j,k⟩,_,rfl⟩ := List.mem_map.mp hg
    cases op <;> simp [gate]
  · intro a b hb
    apply sim a ts (List.ofFn b) (List.ofFn f) (by simp)
    intro i
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    by_cases lt : i < 25
    · simpa only [dif_pos lt,Option.getD_some] using hb ⟨i,lt⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,lt]
end PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.Outside.L_meta_18502_aux in
theorem PEqualNP.Outside.L_meta_18502 : (have x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); ∀ (x2 : Fin (25 : ℕ) → Set x1) (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.length ∧ x5.output = x4 ∧ ∀ (x6 : x1) (x7 : Fin (25 : ℕ) → Bool), (∀ (x8 : Fin (25 : ℕ)), x7 x8 = Bool.true ↔ x6 ∈ x2 x8) → ∀ (x9 : ℕ), (x5.wires (List.ofFn x7)).getD x9 Bool.false = Bool.true ↔ x6 ∈ (List.foldl (fun (x10 : List (Set x1)) (x11 : Bool × ℕ × ℕ) => x10.concat (if x11.1 = Bool.true then x10.getD x11.2.1 ∅ ∩ x10.getD x11.2.2 ∅ else x10.getD x11.2.1 ∅ ∪ x10.getD x11.2.2 ∅)) (List.ofFn x2) x3).getD x9 ∅) := compile
