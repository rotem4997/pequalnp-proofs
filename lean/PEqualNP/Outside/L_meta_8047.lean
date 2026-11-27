import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8047

open PEqualNP.CircuitLowerBounds

theorem getD_tb (v : List ℕ) (i k : ℕ) :
    (v.getD i 0).testBit k = (v.map (fun x => x.testBit k)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[i]? <;> simp

theorem foldr_lor_tb (l : List ℕ) (k : ℕ) :
    (List.foldr (fun (x y : ℕ) => x ||| y) 0 l).testBit k
      = (l.map (fun x => x.testBit k)).any id := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.testBit_lor, ih]

theorem foldr_land_tb (l : List ℕ) (k n : ℕ) (hk : k < n) :
    (List.foldr (fun (x y : ℕ) => x &&& y) (2 ^ n - 1) l).testBit k
      = (l.map (fun x => x.testBit k)).all id := by
  induction l with
  | nil => simp [Nat.testBit_two_pow_sub_one, hk]
  | cons a l ih => simp [Nat.testBit_land, ih]

theorem inv (n k : ℕ) (hk : k < n) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (v : List ℕ) :
    (List.foldl (fun (x5 : List ℕ) (x6 : Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ n - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) v gs).map (fun x => x.testBit k)
      = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (v.map (fun x => x.testBit k)) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    rw [List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hop := hg g (List.mem_cons_self ..)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h
    · rw [h]
      have e : GateOp.and.eval [true, false] = false := rfl
      rw [e, if_neg (by decide), foldr_land_tb _ _ _ hk]
      simp only [GateOp.eval, List.map_map, Function.comp_def, getD_tb]
    · rw [h]
      have e : GateOp.or.eval [true, false] = true := rfl
      rw [e, if_pos rfl, foldr_lor_tb]
      simp only [GateOp.eval, List.map_map, Function.comp_def, getD_tb]

end PEqualNP.Outside.L_meta_8047

theorem PEqualNP.Outside.L_meta_8047 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x5 : List ℕ := List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ x1 - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) x3 x2.gates;     ∀ x6 < x1, (x5.getD x2.output (0 : ℕ)).testBit x6 = x2.eval (List.map (fun (x8 : ℕ) => x8.testBit x6) x3) := by
  intro x1 x2 x3 hm
  intro x5 k hk
  exact (PEqualNP.Outside.L_meta_8047.getD_tb _ _ _).trans
    (congrArg (fun l => List.getD l x2.output false)
      (PEqualNP.Outside.L_meta_8047.inv x1 k hk x2.gates (fun g hg => (hm g hg).1) x3))
