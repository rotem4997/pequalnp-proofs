import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5685_43
    (ordinary : ∀ P : List (Bool × Fin 30 × Fin 30), P.length ≤ 18 →
      (32767 : BitVec 30) ∉ P.foldl (fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b])
        ([579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823] : List (BitVec 30)))
    (oneMissing : ∀ P : List (Bool × Fin 30 × Fin 30), P.length ≤ 17 →
      ∀ w ∈ P.foldl (fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b]) ([579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823] : List (BitVec 30)), w ||| 1 ≠ 32767) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).all id]) ≠ x6.2) := by
  intro C items mono size arity
  let samples : List (Nat × Bool) := [(3,true),(6,true),(12,true),(24,true),(17,true),(33,true),(66,true),(132,true),(264,true),(528,true),(160,true),(640,true),(576,true),(320,true),(288,true),(50,false),(69,false),(104,false),(116,false),(138,false),(201,false),(208,false),(276,false),(385,false),(402,false),(521,false),(548,false),(554,false),(770,false),(773,false)]
  let bank (side : Bool) : List (BitVec 30) :=
    [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823,if side then 536936448 else 1]
  let codes : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,0,1,11,12,13,14,15,16,17,18,19,10,11,2,12,20,21,22,23,24,25,26,27,10,20,3,13,21,28,29,30,31,32,33,34,10,28,4,14,22,29,35,36,37,38,39,40,10,35,5,15,23,30,36,41,42,43,44,45,10,41,6,16,24,31,37,42,46,47,48,49,10,46,7,17,25,32,38,43,47,50,51,52,10,50,8,18,26,33,39,44,48,51,53,54,10,53,9,19,27,34,40,45,49,52,54,55,10,55,10,10,10,10,10,10,10,10,10,10,10,10,0,11,20,28,35,41,46,50,53,55,10,56]
  let layouts : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7,8,9,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,12,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,12,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,1],#[0,4,3,2,1,5,9,8,7,6,12,4,3,2,1,0,5,9,8,7,6,14,13,12,11,10,15,25,26,27,22,29,28,19,23,24,16,17,18,21,20,1],#[0,4,3,2,1,5,9,8,7,6,12,4,3,2,1,0,5,9,8,7,6,14,13,12,11,10,15,25,26,27,22,29,28,19,23,24,16,17,18,21,20,0],#[0,5,8,3,4,1,7,6,2,9,12,5,14,8,3,4,0,10,13,2,9,6,12,11,7,1,15,23,19,24,17,20,21,22,16,18,25,28,27,26,29,0],#[0,1,6,8,5,4,2,9,3,7,12,0,6,13,14,5,4,1,12,8,10,9,11,7,2,3,15,16,22,18,28,29,26,17,25,27,23,21,24,19,20,1],#[0,4,3,8,5,1,9,2,6,7,12,5,10,7,1,0,4,14,11,2,6,9,12,13,8,3,15,23,22,24,26,29,28,19,25,27,16,21,18,17,20,1],#[0,5,8,3,4,1,7,6,2,9,12,5,14,8,3,4,0,10,13,2,9,6,12,11,7,1,15,23,19,24,17,20,21,22,16,18,25,28,27,26,29,1],#[0,4,9,6,1,5,3,7,8,2,12,4,9,12,6,0,5,3,11,13,1,10,7,2,8,14,15,25,17,27,21,20,19,28,23,24,16,26,18,22,29,1],#[0,1,2,3,4,5,6,7,8,9,10,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[4,0,1,2,3,9,5,6,7,8,12,1,2,3,4,0,6,7,8,9,5,13,14,10,11,12,16,19,21,20,22,24,23,25,28,29,15,17,18,26,27,0],#[4,0,1,2,3,9,5,6,7,8,12,1,2,3,4,0,6,7,8,9,5,13,14,10,11,12,16,19,21,20,22,24,23,25,28,29,15,17,18,26,27,1],#[1,0,4,3,2,6,5,9,8,7,12,0,4,3,2,1,6,5,9,8,7,12,11,10,14,13,16,15,17,18,25,27,26,22,28,29,19,21,20,23,24,1],#[1,0,4,9,6,2,5,3,7,8,12,0,5,10,7,1,6,4,14,11,2,13,8,3,9,12,16,15,21,18,23,24,22,26,28,29,19,17,20,25,27,1],#[4,0,5,8,3,9,1,7,6,2,12,6,12,9,4,0,1,13,11,3,5,7,10,14,8,2,16,28,22,29,21,24,23,25,19,20,15,26,18,17,27,0],#[4,0,1,6,9,3,5,2,8,7,12,1,7,10,5,0,6,2,11,14,4,12,9,3,8,13,16,19,17,20,26,27,25,23,28,29,15,21,18,22,24,1],#[5,0,4,3,8,7,1,9,2,6,12,6,13,8,2,1,0,12,14,3,7,5,10,11,9,4,16,28,25,29,17,27,26,22,15,18,19,23,20,21,24,1],#[4,0,5,8,3,9,1,7,6,2,12,6,12,9,4,0,1,13,11,3,5,7,10,14,8,2,16,28,22,29,21,24,23,25,19,20,15,26,18,17,27,1],#[0,1,2,3,4,5,6,7,8,9,2,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[8,5,0,1,6,3,7,4,2,9,12,2,8,14,10,7,1,3,13,5,11,6,12,9,4,0,19,22,15,24,17,18,21,23,16,20,26,28,27,25,29,0],#[3,4,0,1,2,8,9,5,6,7,12,2,3,4,0,1,7,8,9,5,6,11,12,13,14,10,19,22,23,24,25,29,28,15,26,27,16,21,20,17,18,1],#[3,4,0,5,8,2,9,1,7,6,12,7,10,5,0,1,2,11,14,4,6,8,13,12,9,3,19,26,25,27,23,29,28,15,22,24,16,17,20,21,18,1],#[6,1,0,4,9,8,2,5,3,7,12,1,6,13,8,2,7,0,12,14,3,11,9,4,5,10,19,16,23,20,28,29,25,17,26,27,22,21,24,15,18,1],#[3,4,0,5,8,2,9,1,7,6,12,7,10,5,0,1,2,11,14,4,6,8,13,12,9,3,19,26,25,27,23,29,28,15,22,24,16,17,20,21,18,0],#[8,5,0,1,6,3,7,4,2,9,12,2,8,14,10,7,1,3,13,5,11,6,12,9,4,0,19,22,15,24,17,18,21,23,16,20,26,28,27,25,29,1],#[8,5,0,4,3,6,7,1,9,2,12,7,11,9,3,2,1,10,12,4,8,6,13,14,5,0,19,26,15,27,21,18,17,25,16,20,22,28,24,23,29,1],#[0,1,2,3,4,5,6,7,8,9,3,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[2,3,4,0,1,7,8,9,5,6,12,3,4,0,1,2,8,9,5,6,7,14,10,11,12,13,22,25,28,29,15,27,26,16,17,18,19,23,24,21,20,0],#[3,8,5,0,4,2,6,7,1,9,12,8,14,5,4,3,2,13,10,0,9,7,11,12,6,1,22,17,16,18,23,20,21,15,19,24,25,26,29,28,27,1],#[8,3,4,0,5,6,2,9,1,7,12,8,13,6,1,2,3,14,12,0,7,9,11,10,5,4,22,17,15,18,28,27,26,16,25,29,19,21,24,23,20,1],#[8,6,1,0,5,3,9,2,4,7,12,2,7,10,14,8,3,1,11,5,13,9,12,6,0,4,22,19,15,24,26,27,28,23,25,29,17,21,18,16,20,1],#[3,8,5,0,4,2,6,7,1,9,12,8,14,5,4,3,2,13,10,0,9,7,11,12,6,1,22,17,16,18,23,20,21,15,19,24,25,26,29,28,27,0],#[6,8,5,0,1,9,3,7,4,2,12,3,9,12,13,8,2,4,11,6,14,7,10,5,0,1,22,25,16,29,21,20,23,28,19,24,17,26,18,15,27,1],#[0,1,2,3,4,5,6,7,8,9,4,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[1,6,8,5,0,2,9,3,7,4,12,4,5,10,11,9,3,0,14,7,12,8,13,6,1,2,25,15,19,27,23,24,28,26,22,29,21,17,20,16,18,1],#[4,3,8,5,0,9,2,6,7,1,12,9,12,6,0,4,3,11,13,1,5,8,14,10,7,2,25,21,19,20,28,24,23,16,22,29,15,17,27,26,18,1],#[5,8,3,4,0,7,6,2,9,1,12,9,11,7,2,3,4,12,10,1,8,5,14,13,6,0,25,21,16,20,26,18,17,19,15,27,22,23,29,28,24,1],#[4,9,6,1,0,3,7,8,2,5,12,3,8,14,5,4,9,2,13,10,0,12,6,1,7,11,25,22,26,29,17,18,16,23,21,20,15,28,27,19,24,1],#[4,3,8,5,0,9,2,6,7,1,12,9,12,6,0,4,3,11,13,1,5,8,14,10,7,2,25,21,19,20,28,24,23,16,22,29,15,17,27,26,18,0],#[0,1,2,3,4,5,6,7,8,9,5,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[4,3,8,6,9,0,2,5,1,7,12,14,13,6,0,5,10,8,12,1,4,11,9,3,2,7,23,17,19,20,28,27,25,16,26,29,15,21,24,22,18,1],#[4,3,2,7,9,0,8,1,5,6,12,10,7,1,0,5,14,11,2,6,4,8,3,9,12,13,23,26,28,29,19,27,25,16,17,20,15,22,24,21,18,0],#[5,8,3,2,7,0,6,4,1,9,12,14,8,2,7,10,5,13,3,1,11,4,9,12,6,0,23,17,16,20,22,18,21,19,15,24,26,25,29,28,27,0],#[4,9,6,8,3,0,7,1,5,2,12,10,11,9,4,5,14,7,12,3,0,13,6,1,2,8,23,26,22,29,21,18,16,25,17,20,15,28,24,19,27,1],#[0,1,2,3,4,5,6,7,8,9,6,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[9,4,3,8,6,7,0,2,5,1,12,12,11,7,1,6,13,9,10,2,0,14,5,4,3,8,28,21,22,24,26,18,15,19,17,27,16,23,29,25,20,1],#[9,4,3,2,7,6,0,8,1,5,12,13,8,2,1,6,12,14,3,7,0,9,4,5,10,11,28,17,26,27,22,18,15,19,21,24,16,25,29,23,20,0],#[3,4,9,7,2,8,0,6,5,1,12,12,9,4,0,6,13,11,3,5,1,8,2,7,10,14,28,21,23,24,25,20,19,15,17,27,16,22,29,26,18,0],#[0,1,2,3,4,5,6,7,8,9,7,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[6,9,4,3,8,1,7,0,2,5,12,10,14,8,2,7,11,5,13,3,1,12,6,0,4,9,26,23,25,29,17,20,16,22,21,18,19,28,27,15,24,1],#[3,8,5,7,2,4,6,0,9,1,12,11,9,4,5,10,7,12,3,0,14,2,8,13,6,1,26,21,16,18,25,20,17,15,19,27,23,22,29,28,24,0],#[0,1,2,3,4,5,6,7,8,9,8,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[8,6,9,4,3,5,1,7,0,2,12,13,12,9,3,8,14,6,11,4,2,10,7,1,0,5,17,28,15,27,21,24,19,25,23,20,22,26,18,16,29,1],#[0,1,2,3,4,5,6,7,8,9,9,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0],#[0,1,2,3,4,5,6,7,8,9,11,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,0]]
  let layout (p q : Fin 12) := layouts.getD (codes.getD (12*p.val+q.val) 0) #[]
  let side (p q : Fin 12) := decide ((layout p q).getD 41 0 = 1)
  let coord (p q : Fin 12) (i : Nat) := (layout p q).getD i 0
  let row (p q : Fin 12) (r : Fin 30) := samples.getD ((layout p q).getD (11+r.val) 0) (0,false)
  let bitAt (r : Fin 30) (x : BitVec 30) := x.getLsbD r.val
  let src (p : Fin 12) (x : List Bool) := if p.val=11 then true else x.getD p.val false
  have range : ∀ (p q : Fin 12) (i : Fin 11), coord p q i.val < 13 := by decide +kernel
  have data : ∀ (p q : Fin 12) (r : Fin 30),
      let tag := row p q r
      let input := List.ofFn (fun i : Fin 10 => tag.1.testBit i.val)
      let w := bank (side p q)
      tag ∈ samples ∧ tag.2 = bitAt r 32767 ∧
        (∀ i : Fin 10, bitAt r (w.getD (coord p q i.val) 0) = input.getD i.val false) ∧
        bitAt r (w.getD (coord p q 10) 0) = (src p input && src q input) := by decide +kernel
  let conv (k : Nat) : Fin 12 := ⟨min k 10,by omega⟩
  let p := (items.map conv).getD 0 11
  let q := (items.map conv).getD 1 11
  have val (x : List Bool) (hl : x.length=10) (i : Nat) : src (conv i) x = x.getD i false := by
    by_cases h : i < 10
    · simp [src,conv,Nat.min_eq_left (show i ≤ 10 by omega),show i ≠ 11 by omega]
    · simp only [src,conv,Nat.min_eq_right (show 10 ≤ i by omega),List.getD_eq_default x false (show x.length ≤ 10 by omega),
        List.getD_eq_default x false (show x.length ≤ i by omega)]
      decide
  have supplied (x : List Bool) (hl : x.length=10) :
      (items.map (fun i => x.getD i false)).all id = (src p x && src q x) := by
    dsimp only [p,q]
    cases items with
    | nil => simp [src]
    | cons i l =>
      cases l with
      | nil =>
        change (x.getD i false && true) = (src (conv i) x && true)
        rw [val x hl]
      | cons j tail =>
        cases tail with
        | nil => simp [val x hl]
        | cons v l => simp at arity
  let ren (i : Nat) := if i<11 then coord p q i else i+2
  let narrow (i : Nat) : Fin 30 := if h : ren i < 30 then ⟨ren i,h⟩ else 10
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  let cmd (g : Gate) : Bool × Fin 30 × Fin 30 :=
    let isAnd := decide (g.op=GateOp.and)
    let neutral : Fin 30 := if isAnd then 11 else 10
    (isAnd,(g.inputs[0]?).elim neutral narrow,(g.inputs[1]?).elim neutral narrow)
  let step := fun (w : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) =>
          let a := w.getD c.2.1.val 0
          let b := w.getD c.2.2.val 0
          w ++ [if c.1 then a &&& b else a ||| b]
  let physical (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]
  have app {α : Type} (xs : List α) (v d : α) (k : Nat) :
      (xs++[v]).getD k d = if k=xs.length then v else xs.getD k d := by
    by_cases eq : k=xs.length
    · subst k; simp
    by_cases small : k<xs.length
    · rw [if_neg eq]; exact List.getD_append xs [v] d k small
    · rw [if_neg eq,List.getD_eq_default (xs++[v]) d (by simp;omega),List.getD_eq_default xs d (by omega)]
  have simulate (r : Fin 30) (gs : List Gate) (legal : ∀ g ∈ gs,
      (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
      (w : List Bool) (v : List (BitVec 30)) (t : Nat)
      (hw : w.length=11+t) (hv : v.length=13+t) (limit : v.length+gs.length≤31)
      (c0 : v.getD 10 0=0) (c1 : v.getD 11 0=1073741823)
      (agree : ∀ j, bitAt r (v.getD (ren j) 0) = w.getD j false) (j : Nat) :
      bitAt r (((gs.map cmd).foldl step v).getD (ren j) 0) = (gs.foldl physical w).getD j false := by
    induction gs generalizing w v t with
    | nil => exact agree j
    | cons g gs ih =>
      have bound : v.length≤30 := by simp only [List.length_cons] at limit; omega
      have read (a : Nat) : bitAt r (v.getD (narrow a).val 0) = w.getD a false := by
        by_cases h : ren a<30
        · simpa [narrow,h] using agree a
        · have hvv : v.getD (ren a) 0=0 := List.getD_eq_default _ _ (by omega)
          simp only [narrow,h,↓reduceDIte]
          change bitAt r (v.getD 10 0) = w.getD a false
          rw [c0]
          simpa only [hvv] using agree a
      have zeroVal : bitAt r (v.getD 10 0) = false := by rw [c0]; simp [bitAt]
      have oneVal : bitAt r (v.getD 11 0) = true := by
        rw [c1]
        exact (show ∀ k : Fin 30, bitAt k 1073741823 = true by decide +kernel) r
      let c := cmd g
      let z := if c.1 then v.getD c.2.1.val 0 &&& v.getD c.2.2.val 0 else v.getD c.2.1.val 0 ||| v.getD c.2.2.val 0
      let b := g.op.eval (g.inputs.map (fun k => w.getD k false))
      have brz : bitAt r z = b := by
        obtain ⟨op,len⟩ := legal g (by simp)
        have band (u vi : BitVec 30) : bitAt r (u &&& vi) = (bitAt r u && bitAt r vi) := by simp [bitAt]
        have bor (u vi : BitVec 30) : bitAt r (u ||| vi) = (bitAt r u || bitAt r vi) := by simp [bitAt]
        rcases op with op|op <;> cases hin : g.inputs with
        | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,zeroVal,oneVal,-List.getD_eq_getElem?_getD] <;> first | exact zeroVal | exact oneVal
        | cons a tail =>
          cases tail with
          | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,zeroVal,oneVal,read,-List.getD_eq_getElem?_getD] <;> first | exact (congrArg₂ Bool.and (read a) oneVal).trans (Bool.and_true _) | exact (congrArg₂ Bool.or (read a) zeroVal).trans (Bool.or_false _)
          | cons d tail =>
            cases tail with
            | nil => simp [z,b,c,cmd,op,hin,andEval,orEval,band,bor,read,-List.getD_eq_getElem?_getD] <;> first | exact congrArg₂ Bool.and (read a) (read d) | exact congrArg₂ Bool.or (read a) (read d)
            | cons e rem => simp [hin] at len
      have fresh (k : Nat) : ren k=v.length ↔ k=w.length := by
        by_cases small : k<11
        · have rr := range p q ⟨k,small⟩
          simp only [ren,small,↓reduceIte]; change coord p q k < 13 at rr; omega
        · simp only [ren,small,↓reduceIte]; omega
      have matchNext (k : Nat) : bitAt r ((v++[z]).getD (ren k) 0) = (w++[b]).getD k false := by
        rw [app,app]
        by_cases h : k = w.length
        · rw [if_pos h,if_pos ((fresh k).mpr h)]; exact brz
        · rw [if_neg h,if_neg (fun e => h ((fresh k).mp e))]; exact agree k
      change bitAt r (((gs.map cmd).foldl step (v++[z])).getD (ren j) 0) =
        (gs.foldl physical (w++[b])).getD j false
      apply ih (fun g h => legal g (by simp [h])) (w++[b]) (v++[z]) (t+1)
      · simp [hw,Nat.add_assoc]
      · simp [hv,Nat.add_assoc]
      · simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at limit ⊢; omega
      · rw [List.getD_append _ _ _ _ (by omega)]; exact c0
      · rw [List.getD_append _ _ _ _ (by omega)]; exact c1
      · exact matchNext
  let W := bank (side p q)
  let program := C.gates.map cmd
  let result := program.foldl step W
  have plen : program.length ≤ 18 := by change C.gates.length ≤ 18 at size; simpa [program] using size
  let normal : List (BitVec 30) := [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048,0,1073741823]
  let run (Q : List (Bool × Fin 30 × Fin 30)) := Q.foldl step normal
  let word (v : List (BitVec 30)) (c : Bool × Fin 30 × Fin 30) :=
    if c.1 then v.getD c.2.1.val 0 &&& v.getD c.2.2.val 0 else v.getD c.2.1.val 0 ||| v.getD c.2.2.val 0
  let touches (c : Bool × Fin 30 × Fin 30) := decide (c.2.1.val=12 ∨ c.2.2.val=12)
  let seed := normal ++ [0]
  have runSize (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30)) :
      (P.foldl step v).length = v.length+P.length := by
    induction P generalizing v with
    | nil => simp
    | cons c cs ih =>
      change (cs.foldl step (v++[word v c])).length = _
      rw [ih]; simp; omega
  have previous (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30)) (j : Nat)
      (hj : j < v.length) : (P.foldl step v).getD j 0 = v.getD j 0 := by
    induction P generalizing v with
    | nil => rfl
    | cons c cs ih =>
      change (cs.foldl step (v++[word v c])).getD j 0 = _
      rw [ih _ (by simp;omega)]
      exact List.getD_append _ _ _ _ hj
  have atMem (v : List (BitVec 30)) (k : Nat) (hz : (0 : BitVec 30) ∈ v) : v.getD k 0 ∈ v := by
    by_cases h : k<v.length
    · rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
    · rwa [List.getD_eq_default _ _ (by omega)]
  have zeroQ (Q : List (Bool × Fin 30 × Fin 30)) : (0 : BitVec 30) ∈ run Q := by
    have e : (run Q).getD 10 0 = 0 := previous Q normal 10 (by decide +kernel)
    have h : 10 < (run Q).length := by change 10<(Q.foldl step normal).length; rw [runSize]; change 10<12+Q.length; omega
    rw [←e,List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
  have zOr (v : BitVec 30) : (0 : BitVec 30) ||| v = v := by exact BitVec.zero_or
  have orZ (v : BitVec 30) : v ||| (0 : BitVec 30) = v := by exact BitVec.or_zero
  have zAnd (v : BitVec 30) : (0 : BitVec 30) &&& v = 0 := by exact BitVec.zero_and
  have andZ (v : BitVec 30) : v &&& (0 : BitVec 30) = 0 := by exact BitVec.and_zero
  have copy (P : List (Bool × Fin 30 × Fin 30)) (v : List (BitVec 30))
      (Q : List (Bool × Fin 30 × Fin 30)) (budget : Q.length+P.length ≤ 18)
      (hv : 13≤v.length) (vz : v.getD 12 0=0) (incl : ∀ w∈v, w∈run Q) :
      ∃ D, D.length ≤ Q.length + P.countP (fun c => !touches c) ∧
        ∀ w∈P.foldl step v, w∈run D := by
    induction P generalizing v Q with
    | nil => exact ⟨Q,by simp,incl⟩
    | cons c cs ih =>
      have lim : Q.length+cs.length+1 ≤18 := by simp only [List.length_cons] at budget; omega
      let z := word v c
      have inext (k : Fin 30) : v.getD k.val 0 ∈ run Q := by
        by_cases h : k.val<v.length
        · rw [List.getD_eq_getElem _ _ h]; exact incl _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (by omega)]; exact zeroQ Q
      have vz' : (v++[z]).getD 12 0 = 0 :=
        (List.getD_append _ _ _ _ (by omega)).trans vz
      have len' : 13 ≤ (v++[z]).length := by simp;omega
      by_cases touched : touches c = true
      · have hw : z ∈ run Q := by
          have choice : c.2.1.val=12 ∨ c.2.2.val=12 := of_decide_eq_true touched
          rcases choice with ha|hb
          · cases op : c.1
            · simpa only [z,word,op,Bool.false_eq_true,↓reduceIte,ha,vz,zOr] using inext c.2.2
            · simpa only [z,word,op,↓reduceIte,ha,vz,zAnd] using zeroQ Q
          · cases op : c.1
            · simpa only [z,word,op,Bool.false_eq_true,↓reduceIte,hb,vz,orZ] using inext c.2.1
            · simpa only [z,word,op,↓reduceIte,hb,vz,andZ] using zeroQ Q
        have inc (w) (h : w ∈ v++[z]) : w ∈ run Q := by
          simp only [List.mem_append,List.mem_singleton] at h
          exact h.elim (incl w) (fun e => e ▸ hw)
        obtain ⟨D,hD,hW⟩ := ih (v++[z]) Q (by omega) len' vz' inc
        exact ⟨D,by simpa [List.countP_cons,touched] using hD,hW⟩
      · have Qlen : (run Q).length < 30 := by
          change (Q.foldl step normal).length < 30
          rw [runSize]; change 12+Q.length<30; omega
        have pick (k : Fin 30) : ∃ i : Fin 30, (run Q).getD i.val 0 = v.getD k.val 0 := by
          obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp (inext k)
          exact ⟨⟨j,by omega⟩,(List.getD_eq_getElem _ _ hj).trans eq⟩
        obtain ⟨a,ha⟩ := pick c.2.1
        obtain ⟨b,hb⟩ := pick c.2.2
        let next := Q++[(c.1,a,b)]
        have eq : run next = run Q ++ [z] := by
          change (Q++[(c.1,a,b)]).foldl step normal = _
          rw [List.foldl_append]
          change run Q ++ [if c.1 then (run Q).getD a.val 0 &&& (run Q).getD b.val 0 else (run Q).getD a.val 0 ||| (run Q).getD b.val 0] = _
          rw [ha,hb]
        have inc (w) (h : w ∈ v++[z]) : w ∈ run next := by
          rw [eq]
          simp only [List.mem_append,List.mem_singleton] at h ⊢
          exact h.imp (incl w) id
        have length : next.length=Q.length+1 := by simp [next]
        obtain ⟨D,hD,hW⟩ := ih (v++[z]) next (by omega) len' vz' inc
        have nt : touches c=false := Bool.eq_false_iff.mpr touched
        refine ⟨D,?_,hW⟩
        simp only [List.countP_cons,nt,Bool.not_false,↓reduceIte]
        omega
  have compare (r : Fin 30) (rel : Bool → Bool → Prop)
      (gate : ∀ a b c d, rel a b → rel c d → rel (a && c) (b && d) ∧ rel (a || c) (b || d))
      (skip : Nat → Prop) (P : List (Bool × Fin 30 × Fin 30))
      (clean : ∀ c∈P, ¬skip c.2.1.val ∧ ¬skip c.2.2.val)
      (v w : List (BitVec 30)) (length : v.length=w.length)
      (agree : ∀ k, ¬skip k → rel (bitAt r (v.getD k 0)) (bitAt r (w.getD k 0))) :
      ∀ k, ¬skip k → rel (bitAt r ((P.foldl step v).getD k 0)) (bitAt r ((P.foldl step w).getD k 0)) := by
    induction P generalizing v w with
    | nil => exact agree
    | cons c cs ih =>
      apply ih (fun g hg => clean g (by simp [hg])) (v++[word v c]) (w++[word w c]) (by simp [length])
      intro k hk
      rw [app,app,length]
      by_cases eq : k=w.length
      · rw [if_pos eq,if_pos eq]
        obtain ⟨nx,ny⟩ := clean c (by simp)
        have zz := gate _ _ _ _ (agree _ nx) (agree _ ny)
        cases op : c.1
        · simpa only [word,op,Bool.false_eq_true,↓reduceIte,bitAt,BitVec.getLsbD_or] using zz.2
        · simpa only [word,op,↓reduceIte,bitAt,BitVec.getLsbD_and] using zz.1
      · rw [if_neg eq,if_neg eq]; exact agree k hk
  have baseBits : ∀ (s : Bool) (r : Fin 30) (i : Fin 13),
      let a := bitAt r (seed.getD i.val 0)
      let b := bitAt r ((bank s).getD i.val 0)
      (a=true → b=true) ∧ (i.val ≠ 12 → a=b) ∧ (r.val≠0 → bitAt r 32767=true → a=b) := by decide +kernel
  have bits (r : Fin 30) (i : Nat) :
      let a := bitAt r (seed.getD i 0)
      let b := bitAt r (W.getD i 0)
      (a=true → b=true) ∧ (i≠12 → a=b) ∧ (r.val≠0 → bitAt r 32767=true → a=b) := by
    by_cases h : i<13
    · exact baseBits (side p q) r ⟨i,h⟩
    · rw [List.getD_eq_default seed _ (by change 13 ≤ i; omega),List.getD_eq_default W _ (by change 13 ≤ i; omega)]
      exact ⟨id,fun _ => rfl,fun _ _ => rfl⟩
  have reject : (32767 : BitVec 30) ∉ result := by
    intro member
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp member
    have high : result.getD j 0=32767 := (List.getD_eq_getElem _ _ hj).trans e
    have jValid : j≠12 := by
      rintro rfl
      have kept : result.getD 12 0 = W.getD 12 0 := previous program W 12 (by change 12 < 13; decide)
      have impossible : W.getD 12 0 ≠ 32767 := by cases h : side p q <;> simp [W,h,bank]
      exact impossible (kept.symm.trans high)
    let low := program.foldl step seed
    have ls : seed.length=13 := rfl
    have lw : W.length=13 := rfl
    have sz : low.length=result.length :=
      (runSize program seed).trans ((congrArg (fun n : Nat => n+program.length) (ls.trans lw.symm)).trans (runSize program W).symm)
    have jl : j < low.length := lt_of_lt_of_eq hj sz.symm
    have inlow : low.getD j 0 ∈ low := by rw [List.getD_eq_getElem low 0 jl]; exact List.getElem_mem jl
    have inc (v) (h : v∈seed) : v∈run [] := by
      change v∈normal
      simp only [seed,List.mem_append,List.mem_singleton] at h
      exact h.elim id (fun e => e ▸ (by decide +kernel : (0 : BitVec 30) ∈ normal))
    obtain ⟨D,length,cover⟩ := copy program seed [] (by simpa using plen) (by decide +kernel) (by decide +kernel) inc
    have inD := cover _ inlow
    have eqRule : ∀ a b c d : Bool, a=b → c=d → (a && c)=(b && d) ∧ (a || c)=(b || d) := by decide
    have impRule : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
        ((a&&c)=true → (b&&d)=true) ∧ ((a||c)=true → (b||d)=true) := by decide
    by_cases used : ∃ c∈program, touches c=true
    · have saving (P : List (Bool × Fin 30 × Fin 30)) (h : ∃ c∈P, touches c=true) :
          P.countP (fun c => !touches c) < P.length := by
        induction P with
        | nil => simp at h
        | cons c cs ih =>
          by_cases hit : touches c=true
          · simpa [List.countP_cons,hit] using (Nat.lt_succ_of_le (List.countP_le_length (p:=fun c => !touches c) (l:=cs)))
          · obtain ⟨g,hg,good⟩ := h
            have tail : g∈cs := (List.mem_cons.mp hg).resolve_left (fun eq => hit (eq ▸ good))
            have lt := ih ⟨g,tail,good⟩
            have neg : touches c=false := Bool.eq_false_iff.mpr hit
            simp [List.countP_cons,neg,lt]
      have dsize : D.length≤17 := by have save := saving program used; simp only [List.length_nil,Nat.zero_add] at length;omega
      apply oneMissing D dsize _ inD
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let r : Fin 30 := ⟨i,hi⟩
      change bitAt r ((low.getD j 0) ||| 1) = bitAt r 32767
      have mask : ∀ r : Fin 30, bitAt r 1 = decide (r.val=0) := by decide +kernel
      have bor (a b : BitVec 30) : bitAt r (a ||| b) = (bitAt r a || bitAt r b) := by simp [bitAt]
      rw [bor,mask]
      let f := bitAt r (low.getD j 0)
      change (f || decide (r.val=0)) = bitAt r 32767
      by_cases lead : r.val=0
      · have yes : bitAt r 32767=true := (show ∀ z : Fin 30, z.val=0 → bitAt z 32767=true by decide +kernel) _ lead
        exact (congrArg (fun x => f || x) (decide_eq_true lead)).trans ((Bool.or_true f).trans yes.symm)
      · have lowToHigh := compare r (fun a b => a=true → b=true) impRule (fun _ => False) program
            (fun _ _ => ⟨id,id⟩) seed W (ls.trans lw.symm) (fun k _ => (bits r k).1) j id
        have highToLow (positive : bitAt r 32767 = true) : f=true := by
          have eq := compare r Eq eqRule (fun _ => False) program (fun _ _ => ⟨id,id⟩)
            seed W (ls.trans lw.symm) (fun k _ => (bits r k).2.2 lead positive) j id
          exact eq.trans ((congrArg (bitAt r) high).trans positive)
        have valEq : f=bitAt r 32767 := Bool.eq_iff_iff.mpr
          ⟨fun h => (congrArg (bitAt r) high).symm.trans (lowToHigh h),highToLow⟩
        exact (congrArg (fun x => f || x) (decide_eq_false lead)).trans ((Bool.or_false f).trans valEq)
    · have dsize : D.length≤18 := by
        have sm := List.countP_le_length (p:=fun c => !touches c) (l:=program)
        simp only [List.length_nil,Nat.zero_add] at length
        omega
      have same : low.getD j 0=32767 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        let r : Fin 30 := ⟨i,hi⟩
        have clean (c) (h : c∈program) : c.2.1.val≠12 ∧ c.2.2.val≠12 := by
          have no (w : c.2.1.val=12 ∨ c.2.2.val=12) : False :=
            used ⟨c,h,decide_eq_true w⟩
          exact ⟨fun a => no (Or.inl a),fun b => no (Or.inr b)⟩
        have rr := compare r Eq eqRule (fun k => k=12) program clean seed W (ls.trans lw.symm)
          (fun k ne => (bits r k).2.1 ne) j jValid
        change bitAt r (low.getD j 0)=bitAt r (result.getD j 0) at rr
        exact rr.trans (congrArg (bitAt r) high)
      exact ordinary D dsize ((congrArg (fun x : BitVec 30 => x ∈ run D) same).mp inD)
  by_contra noWitness
  push Not at noWitness
  have out : result.getD (ren C.output) 0 = (32767 : BitVec 30) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i lt
    let r : Fin 30 := ⟨i,lt⟩
    let lab := row p q r
    let x := List.ofFn (fun j : Fin 10 => lab.1.testBit j.val)
    let add := (items.map (fun k => x.getD k false)).all id
    obtain ⟨mem,right,prim,extra⟩ := data p q r
    have hx : x.length=10 := by simp [x]
    have bankLen : W.length=13 := by cases side p q <;> rfl
    have init (j : Nat) : bitAt r (W.getD (ren j) 0) = (x++[add]).getD j false := by
      rw [app,hx]
      by_cases hi : j<10
      · simpa only [ren,show j<11 by omega,↓reduceIte,show j≠10 by omega,ite_false] using prim ⟨j,hi⟩
      by_cases he : j=10
      · subst j
        simpa only [ren,if_pos (by decide : 10<11),ite_true,add,supplied x hx] using extra
      · have large : 11 ≤ j := by omega
        simp only [ren,show ¬j<11 by omega,↓reduceIte,he,ite_false]
        rw [List.getD_eq_default W _ (by omega),List.getD_eq_default x _ (by omega)]
        simp [bitAt]
    have forward := simulate r C.gates (fun g hg => by simpa using mono g hg) (x++[add]) W 0
      (by simp [hx]) (by simp [bankLen]) (by change C.gates.length ≤ 18 at size; omega)
      (by cases side p q <;> rfl) (by cases side p q <;> rfl) init C.output
    change bitAt r (result.getD (ren C.output) 0) = bitAt r 32767
    exact forward.trans ((Classical.not_not.mp (noWitness lab mem)).trans right)
  by_cases h : ren C.output < result.length
  · apply reject
    rw [←out,List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ (by omega)] at out
    exact (by decide : (0 : BitVec 30) ≠ 32767) out
