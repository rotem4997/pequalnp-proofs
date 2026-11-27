import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Set vertex four to false. Two gates reading either polarity can both disappear.
-- With at most one such reader, the same remaining circuit must realize two different eight-input functions.
theorem PEqualNP.Outside.R_meta_1666_873
    (cofactor : ¬HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (eliminate : let read := fun g : Gate => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 4 || i == 9)
      let input := fun (b : Bool) (x : Fin 8 → Bool) => [x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7,!b]
      ∀ D : Circuit, FanInTwo D → 2 ≤ D.gates.countP read →
      (∃ x, D.eval (input false x)=false) →
      ∃ R : Circuit, FanInTwo R ∧ R.size+2≤D.size ∧
        ∀ x, R.eval (List.ofFn x)=D.eval (input false x))
    (singleRead : let read := fun g : Gate => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 4 || i == 9)
      let input := fun (b : Bool) (x : Fin 8 → Bool) => [x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7,!b]
      let z := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ D : Circuit, FanInTwo D → D.size≤14 → D.gates.countP read≤1 →
      (∀ x, D.eval (input false x)=z x) →
      ∃ x, D.eval (input true x) ≠ (z x || x 0 || x 3))
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let f := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let input := fun (b : Bool) (x : Fin 8 → Bool) => [x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7,!b]
  let read := fun g : Gate => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => i == 4 || i == 9)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have headVal (g : PEqualNP.CircuitLowerBounds.Gate) (tail : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: tail, o⟩ (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    let w := List.ofFn x
    have hl : w.length = 9 := by simp [w]
    change (tail.foldl step (step w g)).getD 9 false = _
    rw [preserved tail (step w g) 9 (by simp [step, hl])]
    simpa only [step, w, List.length_ofFn] using
      atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
  have truth : ∀ (b : Bool) (x : Fin 8 → Bool),
      (let t : Fin 9 → Bool := (4 : Fin 9).insertNth b x
       (t 0 && t 1) || (t 1 && t 2) || (t 2 && t 3) || (t 3 && t 4) || (t 4 && t 0) ||
       (t 0 && t 5) || (t 1 && t 6) || (t 2 && t 7) || (t 3 && t 8) || (t 5 && t 7) ||
       (t 6 && t 8) || (t 8 && t 5)) = (if b then (f x || x 0 || x 3) else f x) := by
    decide +kernel
  intro C fan first eq
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil =>
    have h := first (fun _ => false)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false=true at h
    contradiction
  | cons g rest =>
    by_contra small
    let D : Circuit := ⟨rest,o⟩
    have size : D.size≤14 := by
      change ¬16≤rest.length+1 at small
      change rest.length≤14
      omega
    have mon : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem g ha)
    have common (b : Bool) (x : Fin 8 → Bool) :
        D.eval (input b x) = (if b then (f x || x 0 || x 3) else f x) := by
      let t : Fin 9 → Bool := (4 : Fin 9).insertNth b x
      have val := (headVal g rest o t).symm.trans (first t)
      have at4 : t 4=b := by simp [t]
      change g.op.eval (g.inputs.map fun i => (List.ofFn t).getD i false) = !(t 4) at val
      have listed : ∀ (b : Bool) (x : Fin 8 → Bool),
          List.ofFn ((4 : Fin 9).insertNth (α:=fun _ => Bool) b x) ++ [!b]=input b x := by decide +kernel
      have start : step (List.ofFn t) g=input b x := by
        change List.ofFn t ++ [g.op.eval _]=_
        rw [val,at4]
        exact listed b x
      have orig := congrFun eq t
      change D.eval (step (List.ofFn t) g) = _ at orig
      rw [start] at orig
      exact orig.trans (truth b x)
    have zero (x : Fin 8 → Bool) : D.eval (input false x)=f x := common false x
    by_cases two : 2≤D.gates.countP read
    · obtain ⟨R,fr,sr,e⟩ := eliminate D mon two ⟨fun _ => false,by simpa [f,input] using zero (fun _ => false)⟩
      apply cofactor
      exact ⟨R,fr,by omega,fun x => (e x).trans (zero x)⟩
    · obtain ⟨x,bad⟩ := singleRead D mon size (by omega : D.gates.countP read≤1) zero
      exact bad (common true x)
