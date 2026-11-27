import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The forced cofactor is the edge function of a six-cycle with two free OR inputs.
-- Fixing the selector drops each of its effective readers, so at most three can remain.
-- Move the selector immediately after its tapped gate before testing the residual programs.
theorem PEqualNP.Outside.R_meta_2191_17 :
  (let f := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)
   ∀ (A B : Circuit) (k : Bool), FanInTwo A → FanInTwo B →
     (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = (f x || x 0 || x 3)) →
     10 + B.gates.countP (fun g =>
       (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (8 + A.size))
       ≤ A.size + B.size) →
  (let f := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)
   let h := fun x : Fin 8 → Bool => f x || x 0 || x 3
   ∀ (A B : Circuit) (k : Bool), FanInTwo A → FanInTwo B → A.output + 1 = 8 + A.size →
     10 + B.gates.countP (fun g =>
       (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (8 + A.size))
       ≤ A.size + B.size →
     (∀ i : Fin 8, (circuitFun 8 A ≠ fun x => x i) ∧ (circuitFun 8 A ≠ fun x => !(x i))) →
     (∀ x, f x ≠ h x → circuitFun 8 A x = !k) →
     (∀ x, B.eval (A.wires (List.ofFn x) ++ [circuitFun 8 A x]) = f x) →
     (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) → 14 ≤ A.size + B.size) →
  have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     PEqualNP.MetaComplexity.FanInTwo x4 →       x3.size + x4.size ≤ (13 : ℕ) →         x5 < (8 : ℕ) + x3.size →           have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x3.wires (List.ofFn x11);           have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x5 Bool.false;           (∀ (x13 : Fin (8 : ℕ)), (x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → x12 x14 = !x6) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x11 x15 ++ [x12 x15]) = x1 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x11 x16 ++ [x6]) ≠ x2 x16 := by
  intro saving sparse
  dsimp only at saving sparse ⊢
  intro A B tap k fanA fanB budget valid notLiteral switches neutral
  by_contra! forced
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  let ren := fun (f : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map f)
  have growth (gs : List Gate) (w : List Bool) :
      ∃ more, run gs w = w ++ more ∧ more.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run],rfl⟩
    | cons g gs ih =>
      obtain ⟨rest,e,len⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: rest,?_,by simp [len]⟩
      change run gs (step w g) = _
      rw [e]
      simp [step,List.append_assoc]
  have runLength (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    obtain ⟨more,e,n⟩ := growth gs w
    simp [e,n]
  have runAppend (l r : List Gate) (w : List Bool) : run (l ++ r) w = run r (run l w) := by
    simp only [run, List.foldl_append]
  have translate (f : ℕ → ℕ) (u v : List Bool)
      (read : ∀ (z : List Bool) i, (v ++ z).getD (f i) false = (u ++ z).getD i false)
      (gs : List Gate) : ∃ z, run gs u = u ++ z ∧ run (gs.map (ren f)) v = v ++ z ∧ z.length = gs.length := by
    induction gs using List.reverseRecOn with
    | nil => exact ⟨[],by simp [run],by simp [run],rfl⟩
    | append_singleton gs g ih =>
      obtain ⟨z,old,fresh,len⟩ := ih
      let b := g.op.eval (g.inputs.map fun i => (u ++ z).getD i false)
      refine ⟨z ++ [b],?_,?_,by simp [len]⟩
      · rw [runAppend,old]
        simp only [run,List.foldl_cons,List.foldl_nil,step,b,List.append_assoc]
      · rw [List.map_append,runAppend,fresh]
        simp only [List.map_cons,List.map_nil,run,List.foldl_cons,List.foldl_nil,step,ren,
          List.map_map,Function.comp_def,read,b,List.append_assoc]
  have notInput : 8 ≤ tap := by
    by_contra! lt
    let i : Fin 8 := ⟨tap,lt⟩
    apply (notLiteral i).1
    funext x
    obtain ⟨z,base,_⟩ := growth A.gates (List.ofFn x)
    change (run A.gates (List.ofFn x)).getD tap false = x i
    rw [base,List.getD_append _ _ _ _ (by simp; omega),List.getD_eq_getElem _ _ (by simp; omega)]
    exact List.getElem_ofFn _
  let stop := tap + 1 - 8
  let first := A.gates.take stop
  let rest := A.gates.drop stop
  let d := 8 + first.length
  let m := 8 + A.size
  have stopBound : stop ≤ A.gates.length := by
    change tap < 8 + A.gates.length at valid
    dsimp [stop]
    omega
  have firstLen : first.length = stop := by simp [first, Nat.min_eq_left stopBound]
  have lastAt : tap + 1 = d := by dsimp [d]; rw [firstLen]; dsimp [stop]; omega
  have restLen : d + rest.length = m := by
    change 8 + first.length + (A.gates.drop stop).length = 8 + A.gates.length
    rw [firstLen,List.length_drop]
    omega
  have parts : first ++ rest = A.gates := List.take_append_drop _ _
  let shift := fun i : ℕ => if i < d then i else i + 1
  let perm := fun i : ℕ => if i < d then i else if i < m then i + 1 else if i = m then d else i
  let P : Circuit := ⟨first,tap⟩
  let Q : Circuit := ⟨rest.map (ren shift) ++ B.gates.map (ren perm),perm B.output⟩
  have fp : FanInTwo P := by
    intro g hg
    exact fanA g (parts ▸ List.mem_append_left rest hg)
  have fq : FanInTwo Q := by
    intro g hg
    obtain left | right := List.mem_append.mp hg
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp left
      have h := fanA a (parts ▸ List.mem_append_right first ha)
      exact ⟨h.1,by simpa [ren] using h.2⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp right
      have h := fanB a ha
      exact ⟨h.1,by simpa [ren] using h.2⟩
  have total : P.size + Q.size = A.size + B.size := by
    change first.length + (rest.map (ren shift) ++ B.gates.map (ren perm)).length = A.gates.length + B.gates.length
    simp only [List.length_append,List.length_map]
    have h := congrArg List.length parts
    rw [List.length_append] at h
    omega
  have value (x : Fin 8 → Bool) : circuitFun 8 P x = (A.wires (List.ofFn x)).getD tap false := by
    let u := run first (List.ofFn x)
    have hu : u.length = d := by simp [u,runLength,d]
    obtain ⟨z,old,_⟩ := growth rest u
    change u.getD tap false = (run A.gates (List.ofFn x)).getD tap false
    rw [← parts,runAppend]
    change _ = (run rest u).getD tap false
    rw [old,List.getD_append _ _ _ _ (by omega)]
  have transport (x : Fin 8 → Bool) (b : Bool) :
      Q.eval (P.wires (List.ofFn x) ++ [b]) = B.eval (A.wires (List.ofFn x) ++ [b]) := by
    let u := run first (List.ofFn x)
    have hu : u.length = d := by simp [u,runLength,d]
    have inserted (z : List Bool) (i : ℕ) :
        ((u ++ [b]) ++ z).getD (shift i) false = (u ++ z).getD i false := by
      by_cases h : i < d
      · have a : i < u.length := by omega
        simp only [shift,ite_eq_left h,List.append_assoc,List.getD_append _ _ _ _ a]
      · have a : u.length ≤ i := by omega
        have a' : (u ++ [b]).length ≤ i+1 := by simp [hu]; omega
        simp only [shift,ite_eq_right h,List.getD_append_right _ _ _ _ a',
          List.getD_append_right _ _ _ _ a,List.length_append,List.length_singleton]
        congr 1
        omega
    obtain ⟨z,old,new,len⟩ := translate shift u (u ++ [b]) inserted rest
    have lengthSum : (u ++ z).length = m := by simp [hu,len,restLen]
    have between (i : ℕ) :
        ((u ++ [b]) ++ z).getD (perm i) false = ((u ++ z) ++ [b]).getD i false := by
      by_cases firstPart : i < d
      · have a : i < u.length := by omega
        simp only [perm,ite_eq_left firstPart,List.append_assoc,List.getD_append _ _ _ _ a]
      by_cases middle : i < m
      · have e : perm i = shift i := by simp [perm,shift,firstPart,middle]
        rw [e, inserted]
        exact (List.getD_append (u ++ z) [b] false i (by rw [lengthSum]; exact middle)).symm
      by_cases endAt : i = m
      · subst i
        have hd : d ≤ m := by omega
        have e : perm m = d := by simp [perm, Nat.not_lt.mpr hd]
        rw [e,List.getD_append (u ++ [b]) z false d (by simp [hu]),
          List.getD_append_right u [b] false d (by omega),
          List.getD_append_right (u ++ z) [b] false m (by omega),hu,lengthSum]
        simp
      · have e : perm i = i := by simp [perm,firstPart,middle,endAt]
        rw [e]
        have ln : ((u ++ [b]) ++ z).length ≤ i := by simp [hu,len]; omega
        have lo : ((u ++ z) ++ [b]).length ≤ i := by
          rw [List.length_append,lengthSum,List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ ln,List.getD_eq_default _ _ lo]
    let u0 := (u ++ z) ++ [b]
    let v0 := (u ++ [b]) ++ z
    have sizes : v0.length = u0.length := by simp [u0,v0]
    have hu0 : u0.length = m + 1 := by
      change ((u ++ z) ++ [b]).length = _
      rw [List.length_append,lengthSum,List.length_singleton]
    have atBase (w : List Bool) (i : ℕ) : (v0 ++ w).getD (perm i) false = (u0 ++ w).getD i false := by
      by_cases inside : i < u0.length
      · have bound : perm i < v0.length := by
          change (if i < d then i else if i < m then i+1 else if i=m then d else i) < _
          rw [sizes,hu0]
          split_ifs <;> omega
        rw [List.getD_append _ _ _ _ bound,List.getD_append _ _ _ _ inside]
        exact between i
      · have e : perm i = i := by
          have a : ¬ i < d := by omega
          have a' : ¬ i < m := by omega
          have ne : i ≠ m := by omega
          simp [perm,a,a',ne]
        rw [e,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),sizes]
    obtain ⟨w,oldB,newB,_⟩ := translate perm u0 v0 atBase B.gates
    change (run (rest.map (ren shift) ++ B.gates.map (ren perm)) ((run first (List.ofFn x)) ++ [b])).getD (perm B.output) false =
      (run B.gates ((run A.gates (List.ofFn x)) ++ [b])).getD B.output false
    rw [runAppend, ← parts,runAppend]
    change (run (B.gates.map (ren perm)) (run (rest.map (ren shift)) (u ++ [b]))).getD _ _ =
      (run B.gates ((run rest u) ++ [b])).getD _ _
    rw [new,old]
    change (run (B.gates.map (ren perm)) v0).getD _ _ = (run B.gates u0).getD _ _
    rw [newB,oldB]
    exact atBase w B.output
  have forceP (x : Fin 8 → Bool) : Q.eval (P.wires (List.ofFn x) ++ [k]) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4) || x 0 || x 3) := (transport x k).trans (forced x)
  have limit := saving P Q k fp fq forceP
  have result := sparse P Q k fp fq lastAt limit
    (by simpa only [funext value] using notLiteral)
    (by intro x hx; rw [value]; exact switches x hx)
    (by intro x; rw [value,transport]; exact neutral x) forceP
  omega
