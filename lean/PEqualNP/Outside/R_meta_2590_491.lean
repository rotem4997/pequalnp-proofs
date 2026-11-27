import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 30000000 in
theorem PEqualNP.Outside.R_meta_2590_491
  (compress : ∀ C : Circuit, Monotone2 C → C.size≤19 → circuitFun 10 C = (fun x : Fin 10 → Bool => decide (∃i : Fin 5,
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
         x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
         x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) = true)) →
    ∃(B : Circuit) (w : ℕ) (q : Bool), IsAO2 10 B ∧ (16≤B.size ∧ B.size≤18) ∧ (w≠0 ∧ w<10+B.size ∧ ∀j (g : Gate), 10+j≤w → B.gates[j]?=some g → 0∉g.inputs) ∧
      ∀x : Fin 10→Bool, let h := (B.wires (List.ofFn (Function.update x 0 false))).getD w false;
      circuitFun 10 B (Function.update x 0 (if q then x 0 && h else x 0 || h)) = circuitFun 10 C x)
  (andRows : ∀ (B : Circuit) (w : ℕ), IsAO2 10 B → (16≤B.size ∧ B.size≤18) → (w≠0 ∧ w<10+B.size ∧ ∀j (g : Gate), 10+j≤w → B.gates[j]?=some g → 0∉g.inputs) →
    let row (k : ℕ) (i : Fin 10) := k.testBit i.val
    let guard (k : ℕ) := (B.wires (List.ofFn (Function.update (row k) 0 false))).getD w false
    let read (k : ℕ) := circuitFun 10 B (Function.update (row k) 0 ((row k 0) && guard k))
    (∀ k ∈ ([2,16,32] : List ℕ), guard k=true) →
     ¬((∀ k ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), read k=true) ∧
       (∀ k ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), read k=false)))
  (orRows : ∀ (B : Circuit) (w : ℕ), IsAO2 10 B → (16≤B.size ∧ B.size≤18) → (w≠0 ∧ w<10+B.size ∧ ∀j (g : Gate), 10+j≤w → B.gates[j]?=some g → 0∉g.inputs) →
    let row (k : ℕ) (i : Fin 10) := k.testBit i.val
    let guard (k : ℕ) := (B.wires (List.ofFn (Function.update (row k) 0 false))).getD w false
    let read (k : ℕ) := circuitFun 10 B (Function.update (row k) 0 ((row k 0) || guard k))
    (∀ k ∈ ([50,104,116,138,208,276,402,548,554,770] : List ℕ), guard k=false) →
     ¬((∀ k ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), read k=true) ∧
       (∀ k ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), read k=false))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hc hs he
  let F := (fun x : Fin 10 → Bool => decide (∃i : Fin 5,
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
         x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
         x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) = true))
  have form : circuitFun 10 C=F := by
    funext x
    have table : ∀x : Fin 10→Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)=F x := by decide
    exact (he x).trans (table x)
  obtain ⟨B,w,q,law,size,legal,simulate⟩ := compress C hc hs form
  let row (k : ℕ) (i : Fin 10) := k.testBit i.val
  let guard (k : ℕ) := (B.wires (List.ofFn (Function.update (row k) 0 false))).getD w false
  have simulateRow (k : ℕ) : circuitFun 10 B (Function.update (row k) 0
      (if q then row k 0 && guard k else row k 0 || guard k)) = F (row k) :=
    (simulate (row k)).trans (congrFun form _)
  have pivotal (k : ℕ) (bit0 : row k 0=false) (off : F (row k)=false)
      (on : F (Function.update (row k) 0 true)=true) : guard k=q := by
    have l := simulateRow k
    have r := (simulate (Function.update (row k) 0 true)).trans (congrFun form _)
    simp only [guard,Function.update_self,Function.update_idem] at r l ⊢
    rw [on] at r
    rw [off,bit0] at l
    generalize (B.wires (List.ofFn (Function.update (row k) 0 false))).getD w false = b at l r ⊢
    cases q <;> cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.true_or,Bool.or_true,
      Bool.false_or,Bool.or_false,Bool.true_and,Bool.and_true,Bool.false_and,Bool.and_false] at l r ⊢ <;>
      first | rfl | exact Bool.noConfusion (l.symm.trans r)
  have pos : ∀k∈([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), F (row k)=true := by decide
  have neg : ∀k∈([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), F (row k)=false := by decide
  cases q with
  | false =>
    apply orRows B w law size legal
    · intro k hk
      have data : ∀k∈([50,104,116,138,208,276,402,548,554,770] : List ℕ), row k 0=false ∧ F (row k)=false ∧ F (Function.update (row k) 0 true)=true := by decide
      obtain ⟨bit0,off,on⟩:=data k hk
      exact pivotal k bit0 off on
    · exact ⟨fun k h=>(simulateRow k).trans (pos k h),fun k h=>(simulateRow k).trans (neg k h)⟩
  | true =>
    apply andRows B w law size legal
    · intro k hk
      have data : ∀k∈([2,16,32] : List ℕ), row k 0=false ∧ F (row k)=false ∧ F (Function.update (row k) 0 true)=true := by decide
      obtain ⟨bit0,off,on⟩:=data k hk
      exact pivotal k bit0 off on
    · exact ⟨fun k h=>(simulateRow k).trans (pos k h),fun k h=>(simulateRow k).trans (neg k h)⟩
