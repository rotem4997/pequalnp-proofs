import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2766_317
    (normalize : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10)))
      let T (D : Circuit) := (∃ m ∈ ([3,12,24,17,33,264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false])=false) ∧
          (∃ m ∈ ([50,116,208,276,402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true])=true)
      ∀ D : Circuit, D.gates.length=14 → Monotone2 D → D.output=23 →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3])=f x) → T D)
    (exclude : let T (D : Circuit) := (∃ m ∈ ([3,12,24,17,33,264] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false])=false) ∧
          (∃ m ∈ ([50,116,208,276,402] : List ℕ), D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true])=true)
      let v (D : Circuit) (m : ℕ) := D.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3])
      ∀ D : Circuit, D.gates.length=14 → Monotone2 D → D.output=23 → T D →
        (∀ m ∈ ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ), v D m=true) →
        ¬∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), v D m=false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C form count good
  obtain ⟨size,cout,first,restr⟩ := form
  have allops : Monotone2 C := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    have gs := restr i hi
    dsimp only at gs
    rcases gs with eq | ⟨a,_,eq⟩ | ⟨a,b,_,_,_,eq|eq⟩
    · rw [eq];exact ⟨Or.inl rfl,by decide⟩
    · have z := (List.countP_eq_zero.mp count) C.gates[i] (List.getElem_mem hi)
      rw [eq] at z; contradiction
    · rw [eq];exact ⟨Or.inl rfl,by simp⟩
    · rw [eq];exact ⟨Or.inr rfl,by simp⟩
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10)))
  have projection : circuitFun 9 C=f := by
    rw [good]
    decide +kernel
  cases hg : C.gates with
  | nil => simp [hg] at size
  | cons h gs =>
    have hfirst : h=⟨.or,[0,3]⟩ := by simpa [hg] using first
    subst h
    let D : Circuit := ⟨gs,23⟩
    have dm : Monotone2 D := fun g h => allops g (by rw [hg];exact List.mem_cons_of_mem _ h)
    have dlen : D.gates.length=14 := by change gs.length=14;simp [hg] at size;omega
    have exactD (x : Fin 9 → Bool) : D.eval (List.ofFn x++[x 0 || x 3])=f x := by
      have q := congrFun projection x
      change (C.wires (List.ofFn x)).getD C.output false=_ at q
      rw [cout] at q
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD 23 false = _ at q
      rw [hg,List.foldl_cons] at q
      have val : GateOp.or.eval ([0,3].map fun i => (List.ofFn x).getD i false)=(x 0 || x 3) := by
        change ([0,3].map fun i => (List.ofFn x).getD i false).any id = _
        simp [List.getD_eq_getElem?_getD]
      rw [val] at q;exact q
    have mark := normalize D dlen dm rfl exactD
    apply exclude D dlen dm rfl mark
    · intro m hm
      refine (exactD (fun i => m.testBit i.val)).trans ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    · intro m hm
      refine (exactD (fun i => m.testBit i.val)).trans ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
