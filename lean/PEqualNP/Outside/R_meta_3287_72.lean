import Mathlib.Tactic
import Mathlib.Data.List.GetD
import PEqualNP.Defs

-- Remove an inessential auxiliary input without spending a gate, and exhibit cofactors.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3287_72
    (lower14 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) 14)
    (remaining : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 14 ∧
      D.gates.countP (fun g => g.op.eval [false]) = 2 ∧
      (∀ j ∈ [0,1,2,4,7,8], D.gates.countP (fun g => g.inputs.contains j) ≤ 1) ∧
      (∀ i : Fin 10, ∃ p q : Fin 10 → Bool,
        (∀ j, j ≠ i → p j = q j) ∧ D.eval (List.ofFn p) ≠ D.eval (List.ofFn q)) ∧
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool,
        p i = b ∧ q i = b ∧ D.eval (List.ofFn p) ≠ D.eval (List.ofFn q)) ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.false]) x1.gates = (2 : ℕ) → (∀ x5 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.contains x5) x1.gates ≤ (1 : ℕ)) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))]) ≠ (fun (x7 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) x6 := by
  intro C fan size notCount sparse
  by_contra! agrees
  let target (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),
    (1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let input (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x
  let liftInput (x : Fin 9 → Bool) := input x (x 0 || x 2)
  let evaluate (y : Fin 10 → Bool) := C.eval (List.ofFn y)
  let difference (i : Fin 10) := ∃ p q : Fin 10 → Bool,
    (∀ j, j ≠ i → p j = q j) ∧ evaluate p ≠ evaluate q
  have inputList (x : Fin 9 → Bool) (b : Bool) : List.ofFn (input x b) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ_last]
    simp [input]
    rfl
  have correctly (x : Fin 9 → Bool) : evaluate (liftInput x) = target x := by
    change C.eval (List.ofFn (input x (x 0 || x 2))) = target x
    rw [inputList]
    exact agrees x
  have auxiliary : difference 9 := by
    by_contra h
    change ¬ ∃ p q : Fin 10 → Bool, (∀ j, j ≠ 9 → p j = q j) ∧ evaluate p ≠ evaluate q at h
    push_neg at h
    let renumber (i : ℕ) := if i < 9 then i else if i = 9 then 9 + C.gates.length else i - 1
    let rename (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map renumber⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map rename, renumber C.output⟩
    have allowed : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      obtain ⟨before, member, rfl⟩ := List.mem_map.mp hg
      simpa [rename] using fan before member
    have budget : D.size ≤ 14 := by
      change (C.gates.map rename).length ≤ 14
      rw [List.length_map]
      exact le_of_eq size
    apply lower14
    refine ⟨D, allowed, budget, ?_⟩
    intro x
    let inputs := List.ofFn x
    let runGate (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have inputLength : inputs.length = 9 := List.length_ofFn
    have get (vals : List Bool) (bound : vals.length ≤ C.gates.length) (i : ℕ) :
        (inputs ++ [false] ++ vals).getD i false = (inputs ++ vals).getD (renumber i) false := by
      rw [List.append_assoc]
      by_cases before : i < 9
      · simp only [renumber, ite_eq_left before]
        have atInput : i < inputs.length := by simpa [inputLength] using before
        rw [List.getD_append _ _ _ _ atInput, List.getD_append _ _ _ _ atInput]
      · have past : inputs.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ past]
        by_cases atRemoved : i = 9
        · subst i
          have index : renumber 9 = 9 + C.gates.length := by simp [renumber]
          have mapped : (inputs ++ vals).getD (9 + C.gates.length) false = false := by
            apply List.getD_eq_default
            rw [List.length_append]
            omega
          rw [index, mapped]
          simp [inputLength, List.getD_eq_getElem?_getD]
        · have index : renumber i = i - 1 := by simp [renumber, before, atRemoved]
          rw [index, List.getD_append_right _ _ _ _ (by omega : inputs.length ≤ i - 1)]
          have skip : [false].length ≤ i - inputs.length := by simp; omega
          rw [List.getD_append_right _ _ _ _ skip]
          simp only [List.length_singleton]
          congr 1
    have simulation (gs : List PEqualNP.CircuitLowerBounds.Gate) (vals : List Bool)
        (bound : vals.length + gs.length ≤ C.gates.length) :
        ∃ rest : List Bool, rest.length ≤ C.gates.length ∧
          gs.foldl runGate (inputs ++ [false] ++ vals) = inputs ++ [false] ++ rest ∧
          (gs.map rename).foldl runGate (inputs ++ vals) = inputs ++ rest := by
      induction gs generalizing vals with
      | nil => exact ⟨vals, by simpa using bound, rfl, rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => (inputs ++ [false] ++ vals).getD i false)
        have evalEq : runGate (inputs ++ vals) (rename g) = inputs ++ vals ++ [bit] := by
          simp only [runGate, rename, List.map_map, bit]
          congr 2
          apply congrArg g.op.eval
          exact List.map_congr_left (fun i _ => (get vals (by omega) i).symm)
        have bound' : (vals ++ [bit]).length + gs.length ≤ C.gates.length := by
          simp only [List.length_append, List.length_nil, List.length_cons] at bound ⊢
          omega
        simpa only [List.map_cons, List.foldl_cons, evalEq, runGate, bit, List.append_assoc]
          using ih (vals ++ [bit]) bound'
    obtain ⟨rest, length, before, after⟩ := simulation C.gates [] (by simp)
    have dropEq : D.eval (List.ofFn x) = evaluate (input x false) := by
      change ((C.gates.map rename).foldl runGate inputs).getD (renumber C.output) false = _
      simp only [List.append_nil] at before after
      rw [after, ← get rest length C.output, ← before]
      change C.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn (input x false))
      rw [inputList]
    have off : ∀ j : Fin 10, j ≠ 9 → input x false j = liftInput x j := by
      intro j
      refine Fin.lastCases ?_ (fun k _ => ?_) j
      · exact fun hn => (hn rfl).elim
      · simp [input, liftInput]
    exact dropEq.trans ((h _ _ off).trans (correctly x))
  have allEssential (i : Fin 10) : difference i := by
    refine Fin.lastCases auxiliary (fun k => ?_) i
    let low (j : Fin 9) : ℕ := ![20,1,9,4,1,1,2,4,8] j
    let high (j : Fin 9) : ℕ := ![21,3,13,12,17,33,66,132,264] j
    let bits (m : ℕ) (j : Fin 9) := m.testBit j.val
    have witnesses : ∀ j : Fin 9,
        (∀ t : Fin 10, t ≠ j.castSucc → liftInput (bits (low j)) t = liftInput (bits (high j)) t) ∧
        target (bits (low j)) ≠ target (bits (high j)) := by decide +kernel
    exact ⟨_, _, (witnesses k).1, by simpa only [correctly] using (witnesses k).2⟩
  have allCofactors (i : Fin 10) (b : Bool) : ∃ p q : Fin 10 → Bool,
      p i = b ∧ q i = b ∧ evaluate p ≠ evaluate q := by
    let low (j : Fin 10) (b : Bool) : ℕ := if b then ![1,2,4,8,16,32,64,128,256,1] j else 0
    let high (j : Fin 10) (b : Bool) : ℕ :=
      if b then ![3,3,6,11,17,33,66,131,259,3] j else ![6,12,3,3,3,3,3,3,3,24] j
    let bits (m : ℕ) (j : Fin 9) := m.testBit j.val
    have witnesses : ∀ (j : Fin 10) (b : Bool),
        liftInput (bits (low j b)) j = b ∧ liftInput (bits (high j b)) j = b ∧
        target (bits (low j b)) ≠ target (bits (high j b)) := by decide +kernel
    exact ⟨_, _, (witnesses i b).1, (witnesses i b).2.1,
      by simpa only [correctly] using (witnesses i b).2.2⟩
  exact remaining ⟨C, fan, size, notCount, sparse, allEssential, allCofactors, agrees⟩
