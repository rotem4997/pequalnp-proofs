import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4035_534
    (columns :
      let z := fun (d m : Nat) => (List.range 11).map (fun i => (m+128).testBit (d / 8^i % 8))
      let count := fun (C : Circuit) (d : Nat) => ((List.range (11+C.size)).map (fun w =>
        (List.range 64).map (fun m => (C.wires (z d m)).getD w false))).toFinset.card
      ∀ (C : Circuit) (d : Nat), FanInTwo C → d∈([8098112054,7024370231,7876514230,7876514238,8394239046,8394243142,8167830598,8167863366] : List Nat) →
        (∀ m : Fin 64,C.eval (z d m.val)=(0xfffffaeaffc8f8c8 : Nat).testBit m.val) → 16≤count C d)
    (filtered :
      let z := fun (d m : Nat) => (List.range 11).map (fun i => (m+128).testBit (d / 8^i % 8))
      let count := fun (C : Circuit) (d : Nat) => ((List.range (11+C.size)).map (fun w =>
        (List.range 64).map (fun m => (C.wires (z d m)).getD w false))).toFinset.card
      let uses := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
      let test := fun (x : Fin 10→Bool) => (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))))
      ∀ C : Circuit, FanInTwo C → C.size≤18 → (∀ g∈C.gates,0∉uses g) →
        (∃ i k : Fin C.gates.length,∀ j : Fin C.gates.length,10∈uses (C.gates.get j) → j=i ∨ j=k) →
        (∀ d∈([8098112054,7024370231,7876514230,7876514238,8394239046,8394243142,8167830598,8167863366] : List Nat),16≤count C d) →
        ∃ x,C.eval (List.ofFn x ++ [!x 0])≠test x)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  let z := fun (d m : Nat) => (List.range 11).map (fun i => (m+128).testBit (d / 8^i % 8))
  let count := fun (C : Circuit) (d : Nat) => ((List.range (11+C.size)).map (fun w =>
    (List.range 64).map (fun m => (C.wires (z d m)).getD w false))).toFinset.card
  let uses := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
  let test := fun (x : Fin 10→Bool) => (List.finRange 5).any (fun i =>
    (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))))
  let f := fun x : Fin 10→Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  classical
  intro C hf size ok no0 two
  change ∀ x : Fin 10→Bool,C.eval (List.ofFn x ++ [!x 0])=f x at ok
  have usage (g : Gate) (legal : g∈C.gates) : uses g = if g.op=.not then g.inputs.take 1 else g.inputs := by
    have ops := (hf g legal).1
    change g.op=.and ∨ g.op=.or ∨ g.op=.not at ops
    have an : GateOp.and.eval [false,false]=false := rfl
    have oo : GateOp.or.eval [false,false]=false := rfl
    have nn : GateOp.not.eval [false,false]=true := rfl
    rcases ops with h|h|h <;> simp [uses,h,an,oo,nn]
  have take1 (l : List Nat) (w : Nat) : w∈l.take 1 ↔ l.head?=some w := by cases l <;> simp [eq_comm]
  have none (g : Gate) (mem : g∈C.gates) : 0∉uses g := by
    obtain ⟨j,hj,eqn⟩ := List.mem_iff_getElem.mp mem
    have h := no0 ⟨j,hj⟩
    subst g
    rw [usage _ (List.getElem_mem hj)]
    split
    · rw [take1]; exact h.1 (by assumption)
    · exact h.2 (by assumption)
  obtain ⟨a,b,bound⟩ := two
  have cap (j : Fin C.gates.length) (mem : 10∈uses (C.gates.get j)) : j=a ∨ j=b := by
    rw [usage _ (List.get_mem _ _)] at mem
    split at mem
    · exact (bound j).1 (by assumption) ((take1 _ _).mp mem)
    · exact (bound j).2 (by assumption) mem
  have restrictions : ∀ d∈([8098112054,7024370231,7876514230,7876514238,8394239046,8394243142,8167830598,8167863366] : List Nat),∀ m : Fin 64, ∃ x : Fin 10→Bool,
      z d m.val=List.ofFn x ++ [!x 0] ∧ f x=(0xfffffaeaffc8f8c8 : Nat).testBit m.val := by
    let liftRow := fun (d : Nat) (m : Fin 64) (i : Fin 10) => (m.val+128).testBit (d / 8^i.val % 8)
    have audit : (([8098112054,7024370231,7876514230,7876514238,8394239046,8394243142,8167830598,8167863366] : List Nat)).all (fun d => decide (∀ m : Fin 64,
        z d m.val=List.ofFn (liftRow d m) ++ [!(liftRow d m 0)] ∧ f (liftRow d m)=(0xfffffaeaffc8f8c8 : Nat).testBit m.val))=true := by decide
    intro d hd m
    exact ⟨liftRow d m,(of_decide_eq_true (List.all_eq_true.mp audit d hd)) m⟩
  have budget (d : Nat) (hd : d∈([8098112054,7024370231,7876514230,7876514238,8394239046,8394243142,8167830598,8167863366] : List Nat)) : 16≤count C d := by
    apply columns C d hf hd
    intro m
    obtain ⟨x,hx,goal⟩ := restrictions d hd m
    exact (congrArg C.eval hx).trans ((ok x).trans goal)
  obtain ⟨x,wrong⟩ := filtered C hf size none ⟨a,b,cap⟩ budget
  have same : ∀ y : Fin 10→Bool,f y=test y := by decide
  exact wrong ((ok x).trans (same x))
