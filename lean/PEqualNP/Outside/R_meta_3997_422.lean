import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3997_422
    (h₁ : ∀(n : Nat) (C : Circuit),FanInTwo C → C.eval (List.ofFn (fun _ : Fin n=>false))=false → ∀u v : Fin n,let p:=(fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)); ∃t,t+C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)≤C.size ∧ HasCircuitSize n (fun x=>C.eval (List.ofFn (Function.update (Function.update x u false) v false))) t)
    (h₂ : ∀(n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit),12≤n → (∀v : Fin n,(G.neighborSet v).ncard≤3) → FanInTwo C → let p := (fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)); let d := fun i : Fin n => C.gates.countP (fun g=>(p g).contains i.val); (∀v : Fin n,1≤d v) → (∀u v : Fin n,u≠v → ¬G.Adj u v → C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)≤7) → (∀v : Fin n,d v≤6) ∧ (∀S : Finset (Fin n),(∀v∈S,4≤d v) → S.card≤8))
    (h₃ : ∀(n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit),(∀v : Fin n,(G.neighborSet v).ncard=3) → (∀u : Fin n,∀w : G.Walk u u,w.IsCycle → 7≤w.length) → (∀x : Fin n→Bool,C.eval (List.ofFn x)=true ↔ ∃i j,G.Adj i j ∧ x i=true ∧ x j=true) → IsMinimalCircuit n C → C.size+1<2*n → let p := (fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)); let d := fun i : Fin n => C.gates.countP (fun g=>(p g).contains i.val); (∀v : Fin n,1≤d v) ∧ (∃u : Fin n,(C.output::C.gates.flatMap Gate.inputs).count u.val=1 ∧ ∀g∈C.gates,g.op≠.not → u.val∈g.inputs → ∀w∈g.inputs,w=u.val ∨ n≤w))
    (h₄ : ∀(n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit),30≤n → Even n → G.Colorable 2 → (∀v : Fin n,(G.neighborSet v).ncard=3) → (∀u : Fin n,∀w : G.Walk u u,w.IsCycle → 7≤w.length) → (∀x : Fin n→Bool,C.eval (List.ofFn x)=true ↔ ∃i j,G.Adj i j ∧ x i=true ∧ x j=true) → IsMinimalCircuit n C → C.size+1<2*n → let p := (fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)); let d := fun i : Fin n => C.gates.countP (fun g=>(p g).contains i.val); ((∀v : Fin n,d v≤6) ∧ (∀S : Finset (Fin n),(∀v∈S,4≤d v) → S.card≤8)) → (∃u : Fin n,(C.output::C.gates.flatMap Gate.inputs).count u.val=1 ∧ ∀g∈C.gates,g.op≠.not → u.val∈g.inputs → ∀w∈g.inputs,w=u.val ∨ n≤w) → ∃u v : Fin n,u≠v ∧ ¬G.Adj u v ∧ ∃t,t+8≤C.size ∧ HasCircuitSize n (fun x=>C.eval (List.ofFn (Function.update (Function.update x u false) v false))) t)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  intro n G f large even bip deg girth _ correct s lowSize possible
  classical
  have existsSize : ∃t : Nat,HasCircuitSize n f t:=⟨s,possible⟩
  obtain ⟨C,fan,cap,labels⟩:=Nat.find_spec existsSize
  have sz : C.size≤s:=cap.trans (Nat.find_min' existsSize possible)
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan,?_⟩
    intro D dFan same
    exact cap.trans (Nat.find_min' existsSize (show HasCircuitSize n f D.size from
      ⟨D,dFan,le_rfl,fun x=>(congrFun same x).trans (labels x)⟩))
  have right (x : Fin n→Bool) : C.eval (List.ofFn x)=true ↔ ∃i j,G.Adj i j ∧ x i=true ∧ x j=true := by
    rw [labels];exact correct x
  have cLow : C.size+1<2*n:=by omega
  let p:=(fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2))
  let d:=fun i : Fin n=>C.gates.countP (fun g=>(p g).contains i.val)
  have special:=h₃ n G C deg girth right minimal cLow
  have rel (u v : Fin n) : (fun x : Fin n→Bool=>C.eval (List.ofFn (Function.update (Function.update x u false) v false)))=
      (fun x=>f (Function.update (Function.update x u false) v false)) := funext (fun x=>labels _)
  by_cases pair : ∃u v : Fin n,u≠v ∧ ¬G.Adj u v ∧ 8≤C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)
  · obtain ⟨u,v,ne,non,big⟩:=pair
    have zero : C.eval (List.ofFn (fun _:Fin n=>false))=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨i,j,_,no,_⟩:=(right _).mp h
      contradiction
    obtain ⟨t,save,build⟩:=h₁ n C fan zero u v
    change t+C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)≤C.size at save
    rw [rel u v] at build
    exact ⟨u,v,ne,non,t,by omega,build⟩
  · have limits (u v : Fin n) (ne : u≠v) (non : ¬G.Adj u v) : C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)≤7 := by
      by_contra! high
      exact pair ⟨u,v,ne,non,high⟩
    have prof:=h₂ n G C (by omega) (fun v=>(deg v).le) fan special.1 limits
    obtain ⟨u,v,ne,non,t,save,build⟩:=h₄ n G C large even bip deg girth right minimal cLow prof special.2
    rw [rel u v] at build
    exact ⟨u,v,ne,non,t,by omega,build⟩
