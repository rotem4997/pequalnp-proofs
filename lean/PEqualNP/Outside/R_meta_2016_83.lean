import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2016_83
    (single : let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ (c d : Circuit) (a b : ℕ), FanInTwo c → c.size = 11 → circuitFun 7 c = f →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) c.gates d.gates →
      (∀ x, (d.wires (true :: List.ofFn x)).getD (c.output+1) false = (f x || x 2)) →
      (c.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length < 2)
    (pair : let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ (c d : Circuit) (a b : ℕ), FanInTwo c → c.size = 11 → circuitFun 7 c = f →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) c.gates d.gates →
      (∀ x, (d.wires (true :: List.ofFn x)).getD (c.output+1) false = (f x || x 0 || x 3)) →
      (c.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length ≥ 2) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  intro graph
  rintro ⟨c, fan, size, base, mixed⟩
  let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  have eBase : ∀ x : Fin 7 → Bool, graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = f x := by decide
  have eSingle : ∀ x : Fin 7 → Bool, graph (Fin.insertNth 0 false (Fin.insertNth 3 true x)) = (f x || x 2) := by decide
  have ePair : ∀ x : Fin 7 → Bool, graph (Fin.insertNth 0 true (Fin.insertNth 3 false x)) = (f x || x 0 || x 3) := by decide
  have hf : circuitFun 7 c = f := funext fun x => (congrFun base x).trans (eBase x)
  obtain ⟨a,b,d,hd,ports,vals⟩ := mixed false
  obtain ⟨u,v,t,ht,ports',vals'⟩ := mixed true
  have lo := single c d a b fan size hf ports (by
    intro x
    rw [← hd]
    exact (vals x).trans (eSingle x))
  have hi := pair c t u v fan size hf ports' (by
    intro x
    rw [← ht]
    exact (vals' x).trans (ePair x))
  exact (Nat.not_lt_of_ge hi) lo
