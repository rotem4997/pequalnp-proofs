import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count the unused operand slot of each inversion. A cover gives a circuit
-- four gates smaller after deleting one of its cubic vertices.
-- The structural child asks for an independent set of a specified size.
set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_4107_418
    (slots : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let twoReads : Fin n → Nat := fun v => (C.gates.filter fun g => g.inputs.contains v.val).length
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ g ∈ C.gates, g.inputs.length + (g.op.eval [false]).toNat ≤ 2) →
      (∀ v ∉ A, 2 ≤ twoReads v) →
      A.card + 3*Aᶜ.card + C.gates.countP (fun g => g.op.eval [false]) ≤
        C.size + 1 + (Aᶜ.filter fun v => twoReads v = 2).card)
    (cover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      (∀ v ∉ A, (G.neighborSet v).ncard=3) → (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      ∃ v ∉ A, ∃ s, s+5 ≤ A.card+G.edgeFinset.card+T.card ∧
        HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let rd := fun v : Fin n => C.gates.filter fun g => g.inputs.contains v.val
      let f := graphFun G A
      (∀ v ∉ A, (G.neighborSet v).ncard=3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2)) →
      (∀ v ∉ A, 2 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ((rd v).length=3 → ∀ g ∈ rd v, g.op=.or)) →
      (∃ v ∉ A, (rd v).length=2 ∧ ∃ g ∈ rd v, g.op=.not) →
      (∀ v ∉ A, ∀ s, HasCircuitSize n (fun x => f (Function.update x v false)) s → C.size ≤ s+3) →
      ∃ I ⊆ Aᶜ, (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) ∧
        2*(Aᶜ.filter fun v => (rd v).length=2).card ≤ Aᶜ.card+2*I.card+2*C.gates.countP (fun g => g.op.eval [false])) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : List PEqualNP.CircuitLowerBounds.Gate) (x15 : PEqualNP.CircuitLowerBounds.Gate) (x16 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x14 ++ x15 :: x16 → (x15.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x18 < x1 + x14.length, x15.inputs = [x18]) ∨ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x18 < x1 + x14.length, ∃ x19 < x1 + x14.length, x18 ≠ x19 ∧ x15.inputs = [x18, x19]) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  dsimp only
  intro n G dec A C deg girth isolated edge minimum computes normalized bounds hasNot
  have arity (g : Gate) (hg : g ∈ C.gates) :
      g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2) := by
    obtain ⟨pre,post,eq⟩ := List.append_of_mem hg
    rcases normalized pre g post eq with ⟨op,a,_,hin⟩ | ⟨op,a,_,b,_,ab,hin⟩
    · have hn : GateOp.not.eval [false] = true := rfl
      simp [op,hin,hn]
    · have ha : GateOp.and.eval [false] = false := rfl
      have ho : GateOp.or.eval [false] = false := rfl
      rcases op with op|op <;> simp [op,hin,ab,ha,ho]
  have row (g : Gate) (hg : g ∈ C.gates) : g.inputs.length + (g.op.eval [false]).toNat ≤ 2 := by
    rw [(arity g hg).2]
    cases g.op.eval [false] <;> decide
  have lower := slots n G A C minimum computes row (fun v hv => (bounds v hv).1)
  change A.card + 3*Aᶜ.card + C.gates.countP (fun g => g.op.eval [false]) ≤
    C.size + 1 + (Aᶜ.filter (fun v : Fin n => (C.gates.filter (fun g => g.inputs.contains v.val)).length=2)).card at lower
  by_contra missing
  have noSaving (v : Fin n) (hv : v ∉ A) (s : ℕ)
      (h : HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s) : C.size ≤ s+3 := by
    by_contra! small
    exact missing ⟨v,hv,s,by omega,h⟩
  obtain ⟨I,inside,independent,credit⟩ :=
    charge n G A C deg girth isolated minimum computes arity bounds hasNot noSaving
  change 2*(Aᶜ.filter (fun v : Fin n => (C.gates.filter (fun g => g.inputs.contains v.val)).length = 2)).card ≤
    Aᶜ.card + 2*I.card + 2*C.gates.countP (fun g => g.op.eval [false]) at credit
  have cv : ∀ u v, G.Adj u v → u ∈ Aᶜ \ I ∨ v ∈ Aᶜ \ I := by
    intro u v e
    by_cases inI : u ∈ I
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (isolated _ _ e.symm),
        fun h => independent u inI v h e⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (isolated _ _ e),inI⟩)
  have dA (v : Fin n) (hv : v ∈ A) : G.degree v = 0 := by
    exact (G.degree_eq_zero v).mpr (fun u adj => isolated v u adj hv)
  have dU (v : Fin n) (hv : v ∈ Aᶜ) : G.degree v=3 := by
    rw [←G.ncard_neighborSet]; exact deg v (Finset.mem_compl.mp hv)
  have count := G.sum_degrees_eq_twice_card_edges
  rw [←A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dU] at count
  simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul] at count
  obtain ⟨v,hv,s,hsize,small⟩ := cover n G A (Aᶜ \ I) cv deg isolated edge
  rw [Finset.card_sdiff_of_subset inside] at hsize
  have isize := Finset.card_le_card inside
  exact missing ⟨v,hv,s,by omega,small⟩
