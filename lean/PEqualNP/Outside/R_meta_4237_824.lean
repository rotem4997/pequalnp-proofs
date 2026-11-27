import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- A witness records shared gates in topological order. For each earlier-later
-- pair, an input separates whether those gates agree with the output.
theorem PEqualNP.Outside.R_meta_4237_824 :
(∀ (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
  ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
    ¬(∃ Q : Finset (Fin C.gates.length), Q.card = k+1 ∧
      (∀ j ∈ Q, ∃ a b : Fin C.gates.length, a ≠ b ∧ j < a ∧ n+j.val ∈ (gateAt C a.val).inputs ∧
          j < b ∧ n+j.val ∈ (gateAt C b.val).inputs) ∧
      ∀ t ∈ Q, ∀ i ∈ Q, t < i → ∃ x : Fin n → Bool,
        (∃ U : Finset (Fin n), U.card ≤ 2 ∧ G.IsClique (U : Set (Fin n)) ∧
          ((∀ v, x v = true ↔ v ∈ U) ∨ (∀ v, x v = true ↔ v ∉ U ∧ ∃ w ∈ U, G.Adj v w))) ∧
        gateVal n C i.val x = circuitFun n C x ∧ gateVal n C t.val x ≠ circuitFun n C x) →
    G.edgeFinset.card ≤ (2^(k+1)-1)*(C.size+1)) →
(∃ k K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
  (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
  ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    (∃ Q : Finset (Fin C.gates.length), Q.card = k+1 ∧
      (∀ j ∈ Q, ∃ a b : Fin C.gates.length, a ≠ b ∧ j < a ∧ n+j.val ∈ (gateAt C a.val).inputs ∧
          j < b ∧ n+j.val ∈ (gateAt C b.val).inputs) ∧
      ∀ t ∈ Q, ∀ i ∈ Q, t < i → ∃ x : Fin n → Bool,
        (∃ U : Finset (Fin n), U.card ≤ 2 ∧ G.IsClique (U : Set (Fin n)) ∧
          ((∀ v, x v = true ↔ v ∈ U) ∨ (∀ v, x v = true ↔ v ∉ U ∧ ∃ w ∈ U, G.Adj v w))) ∧
        gateVal n C i.val x = circuitFun n C x ∧ gateVal n C t.val x ≠ circuitFun n C x) →
    G.edgeFinset.card ≤ K*(C.size+1)) →
∃ (x1 : ℕ) (x2 : ℕ), ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj], (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) → (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) → ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 → PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ → ∀ x11 ⊆ {x12 ∈ x4.edgeFinset | ¬∃ (x13 : Fin x3) (x14 : Fin x3), x12 = s(x13, x14) ∧ ∃ (x15 : Fin x8.gates.length), PEqualNP.EdgeOwnership.Owns x3 x8 (↑x15) x13 x14 ∧ ∀ (x16 x17 : Fin x3), PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x15) (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true → x4.Adj x16 x17}, (∀ (x13 : Fin x3), {x14 ∈ x11 | x13 ∈ x14}.card = (0 : ℕ) ∨ x1 < {x14 ∈ x11 | x13 ∈ x14}.card) → x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  intro easy hard
  obtain ⟨k,K,whenWitness⟩ := hard
  let A := 2^(k+1)-1
  refine ⟨0,max A K,?_⟩
  intro n G inst degree girth givenC givenMono givenFun S inside _
  let candidates (s : ℕ) := ∃ C : Circuit, C.size = s ∧ Monotone2 C ∧ circuitFun n C = graphFun G ∅
  have existsSize : ∃ s, candidates s := ⟨givenC.size,givenC,rfl,givenMono,givenFun⟩
  obtain ⟨C,hsize,mono,computes⟩ := Nat.find_spec existsSize
  have minimal : IsMinimalMonoCircuit n C := by
    refine ⟨mono,fun D dMono same => ?_⟩
    exact hsize.le.trans (Nat.find_min' existsSize ⟨D,rfl,dMono,same.trans computes⟩)
  have cost := minimal.2 givenC givenMono (givenFun.trans computes.symm)
  have small : G.edgeFinset.card ≤ max A K*(C.size+1) := by
    by_cases witness : ∃ Q : Finset (Fin C.gates.length), Q.card = k+1 ∧
      (∀ j ∈ Q, ∃ a b : Fin C.gates.length, a ≠ b ∧ j < a ∧ n+j.val ∈ (gateAt C a.val).inputs ∧
          j < b ∧ n+j.val ∈ (gateAt C b.val).inputs) ∧
      ∀ t ∈ Q, ∀ i ∈ Q, t < i → ∃ x : Fin n → Bool,
        (∃ U : Finset (Fin n), U.card ≤ 2 ∧ G.IsClique (U : Set (Fin n)) ∧
          ((∀ v, x v = true ↔ v ∈ U) ∨ (∀ v, x v = true ↔ v ∉ U ∧ ∃ w ∈ U, G.Adj v w))) ∧
        gateVal n C i.val x = circuitFun n C x ∧ gateVal n C t.val x ≠ circuitFun n C x
    · exact (whenWitness n G degree girth C minimal computes witness).trans
        (Nat.mul_le_mul_right _ (le_max_right A K))
    · exact (easy k n G girth C mono computes witness).trans
        (Nat.mul_le_mul_right _ (le_max_left A K))
  have edges : S ⊆ G.edgeFinset := fun _ h => (Finset.mem_filter.mp (inside h)).1
  exact (Finset.card_le_card edges).trans
    (small.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right cost 1)))
