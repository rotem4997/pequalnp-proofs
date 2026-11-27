import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

-- The three restrictions use disjoint point sets and disjoint line sets.
-- Each restricted incidence graph has the cyclic Fano presentation of L_meta_634.
-- Only gates true with every input of a block switched on can survive its restriction.
-- The balance hypothesis asks for one block on which at most a third of the gates are true.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4199_721
    (compress : ∀ (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit), Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
      ∃ D : AndCountCircuit n, D.WellFormed ∧ D.Computes G ∧
        D.size ≤ C.gates.countP (fun g : Gate => GateOp.casesOn g.op true false false (fun _ => false) false))
    (balance : let G := SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧
          (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List Nat))
      let e : Fin 3 → Fin 14 → Fin 42 := fun r j =>
        Fin.ofNat 42 (if j.val < 7 then (9 * j.val + r.val) % 21
          else 21 + (9 * (j.val - 7) + r.val + 5) % 21)
      ∀ D : AndCountCircuit 42, D.WellFormed → D.Computes G →
        ∃ E : AndCountCircuit 42, ∃ r : Fin 3, E.WellFormed ∧ E.Computes G ∧
          E.size ≤ D.size ∧ 3 * {j : Fin E.size | E.gateVal (Finset.univ.image (e r)) j = true}.ncard ≤ E.size)
    (project : ∀ (n m : Nat) (e : Fin m → Fin n) (E : AndCountCircuit n), E.WellFormed →
      ∃ B : AndCountCircuit m, B.WellFormed ∧
        (∀ U : Finset (Fin m), B.eval U = E.eval (U.image e)) ∧
        B.size ≤ {j : Fin E.size | E.gateVal (Finset.univ.image e) j = true}.ncard)
    (fano : let F := SimpleGraph.fromRel (fun a b : Fin 14 =>
          a.val < 7 ∧ 7 ≤ b.val ∧
          (a.val + 7 - (b.val - 7)) % 7 ∈ ([0, 1, 3] : List Nat))
      ∀ B : AndCountCircuit 14, B.WellFormed → B.Computes F → 7 ≤ B.size) :
    ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧
          (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List Nat)) ∧
          x a = true ∧ x b = true) →
      21 ≤ C.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) := by
  let R : Fin 42 → Fin 42 → Prop := fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧
          (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List Nat)
  let G := SimpleGraph.fromRel R
  let S : Fin 14 → Fin 14 → Prop := fun a b : Fin 14 =>
          a.val < 7 ∧ 7 ≤ b.val ∧
          (a.val + 7 - (b.val - 7)) % 7 ∈ ([0, 1, 3] : List Nat)
  let F := SimpleGraph.fromRel S
  let e : Fin 3 → Fin 14 → Fin 42 := fun r j =>
        Fin.ofNat 42 (if j.val < 7 then (9 * j.val + r.val) % 21
          else 21 + (9 * (j.val - 7) + r.val + 5) % 21)
  have geometry : ∀ r : Fin 3, ∀ i j : Fin 14, G.Adj (e r i) (e r j) ↔ F.Adj i j := by
    change ∀ r : Fin 3, ∀ i j : Fin 14,
      (e r i ≠ e r j ∧ (R (e r i) (e r j) ∨ R (e r j) (e r i))) ↔
      (i ≠ j ∧ (S i j ∨ S j i))
    dsimp only [e, R, S]
    decide +kernel
  intro C hC hEval
  have evalG (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 42, G.Adj a b ∧ x a = true ∧ x b = true := by
    rw [hEval x]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have ne : a ≠ b := by
        intro eq
        subst b
        have := hab.1
        have := hab.2.1
        omega
      exact ⟨a, b, ⟨ne, Or.inl hab⟩, ha, hb⟩
    · rintro ⟨a, b, ⟨_, hab | hba⟩, ha, hb⟩
      · exact ⟨a, b, hab, ha, hb⟩
      · exact ⟨b, a, hba, hb, ha⟩
  obtain ⟨D, wf, correct, cost⟩ := compress 42 G C hC evalG
  obtain ⟨E, r, wfE, correctE, small, third⟩ := balance D wf correct
  obtain ⟨B, wfB, evalB, live⟩ := project 42 14 (e r) E wfE
  have lower : 7 ≤ B.size := by
    apply fano B wfB
    intro U
    rw [evalB U, correctE]
    constructor
    · rintro ⟨a, ha, b, hb, adj⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨i, hi, j, hj, (geometry r i j).mp adj⟩
    · rintro ⟨i, hi, j, hj, adj⟩
      exact ⟨e r i, Finset.mem_image_of_mem (e r) hi,
        e r j, Finset.mem_image_of_mem (e r) hj, (geometry r i j).mpr adj⟩
  have seven := lower.trans live
  change 3 * {j : Fin E.size | E.gateVal (Finset.univ.image (e r)) j = true}.ncard ≤ E.size at third
  have result : 21 ≤ D.size := by omega
  exact result.trans cost
