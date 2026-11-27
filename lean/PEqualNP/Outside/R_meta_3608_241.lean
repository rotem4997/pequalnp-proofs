import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3608_241
    (normal : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (V : Fin n → Fin m → Bool), PEqualNP.MetaComplexity.FanInTwo C →
      let I := (fun _ : Fin m => false) :: List.ofFn V
      ∃ S : List (Fin m → Bool),
        S.length ≤ C.gates.countP (fun g => !(g.op.eval [false])) ∧
        (∀ (k : ℕ) (hk : k < S.length),
        ∃ a ∈ I ++ S.take k, ∃ b ∈ I ++ S.take k, ∃ u v : Bool,
          S[k] = fun r => (a r ^^ u) && (b r ^^ v)) ∧
        ∃ a ∈ I ++ S, ∃ u : Bool, ∀ r : Fin m,
          C.eval (List.ofFn (fun i => V i r)) = (a r ^^ u))
    (finiteSearch : ∀ S : List (Fin 512 → Bool), S.length ≤ 12 →
      let V := fun (i : Fin 10) (r : Fin 512) =>
        if i.val < 9 then (0 + r.val).testBit i.val else (0 + r.val).testBit 0 || (0 + r.val).testBit 2
      let I := (fun _ : Fin 512 => false) :: List.ofFn V
      (∀ (k : ℕ) (hk : k < S.length),
        ∃ a ∈ I ++ S.take k, ∃ b ∈ I ++ S.take k, ∃ u v : Bool,
          S[k] = fun r => (a r ^^ u) && (b r ^^ v)) →
      ∀ a ∈ I ++ S, ∀ u : Bool, ∃ r : Fin 512,
        (a r ^^ u) ≠ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => r.val &&& e == e)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (14 : ℕ) →       x1.output = (23 : ℕ) →         (∀ x5 ∈ x1.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) →           (∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), x6 < x7 ∧ (3 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (6 : ℕ) ∧ ↑x7 < (13 : ℕ) ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x8 : Fin x1.gates.length), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → x8 = x6 ∨ x8 = x7) →             have x7 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;             have x8 : Finset ℕ := {x8 ∈ Finset.range (23 : ℕ) | (2 : ℕ) ≤ List.count x8 x7};             (∀ x9 < (23 : ℕ), x9 ∈ x7) → x8.card ≤ (3 : ℕ) → (∀ x11 ∈ x1.gates, ∀ (x13 x14 : Fin (9 : ℕ)), x13 ≠ x14 → x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11.inputs = [↑x13, ↑x14] → ↑x13 ∈ x8 ∨ ↑x14 ∈ x8) → ∃ x12 < (512 : ℕ), x1.eval ((List.ofFn fun (x13 : Fin (9 : ℕ)) => x12.testBit ↑x13) ++ [x12.testBit (0 : ℕ) || x12.testBit (2 : ℕ)]) ≠ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x13 : ℕ) => x12 &&& x13 == x13 := by
  intro C fan size _ _ hnot
  dsimp only
  intro _ _ _
  obtain ⟨i, j, hij, _, _, _, hi, hj, _⟩ := hnot
  let P := fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [false]
  have count : 2 ≤ C.gates.countP P := by
    rw [List.countP_eq_length_filter]
    have hmem (k : Fin C.gates.length) (h : (C.gates.get k).op = .not) :
        P (C.gates.get k) = true := by
      change (C.gates.get k).op.eval [false] = true
      rw [h]
      rfl
    have enough : ((List.finRange C.gates.length).filter (fun k => P (C.gates.get k))).length ≥ 2 := by
      let A := ((List.finRange C.gates.length).filter (fun k => P (C.gates.get k)))
      have ai : i ∈ A := List.mem_filter.mpr ⟨List.mem_finRange _, hmem i hi⟩
      have aj : j ∈ A := List.mem_filter.mpr ⟨List.mem_finRange _, hmem j hj⟩
      have distinct : i ≠ j := ne_of_lt hij
      have sub : ({i,j} : Finset (Fin C.gates.length)) ⊆ A.toFinset := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact List.mem_toFinset.mpr ai
        · exact List.mem_toFinset.mpr (Finset.mem_singleton.mp hk ▸ aj)
      have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
      simpa [A, distinct] using bound
    calc
      2 ≤ _ := enough
      _ = ((List.finRange C.gates.length).filter (P ∘ C.gates.get) |>.map C.gates.get).length :=
        (List.length_map ..).symm
      _ = _ := by rw [← List.filter_map, List.map_get_finRange]
  have total := C.gates.length_eq_countP_add_countP P
  have complement : (fun g => decide (¬ P g = true)) = (fun g => !(P g)) := by
    funext g
    cases P g <;> rfl
  rw [complement] at total
  change C.gates.length = 14 at size
  let V := fun (i : Fin 10) (r : Fin 512) =>
        if i.val < 9 then (0 + r.val).testBit i.val else (0 + r.val).testBit 0 || (0 + r.val).testBit 2
  obtain ⟨S, budget, built, a, ha, u, eval⟩ := normal 10 512 C V fan
  have budget' : S.length ≤ 12 := by
    change S.length ≤ C.gates.countP (fun g => !(P g)) at budget
    omega
  obtain ⟨r, hr⟩ := finiteSearch S budget' built a ha u
  refine ⟨r.val, r.isLt, ?_⟩
  have hx : List.ofFn (fun i => V i r) =
      List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 2] := by
    simp only [V, Nat.zero_add]
    rw [List.ofFn_succ_last]
    congr 1
  rw [← hx, eval]
  exact hr
