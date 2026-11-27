import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Either some AND directly reads another AND, or a nested AND is only reached
-- through other gates. The first child is the direct surgery on the two-wire
-- property. The second is a shrink that keeps the two distinguished wires
-- (allowing the second wire to grow only where the first is already false).
-- The glue is the case split, then a transport of the two-wire property.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5258_1
    (hDirect :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let G := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let ok := fun (C : Circuit) (a b : ℕ) =>
        let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p - l ∈ D → (V a (P p l) && V b (P p l)) = true) ∧
        (∀ Q : Finset (Fin 13), G Q → (V a (N Q) && V b (N Q)) = false) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V a (N Q) < V b (N Q)) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V b (N Q) < V a (N Q))
      ∀ (C : Circuit) (a b : ℕ), ok C a b → C.size < 63 →
        (∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
          26 + i ∈ (gateAt C j).inputs) →
        ∃ (E : Circuit) (a' b' : ℕ), ok E a' b' ∧ E.size < C.size)
    (hIndirect :
      ∀ (C : Circuit) (a b : ℕ),
        Monotone2 C → ReadsBack 26 C → C.size < 63 →
        (∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
          InCone 26 C i j) →
        (¬∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
          26 + i ∈ (gateAt C j).inputs) →
        ∃ (E : Circuit) (a' b' : ℕ),
          Monotone2 E ∧ ReadsBack 26 E ∧ E.size < C.size ∧
          ∀ x : List Bool,
            (E.wires x).getD a' false = (C.wires x).getD a false ∧
            ((C.wires x).getD b false = true → (E.wires x).getD b' false = true) ∧
            ((C.wires x).getD a false = true →
              (E.wires x).getD b' false = (C.wires x).getD b false)) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) =>   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), x5 x6 x7 x8 → x6.size < (63 : ℕ) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x5 x12 x13 x14 ∧ x12.size < x6.size := by
  intro x1 x2 x3 x4 x5 C a b hok hsz hcone
  dsimp only [x5] at hok
  rcases hok with ⟨hmon, hback, hpos, hneg, hex1, hex2⟩
  have and_eq_true {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
    revert h; cases x <;> cases y <;> decide
  have and_eq_false {x y : Bool} (h : (x && y) = false) : x = false ∨ y = false := by
    revert h; cases x <;> cases y <;> decide
  have lt_bool {x y : Bool} (h : x < y) : x = false ∧ y = true := by
    revert h; cases x <;> cases y <;> decide
  have false_lt_true : false < true := by decide
  by_cases hdir :
      ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
        26 + i ∈ (gateAt C j).inputs
  · have hok' : (let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let G := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let ok := fun (C : Circuit) (a b : ℕ) =>
        let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p - l ∈ D → (V a (P p l) && V b (P p l)) = true) ∧
        (∀ Q : Finset (Fin 13), G Q → (V a (N Q) && V b (N Q)) = false) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V a (N Q) < V b (N Q)) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V b (N Q) < V a (N Q))
      ok C a b) := by
      dsimp
      refine ⟨hmon, hback, ?_, ?_, ?_, ?_⟩
      · intro p l hp; exact hpos p l hp
      · intro Q hQ; exact hneg Q hQ
      · exact hex1
      · exact hex2
    obtain ⟨E, a', b', hEok, hEsz⟩ := hDirect C a b hok' hsz hdir
    refine ⟨E, a', b', ?_, hEsz⟩
    dsimp only [x5, x1, x2, x3, x4]
    dsimp at hEok
    exact hEok
  · obtain ⟨E, a', b', hmonE, hbackE, hEsz, hwire⟩ :=
      hIndirect C a b hmon hback hsz hcone hdir
    refine ⟨E, a', b', ?_, hEsz⟩
    dsimp only [x5]
    refine ⟨hmonE, hbackE, ?_, ?_, ?_, ?_⟩
    · intro p l hp
      obtain ⟨ha, hb⟩ := and_eq_true (hpos p l hp)
      obtain ⟨hwa, hwb_true, hwb_eq⟩ := hwire (x2 p l)
      rw [hwa, ha, hwb_eq ha, hb]
      rfl
    · intro Q hQ
      obtain ⟨hwa, hwb_true, hwb_eq⟩ := hwire (x3 Q)
      rcases and_eq_false (hneg Q hQ) with ha | hb
      · rw [hwa, ha]; rfl
      · cases hA : (C.wires (x3 Q)).getD a false
        · rw [hwa, hA]; rfl
        · rw [hwa, hA, hwb_eq hA, hb]; rfl
    · obtain ⟨Q, hQ, hlt⟩ := hex1
      obtain ⟨ha, hb⟩ := lt_bool hlt
      obtain ⟨hwa, hwb_true, _⟩ := hwire (x3 Q)
      exact ⟨Q, hQ, by rw [hwa, ha, hwb_true hb]; exact false_lt_true⟩
    · obtain ⟨Q, hQ, hlt⟩ := hex2
      obtain ⟨hb, ha⟩ := lt_bool hlt
      obtain ⟨hwa, _, hwb_eq⟩ := hwire (x3 Q)
      exact ⟨Q, hQ, by rw [hwa, ha, hwb_eq ha, hb]; exact false_lt_true⟩
