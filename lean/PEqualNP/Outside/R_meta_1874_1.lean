import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Child 1: one AND reading an AND can be removed below 63 gates (gate elimination).
-- Child 2: without an AND reading an AND the two-wire separation needs 63 gates.
theorem PEqualNP.Outside.R_meta_1874_1 :
  (let D : Finset (Fin 13) := {0, 1, 3, 9}
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
    ∀ (C : Circuit) (a b : ℕ), ok C a b → C.size < 63 → (∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
      ∃ (E : Circuit) (a' b' : ℕ), ok E a' b' ∧ E.size < C.size) →
  (let D : Finset (Fin 13) := {0, 1, 3, 9}
    let P := fun (p l : Fin 13) =>
      List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
    let N := fun (Q : Finset (Fin 13)) =>
      List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
    let G := fun (Q : Finset (Fin 13)) =>
      Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
    ∀ (C : Circuit) (a b : ℕ),
      let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
      Monotone2 C ∧ ReadsBack 26 C ∧
      (∀ p l : Fin 13, p - l ∈ D → (V a (P p l) && V b (P p l)) = true) ∧
      (∀ Q : Finset (Fin 13), G Q → (V a (N Q) && V b (N Q)) = false) ∧
      (∃ Q : Finset (Fin 13), G Q ∧ V a (N Q) < V b (N Q)) ∧
      (∃ Q : Finset (Fin 13), G Q ∧ V b (N Q) < V a (N Q)) →
      ¬ (∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) → 63 ≤ C.size) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro shrink flat
  have abstract : ∀ (ok : Circuit → ℕ → ℕ → Prop) (nested : Circuit → Prop),
      (∀ (C : Circuit) (a b : ℕ), ok C a b → C.size < 63 → nested C →
        ∃ (E : Circuit) (a' b' : ℕ), ok E a' b' ∧ E.size < C.size) →
      (∀ (C : Circuit) (a b : ℕ), ok C a b → ¬ nested C → 63 ≤ C.size) →
      ∀ (C : Circuit) (a b : ℕ), ok C a b → 63 ≤ C.size := by
    intro ok nested hs hf
    have lower : ∀ n : ℕ, ∀ (C : Circuit) (a b : ℕ), C.size = n → ok C a b → 63 ≤ C.size := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n smaller =>
        intro C a b hsize hok
        by_cases hnested : nested C
        · by_contra hbound
          obtain ⟨E, a', b', hEok, hEsmall⟩ := hs C a b hok (by omega) hnested
          have := smaller E.size (by omega) E a' b' rfl hEok
          omega
        · exact hf C a b hok hnested
    intro C a b hok
    exact lower C.size C a b rfl hok
  have lt_of (x y : Bool) (hx : x = false) (hy : y = true) : x < y := by
    subst hx; subst hy; decide
  intro C a b hmon hback _ _ x8 x9 x10 x11 x12 hpos hneg hex1 hex2
  have hpos' : ∀ p l : Fin 13, p - l ∈ x8 → (x12 a (x9 p l) && x12 b (x9 p l)) = true := by
    intro p l h
    obtain ⟨h1, h2⟩ := hpos p l h
    rw [h1, h2]; rfl
  have hneg' : ∀ Q : Finset (Fin 13), x11 Q → (x12 a (x10 Q) && x12 b (x10 Q)) = false := by
    intro Q h
    rcases hneg Q h with h1 | h1 <;> simp [h1]
  obtain ⟨Q1, g1, f1, t1⟩ := hex1
  obtain ⟨Q2, g2, f2, t2⟩ := hex2
  exact abstract _ _ shrink flat C a b
    ⟨hmon, hback, hpos', hneg', ⟨Q1, g1, lt_of _ _ f1 t1⟩, ⟨Q2, g2, lt_of _ _ f2 t2⟩⟩
