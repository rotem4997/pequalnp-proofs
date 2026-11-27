import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2063_1
    (hDeg :
      have d : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have rows : Bool → List Bool → Prop := fun (sign : Bool) (x : List Bool) =>
        if sign then
          ∃ (i l : Fin (13 : ℕ)), i - l ∈ d ∧
            x = (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = i)) ++
              List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = l)
        else
          ∃ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) ∧
            (∀ (l : Fin (13 : ℕ)), {i ∈ Q | i - l ∈ d}.card ≤ (2 : ℕ)) ∧
            x = (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ Q)) ++
              List.ofFn fun (l : Fin (13 : ℕ)) => Decidable.decide (∀ i ∈ Q, i - l ∉ d);
      have valid : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C ∧
          ∀ (s : Bool) (x : List Bool), rows s x → C.eval x = s;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), valid C → C.size < (64 : ℕ) →
        (∃ g ∈ C.gates, g.inputs.length < (2 : ℕ) ∨ g.inputs.getD (0 : ℕ) (0 : ℕ) = g.inputs.getD (1 : ℕ) (0 : ℕ)) →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit), valid C' ∧ C'.size < C.size)
    (hCore :
      have d : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have rows : Bool → List Bool → Prop := fun (sign : Bool) (x : List Bool) =>
        if sign then
          ∃ (i l : Fin (13 : ℕ)), i - l ∈ d ∧
            x = (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = i)) ++
              List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = l)
        else
          ∃ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) ∧
            (∀ (l : Fin (13 : ℕ)), {i ∈ Q | i - l ∈ d}.card ≤ (2 : ℕ)) ∧
            x = (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ Q)) ++
              List.ofFn fun (l : Fin (13 : ℕ)) => Decidable.decide (∀ i ∈ Q, i - l ∉ d);
      have valid : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C ∧
          ∀ (s : Bool) (x : List Bool), rows s x → C.eval x = s;
      have ands : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop :=
        fun C i j =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone (26 : ℕ) C i j;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        valid C → C.size < (64 : ℕ) →
          (∀ (i j : ℕ), ands C i j →
            ∃ (x : List Bool), rows Bool.false x ∧ (C.wires x).getD ((26 : ℕ) + i) Bool.false = Bool.true) →
          (∃ (i j : ℕ), ands C i j) →
          (∀ g ∈ C.gates, g.inputs.length = (2 : ℕ) ∧ g.inputs.getD (0 : ℕ) (0 : ℕ) ≠ g.inputs.getD (1 : ℕ) (0 : ℕ)) →
          ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit), valid C' ∧ C'.size < C.size) :
    have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  intro x1 x2 x3 x4 C hMono hRB hOK hSize hDirty hNest
  let d : Finset (Fin 13) := {0, 1, 3, 9}
  let rows : Bool → List Bool → Prop := fun sign x =>
    if sign then
      ∃ i l : Fin 13, i - l ∈ d ∧
        x = (List.ofFn fun a : Fin 13 => Decidable.decide (a = i)) ++
          List.ofFn fun a : Fin 13 => Decidable.decide (a = l)
    else
      ∃ Q : Finset (Fin 13), Q.card = 4 ∧
        (∀ l : Fin 13, {i ∈ Q | i - l ∈ d}.card ≤ 2) ∧
        x = (List.ofFn fun a : Fin 13 => Decidable.decide (a ∈ Q)) ++
          List.ofFn fun l : Fin 13 => Decidable.decide (∀ i ∈ Q, i - l ∉ d)
  let valid : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun A =>
    PEqualNP.MetaComplexity.Monotone2 A ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 A ∧
      ∀ s x, rows s x → A.eval x = s
  let ands : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun A i j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt A i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt A j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.EdgeOwnership.InCone 26 A i j
  have hd : ∀ a : Fin 13, a ∈ d ↔ x1 a = true := by
    intro a
    change a ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
      Decidable.decide (a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 9) = true
    simp
  have hd_not : ∀ a : Fin 13, a ∉ d ↔ x1 a = false := by
    intro a
    rw [hd a]
    cases x1 a <;> simp
  have hfilt : ∀ (Q : Finset (Fin 13)) (l : Fin 13),
      {i ∈ Q | i - l ∈ d} = {i ∈ Q | x1 (i - l) = true} :=
    fun Q l => Finset.filter_congr fun i _ => hd (i - l)
  have hpack : ∀ Q : Finset (Fin 13),
      ((List.ofFn fun a : Fin 13 => Decidable.decide (a ∈ Q)) ++
        List.ofFn fun l : Fin 13 => Decidable.decide (∀ i ∈ Q, i - l ∉ d)) = x3 Q := by
    intro Q
    apply congrArg (List.append _)
    apply congrArg List.ofFn
    funext l
    exact decide_eq_decide.mpr (forall₂_congr fun i _ => hd_not (i - l))
  have bridge : ∀ A : PEqualNP.CircuitLowerBounds.Circuit,
      valid A ↔ PEqualNP.MetaComplexity.Monotone2 A ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 A ∧ x4 A := by
    intro A
    constructor
    · rintro ⟨hM, hR, rule⟩
      refine ⟨hM, hR, ⟨?_, ?_⟩⟩
      · intro p l hp
        exact rule true _ ⟨p, l, (hd (p - l)).2 hp, rfl⟩
      · intro Q hQ
        have hx : rows false (x3 Q) := by
          refine ⟨Q, hQ.1, ?_, (hpack Q).symm⟩
          intro l
          rw [hfilt]
          exact hQ.2 l
        exact rule false _ hx
    · rintro ⟨hM, hR, hPos, hNeg⟩
      refine ⟨hM, hR, ?_⟩
      intro s x row
      cases s
      · obtain ⟨Q, hcard, hlines, rfl⟩ := row
        rw [hpack]
        exact hNeg Q ⟨hcard, fun l => by rw [← hfilt]; exact hlines l⟩
      · obtain ⟨p, l, hp, rfl⟩ := row
        exact hPos p l ((hd (p - l)).1 hp)
  have hv : valid C := (bridge C).mpr ⟨hMono, hRB, hOK⟩
  by_cases hD : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0
  · obtain ⟨C', hv', hsz⟩ := hDeg C hv hSize hD
    obtain ⟨hM', hR', hOK'⟩ := (bridge C').mp hv'
    exact ⟨C', hM', hR', hOK', hsz⟩
  · have hStrict : ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
      intro g hg
      refine ⟨Nat.le_antisymm (hMono g hg).2 (Nat.le_of_not_lt fun hlt => hD ⟨g, hg, Or.inl hlt⟩), ?_⟩
      intro heq
      exact hD ⟨g, hg, Or.inr heq⟩
    have hDirty' : ∀ i j : ℕ, ands C i j →
        ∃ x, rows false x ∧ (C.wires x).getD (26 + i) false = true := by
      intro i j hij
      obtain ⟨Q, hQ, hw⟩ := hDirty i j hij.1 hij.2.1 hij.2.2
      refine ⟨x3 Q, ?_, hw⟩
      refine ⟨Q, hQ.1, ?_, (hpack Q).symm⟩
      intro l
      rw [hfilt]
      exact hQ.2 l
    have hNest' : ∃ i j : ℕ, ands C i j := hNest
    obtain ⟨C', hv', hsz⟩ := hCore C hv hSize hDirty' hNest' hStrict
    obtain ⟨hM', hR', hOK'⟩ := (bridge C').mp hv'
    exact ⟨C', hM', hR', hOK', hsz⟩
