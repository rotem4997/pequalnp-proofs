import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2706_648
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C' ∧
        C'.size ≤ C.size ∧
        ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C →
      (¬ ∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 14 C g1 g2) →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14,
            (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true) →
      27 ≤ C.size)
    (h3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C →
      (∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 14 C g1 g2) →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14,
            (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true) →
      27 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → (26 : ℕ) ≤ x1.size := by
  classical
  intro C a b hM ha hb
  dsimp only
  intro hA hB _ _
  have extend : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      ∃ y, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ x) = x ++ y ∧ y.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro x; exact ⟨[], (List.append_nil x).symm, rfl⟩
    | cons g gs ih =>
      intro x
      let z := g.op.eval (g.inputs.map fun i => x.getD i false)
      obtain ⟨y, hy, hyl⟩ := ih (x ++ [z])
      refine ⟨z :: y, ?_, by simp [hyl]⟩
      have hstep : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: gs, 0⟩ x =
          PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (x ++ [z]) := rfl
      rw [hstep, hy]
      simp [List.append_assoc]
  let g : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [g], 14 + C.gates.length⟩
  have hDM : PEqualNP.MetaComplexity.Monotone2 D := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hM k hk
    · have : k = g := by simpa using hk
      subst this
      exact ⟨Or.inr rfl, by simp [g]⟩
  have hDval : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) =
      ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false) := by
    intro x
    obtain ⟨y, hy, hyl⟩ := extend C.gates (List.ofFn x)
    have hw : C.wires (List.ofFn x) = List.ofFn x ++ y := hy
    have hlen : (C.wires (List.ofFn x)).length = 14 + C.gates.length := by
      rw [hw, List.length_append, List.length_ofFn, hyl]
    have hD : D.wires (List.ofFn x) = C.wires (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false)] := by
      change (C.gates ++ [g]).foldl _ _ = _
      rw [List.foldl_append]
      rfl
    change (D.wires (List.ofFn x)).getD (14 + C.gates.length) false = _
    rw [hD, ← hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]
    have key : ∀ p q : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p, q] = (p || q) := by
      intro p q; cases p <;> cases q <;> rfl
    exact key _ _
  have hEval : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
    intro x
    rw [hDval x]
    constructor
    · intro h
      by_contra hn
      obtain ⟨e1, e2⟩ := hB x hn
      rw [e1, e2] at h
      cases h
    · intro h
      rcases hA x h with e | e
      · rw [e]; rfl
      · rw [e]; exact Bool.or_true _
  have hGoal : 27 ≤ D.size := by
    rcases h1 D hDM with ⟨C', hMono', hRB', hSize', hEq'⟩
    have hEval' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
      intro x
      rw [hEq' x]
      exact hEval x
    by_cases hN : ∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 14 C' g1 g2
    · exact le_trans (h3 C' hMono' hRB' hN hEval') hSize'
    · exact le_trans (h2 C' hMono' hRB' hN hEval') hSize'
  have hsz : D.size = C.size + 1 := by
    change (C.gates ++ [g]).length = C.gates.length + 1
    simp
  omega
