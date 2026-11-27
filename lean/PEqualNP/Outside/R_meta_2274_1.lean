import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2274_1
    (norm :
      let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
          (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ hit x) ∧ D.size ≤ C.size ∧
          ∃ (op : PEqualNP.CircuitLowerBounds.GateOp) (rest : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
            D.gates = ⟨op, [a, b]⟩ :: rest ∧ a < 14 ∧ b < 14 ∧ a ≠ b)
    (orFirst :
      let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let tailOK := fun (T : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin 14) =>
        ∀ x : Fin 14 → Bool, T.eval (List.ofFn x ++
          [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x 0, x j]]) = true ↔ hit x
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (rest : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
        C.gates = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ :: rest → a < 14 → b < 14 → a ≠ b → PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
        ∃ T : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 T ∧ T.size + 1 ≤ C.size ∧
          (tailOK T 1 ∨ tailOK T 7 ∨ tailOK T 9))
    (andEdge :
      let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let withoutEdge := fun T : PEqualNP.CircuitLowerBounds.Circuit =>
        (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
          (T.eval (List.ofFn x) = true ↔ hit x)) ∧
        T.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (rest : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
        C.gates = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ :: rest → ((a, b) ∈ edges ∨ (b, a) ∈ edges) → PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
        ∃ T : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 T ∧ ((T.size + 2 ≤ C.size ∧ withoutEdge T) ∨
          (T.size + 1 ≤ C.size ∧ ∀ x : Fin 14 → Bool, T.eval (List.ofFn x) = true ↔ hit x)))
    (andOff :
      let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (rest : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
        C.gates = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ :: rest → a < 14 → b < 14 →
        ¬ ((a, b) ∈ edges ∨ (b, a) ∈ edges) → PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
        ∃ T : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 T ∧ T.size + 1 ≤ C.size ∧
          ∀ x : Fin 14 → Bool, T.eval (List.ofFn x) = true ↔ hit x) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 : Fin (14 : ℕ) → Bool), x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x5) = Bool.true ↔ x2 x5)) ∧ x4.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = (0 : Fin (14 : ℕ)) ∨ x5 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x7 : Fin (14 : ℕ) → Bool), x5.eval (List.ofFn x7) = Bool.true ↔ x2 x7) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (x8.size + (2 : ℕ) ≤ x5.size ∧ x4 x8 ∨ x8.size + (1 : ℕ) ≤ x5.size ∧ (x3 x8 (1 : Fin (14 : ℕ)) ∨ x3 x8 (7 : Fin (14 : ℕ)) ∨ x3 x8 (9 : Fin (14 : ℕ)))) := by
  intro x1 x2 x3 x4
  have main : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), C.size ≤ m →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ x2 x) →
      ∃ T : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 T ∧
        (T.size + 2 ≤ C.size ∧ x4 T ∨ T.size + 1 ≤ C.size ∧ (x3 T 1 ∨ x3 T 7 ∨ x3 T 9)) := by
    intro m
    induction m with
    | zero =>
      intro C hsz hM hC
      obtain ⟨D, hMD, hCD, hDsz, op, rest, a, b, hg, _, _, _⟩ := norm C hM hC
      have hlen : D.size = rest.length + 1 := by
        show D.gates.length = rest.length + 1
        rw [hg]
        rfl
      omega
    | succ m ih =>
      intro C hsz hM hC
      obtain ⟨D, hMD, hCD, hDsz, op, rest, a, b, hg, ha, hb, hab⟩ := norm C hM hC
      have hop := (hMD ⟨op, [a, b]⟩ (by rw [hg]; exact List.mem_cons_self)).1
      have descend : ∀ T : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 T → T.size + 1 ≤ D.size →
          (∀ x : Fin 14 → Bool, T.eval (List.ofFn x) = true ↔ x2 x) →
          ∃ T' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 T' ∧
            (T'.size + 2 ≤ C.size ∧ x4 T' ∨
              T'.size + 1 ≤ C.size ∧ (x3 T' 1 ∨ x3 T' 7 ∨ x3 T' 9)) := by
        intro T hMT hs hT
        obtain ⟨T', hMT', hT'⟩ := ih T (by omega) hMT hT
        refine ⟨T', hMT', ?_⟩
        rcases hT' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inr ⟨by omega, h2⟩
      rcases Set.mem_insert_iff.mp hop with h | h
      · subst h
        by_cases he : (a, b) ∈ x1 ∨ (b, a) ∈ x1
        · obtain ⟨T, hMT, hT⟩ := andEdge D rest a b hg he hMD hCD
          rcases hT with ⟨hs, hw⟩ | ⟨hs, hT⟩
          · exact ⟨T, hMT, Or.inl ⟨by omega, hw⟩⟩
          · exact descend T hMT hs hT
        · obtain ⟨T, hMT, hs, hT⟩ := andOff D rest a b hg ha hb he hMD hCD
          exact descend T hMT hs hT
      · have h' := Set.mem_singleton_iff.mp h
        subst h'
        obtain ⟨T, hMT, hs, hT⟩ := orFirst D rest a b hg ha hb hab hMD hCD
        exact ⟨T, hMT, Or.inr ⟨by omega, hT⟩⟩
  exact fun C hM hC => main C.size C le_rfl hM hC
