import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3402_419
    (h_and :
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D →
        (∀ x : Fin 9 → Bool,
          D.eval (List.ofFn x) =
            [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
             ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
             ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
             ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
              fun e : Fin 9 × Fin 9 => x e.1 && x e.2) →
        5 ≤ PEqualNP.ReadTwo.nAnd D)
    (h_or :
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D →
        (∀ x : Fin 9 → Bool,
          D.eval (List.ofFn x) =
            [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
             ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
             ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
             ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
              fun e : Fin 9 × Fin 9 => x e.1 && x e.2) →
        11 ≤ PEqualNP.ReadTwo.nOr D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (14 : ℕ) ≤ x1.size := by
  intro C T hfan hcard hnots hcomp
  let first : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩
  let second : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, T.toList.map Fin.val⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨first :: second :: C.gates, C.output⟩
  have hnoNot : ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg hnot
    have hmem : g ∈ C.gates.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
          (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _)) := by
      rw [List.mem_filter]
      exact ⟨hg, by simp [hnot]⟩
    have hpos : 0 < PEqualNP.NotBracket.notCount C := List.length_pos_of_mem hmem
    omega
  have hmono : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · exact ⟨by simp [second], by simpa [second] using hcard⟩
    · obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have hne := hnoNot g hg
      refine ⟨?_, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hne
  have hval : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x) =
        C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) := by
    intro x
    let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have h1 : step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
      change List.ofFn x ++ [([(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false].any id)] = _
      simp [List.getD_eq_getElem?_getD]
    have hread : ∀ i : Fin 9, (List.ofFn x ++ [x 0 || x 4]).getD i.val false = x i := by
      intro i
      have hlt : i.val < (List.ofFn x).length := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_eq_getElem hlt, List.getElem_ofFn]
      rfl
    have h2 : step (List.ofFn x ++ [x 0 || x 4]) second =
        List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)] := by
      have hmap :
          (T.toList.map Fin.val).map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
            T.toList.map x := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hread i
      have heq : (T.toList.map x).any id = decide (∃ a ∈ T, x a = true) := by
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true]
      change (List.ofFn x ++ [x 0 || x 4]) ++
          [((T.toList.map Fin.val).map
            (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)).any id] = _
      rw [hmap]
      simpa [List.append_assoc] using
        congrArg (fun b => List.ofFn x ++ [x 0 || x 4, b]) heq
    change (C.gates.foldl step (step (step (List.ofFn x) first) second)).getD C.output false =
      (C.gates.foldl step _).getD C.output false
    rw [h1, h2]
  have heval : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x) =
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e : Fin 9 × Fin 9 => x e.1 && x e.2 :=
    fun x => (hval x).trans (hcomp x)
  have hsum : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (gs.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.and)
        (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq _ _))).length +
      (gs.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq _ _))).length = gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g rest ih =>
      intro hall
      have ih' := ih (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      rcases hall g List.mem_cons_self with hop | hop <;>
        simp [hop] <;> omega
  have hsplit : PEqualNP.ReadTwo.nAnd D + PEqualNP.ReadTwo.nOr D = D.size := by
    change (D.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.and)
        (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq _ _))).length +
      (D.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq _ _))).length = D.gates.length
    exact hsum D.gates (fun g hg => (hmono g hg).1)
  have hand := h_and D hmono heval
  have hor := h_or D hmono heval
  have hsize : D.size = C.size + 2 := by
    change (first :: second :: C.gates).length = C.gates.length + 2
    simp
  omega
