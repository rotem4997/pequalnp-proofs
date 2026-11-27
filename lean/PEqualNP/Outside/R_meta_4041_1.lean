import PEqualNP.Defs

-- Collapse all 56 subsets Y of the 10-vertex independent set with |Y| <= 2 via
-- monotonicity and Aut(PG(2,4)) (cyclic shifts, x4, polarity, and 8 PGL(3,4) maps),
-- separating the singleton-active case ({0}) from singleton-clean circuits with a
-- minimal ordered binary dirty AND gate on {0, 1} (same-side) or {0, 24} (cross-side).
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4041_1
    (hSingle : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ (124 : ℕ) →
      (∀ x : Fin (42 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
        ∃ u v : Fin (42 : ℕ),
          (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
          x u = Bool.true ∧ x v = Bool.true) →
      (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[k]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD ((42 : ℕ) + k) Bool.false = Bool.true ∧
        ∀ k' < k, ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k']? = Option.some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD ((42 : ℕ) + k') Bool.false = Bool.false) →
      False)
    (hTwoPoints : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ (124 : ℕ) →
      (∀ x : Fin (42 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
        ∃ u v : Fin (42 : ℕ),
          (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
          x u = Bool.true ∧ x v = Bool.true) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (v : Fin (42 : ℕ)),
        C.gates[j]? = Option.some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (i = v))).getD ((42 : ℕ) + j) Bool.false = Bool.false) →
      (∃ (k a b : ℕ),
        C.gates[k]? = Option.some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∧
        a < (42 : ℕ) + k ∧ b < (42 : ℕ) + k ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD a Bool.false = Bool.true ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (1 : ℕ)))).getD a Bool.false = Bool.false ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD b Bool.false = Bool.false ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (1 : ℕ)))).getD b Bool.false = Bool.true ∧
        ∀ k' < k, ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k']? = Option.some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ) ∨ ↑i = (1 : ℕ)))).getD ((42 : ℕ) + k') Bool.false = Bool.false) →
      False)
    (hPointLine : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ (124 : ℕ) →
      (∀ x : Fin (42 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
        ∃ u v : Fin (42 : ℕ),
          (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
          x u = Bool.true ∧ x v = Bool.true) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (v : Fin (42 : ℕ)),
        C.gates[j]? = Option.some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (i = v))).getD ((42 : ℕ) + j) Bool.false = Bool.false) →
      (∃ (k a b : ℕ),
        C.gates[k]? = Option.some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∧
        a < (42 : ℕ) + k ∧ b < (42 : ℕ) + k ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD a Bool.false = Bool.true ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (24 : ℕ)))).getD a Bool.false = Bool.false ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ)))).getD b Bool.false = Bool.false ∧
        (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (24 : ℕ)))).getD b Bool.false = Bool.true ∧
        ∀ k' < k, ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k']? = Option.some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (C.wires (List.ofFn fun i : Fin (42 : ℕ) => Decidable.decide (↑i = (0 : ℕ) ∨ ↑i = (24 : ℕ)))).getD ((42 : ℕ) + k') Bool.false = Bool.false) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by
  -- PG(2,4) incidence and finite automorphism checks (before classical!)
  let incB : Fin 42 → Fin 42 → Bool := fun u v =>
    decide (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
  let adjB : Fin 42 → Fin 42 → Bool := fun u v => incB u v || incB v u
  let pol : Fin 42 → Fin 42 := fun i =>
    if i.val < 21 then ⟨21 + (21 - i.val) % 21, by omega⟩ else ⟨(42 - i.val) % 21, by omega⟩
  let shift1 : Fin 42 → Fin 42 := fun i =>
    if i.val < 21 then ⟨(i.val + 1) % 21, by omega⟩ else ⟨21 + (i.val - 21 + 1) % 21, by omega⟩
  let shift : ℕ → Fin 42 → Fin 42 := fun c i =>
    if i.val < 21 then ⟨(i.val + c) % 21, by omega⟩ else ⟨21 + (i.val - 21 + c) % 21, by omega⟩
  let mul4 : Fin 42 → Fin 42 := fun i =>
    if i.val < 21 then ⟨(4 * i.val) % 21, by omega⟩ else ⟨21 + (4 * (i.val - 21)) % 21, by omega⟩
  let applyTbl : List ℕ → Fin 42 → Fin 42 := fun t i => ⟨(t.getD i.val 0) % 42, Nat.mod_lt _ (by omega)⟩
  let p1 : List ℕ := [0, 2, 1, 3, 11, 17, 12, 14, 16, 18, 19, 4, 6, 13, 7, 15, 8, 5, 9, 10, 20, 28, 22, 29, 31, 37, 38, 40, 21, 23, 39, 24, 32, 34, 33, 35, 36, 25, 26, 30, 27, 41]
  let p2 : List ℕ := [0, 2, 12, 1, 11, 20, 3, 18, 17, 15, 6, 10, 5, 4, 7, 14, 8, 19, 9, 13, 16, 28, 40, 29, 39, 37, 41, 23, 38, 22, 32, 27, 31, 25, 24, 35, 34, 36, 26, 30, 33, 21]
  let p3 : List ℕ := [0, 2, 14, 13, 11, 12, 17, 1, 4, 10, 5, 16, 9, 3, 7, 20, 8, 19, 6, 18, 15, 28, 40, 34, 39, 32, 38, 22, 21, 30, 31, 33, 37, 29, 24, 27, 25, 36, 26, 23, 35, 41]
  let p4 : List ℕ := [0, 3, 4, 18, 13, 7, 8, 1, 16, 2, 9, 14, 6, 10, 15, 17, 20, 19, 5, 11, 12, 41, 24, 25, 39, 33, 28, 29, 21, 23, 30, 35, 34, 27, 36, 22, 37, 40, 26, 31, 32, 38]
  let p5 : List ℕ := [0, 8, 3, 4, 11, 9, 19, 15, 20, 5, 10, 13, 18, 14, 2, 1, 7, 12, 17, 6, 16, 28, 29, 24, 32, 37, 26, 36, 41, 25, 31, 30, 39, 35, 40, 22, 27, 33, 38, 34, 23, 21]
  let p6 : List ℕ := [0, 1, 3, 6, 4, 8, 2, 15, 20, 7, 17, 13, 10, 19, 14, 9, 16, 12, 18, 11, 5, 21, 29, 23, 32, 25, 28, 22, 41, 27, 24, 34, 30, 36, 40, 35, 37, 33, 38, 39, 31, 26]
  let p7 : List ℕ := [0, 11, 6, 3, 8, 4, 16, 9, 5, 14, 17, 19, 10, 13, 7, 15, 2, 12, 18, 1, 20, 28, 32, 23, 29, 25, 21, 37, 26, 31, 34, 24, 36, 30, 33, 35, 22, 40, 38, 39, 27, 41]
  let p8 : List ℕ := [0, 2, 15, 10, 11, 1, 16, 3, 13, 4, 6, 20, 9, 12, 7, 17, 8, 5, 19, 14, 18, 28, 22, 36, 31, 39, 21, 23, 41, 30, 32, 27, 37, 29, 33, 24, 34, 25, 26, 40, 35, 38]
  let baseAut : ℕ → Fin 42 → Fin 42 := fun r =>
    if r = 1 then applyTbl p1
    else if r = 2 then applyTbl p2
    else if r = 3 then applyTbl p3
    else if r = 4 then applyTbl p4
    else if r = 5 then applyTbl p5
    else if r = 6 then applyTbl p6
    else if r = 7 then applyTbl p7
    else if r = 8 then applyTbl p8
    else id
  let mkAut : Bool → ℕ → ℕ → ℕ → Fin 42 → Fin 42 := fun usePol c m r =>
    (baseAut r) ∘ (if m = 1 then mul4 else if m = 2 then mul4 ∘ mul4 else id) ∘
      (shift c) ∘ (if usePol then pol else id)
  have hCheckGen :
      (∀ u v : Fin 42, (pol u = pol v → u = v) ∧ adjB (pol u) (pol v) = adjB u v) ∧
      (∀ u v : Fin 42, (shift1 u = shift1 v → u = v) ∧ adjB (shift1 u) (shift1 v) = adjB u v) ∧
      (∀ u v : Fin 42, (mul4 u = mul4 v → u = v) ∧ adjB (mul4 u) (mul4 v) = adjB u v) ∧
      (∀ r : Fin 9, ∀ u v : Fin 42, (baseAut r.val u = baseAut r.val v → u = v) ∧ adjB (baseAut r.val u) (baseAut r.val v) = adjB u v) := by
    dsimp only [pol, shift1, mul4, baseAut, applyTbl, p1, p2, p3, p4, p5, p6, p7, p8, adjB, incB]
    decide +kernel
  have hv_all : ∀ w : Fin 42, ∃ (b : Bool) (c : Fin 21), mkAut b c.val 0 0 w = ⟨0, by omega⟩ := by
    dsimp only [mkAut, baseAut, shift, pol]
    decide +kernel
  have hCover : ∀ (a b : Fin 42),
      a.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) →
      b.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) →
      a ≠ b →
      (∃ (bp : Bool) (c : Fin 21) (m : Fin 3) (r : Fin 4),
        (mkAut bp c.val m.val r.val a = ⟨0, by omega⟩ ∧ mkAut bp c.val m.val r.val b = ⟨1, by omega⟩) ∨
        (mkAut bp c.val m.val r.val a = ⟨1, by omega⟩ ∧ mkAut bp c.val m.val r.val b = ⟨0, by omega⟩)) ∨
      (∃ (bp : Bool) (c : Fin 21) (m : Fin 3) (r : Fin 9),
        (mkAut bp c.val m.val r.val a = ⟨0, by omega⟩ ∧ mkAut bp c.val m.val r.val b = ⟨24, by omega⟩) ∨
        (mkAut bp c.val m.val r.val a = ⟨24, by omega⟩ ∧ mkAut bp c.val m.val r.val b = ⟨0, by omega⟩)) := by
    dsimp only [mkAut, baseAut, applyTbl, p1, p2, p3, p4, p5, p6, p7, p8, mul4, shift, pol]
    decide +kernel
  classical
  intro C Y hmono hsize hcard hYS hact
  by_contra hno
  have hcomp : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x u = true ∧ x v = true := by
    intro x
    by_contra hbad
    exact hno ⟨x, hbad⟩
  -- Basic wire helpers
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      change gs.foldl step (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
      rw [ht]; simp [step]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs w; obtain ⟨t, ht, hl⟩ := hfold_ext gs w; rw [ht, List.length_append, hl]
  have hfold_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs w i hi; obtain ⟨t, ht, _⟩ := hfold_ext gs w
    rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have hfold_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ)
      (g : PEqualNP.CircuitLowerBounds.Gate), gs[j]? = some g →
      (gs.foldl step w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; cases h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (step w g0).length := by simp [step]
        rw [hfold_lt gs (step w g0) w.length hlt]
        have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) := by
          simp [step]
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, hfold_lt gs (step w g0) i (by simp [step]; omega)]
          simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (step w g0).length + j' = w.length + (j' + 1) := by simp [step]; omega
        rw [List.foldl_cons, ← hlen]
        exact ih (step w g0) j' g hj
  have hmono_fold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl step w1).getD i false = true → (gs.foldl step w2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ h i hi; exact h i hi
    | cons g gs ih =>
      intro hgs w1 w2 hlen hle
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step w1 g) (step w2 g) (by simp [step, hlen])
      intro i hi
      by_cases hlt : i < w1.length
      · have hlt2 : i < w2.length := by omega
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_left hlt2] at hi ⊢
        exact hle i hi
      · by_cases heq : i = w1.length
        · subst heq
          have hi' : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [step, List.getD_eq_getElem?_getD] using hi
          have hgoal : (step w2 g).getD w1.length false = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            rw [hlen]; simp [step, List.getD_eq_getElem?_getD]
          rw [hgoal]
          rcases hgs g List.mem_cons_self with hand | hor
          · rw [hand] at hi' ⊢
            change (g.inputs.map fun i => w1.getD i false).all id = true at hi'
            change (g.inputs.map fun i => w2.getD i false).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq] at hi' ⊢
            intro b hb
            obtain ⟨k, hk, rfl⟩ := hb
            exact hle k (hi' _ ⟨k, hk, rfl⟩)
          · rw [hor] at hi' ⊢
            change (g.inputs.map fun i => w1.getD i false).any id = true at hi'
            change (g.inputs.map fun i => w2.getD i false).any id = true
            simp only [List.any_eq_true, List.mem_map, id_eq] at hi' ⊢
            obtain ⟨_, ⟨k, hk, rfl⟩, hk1⟩ := hi'
            exact ⟨w2.getD k false, ⟨k, hk, rfl⟩, hle k hk1⟩
        · have hge : (step w1 g).length ≤ i := by simp [step]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
  -- Automorphism transport for circuits
  let idxE : (Fin 42 → Fin 42) → ℕ → ℕ := fun e i => if hi : i < 42 then (e ⟨i, hi⟩).val else i
  let changeGate : (Fin 42 → Fin 42) → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun e g => ⟨g.op, g.inputs.map (idxE e)⟩
  let changeC : (Fin 42 → Fin 42) → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Circuit :=
    fun e D => ⟨D.gates.map (changeGate e), idxE e D.output⟩
  have hchange_wires : ∀ (e : Fin 42 → Fin 42) (D : PEqualNP.CircuitLowerBounds.Circuit)
      (x : Fin 42 → Bool) (i : ℕ),
      ((changeC e D).wires (List.ofFn x)).getD (idxE e i) false =
      (D.wires (List.ofFn (x ∘ e))).getD i false := by
    intro e D x i
    have hread : ∀ (extra : List Bool) (k : ℕ),
        (List.ofFn x ++ extra).getD (idxE e k) false = (List.ofFn (x ∘ e) ++ extra).getD k false := by
      intro extra k
      by_cases hk : k < 42
      · have hek : (e ⟨k, hk⟩).val < 42 := (e ⟨k, hk⟩).isLt
        simp only [idxE, dite_eq_left hk]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hek]),
            List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hk]),
            List.getElem?_eq_getElem (by simp [hek]), List.getElem_ofFn,
            List.getElem?_eq_getElem (by simp [hk]), List.getElem_ofFn]
        rfl
      · simp only [idxE, dite_eq_right hk]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp
    have htrace : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (extra : List Bool),
        ∃ rest : List Bool,
          (gs.map (changeGate e)).foldl step (List.ofFn x ++ extra) = List.ofFn x ++ (extra ++ rest) ∧
          gs.foldl step (List.ofFn (x ∘ e) ++ extra) = List.ofFn (x ∘ e) ++ (extra ++ rest) := by
      intro gs
      induction gs with
      | nil => intro extra; exact ⟨[], by simp, by simp⟩
      | cons g gs ih =>
        intro extra
        let y := g.op.eval (g.inputs.map fun k => (List.ofFn (x ∘ e) ++ extra).getD k false)
        have hstep_eq : (changeGate e g).op.eval
            ((changeGate e g).inputs.map fun k => (List.ofFn x ++ extra).getD k false) = y := by
          simp only [changeGate, List.map_map, y]
          congr 1
          apply List.map_congr_left
          intro k _
          exact hread extra k
        obtain ⟨rest, h1, h2⟩ := ih (extra ++ [y])
        refine ⟨y :: rest, ?_, ?_⟩
        · simp only [List.map_cons, List.foldl_cons, step, hstep_eq, List.append_assoc] at h1 ⊢
          exact h1
        · simp only [List.foldl_cons, step, List.append_assoc] at h2 ⊢
          exact h2
    obtain ⟨rest, h1, h2⟩ := htrace D.gates []
    simp only [List.append_nil, List.nil_append] at h1 h2
    change ((D.gates.map (changeGate e)).foldl step (List.ofFn x)).getD (idxE e i) false =
      (D.gates.foldl step (List.ofFn (x ∘ e))).getD i false
    rw [h1, h2]
    exact hread rest i
  have hchange_props : ∀ (e : Fin 42 → Fin 42) (D : PEqualNP.CircuitLowerBounds.Circuit),
      Function.Bijective e → (∀ u v, adjB (e u) (e v) = adjB u v) →
      PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 124 →
      (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true) →
      PEqualNP.MetaComplexity.Monotone2 (changeC e D) ∧ (changeC e D).size ≤ 124 ∧
      (∀ x : Fin 42 → Bool, (changeC e D).eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true) := by
    intro e D hbij hadj hM hS hE
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hM g0 hg0).1, by simpa [changeGate] using (hM g0 hg0).2⟩
    · change (D.gates.map (changeGate e)).length ≤ 124
      rw [List.length_map]; exact hS
    · intro x
      have hev : (changeC e D).eval (List.ofFn x) = D.eval (List.ofFn (x ∘ e)) :=
        hchange_wires e D x D.output
      rw [hev, hE (x ∘ e)]
      have hsym : ∀ (y : Fin 42 → Bool),
          (∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            y u = true ∧ y v = true) ↔
          (∃ u v : Fin 42, adjB u v = true ∧ y u = true ∧ y v = true) := by
        intro y; constructor
        · rintro ⟨u, v, huv, hu, hv⟩
          exact ⟨u, v, by simp only [adjB, incB, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl huv, hu, hv⟩
        · rintro ⟨u, v, huv, hu, hv⟩
          simp only [adjB, Bool.or_eq_true, incB, decide_eq_true_eq] at huv
          rcases huv with h1 | h2
          · exact ⟨u, v, h1, hu, hv⟩
          · exact ⟨v, u, h2, hv, hu⟩
      rw [hsym (x ∘ e), hsym x]
      constructor
      · rintro ⟨u, v, huv, hu, hv⟩
        exact ⟨e u, e v, by rw [hadj u v]; exact huv, hu, hv⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨u0, rfl⟩ := hbij.2 u
        obtain ⟨v0, rfl⟩ := hbij.2 v
        exact ⟨u0, v0, by rw [← hadj u0 v0]; exact huv, hu, hv⟩
  -- Compose generators of Aut(PG(2,4))
  have hShiftAut : ∀ c : ℕ, Function.Bijective (shift c) ∧ ∀ u v, adjB (shift c u) (shift c v) = adjB u v := by
    have hstep : ∀ c i, shift (c + 1) i = shift1 (shift c i) := by
      intro c i
      by_cases h : i.val < 21
      · have hmod : (i.val + c) % 21 < 21 := Nat.mod_lt _ (by omega)
        simp only [shift, shift1, h, hmod, ite_true]
        apply Fin.ext; dsimp only
        rw [Nat.mod_add_mod, Nat.add_assoc]
      · have hmod : ¬ (21 + (i.val - 21 + c) % 21 < 21) := by omega
        simp only [shift, shift1, h, hmod, ite_false]
        apply Fin.ext; dsimp only
        rw [Nat.add_sub_cancel_left, Nat.mod_add_mod, Nat.add_assoc]
    intro c
    induction c with
    | zero =>
      have hid : shift 0 = id := by
        funext i; apply Fin.ext; simp only [shift, id_eq]; split_ifs with h <;> dsimp <;> omega
      rw [hid]; exact ⟨Function.bijective_id, fun _ _ => rfl⟩
    | succ c ih =>
      have hcomp_eq : shift (c + 1) = shift1 ∘ shift c := funext (hstep c)
      rw [hcomp_eq]
      have h1bij : Function.Bijective shift1 := Finite.injective_iff_bijective.mp (fun u v h => (hCheckGen.2.1 u v).1 h)
      exact ⟨h1bij.comp ih.1, fun u v => by rw [Function.comp_apply, Function.comp_apply, (hCheckGen.2.1 _ _).2, ih.2]⟩
  have hMkAut : ∀ (b : Bool) (c : ℕ) (m : ℕ) (r : Fin 9),
      Function.Bijective (mkAut b c m r.val) ∧ ∀ u v, adjB (mkAut b c m r.val u) (mkAut b c m r.val v) = adjB u v := by
    intro b c m r
    have hpol_b : Function.Bijective pol := Finite.injective_iff_bijective.mp (fun u v h => (hCheckGen.1 u v).1 h)
    have hmul_b : Function.Bijective mul4 := Finite.injective_iff_bijective.mp (fun u v h => (hCheckGen.2.2.1 u v).1 h)
    have hbase_b : Function.Bijective (baseAut r.val) := Finite.injective_iff_bijective.mp (fun u v h => (hCheckGen.2.2.2 r u v).1 h)
    have h1 : Function.Bijective (if b then pol else id) ∧ ∀ u v, adjB ((if b then pol else id) u) ((if b then pol else id) v) = adjB u v := by
      cases b
      · exact ⟨Function.bijective_id, fun _ _ => rfl⟩
      · exact ⟨hpol_b, fun u v => (hCheckGen.1 u v).2⟩
    have h2 := hShiftAut c
    have h3 : Function.Bijective (if m = 1 then mul4 else if m = 2 then mul4 ∘ mul4 else id) ∧
        ∀ u v, adjB ((if m = 1 then mul4 else if m = 2 then mul4 ∘ mul4 else id) u)
          ((if m = 1 then mul4 else if m = 2 then mul4 ∘ mul4 else id) v) = adjB u v := by
      by_cases hm1 : m = 1
      · simp only [hm1, ite_true]; exact ⟨hmul_b, fun u v => (hCheckGen.2.2.1 u v).2⟩
      · by_cases hm2 : m = 2
        · simp only [hm1, hm2, ite_false, ite_true]
          refine ⟨hmul_b.comp hmul_b, fun u v => ?_⟩
          change adjB (mul4 (mul4 u)) (mul4 (mul4 v)) = adjB u v
          rw [(hCheckGen.2.2.1 _ _).2, (hCheckGen.2.2.1 u v).2]
        · simp only [hm1, hm2, ite_false]; exact ⟨Function.bijective_id, fun _ _ => rfl⟩
    refine ⟨hbase_b.comp (h3.1.comp (h2.1.comp h1.1)), fun u v => ?_⟩
    simp only [mkAut, Function.comp_apply]
    rw [(hCheckGen.2.2.2 r _ _).2, h3.2, h2.2, h1.2]
  -- Case 1: Check if C has any AND gate firing on a singleton {v}
  by_cases hSing : ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (v : Fin 42),
      C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = true
  · obtain ⟨j0, g0, v0, hj0, hg0, hfire0⟩ := hSing
    obtain ⟨b, c, hev0⟩ := hv_all v0
    let e := mkAut b c.val 0 0
    have he_aut := hMkAut b c.val 0 ⟨0, by omega⟩
    let D := changeC e C
    obtain ⟨hDM, hDS, hDE⟩ := hchange_props e C he_aut.1 he_aut.2 hmono hsize hcomp
    have hD_ex : ∃ k : ℕ, ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        D.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0))).getD (42 + k) false = true := by
      refine ⟨j0, changeGate e g0, ?_, hg0, ?_⟩
      · simp [D, changeC, List.getElem?_map, hj0]
      · have hidx : idxE e (42 + j0) = 42 + j0 := by simp [idxE]
        have hfun : (fun i : Fin 42 => decide (i.val = 0)) ∘ e = fun i : Fin 42 => decide (i = v0) := by
          funext i; simp only [Function.comp_apply]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · intro h0; exact he_aut.1.1 (show e i = e v0 by rw [show e v0 = ⟨0, by omega⟩ from hev0]; exact Fin.ext h0)
          · rintro rfl; exact congrArg Fin.val hev0
        have hw := hchange_wires e C (fun i : Fin 42 => decide (i.val = 0)) (42 + j0)
        rw [hidx, hfun] at hw; exact hw.trans hfire0
    let kmin := Nat.find hD_ex
    obtain ⟨gmin, hgmin, hopmin, hfiremin⟩ := Nat.find_spec hD_ex
    apply hSingle D hDM hDS hDE
    refine ⟨kmin, gmin, hgmin, hopmin, hfiremin, ?_⟩
    intro k' hk' g' hg' hop'
    by_contra hnt
    have ht : (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0))).getD (42 + k') false = true := by
      cases h : (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0))).getD (42 + k') false
      · exact absurd h hnt
      · rfl
    exact Nat.find_min hD_ex hk' ⟨g', hg', hop', ht⟩
  · -- Case 2: C is singleton-clean!
    have hSC : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (v : Fin 42),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false = false := by
      intro j g v hj hg
      cases h : (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD (42 + j) false
      · rfl
      · exact absurd ⟨j, g, v, hj, hg, h⟩ hSing
    obtain ⟨j0, g0, hj0, hg0, hfireY⟩ := hact
    -- Y must have cardinality exactly 2
    have hY2 : ∃ u v : Fin 42, u ∈ Y ∧ v ∈ Y ∧ u ≠ v ∧ ∀ w, w ∈ Y ↔ w = u ∨ w = v := by
      have hcard_eq : Y.card = 2 := by
        by_contra hne2
        have hle1 : Y.card ≤ 1 := by omega
        have hsub : ∃ v0 : Fin 42, ∀ w ∈ Y, w = v0 := by
          have h1 := Finset.card_le_one.mp hle1
          by_cases hemp : Y.Nonempty
          · obtain ⟨v0, hv0⟩ := hemp
            exact ⟨v0, fun w hw => h1 w hw v0 hv0⟩
          · exact ⟨⟨0, by omega⟩, fun w hw => absurd ⟨w, hw⟩ hemp⟩
        obtain ⟨v0, hv0⟩ := hsub
        have hfire_v0 : (C.wires (List.ofFn fun i : Fin 42 => decide (i = v0))).getD (42 + j0) false = true := by
          apply hmono_fold C.gates (fun g hg => by simpa using (hmono g hg).1)
            (List.ofFn fun i : Fin 42 => decide (i ∈ Y))
            (List.ofFn fun i : Fin 42 => decide (i = v0)) (by simp) _ (42 + j0) hfireY
          intro i hi
          by_cases hlt : i < 42
          · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hi
            rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
            simp only [decide_eq_true_eq] at hi ⊢
            exact hv0 _ hi
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
            cases hi
        rw [hSC j0 g0 v0 hj0 hg0] at hfire_v0; cases hfire_v0
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard_eq
      exact ⟨u, v, by simp, by simp, huv, fun w => by simp⟩
    obtain ⟨u, v, huY, hvY, huv, hYuv⟩ := hY2
    have huS : u.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) := hYS u huY
    have hvS : v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) := hYS v hvY
    -- Common extraction lemma: given singleton-clean D with an AND firing on {0, vTgt},
    -- build ordered binary witness on minimal gate k (swapping [a,b] -> [b,a] if needed)
    have hExtract : ∀ (vTgt : ℕ) (hvTgt : vTgt < 42) (hvNz : vTgt ≠ 0)
        (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
            x a = true ∧ x b = true) →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : Fin 42),
          D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn fun i : Fin 42 => decide (i = w))).getD (42 + j) false = false) →
        (∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = vTgt))).getD (42 + j) false = true) →
        ∃ D' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 D' ∧ D'.size ≤ 124 ∧
          (∀ x : Fin 42 → Bool, D'.eval (List.ofFn x) = true ↔
            ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
              x a = true ∧ x b = true) ∧
          (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : Fin 42),
            D'.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            (D'.wires (List.ofFn fun i : Fin 42 => decide (i = w))).getD (42 + j) false = false) ∧
          ∃ (k a b : ℕ),
            D'.gates[k]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∧
            a < 42 + k ∧ b < 42 + k ∧
            (D'.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0))).getD a false = true ∧
            (D'.wires (List.ofFn fun i : Fin 42 => decide (i.val = vTgt))).getD a false = false ∧
            (D'.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0))).getD b false = false ∧
            (D'.wires (List.ofFn fun i : Fin 42 => decide (i.val = vTgt))).getD b false = true ∧
            ∀ k' < k, ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
              D'.gates[k']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              (D'.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = vTgt))).getD (42 + k') false = false := by
      intro vTgt hvTgt hvNz D hDM hDS hDE hDSC hDex
      let k := Nat.find hDex
      obtain ⟨gk, hgk, hopk, hfirek⟩ := Nat.find_spec hDex
      have hmink : ∀ k' < k, ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
          D.gates[k']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = vTgt))).getD (42 + k') false = false := by
        intro k' hk' g' hg' hop'
        cases h : (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = vTgt))).getD (42 + k') false
        · rfl
        · exact absurd ⟨g', hg', hop', h⟩ (Nat.find_min hDex hk')
      let x0 : Fin 42 → Bool := fun i => decide (i.val = 0)
      let x1 : Fin 42 → Bool := fun i => decide (i.val = vTgt)
      let x01 : Fin 42 → Bool := fun i => decide (i.val = 0 ∨ i.val = vTgt)
      have hx0_eq : x0 = fun i : Fin 42 => decide (i = ⟨0, by omega⟩) := by
        funext i; apply Bool.eq_iff_iff.mpr; simp only [x0, decide_eq_true_eq, Fin.ext_iff]
      have hx1_eq : x1 = fun i : Fin 42 => decide (i = ⟨vTgt, hvTgt⟩) := by
        funext i; apply Bool.eq_iff_iff.mpr; simp only [x1, decide_eq_true_eq, Fin.ext_iff]
      -- Before gate k, any wire true on x01 is true on x0 or true on x1
      have hor_cone : ∀ w : ℕ, w < 42 + k →
          (D.wires (List.ofFn x01)).getD w false = true →
          (D.wires (List.ofFn x0)).getD w false = true ∨ (D.wires (List.ofFn x1)).getD w false = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw htw
          by_cases hin : w < 42
          · change (D.gates.foldl step (List.ofFn x01)).getD w false = true at htw
            rw [hfold_lt D.gates (List.ofFn x01) w (by simp [hin]),
                List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at htw
            simp only [x01, decide_eq_true_eq] at htw
            rcases htw with h0 | h1
            · left; change (D.gates.foldl step (List.ofFn x0)).getD w false = true
              rw [hfold_lt D.gates (List.ofFn x0) w (by simp [hin]),
                  List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn]
              simp [x0, h0]
            · right; change (D.gates.foldl step (List.ofFn x1)).getD w false = true
              rw [hfold_lt D.gates (List.ofFn x1) w (by simp [hin]),
                  List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn]
              simp [x1, h1]
          · let j := w - 42
            have hjk : j < k := by omega
            have hjl : j < D.gates.length := by
              have hkl : k < D.gates.length := (List.getElem?_eq_some_iff.mp hgk).1
              omega
            have hwj : w = 42 + j := by omega
            rw [hwj] at htw ⊢
            let gj := D.gates[j]
            have hgj : D.gates[j]? = some gj := List.getElem?_eq_getElem hjl
            have hgj_or : gj.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
              have hm : gj.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gj.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
                simpa using (hDM gj (List.mem_of_getElem? hgj)).1
              rcases hm with hand | hor
              · have hf := hmink j hjk gj hgj hand
                rw [hf] at htw; cases htw
              · exact hor
            have hval01 := hfold_gate D.gates (List.ofFn x01) j gj hgj
            simp only [List.length_ofFn, hgj_or] at hval01
            change (D.gates.foldl step (List.ofFn x01)).getD (42 + j) false =
              (gj.inputs.map fun i => if i < 42 + j then (D.gates.foldl step (List.ofFn x01)).getD i false else false).any id at hval01
            change (D.gates.foldl step (List.ofFn x01)).getD (42 + j) false = true at htw
            rw [hval01] at htw
            simp only [List.any_eq_true, List.mem_map, id_eq] at htw
            obtain ⟨_, ⟨wi, hwi, hite⟩, hwi_t⟩ := htw
            have hwi_lt : wi < 42 + j := by
              by_contra hge; rw [ite_eq_right hge] at hite; rw [← hite] at hwi_t; cases hwi_t
            rw [ite_eq_left hwi_lt] at hite
            have hwi01 : (D.wires (List.ofFn x01)).getD wi false = true := hite.trans hwi_t
            rcases ih wi (by omega) (by omega) hwi01 with hwi0 | hwi1
            · left
              have hv0 := hfold_gate D.gates (List.ofFn x0) j gj hgj
              simp only [List.length_ofFn, hgj_or] at hv0
              change (D.gates.foldl step (List.ofFn x0)).getD (42 + j) false =
                (gj.inputs.map fun i => if i < 42 + j then (D.gates.foldl step (List.ofFn x0)).getD i false else false).any id at hv0
              change (D.gates.foldl step (List.ofFn x0)).getD (42 + j) false = true
              rw [hv0]
              simp only [List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨wi, hwi, by rw [ite_eq_left hwi_lt]; exact hwi0⟩, rfl⟩
            · right
              have hv1 := hfold_gate D.gates (List.ofFn x1) j gj hgj
              simp only [List.length_ofFn, hgj_or] at hv1
              change (D.gates.foldl step (List.ofFn x1)).getD (42 + j) false =
                (gj.inputs.map fun i => if i < 42 + j then (D.gates.foldl step (List.ofFn x1)).getD i false else false).any id at hv1
              change (D.gates.foldl step (List.ofFn x1)).getD (42 + j) false = true
              rw [hv1]
              simp only [List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨wi, hwi, by rw [ite_eq_left hwi_lt]; exact hwi1⟩, rfl⟩
      -- Analyze gk.inputs (length <= 2)
      have hgk_len : gk.inputs.length ≤ 2 := (hDM gk (List.mem_of_getElem? hgk)).2
      have hgk_ev01 := hfold_gate D.gates (List.ofFn x01) k gk hgk
      simp only [List.length_ofFn, hopk] at hgk_ev01
      change (D.gates.foldl step (List.ofFn x01)).getD (42 + k) false =
        (gk.inputs.map fun i => if i < 42 + k then (D.gates.foldl step (List.ofFn x01)).getD i false else false).all id at hgk_ev01
      have hgk_ev0 := hfold_gate D.gates (List.ofFn x0) k gk hgk
      simp only [List.length_ofFn, hopk] at hgk_ev0
      change (D.gates.foldl step (List.ofFn x0)).getD (42 + k) false =
        (gk.inputs.map fun i => if i < 42 + k then (D.gates.foldl step (List.ofFn x0)).getD i false else false).all id at hgk_ev0
      have hgk_ev1 := hfold_gate D.gates (List.ofFn x1) k gk hgk
      simp only [List.length_ofFn, hopk] at hgk_ev1
      change (D.gates.foldl step (List.ofFn x1)).getD (42 + k) false =
        (gk.inputs.map fun i => if i < 42 + k then (D.gates.foldl step (List.ofFn x1)).getD i false else false).all id at hgk_ev1
      have hk_f0 : (D.wires (List.ofFn x0)).getD (42 + k) false = false := by
        rw [hx0_eq]; exact hDSC k gk ⟨0, by omega⟩ hgk hopk
      have hk_f1 : (D.wires (List.ofFn x1)).getD (42 + k) false = false := by
        rw [hx1_eq]; exact hDSC k gk ⟨vTgt, hvTgt⟩ hgk hopk
      cases hinp : gk.inputs with
      | nil =>
        change (D.gates.foldl step (List.ofFn x0)).getD (42 + k) false = false at hk_f0
        rw [hgk_ev0, hinp] at hk_f0; simp at hk_f0
      | cons a rest =>
        cases rest with
        | nil =>
          change (D.gates.foldl step (List.ofFn x01)).getD (42 + k) false = true at hfirek
          rw [hgk_ev01, hinp] at hfirek; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq] at hfirek
          have ha_lt : a < 42 + k := by by_contra hge; rw [ite_eq_right hge] at hfirek; cases hfirek
          rw [ite_eq_left ha_lt] at hfirek
          rcases hor_cone a ha_lt hfirek with ha0 | ha1
          · change (D.gates.foldl step (List.ofFn x0)).getD (42 + k) false = false at hk_f0
            rw [hgk_ev0, hinp] at hk_f0
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, ite_eq_left ha_lt] at hk_f0
            change (D.gates.foldl step (List.ofFn x0)).getD a false = true at ha0
            rw [ha0] at hk_f0; cases hk_f0
          · change (D.gates.foldl step (List.ofFn x1)).getD (42 + k) false = false at hk_f1
            rw [hgk_ev1, hinp] at hk_f1
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, ite_eq_left ha_lt] at hk_f1
            change (D.gates.foldl step (List.ofFn x1)).getD a false = true at ha1
            rw [ha1] at hk_f1; cases hk_f1
        | cons b rest2 =>
          have hr2 : rest2 = [] := by
            rw [hinp] at hgk_len
            simp only [List.length_cons] at hgk_len
            exact List.length_eq_zero_iff.mp (by omega)
          subst hr2
          change (D.gates.foldl step (List.ofFn x01)).getD (42 + k) false = true at hfirek
          rw [hgk_ev01, hinp] at hfirek
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq] at hfirek
          have ha_lt : a < 42 + k := by by_contra hge; rw [ite_eq_right hge] at hfirek; cases hfirek.1
          have hb_lt : b < 42 + k := by by_contra hge; rw [ite_eq_right hge] at hfirek; cases hfirek.2
          rw [ite_eq_left ha_lt, ite_eq_left hb_lt] at hfirek
          have ha_or := hor_cone a ha_lt hfirek.1
          have hb_or := hor_cone b hb_lt hfirek.2
          have hnot0 : ¬ ((D.wires (List.ofFn x0)).getD a false = true ∧ (D.wires (List.ofFn x0)).getD b false = true) := by
            rintro ⟨h1, h2⟩
            change (D.gates.foldl step (List.ofFn x0)).getD (42 + k) false = false at hk_f0
            rw [hgk_ev0, hinp] at hk_f0
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, ite_eq_left ha_lt, ite_eq_left hb_lt, id_eq] at hk_f0
            change (D.gates.foldl step (List.ofFn x0)).getD a false = true at h1
            change (D.gates.foldl step (List.ofFn x0)).getD b false = true at h2
            rw [h1, h2] at hk_f0; cases hk_f0
          have hnot1 : ¬ ((D.wires (List.ofFn x1)).getD a false = true ∧ (D.wires (List.ofFn x1)).getD b false = true) := by
            rintro ⟨h1, h2⟩
            change (D.gates.foldl step (List.ofFn x1)).getD (42 + k) false = false at hk_f1
            rw [hgk_ev1, hinp] at hk_f1
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, ite_eq_left ha_lt, ite_eq_left hb_lt, id_eq] at hk_f1
            change (D.gates.foldl step (List.ofFn x1)).getD a false = true at h1
            change (D.gates.foldl step (List.ofFn x1)).getD b false = true at h2
            rw [h1, h2] at hk_f1; cases hk_f1
          have hgk_eq : gk = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
            cases gk; simp only at hopk hinp; subst hopk; subst hinp; rfl
          rcases ha_or with ha0 | ha1
          · have hb0 : (D.wires (List.ofFn x0)).getD b false = false := by
              cases h : (D.wires (List.ofFn x0)).getD b false; rfl; exact absurd ⟨ha0, h⟩ hnot0
            have hb1 : (D.wires (List.ofFn x1)).getD b false = true := by
              rcases hb_or with h | h; rw [hb0] at h; cases h; exact h
            have ha1 : (D.wires (List.ofFn x1)).getD a false = false := by
              cases h : (D.wires (List.ofFn x1)).getD a false; rfl; exact absurd ⟨h, hb1⟩ hnot1
            exact ⟨D, hDM, hDS, hDE, hDSC, k, a, b, hgk_eq ▸ hgk, ha_lt, hb_lt, ha0, ha1, hb0, hb1, hmink⟩
          · have hb1 : (D.wires (List.ofFn x1)).getD b false = false := by
              cases h : (D.wires (List.ofFn x1)).getD b false; rfl; exact absurd ⟨ha1, h⟩ hnot1
            have hb0 : (D.wires (List.ofFn x0)).getD b false = true := by
              rcases hb_or with h | h; exact h; rw [hb1] at h; cases h
            have ha0 : (D.wires (List.ofFn x0)).getD a false = false := by
              cases h : (D.wires (List.ofFn x0)).getD a false; rfl; exact absurd ⟨h, hb0⟩ hnot0
            -- Swap [a, b] -> [b, a] at gate k: preserves all wire values on all inputs!
            let gswap : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [b, a]⟩
            let D' : PEqualNP.CircuitLowerBounds.Circuit := ⟨D.gates.set k gswap, D.output⟩
            have hkl : k < D.gates.length := (List.getElem?_eq_some_iff.mp hgk).1
            have hstep_swap : ∀ (w : List Bool), step w gswap = step w gk := by
              intro w
              rw [hgk_eq]
              change w ++ [(w.getD b false && (w.getD a false && true))] =
                     w ++ [(w.getD a false && (w.getD b false && true))]
              simp only [Bool.and_true]; rw [Bool.and_comm]
            have hwires_eq : ∀ (w : List Bool), D'.wires w = D.wires w := by
              intro w
              have haux : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (idx : ℕ) (acc : List Bool),
                  gs[idx]? = some gk → (gs.set idx gswap).foldl step acc = gs.foldl step acc := by
                intro gs
                induction gs with
                | nil => intro _ _ h; cases h
                | cons g gs ih =>
                  intro idx acc hidx
                  cases idx with
                  | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
                    subst hidx
                    simp only [List.set_cons_zero, List.foldl_cons, hstep_swap]
                  | succ idx' =>
                    simp only [List.getElem?_cons_succ] at hidx
                    simp only [List.set_cons_succ, List.foldl_cons]
                    exact ih idx' (step acc g) hidx
              exact haux D.gates k w hgk
            have hD'M : PEqualNP.MetaComplexity.Monotone2 D' := by
              intro g hg
              obtain ⟨idx, hidx, hge⟩ := List.mem_iff_getElem.mp hg
              have hidx' : idx < D.gates.length := by simpa [D'] using hidx
              by_cases hki : idx = k
              · subst hki
                have hg_eq : g = gswap := by rw [← hge]; simp [D']
                rw [hg_eq]; exact ⟨by simp [gswap], by simp [gswap]⟩
              · have hg_eq : g = D.gates[idx]'hidx' := by
                  rw [← hge]; exact List.getElem_set_ne (Ne.symm hki) hidx
                rw [hg_eq]; exact hDM _ (List.getElem_mem hidx')
            have hD'S : D'.size ≤ 124 := by
              change (D.gates.set k gswap).length ≤ 124
              rw [List.length_set]; exact hDS
            have hD'E : ∀ x : Fin 42 → Bool, D'.eval (List.ofFn x) = true ↔
                ∃ p q : Fin 42, (p.val < 21 ∧ 21 ≤ q.val ∧ (q.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
                  x p = true ∧ x q = true := by
              intro x
              have hev : D'.eval (List.ofFn x) = D.eval (List.ofFn x) := by
                unfold PEqualNP.CircuitLowerBounds.Circuit.eval; rw [hwires_eq]
              rw [hev]; exact hDE x
            have hD'SC : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : Fin 42),
                D'.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
                (D'.wires (List.ofFn fun i : Fin 42 => decide (i = w))).getD (42 + j) false = false := by
              intro j g w hj hop
              rw [hwires_eq]
              by_cases hjk : j = k
              · subst hjk; exact hDSC k gk w hgk hopk
              · have hjD : D.gates[j]? = some g := by
                  simpa [D', List.getElem?_set_ne (Ne.symm hjk)] using hj
                exact hDSC j g w hjD hop
            refine ⟨D', hD'M, hD'S, hD'E, hD'SC, k, b, a, ?_, hb_lt, ha_lt, ?_, ?_, ?_, ?_, ?_⟩
            · simp [D', List.getElem?_set_self hkl, gswap]
            · rw [hwires_eq]; exact hb0
            · rw [hwires_eq]; exact hb1
            · rw [hwires_eq]; exact ha0
            · rw [hwires_eq]; exact ha1
            · intro k' hk' g' hg' hop'
              rw [hwires_eq]
              have hne : k ≠ k' := by omega
              have hgD : D.gates[k']? = some g' := by
                simpa [D', List.getElem?_set_ne hne] using hg'
              exact hmink k' hk' g' hgD hop'
    -- Find an automorphism sending {u, v} to {0, 1} or {0, 24}
    rcases hCover u v huS hvS huv with ⟨bp, c, m, r, heuv⟩ | ⟨bp, c, m, r, heuv⟩
    · let e := mkAut bp c.val m.val r.val
      have he_aut := hMkAut bp c.val m.val ⟨r.val, by omega⟩
      let D := changeC e C
      obtain ⟨hDM, hDS, hDE⟩ := hchange_props e C he_aut.1 he_aut.2 hmono hsize hcomp
      have hDSC : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : Fin 42),
          D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn fun i : Fin 42 => decide (i = w))).getD (42 + j) false = false := by
        intro j g w hj hop
        simp only [D, changeC, List.getElem?_map, Option.map_eq_some_iff] at hj
        obtain ⟨g0, hg0, rfl⟩ := hj
        obtain ⟨w0, rfl⟩ := he_aut.1.2 w
        have hidx : idxE e (42 + j) = 42 + j := by simp [idxE]
        have hfun : (fun i : Fin 42 => decide (i = e w0)) ∘ e = fun i : Fin 42 => decide (i = w0) := by
          funext i; simp only [Function.comp_apply]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          exact ⟨fun h => he_aut.1.1 h, fun h => by rw [h]⟩
        have hw := hchange_wires e C (fun i : Fin 42 => decide (i = e w0)) (42 + j)
        rw [hidx, hfun] at hw
        exact hw.trans (hSC j g0 w0 hg0 hop)
      have hDex : ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 1))).getD (42 + j) false = true := by
        refine ⟨j0, changeGate e g0, by simp [D, changeC, List.getElem?_map, hj0], hg0, ?_⟩
        have hidx : idxE e (42 + j0) = 42 + j0 := by simp [idxE]
        have hfun : (fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 1)) ∘ e = fun i : Fin 42 => decide (i ∈ Y) := by
          funext i; simp only [Function.comp_apply]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, hYuv]
          rcases heuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · constructor
            · rintro (h0 | h1')
              · left; exact he_aut.1.1 (by rw [h1]; exact Fin.ext h0)
              · right; exact he_aut.1.1 (by rw [h2]; exact Fin.ext h1')
            · rintro (rfl | rfl)
              · left; simp [e, h1]
              · right; simp [e, h2]
          · constructor
            · rintro (h0 | h1')
              · right; exact he_aut.1.1 (by rw [h2]; exact Fin.ext h0)
              · left; exact he_aut.1.1 (by rw [h1]; exact Fin.ext h1')
            · rintro (rfl | rfl)
              · right; simp [e, h1]
              · left; simp [e, h2]
        have hw := hchange_wires e C (fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 1)) (42 + j0)
        rw [hidx, hfun] at hw; exact hw.trans hfireY
      obtain ⟨D', hM', hS', hE', hSC', hwit⟩ := hExtract 1 (by omega) (by omega) D hDM hDS hDE hDSC hDex
      exact hTwoPoints D' hM' hS' hE' hSC' hwit
    · let e := mkAut bp c.val m.val r.val
      have he_aut := hMkAut bp c.val m.val r
      let D := changeC e C
      obtain ⟨hDM, hDS, hDE⟩ := hchange_props e C he_aut.1 he_aut.2 hmono hsize hcomp
      have hDSC : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (w : Fin 42),
          D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn fun i : Fin 42 => decide (i = w))).getD (42 + j) false = false := by
        intro j g w hj hop
        simp only [D, changeC, List.getElem?_map, Option.map_eq_some_iff] at hj
        obtain ⟨g0, hg0, rfl⟩ := hj
        obtain ⟨w0, rfl⟩ := he_aut.1.2 w
        have hidx : idxE e (42 + j) = 42 + j := by simp [idxE]
        have hfun : (fun i : Fin 42 => decide (i = e w0)) ∘ e = fun i : Fin 42 => decide (i = w0) := by
          funext i; simp only [Function.comp_apply]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          exact ⟨fun h => he_aut.1.1 h, fun h => by rw [h]⟩
        have hw := hchange_wires e C (fun i : Fin 42 => decide (i = e w0)) (42 + j)
        rw [hidx, hfun] at hw
        exact hw.trans (hSC j g0 w0 hg0 hop)
      have hDex : ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (D.wires (List.ofFn fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 24))).getD (42 + j) false = true := by
        refine ⟨j0, changeGate e g0, by simp [D, changeC, List.getElem?_map, hj0], hg0, ?_⟩
        have hidx : idxE e (42 + j0) = 42 + j0 := by simp [idxE]
        have hfun : (fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 24)) ∘ e = fun i : Fin 42 => decide (i ∈ Y) := by
          funext i; simp only [Function.comp_apply]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, hYuv]
          rcases heuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · constructor
            · rintro (h0 | h1')
              · left; exact he_aut.1.1 (by rw [h1]; exact Fin.ext h0)
              · right; exact he_aut.1.1 (by rw [h2]; exact Fin.ext h1')
            · rintro (rfl | rfl)
              · left; simp [e, h1]
              · right; simp [e, h2]
          · constructor
            · rintro (h0 | h1')
              · right; exact he_aut.1.1 (by rw [h2]; exact Fin.ext h0)
              · left; exact he_aut.1.1 (by rw [h1]; exact Fin.ext h1')
            · rintro (rfl | rfl)
              · right; simp [e, h1]
              · left; simp [e, h2]
        have hw := hchange_wires e C (fun i : Fin 42 => decide (i.val = 0 ∨ i.val = 24)) (42 + j0)
        rw [hidx, hfun] at hw; exact hw.trans hfireY
      obtain ⟨D', hM', hS', hE', hSC', hwit⟩ := hExtract 24 (by omega) (by omega) D hDM hDS hDE hDSC hDex
      exact hPointLine D' hM' hS' hE' hSC' hwit
