import Mathlib
import PEqualNP.Defs

-- Collapse any fan-in-2 monotone circuit computing PG(2, 4) into a stripped well-formed
-- AndCountCircuit of size at most the AND-gate count, then decompose the 21-gate lower bound into:
-- 1. Proving 19 <= D.size and the read-degree bounds (at most D.size - 16 per vertex and at most
--    D.size - 14 per non-incident point-line pair) via iterative elimination.
-- 2. Ruling out stripped AndCountCircuits of size 19 meeting those read-degree bounds.
-- 3. Ruling out stripped AndCountCircuits of size 20 meeting those read-degree bounds.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2379_1
    (hBounds :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ D : PEqualNP.AndCount.AndCountCircuit 42,
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        D.size ≤ 20 →
        19 ≤ D.size ∧
        (∀ v : Fin 42, {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard + 16 ≤ D.size) ∧
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ PG4.Adj p l →
          {i : Fin D.size | p ∈ D.leftVars i ∨ p ∈ D.rightVars i ∨ l ∈ D.leftVars i ∨ l ∈ D.rightVars i}.ncard + 14 ≤ D.size))
    (hSize19 :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ D : PEqualNP.AndCount.AndCountCircuit 42,
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        D.size = 19 →
        (∀ v : Fin 42, {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard ≤ 3) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ PG4.Adj p l →
          {i : Fin D.size | p ∈ D.leftVars i ∨ p ∈ D.rightVars i ∨ l ∈ D.leftVars i ∨ l ∈ D.rightVars i}.ncard ≤ 5) →
        False)
    (hSize20 :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ D : PEqualNP.AndCount.AndCountCircuit 42,
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        D.size = 20 →
        (∀ v : Fin 42, {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ PG4.Adj p l →
          {i : Fin D.size | p ∈ D.leftVars i ∨ p ∈ D.rightVars i ∨ l ∈ D.leftVars i ∨ l ∈ D.rightVars i}.ncard ≤ 6) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro C hMono hComp
  have op_and_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have op_or_eval (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
  have sideTrue_def {m : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin m)) (i : Fin m) (v : Fin m → Bool) :
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i v =
      decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl
  have gateValFuel_zero (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin E.size) :
      E.gateValFuel U 0 i = false := rfl
  have gateValFuel_succ (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) (d : ℕ) (i : Fin E.size) :
      E.gateValFuel U (d + 1) i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) := rfl
  have gateVal_def (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin E.size) :
      E.gateVal U i = E.gateValFuel U E.size i := rfl
  have eval_def (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) :
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := rfl
  let PG4 : SimpleGraph (Fin 42) :=
    SimpleGraph.fromRel (fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
  have hDir : ∀ u v : Fin 42,
      ((u.val, v.val) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ))) ↔
      (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := by
    decide +kernel
  have hCompG : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, PG4.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [hComp x]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have h' := (hDir u v).mp huv
      have hne : u ≠ v := by intro h; subst h; omega
      exact ⟨u, v, (SimpleGraph.fromRel_adj ..).mpr ⟨hne, Or.inl h'⟩, hxu, hxv⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      rcases ((SimpleGraph.fromRel_adj ..).mp huv).2 with h | h
      · exact ⟨u, v, (hDir u v).mpr h, hxu, hxv⟩
      · exact ⟨v, u, (hDir v u).mpr h, hxv, hxu⟩
  -- Step 1: Collapse Monotone2 circuit C into a well-formed AndCountCircuit D0 of size equal to the AND-gate count of C.
  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wiresFrom_append (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_ext (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp
  have length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]
  have getD_wiresFrom_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (h : i < w.length) : (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_wiresFrom_take (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k i : ℕ)
      (hk : k ≤ gs.length) :
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega
  have getD_wiresFrom_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length) :
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp
  let andFin : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun i : Fin C.gates.length => (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hAndCard : andFin.card =
      {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
    have hcoe : (andFin : Set (Fin C.gates.length)) =
        {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      ext i; simp [andFin]
    rw [← hcoe, Set.ncard_coe_finset]
  let k : ℕ := andFin.card
  let ordFin : Fin k ↪o Fin C.gates.length := andFin.orderEmbOfFin rfl
  let ord (i : Fin k) : ℕ := (ordFin i).val
  have ord_lt_iff (a b : Fin k) : ord a < ord b ↔ a < b := by
    change (ordFin a).val < (ordFin b).val ↔ a < b
    exact ordFin.lt_iff_lt
  have ok (i : Fin k) : ∃ h : ord i < C.gates.length, C.gates[ord i].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    have hmem : ordFin i ∈ andFin := andFin.orderEmbOfFin_mem rfl i
    have hop : (C.gates.get (ordFin i)).op = PEqualNP.CircuitLowerBounds.GateOp.and :=
      (Finset.mem_filter.mp hmem).2
    exact ⟨(ordFin i).isLt, hop⟩
  have allAnd (j : ℕ) (hj : j < C.gates.length)
      (ha : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and) : ∃ i : Fin k, ord i = j := by
    have hjMem : (⟨j, hj⟩ : Fin C.gates.length) ∈ andFin :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hr : (⟨j, hj⟩ : Fin C.gates.length) ∈ Set.range ordFin := by
      rw [Finset.range_orderEmbOfFin]; exact hjMem
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, congrArg Fin.val hi⟩
  let collVal (U : Finset (Fin 42)) (v : Fin k → Bool)
      (s : Finset (Fin 42) × Finset (Fin k)) : Bool :=
    decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)
  let collCollect (L : List ℕ) (s : ℕ → Finset (Fin 42) × Finset (Fin k)) :
      Finset (Fin 42) × Finset (Fin k) :=
    ⟨L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2)⟩
  have collCollect_true (U : Finset (Fin 42)) (v : Fin k → Bool)
      (L : List ℕ) (s : ℕ → Finset (Fin 42) × Finset (Fin k)) :
      collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
    simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · rintro (⟨x, ⟨j, hj, hxj⟩, hxU⟩ | ⟨i, ⟨j, hj, hij⟩, hvi⟩)
      · exact ⟨j, hj, Or.inl ⟨x, hxj, hxU⟩⟩
      · exact ⟨j, hj, Or.inr ⟨i, hij, hvi⟩⟩
    · rintro ⟨j, hj, ⟨x, hxj, hxU⟩ | ⟨i, hij, hvi⟩⟩
      · exact Or.inl ⟨x, ⟨j, hj, hxj⟩, hxU⟩
      · exact Or.inr ⟨i, ⟨j, hj, hij⟩, hvi⟩
  let collOrig (U : Finset (Fin 42)) (w : ℕ) : Bool :=
    (wiresFrom C.gates (List.ofFn (fun i : Fin 42 => decide (i ∈ U)))).getD w false
  have coll_gate (U : Finset (Fin 42)) (j : ℕ) (h : j < C.gates.length) :
      collOrig U (42 + j) = C.gates[j].op.eval (C.gates[j].inputs.map
        (fun i => if i < 42 + j then collOrig U i else false)) := by
    simpa only [collOrig, List.length_ofFn] using
      getD_wiresFrom_gate C.gates (List.ofFn (fun i : Fin 42 => decide (i ∈ U))) j h
  let collV (U : Finset (Fin 42)) (j : Fin k) : Bool := collOrig U (42 + ord j)
  have coll_prior : ∀ w : ℕ,
      (∀ i < w, ∃ s : Finset (Fin 42) × Finset (Fin k), (∀ j ∈ s.2, 42 + ord j ≤ i) ∧
        ∀ U : Finset (Fin 42), collVal U (collV U) s = collOrig U i) →
      ∃ f : ℕ → Finset (Fin 42) × Finset (Fin k), (∀ i j, j ∈ (f i).2 → 42 + ord j < w) ∧
        ∀ i (U : Finset (Fin 42)), collVal U (collV U) (f i) =
          if i < w then collOrig U i else false := by
    intro w ih
    let f (i : ℕ) : Finset (Fin 42) × Finset (Fin k) :=
      if hi : i < w then (ih i hi).choose else (∅, ∅)
    refine ⟨f, ?_, ?_⟩
    · intro i j hj
      by_cases hi : i < w
      · simp only [f, dite_eq_left hi] at hj
        exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
      · simp [f, hi] at hj
    · intro i U
      by_cases hi : i < w
      · simpa only [f, dite_eq_left hi, ite_eq_left hi] using (ih i hi).choose_spec.2 U
      · simp [f, hi, collVal]
  have coll_wires : ∀ w : ℕ,
      ∃ s : Finset (Fin 42) × Finset (Fin k), (∀ j ∈ s.2, 42 + ord j ≤ w) ∧
        ∀ U : Finset (Fin 42), collVal U (collV U) s = collOrig U w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hinput : w < 42
      · let p : Fin 42 := ⟨w, hinput⟩
        refine ⟨({p}, ∅), by simp, ?_⟩
        intro U
        change collVal U (collV U) ({p}, ∅) =
          (wiresFrom C.gates (List.ofFn (fun i : Fin 42 => decide (i ∈ U)))).getD w false
        rw [getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
        rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
        simp [collVal, p]
      · let j := w - 42
        have hw : 42 + j = w := by dsimp [j]; omega
        by_cases hj : j < C.gates.length
        · obtain h | h := (hMono C.gates[j] (List.getElem_mem hj)).1
          · obtain ⟨z, hz⟩ := allAnd j hj h
            exact ⟨(∅, {z}), by simp [hz, hw], fun U => by simp [collVal, collV, hz, hw]⟩
          · obtain ⟨f, hf, he⟩ := coll_prior w ih
            refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
            · intro z hz
              obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
              exact Nat.le_of_lt (hf i z hi)
            · intro U
              rw [← hw, coll_gate U j hj, show C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or from h, op_or_eval]
              apply Bool.eq_iff_iff.mpr
              rw [collCollect_true]
              simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
              simp_rw [he, hw]
        · refine ⟨(∅, ∅), by simp, ?_⟩
          intro U
          change collVal U (collV U) (∅, ∅) =
            (wiresFrom C.gates (List.ofFn (fun i : Fin 42 => decide (i ∈ U)))).getD w false
          rw [List.getD_eq_default _ _ (by simp only [length_wiresFrom, List.length_ofFn]; omega)]
          simp [collVal]
  have coll_sides (i : Fin k) :
      ∃ l r : Finset (Fin 42) × Finset (Fin k),
        (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
        ∀ U : Finset (Fin 42), U.Nonempty →
          (collVal U (collV U) l && collVal U (collV U) r) = collV U i := by
    obtain ⟨h, hop⟩ := ok i
    let g := C.gates[ord i]
    have hlen := (hMono g (List.getElem_mem h)).2
    obtain ⟨f, hf, he⟩ := coll_prior (42 + ord i) (fun w _ => coll_wires w)
    have ltj (a : ℕ) (z : Fin k) (hz : z ∈ (f a).2) : z < i :=
      (ord_lt_iff z i).mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
    have gate (U : Finset (Fin 42)) :
        collV U i = (g.inputs.map fun j => collVal U (collV U) (f j)).all id := by
      change collOrig U (42 + ord i) = _
      rw [coll_gate U (ord i) h, hop, op_and_eval]
      simp only [he, g]
    cases hL : g.inputs with
    | nil =>
      refine ⟨(Finset.univ, ∅), (Finset.univ, ∅), by simp, by simp, ?_⟩
      intro U hu
      rw [gate, hL]
      simpa [collVal] using (show ∃ x, x ∈ U from hu)
    | cons a L =>
      cases L with
      | nil =>
        refine ⟨f a, f a, ltj a, ltj a, ?_⟩
        intro U _
        simp [gate, hL]
      | cons b L =>
        have hem : L = [] := by rw [hL] at hlen; simpa using hlen
        subst L
        refine ⟨f a, f b, ltj a, ltj b, ?_⟩
        intro U _
        simp [gate, hL]
  choose lSide rSide hlSide hrSide hvSide using coll_sides
  obtain ⟨oSide, _, hoSide⟩ := coll_wires C.output
  let D0 : PEqualNP.AndCount.AndCountCircuit 42 :=
    ⟨k, fun i => (lSide i).1, fun i => (lSide i).2, fun i => (rSide i).1, fun i => (rSide i).2,
      oSide.1, oSide.2⟩
  have hD0WF : D0.WellFormed := fun i => ⟨hlSide i, hrSide i⟩
  have hD0Empty : ∀ (d : ℕ) (i : Fin D0.size), D0.gateValFuel ∅ d i = false := by
    intro d
    induction d with
    | zero => intro i; exact gateValFuel_zero D0 ∅ i
    | succ d ih =>
      intro i
      rw [gateValFuel_succ, sideTrue_def, sideTrue_def]
      simp [ih]
  have hD0Eval : ∀ U : Finset (Fin 42), U.Nonempty → D0.eval U = collVal U (collV U) oSide := by
    intro U hU
    have fuel (d : ℕ) : ∀ i : Fin k, i.val < d → D0.gateValFuel U d i = collV U i := by
      induction d with
      | zero => intro i; omega
      | succ d ih =>
        intro i hd
        have eqSide (s : Finset (Fin 42) × Finset (Fin k)) (hs : ∀ z ∈ s.2, z < i) :
            PEqualNP.AndCount.AndCountCircuit.sideTrue U s.1 s.2 i (D0.gateValFuel U d) = collVal U (collV U) s := by
          rw [sideTrue_def]
          dsimp only [collVal]
          congr 1
          apply propext
          apply or_congr_right
          constructor
          · rintro ⟨j, hj, hji, hval⟩
            exact ⟨j, hj, (ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
          · rintro ⟨j, hj, hval⟩
            have hji := hs j hj
            exact ⟨j, hj, hji, (ih j (by change j.val < i.val at hji; omega)).trans hval⟩
        rw [gateValFuel_succ]
        dsimp only [D0]
        rw [eqSide _ (hlSide i), eqSide _ (hrSide i), hvSide i U hU]
    have gate (i : Fin k) : D0.gateVal U i = collV U i := by
      rw [gateVal_def]
      exact fuel k i i.isLt
    rw [eval_def]
    simp only [gate, collVal, D0]
  have hD0Comp : D0.Computes PG4 := by
    intro U
    by_cases hU : U.Nonempty
    · rw [hD0Eval U hU, hoSide]
      change C.eval (List.ofFn (fun i : Fin 42 => decide (i ∈ U))) = true ↔ _
      rw [hCompG]
      constructor
      · rintro ⟨u, v, hadj, hu, hv⟩
        exact ⟨u, of_decide_eq_true hu, v, of_decide_eq_true hv, hadj⟩
      · rintro ⟨u, hu, v, hv, hadj⟩
        exact ⟨u, v, hadj, decide_eq_true hu, decide_eq_true hv⟩
    · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst hUe
      rw [eval_def]
      simp [gateVal_def, hD0Empty]
  -- Step 2: Strip singleton-true gates from D0 to obtain D.
  have sideTrue_congr {m : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin m)) (i : Fin m)
      (v1 v2 : Fin m → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i v1 =
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i v2 := by
    rw [sideTrue_def, sideTrue_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · rintro (hv | ⟨j, hjF, hji, hvj⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
    · rintro (hv | ⟨j, hjF, hji, hvj⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩
  have gateValFuel_indep (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) :
      ∀ (m : ℕ) (i : Fin E.size), i.val < m →
        ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
          E.gateValFuel U d1 i = E.gateValFuel U d2 i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi d1 d2 hd1 hd2
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
      rw [gateValFuel_succ, gateValFuel_succ]
      have hlt : ∀ j : Fin E.size, j < i → E.gateValFuel U k1 j = E.gateValFuel U k2 j :=
        fun j hji => ih j (by omega) k1 k2 (by omega) (by omega)
      rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ hlt,
          sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ hlt]
  have gateVal_unfold (E : PEqualNP.AndCount.AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin E.size) :
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    have heq : E.gateVal U i = E.gateValFuel U (i.val + 1) i := by
      rw [gateVal_def]
      exact gateValFuel_indep E U E.size i i.isLt E.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
    rw [heq, gateValFuel_succ]
    have hlt : ∀ j : Fin E.size, j < i → E.gateValFuel U i.val j = E.gateVal U j := by
      intro j hji
      rw [gateVal_def]
      exact gateValFuel_indep E U E.size j j.isLt i.val E.size hji j.isLt
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ hlt,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ hlt]
  have gateVal_mono_U (E : PEqualNP.AndCount.AndCountCircuit 42) {U W : Finset (Fin 42)}
      (hUW : U ⊆ W) (i : Fin E.size) : E.gateVal U i = true → E.gateVal W i = true := by
    have hfuel : ∀ (d : ℕ) (j : Fin E.size), E.gateValFuel U d j = true → E.gateValFuel W d j = true := by
      intro d
      induction d with
      | zero => intro j hj; rw [gateValFuel_zero] at hj; exact absurd hj Bool.false_ne_true
      | succ d ih =>
        intro j hj
        rw [gateValFuel_succ, Bool.and_eq_true, sideTrue_def, sideTrue_def,
          decide_eq_true_eq, decide_eq_true_eq] at hj
        rw [gateValFuel_succ, Bool.and_eq_true, sideTrue_def, sideTrue_def,
          decide_eq_true_eq, decide_eq_true_eq]
        constructor
        · rcases hj.1 with ⟨v, hvB, hvU⟩ | ⟨r, hrF, hrj, hrv⟩
          · exact Or.inl ⟨v, hvB, hUW hvU⟩
          · exact Or.inr ⟨r, hrF, hrj, ih r hrv⟩
        · rcases hj.2 with ⟨v, hvB, hvU⟩ | ⟨r, hrF, hrj, hrv⟩
          · exact Or.inl ⟨v, hvB, hUW hvU⟩
          · exact Or.inr ⟨r, hrF, hrj, ih r hrv⟩
    rw [gateVal_def, gateVal_def]
    exact hfuel E.size i
  let singSet (i : Fin D0.size) : Finset (Fin 42) :=
    Finset.univ.filter (fun v : Fin 42 => D0.gateVal {v} i = true)
  let D : PEqualNP.AndCount.AndCountCircuit 42 :=
    { size := D0.size
      leftVars := fun i => (D0.leftVars i ∪ ((D0.leftGates i).filter (fun j => j < i)).biUnion singSet) \ singSet i
      leftGates := D0.leftGates
      rightVars := fun i => (D0.rightVars i ∪ ((D0.rightGates i).filter (fun j => j < i)).biUnion singSet) \ singSet i
      rightGates := D0.rightGates
      outVars := D0.outVars ∪ D0.outGates.biUnion singSet
      outGates := D0.outGates }
  have hDWF : D.WellFormed := hD0WF
  have hDSing : ∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false := by
    intro i v
    have hAux : ∀ (m : ℕ) (j : Fin D.size), j.val < m → D.gateVal {v} j = false := by
      intro m
      induction m with
      | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
      | succ m ih =>
        intro j hj
        rw [Bool.eq_false_iff]
        intro htrue
        rw [gateVal_unfold D {v} j, Bool.and_eq_true] at htrue
        have hL := htrue.1
        have hR := htrue.2
        rw [sideTrue_def, decide_eq_true_eq] at hL hR
        have hLv : v ∈ D.leftVars j := by
          rcases hL with ⟨w, hw, hwv⟩ | ⟨r, _, hrj, hrv⟩
          · rwa [Finset.mem_singleton.mp hwv] at hw
          · rw [ih r (by omega)] at hrv; exact absurd hrv Bool.false_ne_true
        have hRv : v ∈ D.rightVars j := by
          rcases hR with ⟨w, hw, hwv⟩ | ⟨r, _, hrj, hrv⟩
          · rwa [Finset.mem_singleton.mp hwv] at hw
          · rw [ih r (by omega)] at hrv; exact absurd hrv Bool.false_ne_true
        simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_univ, true_and] at hLv hRv
        apply hLv.2
        rw [gateVal_unfold D0 {v} j, Bool.and_eq_true, sideTrue_def, sideTrue_def,
          decide_eq_true_eq, decide_eq_true_eq]
        constructor
        · rcases hLv.1 with hv | ⟨r, ⟨hrF, hrj⟩, hrv⟩
          · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
          · exact Or.inr ⟨r, hrF, hrj, hrv⟩
        · rcases hRv.1 with hv | ⟨r, ⟨hrF, hrj⟩, hrv⟩
          · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
          · exact Or.inr ⟨r, hrF, hrj, hrv⟩
    exact hAux D.size i i.isLt
  have hDDisj : ∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i) := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvL hvR
    have hf := hDSing i v
    have ht : D.gateVal {v} i = true := by
      rw [gateVal_unfold D {v} i, Bool.and_eq_true, sideTrue_def, sideTrue_def]
      exact ⟨decide_eq_true (Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩),
             decide_eq_true (Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩)⟩
    rw [hf] at ht
    exact Bool.false_ne_true ht
  have hDEvalEq : ∀ U : Finset (Fin 42), D.eval U = D0.eval U := by
    intro U
    have hLe : ∀ (m : ℕ) (i : Fin D.size), i.val < m → D.gateVal U i = true → D0.gateVal U i = true := by
      intro m
      induction m with
      | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
      | succ m ih =>
        intro i hi hval
        rw [gateVal_unfold D U i, Bool.and_eq_true, sideTrue_def, sideTrue_def,
          decide_eq_true_eq, decide_eq_true_eq] at hval
        rw [gateVal_unfold D0 U i, Bool.and_eq_true, sideTrue_def, sideTrue_def,
          decide_eq_true_eq, decide_eq_true_eq]
        constructor
        · rcases hval.1 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
          · simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at hvB
            rcases hvB.1 with hvC | ⟨j, ⟨hjF, hji⟩, hjv⟩
            · exact Or.inl ⟨v, hvC, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U D0 (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
          · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
        · rcases hval.2 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
          · simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at hvB
            rcases hvB.1 with hvC | ⟨j, ⟨hjF, hji⟩, hjv⟩
            · exact Or.inl ⟨v, hvC, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U D0 (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
          · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    have hGe : ∀ (m : ℕ) (i : Fin D.size), i.val < m → D0.gateVal U i = true →
        (∃ v ∈ U, D0.gateVal {v} i = true) ∨ D.gateVal U i = true := by
      intro m
      induction m with
      | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
      | succ m ih =>
        intro i hi hval
        by_cases hsing : ∃ v ∈ U, D0.gateVal {v} i = true
        · exact Or.inl hsing
        · right
          have hno : ∀ v ∈ U, D0.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
          rw [gateVal_unfold D0 U i, Bool.and_eq_true, sideTrue_def, sideTrue_def,
            decide_eq_true_eq, decide_eq_true_eq] at hval
          rw [gateVal_unfold D U i, Bool.and_eq_true, sideTrue_def, sideTrue_def,
            decide_eq_true_eq, decide_eq_true_eq]
          constructor
          · rcases hval.1 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
            · refine Or.inl ⟨v, ?_, hvU⟩
              simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨Or.inl hvB, hno v hvU⟩
            · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
              · refine Or.inl ⟨v, ?_, hvU⟩
                simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
                  Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨Or.inr ⟨j, ⟨hjF, hji⟩, hvs⟩, hno v hvU⟩
              · exact Or.inr ⟨j, hjF, hji, hj'⟩
          · rcases hval.2 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
            · refine Or.inl ⟨v, ?_, hvU⟩
              simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨Or.inl hvB, hno v hvU⟩
            · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
              · refine Or.inl ⟨v, ?_, hvU⟩
                simp only [D, singSet, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
                  Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨Or.inr ⟨j, ⟨hjF, hji⟩, hvs⟩, hno v hvU⟩
              · exact Or.inr ⟨j, hjF, hji, hj'⟩
    rw [eval_def, eval_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
      · simp only [D, singSet, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_univ, true_and] at hvO
        rcases hvO with hvC | ⟨j, hjO, hvs⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjO, gateVal_mono_U D0 (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
      · exact Or.inr ⟨j, hjO, hLe D.size j j.isLt hjv⟩
    · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
      · exact Or.inl ⟨v, by simp [D, hvO], hvU⟩
      · rcases hGe D.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
        · refine Or.inl ⟨v, ?_, hvU⟩
          simp only [D, singSet, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨j, hjO, hvs⟩
        · exact Or.inr ⟨j, hjO, hj'⟩
  have hDComp : D.Computes PG4 := by
    intro U
    rw [hDEvalEq U]
    exact hD0Comp U
  have hDOut : D.outVars = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hEv : D.eval {v} = true := by
      rw [eval_def]
      exact decide_eq_true (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
    rcases (hDComp {v}).mp hEv with ⟨a, ha, c, hc, hac⟩
    simp only [Finset.mem_singleton] at ha hc
    subst ha; subst hc
    exact PG4.irrefl hac
  -- Step 3: Apply the three children to conclude 21 <= AND-gate count of C.
  by_contra hlt
  have hle : D.size ≤ 20 := by
    change k ≤ 20
    have : k = {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := hAndCard
    omega
  obtain ⟨hge19, hdeg1, hdeg2⟩ := hBounds D hDWF hDComp hDOut hDSing hDDisj hle
  have hcases : D.size = 19 ∨ D.size = 20 := by omega
  rcases hcases with h19 | h20
  · exact hSize19 D hDWF hDComp hDOut hDSing hDDisj h19
      (fun v => by have := hdeg1 v; omega)
      (fun p l hp hl hna => by have := hdeg2 p l hp hl hna; omega)
  · exact hSize20 D hDWF hDComp hDOut hDSing hDDisj h20
      (fun v => by have := hdeg1 v; omega)
      (fun p l hp hl hna => by have := hdeg2 p l hp hl hna; omega)
