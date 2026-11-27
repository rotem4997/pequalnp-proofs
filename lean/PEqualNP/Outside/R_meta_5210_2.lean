import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5210_2
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
      64 ≤ C.size)
    (h2 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨ (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = ∅) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x10 ≠ x11 ∧ ¬x4 x10 x11 ∧ ¬x4 x11 x10 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  classical
  intro hex
  obtain ⟨C, hbody⟩ := hex
  dsimp only at hbody
  obtain ⟨hsz, hwf, heval, hdirty, _⟩ := hbody
  have hmem_iff : ∀ u t : Fin 13,
      u - t ∈ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13)) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) := by
    intro u t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hm
      rcases hm with h | h | h | h
      · left; exact sub_eq_zero.mp h
      · right; left; rw [← h]; abel
      · right; right; left; rw [← h]; abel
      · right; right; right; rw [← h]; abel
    · intro hm
      rcases hm with rfl | rfl | rfl | rfl
      · left; abel
      · right; left; abel
      · right; right; left; abel
      · right; right; right; abel
  have heval' : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
    intro x
    rw [heval x]
    constructor
    · intro h
      obtain ⟨u, t, hut, hu, ht⟩ := h
      exact ⟨u, t, (hmem_iff u t).mp hut, hu, ht⟩
    · intro h
      obtain ⟨u, t, hut, hu, ht⟩ := h
      exact ⟨u, t, (hmem_iff u t).mpr hut, hu, ht⟩
  let adj3 : Fin 26 → Fin 26 → Prop := fun a b =>
    ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
      ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨
       (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t))
  let G3 : SimpleGraph (Fin 26) :=
    { Adj := adj3
      symm := ⟨by
        intro a b hab
        obtain ⟨u, t, hinc, hor⟩ := hab
        exact ⟨u, t, hinc, hor.symm⟩⟩
      loopless := ⟨by
        intro a haa
        obtain ⟨u, t, _, hor⟩ := haa
        rcases hor with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · have hv := congrArg Fin.val (h1'.symm.trans h2')
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · have hv := congrArg Fin.val (h1'.symm.trans h2')
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega⟩ }
  have hG3 : ∀ a b : Fin 26, G3.Adj a b ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨
         (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t)) := fun _ _ => Iff.rfl
  have hAO2 : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      exact (hwf j _ hget).1
    · intro j hj w hw
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hget]
      rw [hga] at hw
      obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hwf j _ hget
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨_, a, b, hinp, _⟩ := hwf j _ hget
      rw [hinp]
      rfl
  have hgraph_iff : ∀ x : Fin 26 → Bool,
      PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ x = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ u v, G3.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and,
      exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨a, b, ⟨u, t, hinc, hor⟩, ha, hb⟩ := h
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, t, hinc, ha, hb⟩
      · exact ⟨u, t, hinc, hb, ha⟩
    · intro h
      obtain ⟨u, t, hinc, hu, ht⟩ := h
      exact ⟨Fin.castAdd 13 u, Fin.natAdd 13 t, ⟨u, t, hinc, Or.inl ⟨rfl, rfl⟩⟩, hu, ht⟩
  have hfun : PEqualNP.MetaComplexity.circuitFun 26 C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    exact (heval' x).trans (hgraph_iff x).symm
  have hleast : PEqualNP.TopForm.IsLeastAO G3 C := by
    refine ⟨hAO2, hfun, ?_⟩
    intro C' hAO2' hfun'
    have hevalC' : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
      intro x
      have hx : C'.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ x :=
        congrFun hfun' x
      rw [hx]
      exact hgraph_iff x
    exact le_trans hsz (h1 C' hAO2' hevalC')
  have hjunk : PEqualNP.TopForm.junk G3 C = ∅ := h2 G3 C hG3 hleast
  obtain ⟨j, hjlt, hjop, z, hzval, hzeval⟩ := hdirty
  have hzg : PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ z = false := by
    have hfz : C.eval (List.ofFn z) = PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ z :=
      congrFun hfun z
    rw [← hfz]
    exact hzeval
  have hjmem : j ∈ PEqualNP.TopForm.junk G3 C := by
    change j ∈ (Finset.range C.gates.length).filter (fun k =>
      PEqualNP.CleanedNonEdge.IsDirtyAnd 26 G3 C k)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hjlt, ?_⟩
    exact ⟨hjop, hjlt, z, hzval, hzg⟩
  rw [hjunk] at hjmem
  exact Finset.notMem_empty j hjmem
