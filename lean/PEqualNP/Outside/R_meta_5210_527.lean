import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5210_527
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
      64 ≤ C.size)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let v := PEqualNP.EdgeOwnership.gateVal 26 C
      let w := PEqualNP.CleanedNonEdge.wireVal 26 C
      let r := PEqualNP.EdgeOwnership.InCone 26 C
      PEqualNP.TopForm.IsAO2 26 C →
      ∀ p q e : Fin 26 → Bool,
      (∀ u, e u = true → p u = true ∨ q u = true) →
      C.eval (List.ofFn e) = true →
      C.eval (List.ofFn p) = false →
      C.eval (List.ofFn q) = false →
      ∀ i j : Nat,
      (i < C.size ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v i e = true ∧
        ∀ a ∈ (g i).inputs, w a p = false) →
      (j < C.size ∧ (g j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v j e = true ∧
        ∀ a ∈ (g j).inputs, w a q = false) →
      ¬ r i j → ¬ r j i →
      ∃ a < C.size, (g a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        v a e = true ∧ a ≠ i ∧ a ≠ j)
    (h3 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      let s : Nat → Prop := fun k => k < C.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k
          (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨ (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      C.size ≤ 64 →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.TopForm.junk G C ≠ ∅ →
      ¬∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ s i ∧ s j ∧ s k) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x10 ≠ x11 ∧ ¬x4 x10 x11 ∧ ¬x4 x11 x10 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  classical
  rintro ⟨C, hC⟩
  dsimp only at hC
  rcases hC with ⟨hsize, hshape, hfun, hdirty, i, j, hij, hincij, hincji, hi, hj⟩
  let p : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 0
  let q : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 13 13
  let e : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 13
  have gat : ∀ k g, C.gates[k]? = some g →
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
    intro k g hg
    change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
    rw [List.getD_eq_getElem?_getD, hg]
    rfl
  have hc : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
      exact (hshape k g hk).1
    · intro k hk w hw
      have hg := List.getElem?_eq_getElem hk
      obtain ⟨_, u, v, hins, _, hu, hv⟩ := hshape k C.gates[k] hg
      rw [gat k C.gates[k] hg, hins] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨_, u, v, hins, _⟩ := hshape k g hk
      simp [hins]
  have hn : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨_, u, v, hins, huv, _⟩ := hshape k g hk
    simp [hins, huv]
  have bounds : ∀ k, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
      PEqualNP.CircuitLowerBounds.GateOp.and → k < C.size := by
    intro k ha
    by_contra hk
    change ¬ k < C.gates.length at hk
    have hz : PEqualNP.MetaComplexity.NestedCover.gateAt C k =
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      exact List.getD_eq_default _ _ (by change C.gates.length ≤ k; omega)
    rw [hz] at ha
    cases ha
  have hcover : ∀ u, e u = true → p u = true ∨ q u = true := by
    intro u hu
    change decide (u = 0 ∨ u = 13) = true at hu
    change decide (u = 0 ∨ u = 0) = true ∨ decide (u = 13 ∨ u = 13) = true
    simpa only [or_self, decide_eq_true_eq] using hu
  have he : C.eval (List.ofFn e) = true := by
    exact (hfun e).mpr ⟨0, 0, by decide, by decide, by decide⟩
  have hp : C.eval (List.ofFn p) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨u, v, _, _, hv⟩ := (hfun p).mp ht
    change decide (Fin.natAdd 13 v = (0 : Fin 26) ∨ Fin.natAdd 13 v = 0) = true at hv
    have hzero : Fin.natAdd 13 v = (0 : Fin 26) :=
      (of_decide_eq_true hv).elim id id
    have hval := congrArg Fin.val hzero
    change 13 + v.val = 0 at hval
    omega
  have hq : C.eval (List.ofFn q) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨u, v, _, hu, _⟩ := (hfun q).mp ht
    change decide (Fin.castAdd 13 u = (13 : Fin 26) ∨ Fin.castAdd 13 u = 13) = true at hu
    have hthirteen : Fin.castAdd 13 u = (13 : Fin 26) :=
      (of_decide_eq_true hu).elim id id
    have hval := congrArg Fin.val hthirteen
    change u.val = 13 at hval
    have := u.isLt
    omega
  have lower : ∀ k x, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
      PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k b) x = false) →
      ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
        PEqualNP.CleanedNonEdge.wireVal 26 C w x = false := by
    intro k x ha hf w hw
    have hk : k < C.gates.length := bounds k ha
    have hg := List.getElem?_eq_getElem hk
    obtain ⟨_, u, v, hins, _⟩ := hshape k C.gates[k] hg
    have hh := gat k C.gates[k] hg
    rw [hh, hins] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have hf0 := hf (0 : Fin 2)
      change PEqualNP.CleanedNonEdge.wireVal 26 C
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0) x = false at hf0
      rw [hh, hins] at hf0
      exact hf0
    · have hf1 := hf (1 : Fin 2)
      change PEqualNP.CleanedNonEdge.wireVal 26 C
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0) x = false at hf1
      rw [hh, hins] at hf1
      exact hf1
  obtain ⟨k, hk, hka, hke, hki, hkj⟩ := h2 C hc p q e hcover he hp hq i j
    ⟨bounds i hi.1, hi.1, hi.2.2.1, lower i p hi.1 hi.2.2.2⟩
    ⟨bounds j hj.1, hj.1, hj.2.2.1, lower j q hj.1 hj.2.2.2⟩ hincij hincji
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
    rw [hfun x]
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
      exact (hshape j _ hget).1
    · intro j hj w hw
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hget]
      rw [hga] at hw
      obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hshape j _ hget
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨_, a, b, hinp, _⟩ := hshape j _ hget
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
  have hcf : PEqualNP.MetaComplexity.circuitFun 26 C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    exact (heval' x).trans (hgraph_iff x).symm
  have hleast : PEqualNP.TopForm.IsLeastAO G3 C := by
    refine ⟨hAO2, hcf, ?_⟩
    intro C' hAO2' hfun'
    have hevalC' : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
      intro x
      have hx : C'.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ x :=
        congrFun hfun' x
      rw [hx]
      exact hgraph_iff x
    exact le_trans hsize (h1 C' hAO2' hevalC')
  obtain ⟨d, hdlt, hdop, z, hzval, hzeval⟩ := hdirty
  have hzg : PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ z = false := by
    have hfz : C.eval (List.ofFn z) = PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ z :=
      congrFun hcf z
    rw [← hfz]
    exact hzeval
  have hdmem : d ∈ PEqualNP.TopForm.junk G3 C := by
    change d ∈ (Finset.range C.gates.length).filter (fun k =>
      PEqualNP.CleanedNonEdge.IsDirtyAnd 26 G3 C k)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hdlt, ?_⟩
    exact ⟨hdop, hdlt, z, hzval, hzg⟩
  have hjne : PEqualNP.TopForm.junk G3 C ≠ ∅ := by
    intro hj0
    rw [hj0] at hdmem
    exact Finset.notMem_empty d hdmem
  exact h3 G3 C hG3 hleast hsize hn hjne
    ⟨i, j, k, hij, Ne.symm hki, Ne.symm hkj,
      ⟨bounds i hi.1, hi.1, hi.2.2.1⟩,
      ⟨bounds j hj.1, hj.1, hj.2.2.1⟩, ⟨hk, hka, hke⟩⟩
