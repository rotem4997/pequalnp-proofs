import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1482_3
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
      PEqualNP.TopForm.junk G C = ∅)
    (h3 : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨ (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = ∅ →
      PEqualNP.TopForm.andPairs 26 C = 0) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  classical
  rintro ⟨C, hsz, hwf, heval, p, l, hpl, ⟨v, hv0, hvg, hvout⟩, _⟩
  let adj3 : Fin 26 → Fin 26 → Prop := fun a b =>
    ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
      ((a = Fin.castAdd 13 u ∧ b = Fin.natAdd 13 t) ∨
       (b = Fin.castAdd 13 u ∧ a = Fin.natAdd 13 t))
  let G3 : SimpleGraph (Fin 26) :=
    { Adj := adj3
      symm := ⟨by
        rintro a b ⟨u, t, hinc, hor⟩
        exact ⟨u, t, hinc, hor.symm⟩⟩
      loopless := ⟨by
        rintro a ⟨u, t, _, hor⟩
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
    · rintro ⟨a, b, ⟨u, t, hinc, hor⟩, ha, hb⟩
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, t, hinc, ha, hb⟩
      · exact ⟨u, t, hinc, hb, ha⟩
    · rintro ⟨u, t, hinc, hu, ht⟩
      exact ⟨Fin.castAdd 13 u, Fin.natAdd 13 t, ⟨u, t, hinc, Or.inl ⟨rfl, rfl⟩⟩, hu, ht⟩
  have hfun : PEqualNP.MetaComplexity.circuitFun 26 C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    exact (heval x).trans (hgraph_iff x).symm
  have hleast : PEqualNP.TopForm.IsLeastAO G3 C := by
    refine ⟨hAO2, hfun, ?_⟩
    intro C' hAO2' hfun'
    have heval' : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
      intro x
      have hx : C'.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G3 ∅ x :=
        congrFun hfun' x
      rw [hx]
      exact hgraph_iff x
    exact le_trans hsz (h1 C' hAO2' heval')
  have hjunk : PEqualNP.TopForm.junk G3 C = ∅ := h2 G3 C hG3 hleast
  have hand : PEqualNP.TopForm.andPairs 26 C = 0 := h3 G3 C hG3 hleast hjunk
  have hno_and_cone : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone 26 C i j := by
    intro i hi j hj hopi hopj hcone
    unfold PEqualNP.TopForm.andPairs at hand
    have hemp := Finset.card_eq_zero.mp hand
    have hmem : (i, j) ∈ ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun q =>
        (PEqualNP.MetaComplexity.NestedCover.gateAt C q.1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C q.2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C q.1 q.2) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hopi, hopj, hcone⟩
    rw [Finset.eq_empty_iff_forall_notMem] at hemp
    exact hemp (i, j) (by convert hmem)
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have hstep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hstep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons]
      have hlt : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool)
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl step ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < ws.length + j then (gs.foldl step ws).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro ws j g hj; simp at hj
    | cons g0 gs ih =>
      intro ws j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hstep_lt gs (step ws g0) ws.length hlt]
        have hself : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun i => ws.getD i false) := by
          simp only [step, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < ws.length
        · have hilt : i < (step ws g0).length := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          simp only [hi, ↓reduceIte]
          rw [hstep_lt gs (step ws g0) i hilt]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
            Option.getD_none]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j + 1) = (step ws g0).length + j := by omega
        rw [hidx]
        exact ih (step ws g0) j g hj
  let cstep : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (List ℕ) :=
    fun cs g => cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
      (fun w => (w - 26) :: cs.getD (w - 26) [])]
  have hcone_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length →
      (gs.foldl cstep cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons]
      have hlt : i < (cstep cs g).length := by
        simp only [cstep, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (cstep cs g) i hlt]
      simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hcone_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ))
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl cstep cs).getD (cs.length + j) [] =
        (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + (cs.length + j)))).flatMap
          (fun w => (w - 26) ::
            (gs.foldl cstep cs).getD (w - 26) []) := by
    intro gs
    induction gs with
    | nil => intro cs j g hj; simp at hj
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (cstep cs g0).length := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [hcone_lt gs (cstep cs g0) cs.length hlt]
        have hself : (cstep cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
              (fun w => (w - 26) :: cs.getD (w - 26) []) := by
          simp only [cstep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - 26 < cs.length := by omega
        have hwlt1 : w - 26 < (cstep cs g0).length := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [hcone_lt gs (cstep cs g0) (w - 26) hwlt1]
        simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (cstep cs g0).length = cs.length + 1 := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]
        have hidx : cs.length + (j + 1) = (cstep cs g0).length + j := by
          omega
        rw [hidx]
        exact ih (cstep cs g0) j g hj
  have hin_cone_self : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
      C.gates[j]? = some g → u ∈ g.inputs → 26 ≤ u → u < 26 + j →
      PEqualNP.EdgeOwnership.InCone 26 C (u - 26) j := by
    intro j g u hj hu h26 hlt
    change u - 26 ∈ (C.gates.foldl cstep []).getD j []
    have hcg := hcone_gate C.gates [] j g hj
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    refine ⟨u, ?_, List.mem_cons_self⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hu, h26, hlt⟩
  have hin_cone_trans : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u k : ℕ),
      C.gates[j]? = some g → u ∈ g.inputs → 26 ≤ u → u < 26 + j →
      PEqualNP.EdgeOwnership.InCone 26 C k (u - 26) →
      PEqualNP.EdgeOwnership.InCone 26 C k j := by
    intro j g u k hj hu h26 hlt hk
    change k ∈ (C.gates.foldl cstep []).getD (u - 26) [] at hk
    change k ∈ (C.gates.foldl cstep []).getD j []
    have hcg := hcone_gate C.gates [] j g hj
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    refine ⟨u, ?_, List.mem_cons_of_mem _ hk⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hu, h26, hlt⟩
  let xp : Fin 26 → Bool := fun iy => decide (iy = Fin.castAdd 13 p)
  let xl : Fin 26 → Bool := fun ix => decide (ix = Fin.natAdd 13 l)
  let xpl : Fin 26 → Bool := fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l)
  let wp : ℕ → Bool := fun u => (C.wires (List.ofFn xp)).getD u false
  let wl : ℕ → Bool := fun u => (C.wires (List.ofFn xl)).getD u false
  let wpl : ℕ → Bool := fun u => (C.wires (List.ofFn xpl)).getD u false
  have hwire_in : ∀ (x : Fin 26 → Bool) (u : ℕ) (hu : u < 26),
      (C.wires (List.ofFn x)).getD u false = x ⟨u, hu⟩ := by
    intro x u hu
    change (C.gates.foldl step (List.ofFn x)).getD u false = x ⟨u, hu⟩
    have hlen : (List.ofFn x).length = 26 := List.length_ofFn
    have hlt : u < (List.ofFn x).length := by omega
    rw [hstep_lt C.gates (List.ofFn x) u hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have hwire_gate : ∀ (x : Fin 26 → Bool) (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
      C.gates[j]? = some g → g.inputs = [a, b] → a < 26 + j → b < 26 + j →
      (C.wires (List.ofFn x)).getD (26 + j) false =
        g.op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
    intro x j g a b hj hinp ha hb
    change (C.gates.foldl step (List.ofFn x)).getD (26 + j) false =
      g.op.eval [(C.gates.foldl step (List.ofFn x)).getD a false,
        (C.gates.foldl step (List.ofFn x)).getD b false]
    have hlen : (List.ofFn x).length = 26 := List.length_ofFn
    have hg := hstep_gate C.gates (List.ofFn x) j g hj
    rw [hlen] at hg
    rw [hg, hinp]
    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte]
  let hasAnd : ℕ → Prop := fun u =>
    26 ≤ u ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C (u - 26)).op =
          PEqualNP.CircuitLowerBounds.GateOp.and ∨
        ∃ k, PEqualNP.EdgeOwnership.InCone 26 C k (u - 26) ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
            PEqualNP.CircuitLowerBounds.GateOp.and)
  have hind : ∀ u : ℕ, u < 26 + C.gates.length →
      (¬ hasAnd u → wpl u = (wp u || wl u) ∧ wl u = v u) ∧
      wpl u = (wp u || wl u || v u) := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu
      by_cases hlt26 : u < 26
      · have hwp : wp u = decide ((⟨u, hlt26⟩ : Fin 26) = Fin.castAdd 13 p) := hwire_in xp u hlt26
        have hwl : wl u = decide ((⟨u, hlt26⟩ : Fin 26) = Fin.natAdd 13 l) := hwire_in xl u hlt26
        have hwpl : wpl u = decide ((⟨u, hlt26⟩ : Fin 26) = Fin.castAdd 13 p ∨
            (⟨u, hlt26⟩ : Fin 26) = Fin.natAdd 13 l) := hwire_in xpl u hlt26
        have hveq : wl u = v u := by
          rw [hwl]
          by_cases hlt13 : u < 13
          · have h1' := (hv0 ⟨u, hlt13⟩).1
            rw [h1']
            simp only [decide_eq_false_iff_not]
            intro heq
            have hv' := congrArg Fin.val heq
            simp only [Fin.val_natAdd] at hv'
            omega
          · have hsub : u - 13 < 13 := by omega
            have h2' := (hv0 ⟨u - 13, hsub⟩).2
            have hequ : 13 + (u - 13) = u := by omega
            rw [hequ] at h2'
            rw [h2']
            apply decide_eq_decide.mpr
            constructor
            · intro heq
              apply Fin.ext
              have hv' := congrArg Fin.val heq
              dsimp only [Fin.val_natAdd] at hv' ⊢
              omega
            · intro heq
              apply Fin.ext
              have hv' := congrArg Fin.val heq
              dsimp only [Fin.val_natAdd] at hv' ⊢
              omega
        have hwpl_eq : wpl u = (wp u || wl u) := by
          rw [hwpl, hwp, hwl]
          by_cases h1' : (⟨u, hlt26⟩ : Fin 26) = Fin.castAdd 13 p <;>
            by_cases h2' : (⟨u, hlt26⟩ : Fin 26) = Fin.natAdd 13 l <;>
            simp [h1', h2']
        refine ⟨fun _ => ⟨hwpl_eq, hveq⟩, ?_⟩
        rw [hwpl_eq, ← hveq]
        cases wp u <;> cases wl u <;> rfl
      · have hge26 : 26 ≤ u := Nat.le_of_not_lt hlt26
        let j := u - 26
        have hjlt : j < C.gates.length := by omega
        have huj : u = 26 + j := by omega
        have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hjlt
        obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hwf j C.gates[j] hget
        have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
          change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
          simp [List.getD_eq_getElem?_getD, hget]
        have ha_lt : a < u := by omega
        have hb_lt : b < u := by omega
        have iha := ih a ha_lt (by omega)
        have ihb := ih b hb_lt (by omega)
        have hwpj : wp u = C.gates[j].op.eval [wp a, wp b] := by
          rw [huj]; exact hwire_gate xp j C.gates[j] a b hget hinp ha hb
        have hwlj : wl u = C.gates[j].op.eval [wl a, wl b] := by
          rw [huj]; exact hwire_gate xl j C.gates[j] a b hget hinp ha hb
        have hwplj : wpl u = C.gates[j].op.eval [wpl a, wpl b] := by
          rw [huj]; exact hwire_gate xpl j C.gates[j] a b hget hinp ha hb
        have hmem_a : a ∈ C.gates[j].inputs := by rw [hinp]; simp
        have hmem_b : b ∈ C.gates[j].inputs := by rw [hinp]; simp
        have hand_eval : ∀ x1 x2 : Bool,
            PEqualNP.CircuitLowerBounds.GateOp.and.eval [x1, x2] = (x1 && x2) :=
          fun x1 x2 => by cases x1 <;> cases x2 <;> rfl
        have hor_eval : ∀ x1 x2 : Bool,
            PEqualNP.CircuitLowerBounds.GateOp.or.eval [x1, x2] = (x1 || x2) :=
          fun x1 x2 => by cases x1 <;> cases x2 <;> rfl
        rcases hop with hand_op | hor_op
        · have hhas : hasAnd u := ⟨hge26, Or.inl (by rw [hga]; exact hand_op)⟩
          have hna : ¬ hasAnd a := by
            rintro ⟨ha26, ha_op | ⟨k, hk_cone, hk_op⟩⟩
            · have hk_lt : a - 26 < C.gates.length := by omega
              exact hno_and_cone (a - 26) hk_lt j hjlt ha_op (by rw [hga]; exact hand_op)
                (hin_cone_self j C.gates[j] a hget hmem_a ha26 ha)
            · have hkc := hin_cone_trans j C.gates[j] a k hget hmem_a ha26 ha hk_cone
              have hk_lt : k < C.gates.length := by
                by_contra hge
                have hno : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
                    PEqualNP.CircuitLowerBounds.GateOp.or := by
                  change (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
                    PEqualNP.CircuitLowerBounds.GateOp.or
                  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]
                rw [hno] at hk_op
                cases hk_op
              exact hno_and_cone k hk_lt j hjlt hk_op (by rw [hga]; exact hand_op) hkc
          have hnb : ¬ hasAnd b := by
            rintro ⟨hb26, hb_op | ⟨k, hk_cone, hk_op⟩⟩
            · have hk_lt : b - 26 < C.gates.length := by omega
              exact hno_and_cone (b - 26) hk_lt j hjlt hb_op (by rw [hga]; exact hand_op)
                (hin_cone_self j C.gates[j] b hget hmem_b hb26 hb)
            · have hkc := hin_cone_trans j C.gates[j] b k hget hmem_b hb26 hb hk_cone
              have hk_lt : k < C.gates.length := by
                by_contra hge
                have hno : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
                    PEqualNP.CircuitLowerBounds.GateOp.or := by
                  change (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
                    PEqualNP.CircuitLowerBounds.GateOp.or
                  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]
                rw [hno] at hk_op
                cases hk_op
              exact hno_and_cone k hk_lt j hjlt hk_op (by rw [hga]; exact hand_op) hkc
          obtain ⟨hwpla, hvla⟩ := iha.1 hna
          obtain ⟨hwplb, hvlb⟩ := ihb.1 hnb
          have hvj : v u = ((wp a && v b) || (v a && wp b)) := by
            rw [huj]
            exact (hvg j C.gates[j] a b hget hinp).1 hand_op
          refine ⟨fun hn => absurd hhas hn, ?_⟩
          rw [hwplj, hwpj, hwlj, hvj, hand_op, hand_eval, hand_eval, hand_eval]
          rw [hwpla, hwplb, hvla, hvlb]
          exact (show ∀ x1 x2 y1 y2 : Bool,
            ((x1 || y1) && (x2 || y2)) = ((x1 && x2) || (y1 && y2) || ((x1 && y2) || (y1 && x2)))
            by decide) (wp a) (wp b) (v a) (v b)
        · have hvj : v u = (v a || v b) := by
            rw [huj]
            exact (hvg j C.gates[j] a b hget hinp).2 hor_op
          rw [hwplj, hwpj, hwlj, hor_op, hor_eval, hor_eval, hor_eval]
          constructor
          · intro hnu
            have hna : ¬ hasAnd a := by
              rintro ⟨ha26, ha_op | ⟨k, hk_cone, hk_op⟩⟩
              · exact hnu ⟨hge26, Or.inr ⟨a - 26, hin_cone_self j C.gates[j] a hget hmem_a ha26 ha, ha_op⟩⟩
              · exact hnu ⟨hge26, Or.inr ⟨k, hin_cone_trans j C.gates[j] a k hget hmem_a ha26 ha hk_cone, hk_op⟩⟩
            have hnb : ¬ hasAnd b := by
              rintro ⟨hb26, hb_op | ⟨k, hk_cone, hk_op⟩⟩
              · exact hnu ⟨hge26, Or.inr ⟨b - 26, hin_cone_self j C.gates[j] b hget hmem_b hb26 hb, hb_op⟩⟩
              · exact hnu ⟨hge26, Or.inr ⟨k, hin_cone_trans j C.gates[j] b k hget hmem_b hb26 hb hk_cone, hk_op⟩⟩
            obtain ⟨hwpla, hvla⟩ := iha.1 hna
            obtain ⟨hwplb, hvlb⟩ := ihb.1 hnb
            rw [hwpla, hwplb, hvla, hvlb, hvj]
            constructor
            · exact (show ∀ x1 x2 y1 y2 : Bool,
                ((x1 || y1) || (x2 || y2)) = ((x1 || x2) || (y1 || y2)) by decide)
                (wp a) (wp b) (v a) (v b)
            · rfl
          · rw [iha.2, ihb.2, hvj]
            exact (show ∀ x1 y1 z1 x2 y2 z2 : Bool,
              ((x1 || y1 || z1) || (x2 || y2 || z2)) = ((x1 || x2) || (y1 || y2) || (z1 || z2))
              by decide) (wp a) (wl a) (v a) (wp b) (wl b) (v b)
  have hwpl_out : wpl C.output = true := by
    change C.eval (List.ofFn xpl) = true
    rw [heval xpl]
    refine ⟨p, l, hpl, ?_, ?_⟩
    · simp [xpl]
    · simp [xpl]
  have hwp_out : wp C.output = false := by
    change C.eval (List.ofFn xp) = false
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨u, t, _, _, hxt⟩ := (heval xp).mp ht
    simp only [xp, decide_eq_true_eq] at hxt
    have hv' := congrArg Fin.val hxt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv'
    omega
  have hwl_out : wl C.output = false := by
    change C.eval (List.ofFn xl) = false
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨u, t, _, hxu, _⟩ := (heval xl).mp ht
    simp only [xl, decide_eq_true_eq] at hxu
    have hv' := congrArg Fin.val hxu
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv'
    omega
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    have hlen : (C.wires (List.ofFn xpl)).length = 26 + C.gates.length := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hstep_len, List.length_ofFn]
    have hfalse : wpl C.output = false := by
      change (C.wires (List.ofFn xpl)).getD C.output false = false
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show (C.wires (List.ofFn xpl)).length ≤ C.output by omega),
        Option.getD_none]
    rw [hwpl_out] at hfalse
    cases hfalse
  have hfinal := (hind C.output hout_lt).2
  rw [hwpl_out, hwp_out, hwl_out, hvout] at hfinal
  cases hfinal
