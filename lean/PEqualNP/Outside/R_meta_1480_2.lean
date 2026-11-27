import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Normalize an incident flag to wires 0 and 7, then split on the first gate.
theorem PEqualNP.Outside.R_meta_1480_2 :
    (∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .and →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      False) →
    (∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .or →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      False) →
    (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false))) := by
  intro noAnd noOr h
  obtain ⟨C, hsize, hg, hfun, p, l, hinc, ⟨v, vi, vg, vo⟩, ⟨w, wi, wg, wo⟩⟩ := h
  have hget (C : Circuit) (j : ℕ) (hj : j < C.size) : C.gates[j]? = some (gateAt C j) := by
    change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem (show j < C.gates.length from hj),
      List.getD_eq_getElem _ _ (show j < C.gates.length from hj)]
  have hgate (j : ℕ) (hj : j < C.size) :
      ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j :=
    (hg j (gateAt C j) (hget C j hj)).2
  have hopnd (C : Circuit) (j a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) :
      opnd C j 0 = a ∧ opnd C j 1 = b := by
    change (gateAt C j).inputs.getD 0 0 = a ∧ (gateAt C j).inputs.getD 1 0 = b
    rw [hab]
    exact ⟨rfl, rfl⟩
  have hreads :
      ∀ s : Bool, ∃ z : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then Fin.castAdd 7 p else Fin.natAdd 7 l)))
        (∀ i < 14, z i = decide (i = if s then 7 + l.val else p.val)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            z (14 + j) = ((W.getD a false && z b) || (z a && W.getD b false))) ∧
          (g.op = .or → z (14 + j) = (z a || z b))) ∧ z C.output = false := by
    intro s
    cases s
    · refine ⟨w, ?_, ?_, wo⟩
      · intro i hi
        by_cases h : i < 7
        · have he := (wi ⟨i, h⟩).1
          exact he.trans (by congr 1; exact propext Fin.ext_iff)
        · let a : Fin 7 := ⟨i - 7, by omega⟩
          have ha : 7 + a.val = i := by dsimp [a]; omega
          change w i = decide (i = p.val)
          rw [← ha, (wi a).2]
          have hp := p.isLt
          simp [show 7 + a.val ≠ p.val by omega]
      · intro j hj
        obtain ⟨a, b, hab, _⟩ := hgate j hj
        obtain ⟨ha, hb⟩ := hopnd C j a b hab
        simpa only [ha, hb, Bool.false_eq_true, ite_true, ite_false] using (wg j (gateAt C j) a b (hget C j hj) hab)
    · refine ⟨v, ?_, ?_, vo⟩
      · intro i hi
        by_cases h : i < 7
        · change v i = decide (i = 7 + l.val)
          rw [(vi ⟨i, h⟩).1]
          simp [show i ≠ 7 + l.val by omega]
        · let a : Fin 7 := ⟨i - 7, by omega⟩
          have ha : 7 + a.val = i := by dsimp [a]; omega
          change v i = decide (i = 7 + l.val)
          rw [← ha, (vi a).2]
          simp [Fin.ext_iff]
      · intro j hj
        obtain ⟨a, b, hab, _⟩ := hgate j hj
        obtain ⟨ha, hb⟩ := hopnd C j a b hab
        simpa only [ha, hb, Bool.false_eq_true, ite_true, ite_false] using (vg j (gateAt C j) a b (hget C j hj) hab)

  -- The affine maps carry the flag (0, 0) to a chosen incident point and line.
  let I (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3
  let a (p l : Fin 7) : Fin 7 := if p = l then 1 else if p = l + 1 then 2 else 4
  have orbit : ∀ p l : Fin 7, I p l →
      (∀ u t, I (a p l * u + p) (a p l * t + l) ↔ I u t) ∧
      (∀ u t, a p l * u + p = a p l * t + p → u = t) ∧
      (∀ u t, a p l * u + l = a p l * t + l → u = t) := by
    decide +revert
  obtain ⟨preserve, pinj, linj⟩ := orbit p l hinc
  let P : Equiv.Perm (Fin 7) := Equiv.ofBijective (fun u => a p l * u + p)
    (Finite.injective_iff_bijective.mp (fun _ _ h => pinj _ _ h))
  let L : Equiv.Perm (Fin 7) := Equiv.ofBijective (fun t => a p l * t + l)
    (Finite.injective_iff_bijective.mp (fun _ _ h => linj _ _ h))
  let S : Fin 7 ⊕ Fin 7 ≃ Fin 14 := finSumFinEquiv
  let τ : Equiv.Perm (Fin 14) := S.symm.trans ((Equiv.sumCongr P L).trans S)
  have hτp (u : Fin 7) : τ (Fin.castAdd 7 u) = Fin.castAdd 7 (P u) := by
    change S (Sum.map P L (S.symm (Fin.castAdd 7 u))) = _
    have hin : S (Sum.inl u) = Fin.castAdd 7 u := rfl
    rw [← hin, Equiv.symm_apply_apply]
    rfl
  have hτl (t : Fin 7) : τ (Fin.natAdd 7 t) = Fin.natAdd 7 (L t) := by
    change S (Sum.map P L (S.symm (Fin.natAdd 7 t))) = _
    have hin : S (Sum.inr t) = Fin.natAdd 7 t := rfl
    rw [← hin, Equiv.symm_apply_apply]
    rfl
  have hP0 : P 0 = p := by change a p l * 0 + p = p; simp
  have hL0 : L 0 = l := by change a p l * 0 + l = l; simp
  have hτp0 : τ 0 = Fin.castAdd 7 p := by
    change τ (Fin.castAdd 7 0) = _
    rw [hτp, hP0]
  have hτl0 : τ 7 = Fin.natAdd 7 l := by
    change τ (Fin.natAdd 7 (0 : Fin 7)) = _
    rw [hτl, hL0]
  -- Wire evaluation under input renumbering follows the simulation in L-meta-1351.
  let M (ρ : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
    if h : w < 14 then (ρ ⟨w, h⟩).val else w
  have hMlt (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ i < 14 ↔ i < 14 := by
    by_cases h : i < 14
    · simp only [M, dite_eq_left h, h, iff_true]
      exact (ρ ⟨i, h⟩).isLt
    · simp [M, h]
  have hMof (ρ : Equiv.Perm (Fin 14)) (i : Fin 14) : M ρ i.val = (ρ i).val := by
    simp [M, i.isLt]
  have hMinv (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ.symm (M ρ i) = i := by
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change M ρ.symm (M ρ j.val) = j.val
      rw [hMof, hMof, ρ.symm_apply_apply]
    · simp [M, h]
  have hMbound (ρ : Equiv.Perm (Fin 14)) (i j : ℕ) (h : i < 14 + j) : M ρ i < 14 + j := by
    by_cases hi : i < 14
    · have := (hMlt ρ i).2 hi
      omega
    · simpa [M, hi] using h
  let mapGate (ρ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (M ρ)⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalRel (ρ : Equiv.Perm (Fin 14)) (gs : List Gate) :
      ∀ W W' : List Bool, 14 ≤ W.length → W'.length = W.length →
        (∀ w, W'.getD (M ρ w) false = W.getD w false) →
        ∀ w, ((gs.map (mapGate ρ)).foldl step W').getD (M ρ w) false =
          (gs.foldl step W).getD w false := by
    induction gs with
    | nil => intro W W' hW hlen hbase w; exact hbase w
    | cons g gs ih =>
      intro W W' hW hlen hbase w
      simp only [List.map_cons, List.foldl_cons]
      have hv : (mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hbase a
      apply ih (step W g) (step W' (mapGate ρ g)) (by simp [step]; omega)
        (by simp [step, hlen]) _ w
      intro u
      simp only [step, hv]
      rcases Nat.lt_trichotomy u W.length with hlt | heq | hgt
      · have hlt' : M ρ u < W'.length := by
          by_cases hsmall : u < 14
          · have := (hMlt ρ u).2 hsmall
            omega
          · simpa [M, hsmall, hlen] using hlt
        rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
        exact hbase u
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge]]
        have last (w : List Bool) (x : Bool) (h : u = w.length) :
            (w ++ [x]).getD u false = x := by rw [h]; simp
        rw [last W' _ (by omega), last W _ heq]
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge],
          List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have hWires (ρ : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) :
      ((Circuit.mk (C.gates.map (mapGate ρ)) (M ρ C.output)).wires (List.ofFn x)).getD
        (M ρ w) false = (C.wires (List.ofFn (x ∘ ρ))).getD w false := by
    apply evalRel ρ C.gates _ _ (by simp) (by simp) _ w
    intro i
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change (List.ofFn x).getD (M ρ j.val) false = (List.ofFn (x ∘ ρ)).getD j.val false
      rw [hMof]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (ρ j).isLt),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
          List.getElem_ofFn, List.getElem_ofFn]
      rfl
    · rw [show M ρ i = i by simp [M, h],
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  let σ := τ.symm
  let D : Circuit := ⟨C.gates.map (mapGate σ), M σ C.output⟩
  have hDsize : D.size = C.size := List.length_map (mapGate σ)
  have hDget (j : ℕ) : D.gates[j]? = C.gates[j]?.map (mapGate σ) := List.getElem?_map
  have hDgate (j : ℕ) (hj : j < D.size) :
      gateAt D j = mapGate σ (gateAt C j) := by
    have hj' : j < C.size := hDsize ▸ hj
    have h := hDget j
    rw [hget D j hj, hget C j hj'] at h
    exact Option.some.inj h
  have hDinputs (j a b : ℕ) (hj : j < D.size) (hab : (gateAt C j).inputs = [a, b]) :
      (gateAt D j).inputs = [M σ a, M σ b] := by
    rw [hDgate j hj]
    change (gateAt C j).inputs.map (M σ) = _
    rw [hab]
    rfl
  have hDmono : IsAO2 14 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      exact (hg j g' hj).1
    · intro j hj i hi
      obtain ⟨a, b, hab, _, ha, hb⟩ := hgate j (hDsize ▸ hj)
      rw [hDinputs j a b hj hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hMbound σ a j ha
      · exact hMbound σ b j hb
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      obtain ⟨a, b, hab, _⟩ := (hg j g' hj).2
      change (g'.inputs.map (M σ)).length = 2
      simp [hab]
  have hDdistinct (j : ℕ) (hj : j < D.size) : opnd D j 0 ≠ opnd D j 1 := by
    obtain ⟨a, b, hab, hn, _⟩ := hgate j (hDsize ▸ hj)
    obtain ⟨ha, hb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
    rw [ha, hb]
    intro he
    exact hn (by simpa only [hMinv] using congrArg (M σ.symm) he)
  have hDkind : (gateAt D 0).op = .and ∨ (gateAt D 0).op = .or := by
    change ((D.gates[0]?).getD (⟨.or, []⟩ : Gate)).op = .and ∨
      ((D.gates[0]?).getD (⟨.or, []⟩ : Gate)).op = .or
    rw [hDget]
    cases hzero : C.gates[0]? with
    | none => exact Or.inr rfl
    | some g => exact (hg 0 g hzero).1
  have hσp (u : Fin 7) : σ (Fin.castAdd 7 (P u)) = Fin.castAdd 7 u := by
    rw [← hτp]
    exact τ.symm_apply_apply _
  have hσl (t : Fin 7) : σ (Fin.natAdd 7 (L t)) = Fin.natAdd 7 t := by
    rw [← hτl]
    exact τ.symm_apply_apply _
  have hDfun (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 7, I u t ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := hWires σ C x C.output
    rw [he, hfun]
    constructor
    · rintro ⟨u, t, h, hu, ht⟩
      obtain ⟨u, rfl⟩ := P.surjective u
      obtain ⟨t, rfl⟩ := L.surjective t
      refine ⟨u, t, (preserve u t).1 h, ?_, ?_⟩
      · simpa only [Function.comp_apply, hσp] using hu
      · simpa only [Function.comp_apply, hσl] using ht
    · rintro ⟨u, t, h, hu, ht⟩
      exact ⟨P u, L t, (preserve u t).2 h,
        by simpa only [Function.comp_apply, hσp],
        by simpa only [Function.comp_apply, hσl]⟩
  have hDreads :
      ∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires (List.ofFn (fun i : Fin 14 => decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < D.size,
          let g := gateAt D j
          let a := opnd D j 0
          let b := opnd D j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v D.output = false := by
    intro s
    obtain ⟨z, hzinit, hzgate, hzout⟩ := hreads s
    let x : Fin 14 → Bool := fun i => decide (i = if s then 0 else 7)
    have hx : x ∘ σ = fun i : Fin 14 =>
        decide (i = if s then Fin.castAdd 7 p else Fin.natAdd 7 l) := by
      funext i
      apply Bool.decide_congr
      have hh : τ (if s then 0 else 7) = if s then Fin.castAdd 7 p else Fin.natAdd 7 l := by
        cases s
        · simpa using hτl0
        · simpa using hτp0
      rw [← hh]
      exact τ.symm_apply_eq
    have hW (i : ℕ) :
        (D.wires (List.ofFn x)).getD (M σ i) false =
        (C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then Fin.castAdd 7 p else Fin.natAdd 7 l)))).getD i false := by
      rw [← hx]
      exact hWires σ C x i
    have hseed : M σ (if s then 7 + l.val else p.val) = if s then 7 else 0 := by
      cases s
      · change M σ (Fin.castAdd 7 p).val = (0 : Fin 14).val
        rw [← hτp0, hMof, τ.symm_apply_apply]
      · change M σ (Fin.natAdd 7 l).val = (7 : Fin 14).val
        rw [← hτl0, hMof, τ.symm_apply_apply]
    refine ⟨fun i => z (M τ i), ?_, ?_, ?_⟩
    · intro i hi
      change z (M τ i) = decide (i = if s then 7 else 0)
      rw [hzinit _ ((hMlt τ i).2 hi)]
      apply Bool.decide_congr
      constructor
      · intro he
        have he' := congrArg (M σ) he
        change M τ.symm (M τ i) = M σ _ at he'
        rwa [hMinv, hseed] at he'
      · intro he
        have he' := congrArg (M τ) (he.trans hseed.symm)
        change M τ i = M σ.symm (M σ _) at he'
        rwa [hMinv] at he'
    · intro j hj
      have hj' : j < C.size := hDsize ▸ hj
      obtain ⟨a, b, hab, _⟩ := hgate j hj'
      obtain ⟨ha, hb⟩ := hopnd C j a b hab
      obtain ⟨hda, hdb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
      have hOp : (gateAt D j).op = (gateAt C j).op := by rw [hDgate j hj]
      have hwire : M τ (14 + j) = 14 + j := by simp [M, show ¬ 14 + j < 14 by omega]
      have hma : M τ (M σ a) = a := hMinv σ a
      have hmb : M τ (M σ b) = b := hMinv σ b
      have hh := hzgate j hj'
      simp only [ha, hb] at hh
      change ((gateAt D j).op = GateOp.and → z (M τ (14 + j)) =
          (((D.wires (List.ofFn x)).getD (opnd D j 0) false && z (M τ (opnd D j 1))) ||
           (z (M τ (opnd D j 0)) && (D.wires (List.ofFn x)).getD (opnd D j 1) false))) ∧
        ((gateAt D j).op = GateOp.or → z (M τ (14 + j)) =
          (z (M τ (opnd D j 0)) || z (M τ (opnd D j 1))))
      simpa only [hOp, hda, hdb, hwire, hma, hmb, hW] using hh
    · change z (M σ.symm (M σ C.output)) = false
      rwa [hMinv]
  rcases hDkind with hfirst | hfirst
  · exact noAnd D (hDsize ▸ hsize) hDmono hDdistinct hfirst hDfun hDreads
  · exact noOr D (hDsize ▸ hsize) hDmono hDdistinct hfirst hDfun hDreads
