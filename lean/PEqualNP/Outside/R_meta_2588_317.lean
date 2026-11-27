import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.HeptadCover PEqualNP.LowMerge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2588_317
    (orbit :
  let P := (incidences singerLines3).image fun e => pointLineInput 13 13 e.1 e.2
  let N := (quadrangles singerLines3).image fun Q =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)
  let can (a b : ℕ) := (min a b, max a b) ∈ ([(0,1), (13,14), (0,13), (0,14)] : List (ℕ × ℕ))
  ∀ a b : Fin 26, a ≠ b → ∃ f : Fin 26 ≃ Fin 26, can (f a) (f b) ∧
    let pull := fun (x : List Bool) => List.ofFn fun i : Fin 26 => x.getD (f i).val false
    P.image pull = P ∧ N.image pull = N)
    (bound :
  let P := (incidences singerLines3).image fun e => pointLineInput 13 13 e.1 e.2
  let N := (quadrangles singerLines3).image fun Q =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)
  let can (a b : ℕ) := (min a b, max a b) ∈ ([(0,1), (13,14), (0,13), (0,14)] : List (ℕ × ℕ))
  ∀ C : Circuit, IsAO2 26 C →
    can ((gateAt C 0).inputs.getD 0 0) ((gateAt C 0).inputs.getD 1 0) →
    (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) → 2 ≤ andPairs 26 C →
    (∀ x ∈ P, C.eval x = true) → (∀ x ∈ N, C.eval x = false) →
    (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ w ∈ (gateAt C j).inputs,
      ∃ x ∈ N, (C.wires x).getD (26+j) false ≠ (C.wires x).getD w false) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ x4 ∈ x2.gates, x4.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x4.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x2 → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x2.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) = Bool.true) → (∀ x7 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x2.eval (x1 x7) = Bool.false) → (∀ x8 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, ∃ x13 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (x2.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false ≠ (x2.wires (x1 x13)).getD x11 Bool.false) → (64 : ℕ) ≤ x2.size := by
  let P := (incidences singerLines3).image fun e => pointLineInput 13 13 e.1 e.2
  let N := (quadrangles singerLines3).image fun Q =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)
  let can (a b : ℕ) := (min a b, max a b) ∈ ([(0,1), (13,14), (0,13), (0,14)] : List (ℕ × ℕ))
  classical
  dsimp only
  intro C ao diff nested pos neg essential
  have gateDef (K : Circuit) (j : ℕ) : gateAt K j = K.gates.getD j ⟨.or, []⟩ := rfl
  have sizeDef (K : Circuit) : K.size = K.gates.length := rfl
  let _ := gateOpDecEq
  have pairDef (K : Circuit) : andPairs 26 K =
      ((Finset.range K.gates.length ×ˢ Finset.range K.gates.length).filter fun e =>
        (gateAt K e.1).op = GateOp.and ∧ (gateAt K e.2).op = GateOp.and ∧ InCone 26 K e.1 e.2).card := rfl
  have hsize : 0 < C.gates.length := by
    by_contra! empty
    have : C.gates = [] := List.length_eq_zero_iff.mp (by omega)
    simp [pairDef, this] at nested
  have atZero : gateAt C 0 ∈ C.gates := by
    rw [gateDef, List.getD_eq_getElem _ _ hsize]
    exact List.getElem_mem _
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ atZero)
  have ha : a < 26 := ao.2.1 0 hsize a (by simp [hab])
  have hb : b < 26 := ao.2.1 0 hsize b (by simp [hab])
  have dab := diff _ atZero
  simp [hab] at dab
  obtain ⟨f, canon, hP, hN⟩ := orbit ⟨a,ha⟩ ⟨b,hb⟩ (fun he => dab (congrArg Fin.val he))
  let rename (w : ℕ) : ℕ := if h : w < 26 then (f ⟨w,h⟩).val else w
  let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let D : Circuit := ⟨C.gates.map rg, rename C.output⟩
  have low {w : ℕ} (h : w < 26) : rename w < 26 := by simp [rename, h]
  have high {w : ℕ} (h : 26 ≤ w) : rename w = w := by simp [rename, Nat.not_lt.mpr h]
  have earlier {w j : ℕ} (hw : w < 26+j) : rename w < 26+j := by
    by_cases h : w < 26
    · have := low h; omega
    · simpa [high (Nat.le_of_not_lt h)] using hw
  have inject : Function.Injective rename := by
    intro x y e
    by_cases hx : x < 26 <;> by_cases hy : y < 26
    · simp only [rename, hx, hy, dite_true] at e
      exact congrArg Fin.val (f.injective (Fin.ext e))
    · have := low hx; rw [high (by omega : 26 ≤ y)] at e; omega
    · have := low hy; rw [high (by omega : 26 ≤ x)] at e; omega
    · simpa [high (Nat.le_of_not_lt hx), high (Nat.le_of_not_lt hy)] using e
  have dg (j : ℕ) (hj : j < C.gates.length) : gateAt D j = rg (gateAt C j) := by
    simp only [gateDef, D, List.getD_eq_getElem _ _ (by simpa using hj : j < (C.gates.map rg).length),
      List.getElem_map, List.getD_eq_getElem _ _ hj]
  have model : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      exact ao.1 k hk
    · intro j hj w hw
      have hj' : j < C.gates.length := by simpa [D] using hj
      rw [dg j hj'] at hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact earlier (ao.2.1 _ hj' _ hi)
    · intro g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      simpa [rg] using ao.2.2 k hk
  have first : can ((gateAt D 0).inputs.getD 0 0) ((gateAt D 0).inputs.getD 1 0) := by
    simpa [can, dg 0 hsize, rg, hab, rename, ha, hb] using canon
  have distinct : ∀ g ∈ D.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    obtain ⟨s,t,st⟩ := List.length_eq_two.mp (ao.2.2 k hk)
    have d := diff k hk
    simp [st] at d
    simpa [rg, st] using inject.ne d
  have sameCones : cones 26 D = cones 26 C := by
    have one (cs : List (List ℕ)) (g : Gate) : coneStep 26 cs (rg g) = coneStep 26 cs g := by
      have clean (ws : List ℕ) :
          (ws.map rename).filter (fun w => decide (26 ≤ w ∧ w < 26+cs.length)) =
          ws.filter (fun w => decide (26 ≤ w ∧ w < 26+cs.length)) := by
        induction ws with
        | nil => rfl
        | cons w ws ih =>
          simp only [List.map_cons, List.filter_cons, ih]
          by_cases h : w < 26
          · have lo := low h
            simp [Nat.not_le_of_lt h, Nat.not_le_of_lt lo]
          · simp [high (Nat.le_of_not_lt h)]
      change cs ++ [(((g.inputs.map rename).filter _).flatMap _)] = cs ++ [((g.inputs.filter _).flatMap _)]
      rw [clean]
    change (C.gates.map rg).foldl (coneStep 26) [] = C.gates.foldl (coneStep 26) []
    simp [List.foldl_map, one]
  have samePairs : andPairs 26 D = andPairs 26 C := by
    rw [pairDef, pairDef]
    have len : D.gates.length = C.gates.length := List.length_map _
    rw [len]
    congr 1
    ext ⟨i,j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    by_cases h : i < C.gates.length ∧ j < C.gates.length
    · rw [dg _ h.1, dg _ h.2]
      have eqCone : InCone 26 D i j ↔ InCone 26 C i j := by
        change i ∈ (cones 26 D).getD j [] ↔ _
        rw [sameCones]
        exact Iff.rfl
      simp only [rg, eqCone]
    · simp [h]
  let pull := fun (x : List Bool) => List.ofFn fun i : Fin 26 => x.getD (f i).val false
  change P.image pull = P at hP
  change N.image pull = N at hN
  have run (x : List Bool) (hx : x.length = 26) (w : ℕ) :
      (D.wires x).getD (rename w) false = (C.wires (pull x)).getD w false := by
    let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]
    have loop (gs : List Gate) (v u : List Bool) (sz : 26 ≤ u.length) (eqL : u.length = v.length)
        (agree : ∀ i, v.getD (rename i) false = u.getD i false) :
        ∀ i, ((gs.map rg).foldl step v).getD (rename i) false = (gs.foldl step u).getD i false := by
      induction gs generalizing v u with
      | nil => exact agree
      | cons g gs ih =>
        apply ih
        · simp [step]; omega
        · simp [step, eqL]
        · intro j
          by_cases hj : j < u.length
          · have lt : rename j < v.length := by
              by_cases h : j < 26
              · have := low h; omega
              · simpa [high (Nat.le_of_not_lt h), ← eqL] using hj
            exact (List.getD_append _ _ _ _ lt).trans ((agree j).trans (List.getD_append _ _ _ _ hj).symm)
          · rw [high (by omega : 26 ≤ j)]
            simp only [step, rg, List.map_map]
            have vals : g.inputs.map ((fun i => v.getD i false) ∘ rename) =
                g.inputs.map (fun i => u.getD i false) := List.map_congr_left (fun i _ => agree i)
            rw [vals, List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), eqL]
    apply loop C.gates x (pull x) (by simp [pull]) (by simp [pull, hx])
    intro i
    by_cases h : i < 26
    · rw [List.getD_eq_getElem _ _ (by simpa only [pull, List.length_ofFn] using h : i < (pull x).length)]
      simp only [pull, List.getElem_ofFn, rename, h, dite_true]
    · rw [high (Nat.le_of_not_lt h), List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp [pull]; omega)]
  have plen (x : List Bool) (hx : x ∈ P) : x.length = 26 := by
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hx
    change ((List.ofFn fun t : Fin 13 => decide (t = e.1)) ++
      List.ofFn fun t : Fin 13 => decide (t = e.2)).length = 26
    simp only [List.length_append, List.length_ofFn]
  have nlen (x : List Bool) (hx : x ∈ N) : x.length = 26 := by
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hx
    simp
  have pos' : ∀ x ∈ P, C.eval x = true := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact pos _ _ (Finset.mem_filter.mp he).2
  have neg' : ∀ x ∈ N, C.eval x = false := by
    intro x hx
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hx
    exact neg _ hQ
  have sz : 64 ≤ D.size := by
    apply bound D model first distinct (samePairs ▸ nested)
    · intro x hx
      exact (run _ (plen _ hx) _).trans (pos' _ (hP ▸ Finset.mem_image_of_mem pull hx))
    · intro x hx
      exact (run _ (nlen _ hx) _).trans (neg' _ (hN ▸ Finset.mem_image_of_mem pull hx))
    · intro j hj hop w hw
      have hj' : j < C.size := by simpa [sizeDef,D] using hj
      rw [dg _ hj'] at hop hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      obtain ⟨Q,hQ,neq⟩ := essential j hj' hop i hi
      let z := (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)
      have hz : z ∈ N := Finset.mem_image.mpr ⟨Q,hQ,rfl⟩
      rw [← hN] at hz
      obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp hz
      refine ⟨x,hx,?_⟩
      have eqj := run x (nlen _ hx) (26+j)
      rw [high (by omega)] at eqj
      rw [eqj, run _ (nlen _ hx) _, show pull x = z from ex]
      exact neq
  simpa [sizeDef,D] using sz

