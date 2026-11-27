import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4877_741
    (paired :
      let miss := fun (x : Fin 13 → Bool) (l : Fin 13) =>
        !(x l || x (l+1) || x (l+3) || x (l+9))
      let pack := fun (p l : Fin 13 → Bool) => List.ofFn (Fin.addCases p l)
      let unit := fun (p i : Fin 13) => decide (i = p)
      ∃ (C : Circuit) (u v : ℕ),
        let w := fun x i => (C.wires x).getD i false
        let both := fun x => w x u && w x v
        C.size ≤ 63 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        u < 26+C.size ∧ v < 26+C.size ∧ u ≠ v ∧
        (∀ p l, miss (unit p) l = false → both (pack (unit p) (unit l)) = true) ∧
        (∀ x, (List.ofFn x).count true ≤ 3 →
          both (pack x (miss x)) = false ∧
          both (pack (fun p => !(x p || x (p-1) || x (p-3) || x (p-9))) x) = false) ∧
        ∀ b : Bool,
          let x := List.ofFn (fun i : Fin 26 => decide (i.val = if b = true then 13 else 0))
          (w x u || w x v) = false)
    (terminal :
      ∀ (n : ℕ) (C : Circuit) (j u v s : ℕ) (x : Fin n → Bool),
        IsAO2 n C → C.output = n+j → j+1 = C.size →
        C.gates[j]? = some ⟨.and,[u,v]⟩ →
        let w : ℕ → Bool := fun k => (C.wires (List.ofFn x)).getD k false
        w u = false → w v = false →
        ∃ d : ℕ → Bool,
          (∀ i < n, d i = decide (i=s)) ∧
          (∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a,b] →
            (g.op = .and → d (n+k) = (w a && d b || d a && w b)) ∧
            (g.op = .or → d (n+k) = (d a || d b))) ∧
          d C.output = false) :
    have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧             ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       x4.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 x4.output = Bool.false := by
  intro miss pack unit
  obtain ⟨C,u,v,budget,ao,nd,lu,lv,uv,pos,neg,zeros⟩ := paired
  let A : Gate := ⟨.and,[u,v]⟩
  let D : Circuit := ⟨C.gates ++ [A],26+C.size⟩
  have lenC : C.gates.length = C.size := rfl
  have lenD : D.size = C.size+1 := by
    change (C.gates ++ [A]).length = _
    simp [lenC]
  have budgetD : D.size ≤ 64 := by omega
  have getNew : D.gates[C.size]? = some A := by
    change (C.gates ++ [A])[C.gates.length]? = _
    rw [List.getElem?_append_right (by omega)]
    simp
  have newAt : gateAt D C.size = A := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, getNew]
    rfl
  have membership (g : Gate) (hg : g ∈ D.gates) : g ∈ C.gates ∨ g = A := by
    simpa [D] using hg
  have aoD : IsAO2 26 D := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      rcases membership g hg with old | rfl
      · exact ao.1 g old
      · exact Or.inl rfl
    · intro j hj i hi
      change j < D.size at hj
      by_cases old : j < C.size
      · have same : gateAt D j = gateAt C j := List.getD_append _ _ _ _ old
        rw [same] at hi
        exact ao.2.1 j old i hi
      · have index : j = C.size := by omega
        subst j
        rw [newAt] at hi
        have which : i = u ∨ i = v := by simpa [A] using hi
        rcases which with rfl | rfl
        · exact lu
        · exact lv
    · intro g hg
      rcases membership g hg with old | rfl
      · exact ao.2.2 g old
      · rfl
  have ndD (g : Gate) (hg : g ∈ D.gates) : g.inputs.Nodup := by
    rcases membership g hg with old | rfl
    · exact nd g old
    · simp [A,uv]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lengthFold (gs : List Gate) (x : List Bool) :
      (gs.foldl step x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have wireLength (x : List Bool) (hx : x.length = 26) : (C.wires x).length = 26+C.size := by
    change (C.gates.foldl step x).length = _
    rw [lengthFold,hx,lenC]
  have wires (x : List Bool) :
      D.wires x = C.wires x ++ [(C.wires x).getD u false && (C.wires x).getD v false] := by
    change (C.gates ++ [A]).foldl step x = _
    rw [List.foldl_append]
    change step (C.wires x) A = _
    have evalAnd (p q : Bool) : GateOp.and.eval [p,q] = (p && q) := by
      cases p <;> cases q <;> rfl
    change (C.wires x) ++ [GateOp.and.eval [(C.wires x).getD u false, (C.wires x).getD v false]] = _
    rw [evalAnd]
  have ordinary (x : List Bool) (hx : x.length = 26) :
      D.eval x = ((C.wires x).getD u false && (C.wires x).getD v false) := by
    change (D.wires x).getD (26+C.size) false = _
    rw [wires, ← wireLength x hx, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
    rfl
  refine ⟨D,budgetD,aoD,ndD,?_,?_,?_⟩
  · intro p l inc
    rw [ordinary _ (List.length_ofFn ..)]
    exact pos p l inc
  · intro x hx
    rw [ordinary _ (List.length_ofFn ..), ordinary _ (List.length_ofFn ..)]
    exact neg x hx
  · intro b
    let x := fun i : Fin 26 => decide (i.val = if b = true then 13 else 0)
    have off := Bool.or_eq_false_iff.mp (zeros b)
    have offU : (D.wires (List.ofFn x)).getD u false = false := by
      rw [wires,List.getD_append _ _ _ _ (by rw [wireLength _ (List.length_ofFn ..)]; exact lu)]
      exact off.1
    have offV : (D.wires (List.ofFn x)).getD v false = false := by
      rw [wires,List.getD_append _ _ _ _ (by rw [wireLength _ (List.length_ofFn ..)]; exact lv)]
      exact off.2
    exact terminal 26 D C.size u v (if b = true then 0 else 13) x
      aoD rfl lenD.symm getNew offU offV
