import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2602_926
    (shared : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
    let V := fun A : Finset ℕ => PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW 26 A)
    let T := fun i k => ∃ (j : ℕ) (g : Gate) (a b : ℕ),
      C.gates[j]? = some g ∧ k = 26 + j ∧ g.inputs = [a,b] ∧
      ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if V {0,13} a then a else b)) ∧
      V {0,13} i = true ∧ V {0,13} k = true
    let K := fun z j => Relation.ReflTransGen T (26+j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
      ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        V {0,13} a = true ∧ V {z} a = false
    (∃ j, K 0 j ∧ K 13 j) → False)
    (mixed : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
    let V := fun A : Finset ℕ => PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW 26 A)
    let T := fun i k => ∃ (j : ℕ) (g : Gate) (a b : ℕ),
      C.gates[j]? = some g ∧ k = 26 + j ∧ g.inputs = [a,b] ∧
      ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if V {0,13} a then a else b)) ∧
      V {0,13} i = true ∧ V {0,13} k = true
    let K := fun z j => Relation.ReflTransGen T (26+j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
      ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        V {0,13} a = true ∧ V {z} a = false
    (∃ j k, j ≠ k ∧ K 0 j ∧ K 13 k ∧ V {13} (26+j) = false ∧ V {0} (26+k) = false) → False)
    (one : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
    let V := fun A : Finset ℕ => PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW 26 A)
    let T := fun i k => ∃ (j : ℕ) (g : Gate) (a b : ℕ),
      C.gates[j]? = some g ∧ k = 26 + j ∧ g.inputs = [a,b] ∧
      ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if V {0,13} a then a else b)) ∧
      V {0,13} i = true ∧ V {0,13} k = true
    let K := fun z j => Relation.ReflTransGen T (26+j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
      ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        V {0,13} a = true ∧ V {z} a = false
    (∃ j k, j ≠ k ∧ K 0 j ∧ K 13 k ∧ V {13} (26+j) ≠ V {0} (26+k)) → False)
    (singletons : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
    PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
    let V := fun A : Finset ℕ => PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW 26 A)
    let T := fun i k => ∃ (j : ℕ) (g : Gate) (a b : ℕ),
      C.gates[j]? = some g ∧ k = 26 + j ∧ g.inputs = [a,b] ∧
      ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if V {0,13} a then a else b)) ∧
      V {0,13} i = true ∧ V {0,13} k = true
    let K := fun z j => Relation.ReflTransGen T (26+j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
      ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        V {0,13} a = true ∧ V {z} a = false
    (∃ j k, j ≠ k ∧ K 0 j ∧ K 13 k ∧ V {13} (26+j) = true ∧ V {0} (26+k) = true) → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  let gateStep {α : Type} (op : GateOp → List α → α) (dflt : α)
      (ws : List α) (g : Gate) : List α :=
    ws ++ [op g.op (g.inputs.map fun i => ws.getD i dflt)]

  have gateStep_length {α : Type} (op : GateOp → List α → α) (dflt : α) (ws : List α) (g : Gate) :
      (gateStep op dflt ws g).length = ws.length + 1 := by
    simp [gateStep]

  have prefix_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl (gateStep op dflt) ws).getD i dflt = ws.getD i dflt := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by rw [gateStep_length]; omega)]
      simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have wireCount {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) :
      (gs.foldl (gateStep op dflt) ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, gateStep_length, List.length_cons]
      omega

  have indexed_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
      (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
      (gs.foldl (gateStep op dflt) ws).getD (ws.length + j) dflt =
        op g.op (g.inputs.map fun i => (gs.foldl (gateStep op dflt) ws).getD i dflt) := by
    induction gs generalizing ws j with
    | nil => simp at hj
    | cons g0 gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst g0
        rw [Nat.add_zero, List.foldl_cons, prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        have hstep : (gateStep op dflt ws g).getD ws.length dflt =
            op g.op (g.inputs.map fun i => ws.getD i dflt) := by
          simp only [gateStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlt : i < ws.length := by simpa using hback i hi
        rw [prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hidx : ws.length + (j + 1) = (gateStep op dflt ws g0).length + j := by
          rw [gateStep_length]
          omega
        rw [hidx]
        exact ih (gateStep op dflt ws g0) j hj (by simpa only [hidx] using hback)

  let Valid (n : ℕ) (C : Circuit) : Prop :=
    ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

  let val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD i false

  have val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      val C x i = x ⟨i,hi⟩ := by
    have hi' : i < (List.ofFn x).length := by simpa using hi
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = _
    rw [prefix_value _ _ _ _ _ hi', List.getD_eq_getElem _ _ hi', List.getElem_ofFn]

  have val_outside {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
      (hi : n + C.gates.length ≤ i) : val C x i = false := by
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simpa only [wireCount, List.length_ofFn] using hi

  have val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hj : C.gates[j]? = some g) (a b : ℕ) (hg : g.inputs = [a,b])
      (ha : a < n + j) (hb : b < n + j) :
      (g.op = .and → val C x (n + j) = (val C x a && val C x b)) ∧
      (g.op = .or → val C x (n + j) = (val C x a || val C x b)) := by
    have hback : ∀ i ∈ g.inputs, i < (List.ofFn x).length + j := by
      simp only [hg, List.length_ofFn, List.mem_cons, List.not_mem_nil, or_false]
      rintro i (rfl | rfl) <;> assumption
    have hv := indexed_value GateOp.eval false C.gates (List.ofFn x) j g hj hback
    simp only [List.length_ofFn, hg, List.map_cons, List.map_nil] at hv
    constructor
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a && (val C x b && true)) at hv
      simpa only [Bool.and_true] using hv
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a || (val C x b || false)) at hv
      simpa only [Bool.or_false] using hv

  let oneInput (n z : ℕ) : Fin n → Bool :=
    fun i => decide (i.val = z)

  let twoInputs (n p l : ℕ) : Fin n → Bool :=
    fun i => decide (i.val = p ∨ i.val = l)

  let LinearTrace (n : ℕ) (C : Circuit) (other repeated : ℕ) (R : ℕ → Bool) : Prop :=
    (∀ i < n, R i = decide (i = repeated)) ∧
    ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = .and →
        R (n + j) =
          ((val C (oneInput n other) a && R b) || (R a && val C (oneInput n other) b))) ∧
      (g.op = .or → R (n + j) = (R a || R b))

  let linearOp (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
    GateOp.rec (motive := fun _ => Bool × Bool)
      (ins.foldl (fun acc p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
      (ins.any (·.1), ins.any (·.2)) (false,false) (fun _ => (false,false))
      (false,false) op

  have lineSingle_eq_trace (n : ℕ) (C : Circuit) (hC : Valid n C) (other repeated : ℕ)
      (hne : other ≠ repeated) (R : ℕ → Bool) (hR : LinearTrace n C other repeated R)
      (hout : C.output < n + C.gates.length) :
      PEqualNP.ReadK.lineSingle C n (fun i => decide (i = repeated)) other repeated = R C.output := by
    let x := (List.range n).map fun i => i == other || i == repeated
    let start : List (Bool × Bool) :=
      (x.zipIdx).map fun bi => if decide (bi.2 = repeated) then (false,bi.1) else (bi.1,false)
    let W := C.gates.foldl (gateStep linearOp (false,false)) start
    let S := val C (oneInput n other)
    have hlen : start.length = n := by simp [start, x]
    have hparts : ∀ i < n + C.gates.length,
        (W.getD i (false,false)).1 = S i ∧ (W.getD i (false,false)).2 = R i := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro hi
        by_cases hin : i < n
        · have hi' : i < start.length := by rwa [hlen]
          have hx : i < x.length := by simpa [x] using hin
          have hx' : x[i] = (i == other || i == repeated) := by simp [x]
          have h0 : (W.getD i (false,false)) =
              (if decide (i = repeated) then (false,x[i]) else (x[i],false)) := by
            rw [show W.getD i (false,false) = start.getD i (false,false) from
              prefix_value linearOp _ C.gates start i hi', List.getD_eq_getElem _ _ hi']
            simp [start, List.getElem_zipIdx]
          have hS : S i = decide (i = other) := val_input C (oneInput n other) i hin
          rw [h0, hS, hR.1 i hin, hx']
          by_cases hr : i = repeated
          · simp [hr,Ne.symm hne]
          · by_cases ho : i = other <;> simp [hr,ho,hne]
        · let j := i - n
          have heq : i = n + j := by dsimp [j]; omega
          have hj : j < C.gates.length := by omega
          let g := C.gates[j]
          have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hC j g hg
          have ha' := ih a (by omega) (by omega)
          have hb' := ih b (by omega) (by omega)
          have hback : ∀ k ∈ g.inputs, k < start.length + j := by
            simp only [hlen, hinp, List.mem_cons, List.not_mem_nil, or_false]
            rintro k (rfl | rfl) <;> assumption
          have hW := indexed_value linearOp (false,false) C.gates start j g hg hback
          change W.getD (start.length + j) (false,false) =
            linearOp g.op (g.inputs.map fun k => W.getD k (false,false)) at hW
          rw [hlen, ← heq, hinp, List.map_cons, List.map_cons, List.map_nil] at hW
          have ha'' : W.getD a (false,false) = (S a, R a) := Prod.ext ha'.1 ha'.2
          have hb'' : W.getD b (false,false) = (S b, R b) := Prod.ext hb'.1 hb'.2
          rw [ha'', hb''] at hW
          have hv := val_gate C (oneInput n other) j g hg a b hinp ha hb
          have hr := hR.2 j g a b hg hinp
          rw [← heq] at hv hr
          rcases hop with hop | hop
          · rw [hop] at hW
            rw [hW]
            exact ⟨by simpa [linearOp, S] using (hv.1 hop).symm, by
              simpa [linearOp, S] using (hr.1 hop).symm⟩
          · rw [hop] at hW
            rw [hW]
            exact ⟨by simpa [linearOp, S] using (hv.2 hop).symm, by
              simpa [linearOp, S] using (hr.2 hop).symm⟩
    have hfold : PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x = W := by
      change PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x =
        C.gates.foldl (gateStep linearOp (false,false)) start
      unfold PEqualNP.ReadK.linearParts gateStep start
      congr 1
      funext ws g
      cases g.op <;> rfl
    unfold PEqualNP.ReadK.lineSingle
    change ((PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x).getD
      C.output (false,false)).2 = R C.output
    rw [hfold]
    exact (hparts C.output hout).2

  let ActiveStep (n : ℕ) (C : Circuit) (B : ℕ → Bool) (i k : ℕ) : Prop :=
    ∃ j g a b, C.gates[j]? = some g ∧ k = n + j ∧ g.inputs = [a,b] ∧
      ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if B a then a else b)) ∧
      B i = true ∧ B k = true

  let Collides (_n : ℕ) (C : Circuit) (B S : ℕ → Bool) (j : ℕ) : Prop :=
    ∃ g a b, C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a,b] ∧
      B a = true ∧ B b = true ∧ S a = false ∧ S b = false

  have collision (n : ℕ) (C : Circuit) (hC : Valid n C) (other repeated : ℕ)
      (R : ℕ → Bool) (hR : LinearTrace n C other repeated R) :
      let B := val C (twoInputs n other repeated)
      let S := val C (oneInput n other)
      ∀ k, B k = true → S k = false → R k = false →
        ∃ j, Collides n C B S j ∧ Relation.ReflTransGen (ActiveStep n C B) (n + j) k := by
    dsimp only
    let B := val C (twoInputs n other repeated)
    let S := val C (oneInput n other)
    change ∀ k, B k = true → S k = false → R k = false →
      ∃ j, Collides n C B S j ∧ Relation.ReflTransGen (ActiveStep n C B) (n + j) k
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hBk hSk hRk
      by_cases hin : k < n
      · have h0 := val_input C (twoInputs n other repeated) k hin
        have h1 := val_input C (oneInput n other) k hin
        change B k = _ at h0
        change S k = _ at h1
        dsimp only [twoInputs] at h0
        rw [hBk, eq_comm, decide_eq_true_eq] at h0
        dsimp only [oneInput] at h1
        rw [hSk, eq_comm, decide_eq_false_iff_not] at h1
        rcases h0 with h0 | h0
        · exact (h1 h0).elim
        · change k = repeated at h0
          have hinput := hR.1 k hin
          rw [hRk, h0] at hinput
          simp at hinput
      · have hlt : k < n + C.gates.length := by
          by_contra! h
          have hBfalse := val_outside C (twoInputs n other repeated) k h
          exact Bool.noConfusion (hBk.symm.trans hBfalse)
        let j := k - n
        have hk : k = n + j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        obtain ⟨ho, a, b, hinp, _, ha, hb⟩ := hC j g hg
        have back : ∀ i, i < n + j →
            ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if B a then a else b)) →
            B i = true → S i = false → R i = false →
            ∃ j, Collides n C B S j ∧ Relation.ReflTransGen (ActiveStep n C B) (n + j) k := by
          intro i hi hbranch hBi hSi hRi
          have hi' : i < k := by omega
          obtain ⟨j', hc, hp⟩ := ih i hi' hBi hSi hRi
          exact ⟨j', hc, hp.tail ⟨j, g, a, b, hg, hk, hinp, hbranch, hBi, hBk⟩⟩
        have hvB := val_gate C (twoInputs n other repeated) j g hg a b hinp ha hb
        have hvS := val_gate C (oneInput n other) j g hg a b hinp ha hb
        have hvR := hR.2 j g a b hg hinp
        rcases ho with ho | ho
        · have hB : (B a && B b) = true := (hvB.1 ho).symm.trans (hk ▸ hBk)
          have hS : (S a && S b) = false := (hvS.1 ho).symm.trans (hk ▸ hSk)
          have hR : ((S a && R b) || (R a && S b)) = false :=
            (hvR.1 ho).symm.trans (hk ▸ hRk)
          have hBa : B a = true := (Bool.and_eq_true_iff.mp hB).1
          have hBb : B b = true := (Bool.and_eq_true_iff.mp hB).2
          cases hSa : S a <;> cases hSb : S b
          · exact ⟨j, ⟨g, a, b, hg, ho, hinp, hBa, hBb, hSa, hSb⟩, hk.symm ▸ .refl⟩
          · apply back a ha (Or.inl ⟨ho, Or.inl rfl⟩) hBa hSa
            simpa [hSa, hSb] using hR
          · apply back b hb (Or.inl ⟨ho, Or.inr rfl⟩) hBb hSb
            simpa [hSa, hSb] using hR
          · simp [hSa, hSb] at hS
        · have hB : (B a || B b) = true := (hvB.2 ho).symm.trans (hk ▸ hBk)
          have hS : (S a || S b) = false := (hvS.2 ho).symm.trans (hk ▸ hSk)
          have hR : (R a || R b) = false := (hvR.2 ho).symm.trans (hk ▸ hRk)
          cases hBa : B a
          · have hBb : B b = true := by simpa [hBa] using hB
            exact back b hb (Or.inr ⟨ho, by simp [hBa]⟩) hBb
              (Bool.or_eq_false_iff.mp hS).2 (Bool.or_eq_false_iff.mp hR).2
          · exact back a ha (Or.inr ⟨ho, by simp [hBa]⟩) hBa
              (Bool.or_eq_false_iff.mp hS).1 (Bool.or_eq_false_iff.mp hR).1

  let OnPairTrace (n : ℕ) (C : Circuit) (B : ℕ → Bool) (j : ℕ) : Prop :=
    Relation.ReflTransGen (ActiveStep n C B) (n + j) C.output

  have collides_rejects_singleton (n : ℕ) (C : Circuit) (hC : Valid n C)
      (B : ℕ → Bool) (x : Fin n → Bool) (j : ℕ)
      (h : Collides n C B (val C x) j) : val C x (n + j) = false := by
    obtain ⟨g, a, b, hg, ho, hab, _, _, ha, hb⟩ := h
    obtain ⟨_, c, d, hcd, _, hc, hd⟩ := hC j g hg
    have hi : a = c ∧ b = d := by
      simpa only [List.cons.injEq, and_true] using hab.symm.trans hcd
    obtain ⟨rfl, rfl⟩ := hi
    rw [(val_gate C x j g hg a b hab hc hd).1 ho, ha]
    rfl

  have collides_same (n : ℕ) (C : Circuit) (B P L : ℕ → Bool) (j : ℕ)
      (hp : Collides n C B P j) (hl : Collides n C B L j) :
      ∃ g a b, C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a,b] ∧
        B a = true ∧ B b = true ∧ P a = false ∧ P b = false ∧ L a = false ∧ L b = false := by
    obtain ⟨g, a, b, hg, ho, hab, hBa, hBb, hPa, hPb⟩ := hp
    obtain ⟨g', a', b', hg', _, hab', _, _, hLa, hLb⟩ := hl
    have heq : g = g' := Option.some.inj (hg.symm.trans hg')
    subst g'
    have hi : a = a' ∧ b = b' := by
      simpa only [List.cons.injEq, and_true] using hab.symm.trans hab'
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨g,a,b,hg,ho,hab,hBa,hBb,hPa,hPb,hLa,hLb⟩

  have doubleCollision (n : ℕ) (C : Circuit) (hC : Valid n C) (p l : ℕ)
      (R S : ℕ → Bool) (hR : LinearTrace n C p l R) (hS : LinearTrace n C l p S)
      (hB : val C (twoInputs n p l) C.output = true)
      (hP : val C (oneInput n p) C.output = false)
      (hL : val C (oneInput n l) C.output = false)
      (hR0 : R C.output = false) (hS0 : S C.output = false) :
      let B := val C (twoInputs n p l)
      let P := val C (oneInput n p)
      let L := val C (oneInput n l)
      (∃ j, OnPairTrace n C B j ∧ (∃ g a b, C.gates[j]? = some g ∧ g.op = .and ∧
        g.inputs = [a,b] ∧ B a = true ∧ B b = true ∧
        P a = false ∧ P b = false ∧ L a = false ∧ L b = false)) ∨
      ∃ j k, j ≠ k ∧ OnPairTrace n C B j ∧ OnPairTrace n C B k ∧
        Collides n C B P j ∧ Collides n C B L k ∧
        ((L (n+j) = true ∧ P (n+k) = true) ∨ L (n+j) = false ∨ P (n+k) = false) := by
    dsimp only
    obtain ⟨j, hj, hjpath⟩ := collision n C hC p l R hR C.output hB hP hR0
    have hsym : twoInputs n p l = twoInputs n l p := by
      ext i
      apply Bool.eq_iff_iff.mpr
      simp [twoInputs, or_comm]
    rw [hsym] at hB
    obtain ⟨k, hk, hkpath⟩ := collision n C hC l p S hS C.output hB hL hS0
    rw [← hsym] at hk hkpath
    by_cases heq : j = k
    · subst k
      exact Or.inl ⟨j, hjpath, collides_same n C (val C (twoInputs n p l)) (val C (oneInput n p)) (val C (oneInput n l)) j hj hk⟩
    · refine Or.inr ⟨j, k, heq, hjpath, hkpath, hj, hk, ?_⟩
      cases hL' : val C (oneInput n l) (n+j) <;> cases hP' : val C (oneInput n p) (n+k) <;> simp

  have valid_toTopForm (n : ℕ) (C : Circuit) (hC : Valid n C) :
      PEqualNP.TopForm.IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      exact (hC j _ (List.getElem?_eq_getElem hj)).1
    · intro j hj a ha
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      obtain ⟨_, b, c, hinp, _, hb, hc⟩ := hC j g hg
      have hg' : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
        change C.gates.getD j ⟨GateOp.or, []⟩ = g
        simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
      simp only [hg', hinp, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, a, b, ha, _⟩ := hC j _ (List.getElem?_eq_getElem hj)
      simp [ha]
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, a, b, ha, hne, _⟩ := hC j _ (List.getElem?_eq_getElem hj)
      simp [ha, hne]

  let Incidence (C : Circuit) : Prop :=
    ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true

  have incidence_rows (C : Circuit) (hI : Incidence C) :
      val C (twoInputs 26 0 13) C.output = true ∧
      val C (oneInput 26 0) C.output = false ∧
      val C (oneInput 26 13) C.output = false := by
    refine ⟨(hI _).2 ⟨0,0,Or.inl rfl,by decide,by decide⟩, ?_, ?_⟩
    · cases h : val C (oneInput 26 0) C.output
      · rfl
      · obtain ⟨u,t,_,_,ht⟩ := (hI (oneInput 26 0)).1 h
        simp only [oneInput, decide_eq_true_eq, Fin.val_natAdd] at ht
        omega
    · cases h : val C (oneInput 26 13) C.output
      · rfl
      · obtain ⟨u,t,_,hu,_⟩ := (hI (oneInput 26 13)).1 h
        simp only [oneInput, decide_eq_true_eq, Fin.val_castAdd] at hu
        have hlt := u.isLt
        omega

  have ind_pair :
      PEqualNP.ReadTwo.indW 26 ({0,13} : Finset ℕ) = twoInputs 26 0 13 := by
    funext i
    apply Bool.eq_iff_iff.mpr
    change decide (i.val ∈ ({0,13} : Finset ℕ)) = true ↔
      decide (i.val = 0 ∨ i.val = 13) = true
    simp only [Finset.mem_insert, Finset.mem_singleton]

  have ind_one (z : ℕ) :
      PEqualNP.ReadTwo.indW 26 ({z} : Finset ℕ) = oneInput 26 z := by
    funext i
    apply Bool.eq_iff_iff.mpr
    change decide (i.val ∈ ({z} : Finset ℕ)) = true ↔ decide (i.val = z) = true
    simp only [Finset.mem_singleton]

  have localCollision (n : ℕ) (C : Circuit) (B S : ℕ → Bool) (j : ℕ)
      (hc : Collides n C B S j) :
      PEqualNP.ReadTwo.isAnd C j ∧
        ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          B a = true ∧ S a = false := by
    obtain ⟨g,a,b,hg,hop,hab,hBa,hBb,hSa,hSb⟩ := hc
    have hj : j < C.gates.length := by
      by_contra! h
      simp [List.getElem?_eq_none h] at hg
    have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = g
      simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
    refine ⟨⟨hj,hget ▸ hop⟩, ?_⟩
    intro i hi
    simp only [hget, hab, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hBa,hSa⟩
    · exact ⟨hBb,hSb⟩


  rintro ⟨C, hmin, hmax, hC, hI, ⟨R, hR0, hRg, hRf⟩, S, hS0, hSg, hSf⟩
  have hvalid : Valid 26 C := hC
  have hinc : Incidence C := hI
  have hR : LinearTrace 26 C 0 13 R := ⟨hR0,hRg⟩
  have hS : LinearTrace 26 C 13 0 S := ⟨hS0,hSg⟩
  obtain ⟨hB,hP,hL⟩ := incidence_rows C hinc
  have hout : C.output < 26 + C.gates.length := by
    by_contra! hh
    exact Bool.noConfusion (hB.symm.trans (val_outside C (twoInputs 26 0 13) C.output hh))
  have hLR : PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false :=
    (lineSingle_eq_trace 26 C hvalid 0 13 (by decide) R hR hout).trans hRf
  have hLS : PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false :=
    (lineSingle_eq_trace 26 C hvalid 13 0 (by decide) S hS hout).trans hSf
  obtain ⟨hao,hnd⟩ := valid_toTopForm 26 C hvalid
  let V := fun A : Finset ℕ => PEqualNP.ReadTwo.wval C (PEqualNP.ReadTwo.indW 26 A)
  let T := fun i k => ∃ (j : ℕ) (g : Gate) (a b : ℕ),
    C.gates[j]? = some g ∧ k = 26 + j ∧ g.inputs = [a,b] ∧
    ((g.op = .and ∧ (i = a ∨ i = b)) ∨ (g.op = .or ∧ i = if V {0,13} a then a else b)) ∧
    V {0,13} i = true ∧ V {0,13} k = true
  let K := fun z j => Relation.ReflTransGen T (26+j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
    ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      V {0,13} a = true ∧ V {z} a = false
  have hV : ∀ z j, OnPairTrace 26 C (val C (twoInputs 26 0 13)) j →
      Collides 26 C (val C (twoInputs 26 0 13)) (val C (oneInput 26 z)) j → K z j := by
    intro z j hp hc
    dsimp only [K, T, V]
    simp only [ind_pair, ind_one]
    exact ⟨hp, localCollision 26 C _ _ j hc⟩
  rcases doubleCollision 26 C hvalid 0 13 R S hR hS hB hP hL hRf hSf with h | h
  · obtain ⟨j, hpath, g, a, b, hg, ho, hinp, ha, hb, hpa, hpb, hla, hlb⟩ := h
    exact shared C hmin hmax hao hnd hI hLR hLS
      ⟨j, hV 0 j hpath ⟨g,a,b,hg,ho,hinp,ha,hb,hpa,hpb⟩,
        hV 13 j hpath ⟨g,a,b,hg,ho,hinp,ha,hb,hla,hlb⟩⟩
  · obtain ⟨j,k,hjk,hpj,hpk,hp,hl,_⟩ := h
    have hkp := hV 0 j hpj hp
    have hkl := hV 13 k hpk hl
    cases hj : V {13} (26+j) <;> cases hk : V {0} (26+k)
    · exact mixed C hmin hmax hao hnd hI hLR hLS ⟨j,k,hjk,hkp,hkl,hj,hk⟩
    · exact one C hmin hmax hao hnd hI hLR hLS ⟨j,k,hjk,hkp,hkl,by
        change V {13} (26+j) ≠ V {0} (26+k)
        rw [hj,hk]
        decide⟩
    · exact one C hmin hmax hao hnd hI hLR hLS ⟨j,k,hjk,hkp,hkl,by
        change V {13} (26+j) ≠ V {0} (26+k)
        rw [hj,hk]
        decide⟩
    · exact singletons C hmin hmax hao hnd hI hLR hLS ⟨j,k,hjk,hkp,hkl,hj,hk⟩
