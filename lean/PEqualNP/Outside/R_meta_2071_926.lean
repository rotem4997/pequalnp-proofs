import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2071_926
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
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true) := by
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


  have flagTransitive (p l : Fin 13)
      (h : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
      ∃ (α β : Equiv.Perm (Fin 13)),
        α p = 0 ∧ β l = 0 ∧
        ∀ u t, (α u - β t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ↔
          u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let P₁ : Fin 13 → Fin 13 := ![1, 0, 4, 3, 5, 6, 11, 8, 10, 9, 7, 12, 2]
    let L₁ : Fin 13 → Fin 13 := ![0, 4, 3, 2, 5, 10, 8, 7, 9, 6, 11, 12, 1]
    let P₃ : Fin 13 → Fin 13 := ![1, 3, 2, 0, 11, 12, 6, 7, 4, 9, 5, 8, 10]
    let L₃ : Fin 13 → Fin 13 := ![0, 2, 12, 10, 11, 3, 6, 4, 8, 9, 5, 7, 1]
    let P₉ : Fin 13 → Fin 13 := ![1, 3, 2, 9, 5, 6, 12, 8, 4, 0, 11, 7, 10]
    let L₉ : Fin 13 → Fin 13 := ![0, 2, 6, 9, 5, 3, 12, 8, 4, 10, 11, 7, 1]
    let e (f : Fin 13 → Fin 13) (hf : ∀ i j, f i = f j → i = j) : Equiv.Perm (Fin 13) :=
      Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
    have h₁ : ∀ i j, P₁ i - L₁ j ∈ offsets ↔ i - j ∈ offsets := by decide
    have h₃ : ∀ i j, P₃ i - L₃ j ∈ offsets ↔ i - j ∈ offsets := by decide
    have h₉ : ∀ i j, P₉ i - L₉ j ∈ offsets ↔ i - j ∈ offsets := by decide
    have normalize : ∀ d ∈ offsets, ∃ (α β : Equiv.Perm (Fin 13)),
        α d = 0 ∧ β 0 = 0 ∧ ∀ u t, α u - β t ∈ offsets ↔ u - t ∈ offsets := by
      intro d hd
      change d ∈ ({0, 1, 3, 9} : Finset (Fin 13)) at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨Equiv.refl _, Equiv.refl _, rfl, rfl, fun _ _ => Iff.rfl⟩
      · exact ⟨e P₁ (by decide), e L₁ (by decide), rfl, rfl, h₁⟩
      · exact ⟨e P₃ (by decide), e L₃ (by decide), rfl, rfl, h₃⟩
      · exact ⟨e P₉ (by decide), e L₉ (by decide), rfl, rfl, h₉⟩
    obtain ⟨α, β, hp, hl, hpres⟩ := normalize (p-l) h
    refine ⟨(Equiv.subRight l).trans α, (Equiv.subRight l).trans β, hp, ?_, ?_⟩
    · change β (l - l) = 0
      simpa only [sub_self] using hl
    · intro u t
      change α (u-l) - β (t-l) ∈ offsets ↔ u - t ∈ offsets
      rw [hpres]
      rw [show (u-l) - (t-l) = u - t by abel]

  let Offsets : Finset (Fin 13) := {0, 1, 3, 9}
  let Computes (C : Circuit) : Prop :=
    ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 13, u - t ∈ Offsets ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true
  have normalizeCircuit (C : Circuit) (p l : Fin 13) (R S : ℕ → Bool)
      (hmax : C.size ≤ 64) (hC : Valid 26 C) (hI : Computes C)
      (hpl : p - l ∈ Offsets)
      (hR : LinearTrace 26 C p.val (13 + l.val) R)
      (hS : LinearTrace 26 C (13 + l.val) p.val S) :
      ∃ D : Circuit, 63 ≤ D.size ∧ D.size ≤ 64 ∧ Valid 26 D ∧ Computes D ∧
        (∃ R', LinearTrace 26 D 0 13 R' ∧ R' D.output = R C.output) ∧
        (∃ S', LinearTrace 26 D 13 0 S' ∧ S' D.output = S C.output) := by
    obtain ⟨α, β, hα, hβ, hab⟩ := flagTransitive p l hpl
    let join : Fin 13 ⊕ Fin 13 ≃ Fin 26 := finSumFinEquiv
    let e : Equiv.Perm (Fin 26) := join.symm.trans ((Equiv.sumCongr α β).trans join)
    have heP (u : Fin 13) : e (Fin.castAdd 13 u) = Fin.castAdd 13 (α u) := by
      have hu : join (.inl u) = Fin.castAdd 13 u := finSumFinEquiv_apply_left u
      have hv : join (.inl (α u)) = Fin.castAdd 13 (α u) := finSumFinEquiv_apply_left (α u)
      rw [← hu, ← hv]
      simp [e]
    have heL (t : Fin 13) : e (Fin.natAdd 13 t) = Fin.natAdd 13 (β t) := by
      have ht : join (.inr t) = Fin.natAdd 13 t := finSumFinEquiv_apply_right t
      have hv : join (.inr (β t)) = Fin.natAdd 13 (β t) := finSumFinEquiv_apply_right (β t)
      rw [← ht, ← hv]
      simp [e]

    let relabel (f : Equiv.Perm (Fin 26)) (i : ℕ) : ℕ :=
      if hi : i < 26 then (f ⟨i, hi⟩).val else i
    let q := relabel e
    let r := relabel e.symm
    have label_input (f : Equiv.Perm (Fin 26)) (i : Fin 26) : relabel f i.val = (f i).val :=
      dite_eq_left i.isLt
    have label_gate (f : Equiv.Perm (Fin 26)) {i : ℕ} (hi : 26 ≤ i) : relabel f i = i :=
      dite_eq_right (Nat.not_lt.mpr hi)
    have label_lt (f : Equiv.Perm (Fin 26)) (i b : ℕ) (hb : 26 ≤ b) :
        relabel f i < b ↔ i < b := by
      by_cases hi : i < 26
      · rw [label_input f (⟨i,hi⟩ : Fin 26)]
        exact iff_of_true (lt_of_lt_of_le (f ⟨i,hi⟩).isLt hb) (lt_of_lt_of_le hi hb)
      · rw [label_gate f (Nat.le_of_not_gt hi)]
    have label_inverse (f : Equiv.Perm (Fin 26)) (i : ℕ) :
        relabel f.symm (relabel f i) = i := by
      by_cases hi : i < 26
      · rw [label_input f (⟨i,hi⟩ : Fin 26), label_input, f.symm_apply_apply]
      · have hi' := Nat.le_of_not_gt hi
        rw [label_gate f hi', label_gate f.symm hi']
    have hrq (i : ℕ) : r (q i) = i := label_inverse e i
    have hqr (i : ℕ) : q (r i) = i := label_inverse e.symm i
    have hqinj : Function.Injective q := (show Function.LeftInverse r q from hrq).injective

    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map q⟩
    let oldG := C.gates.map mapGate
    let pad : Gate := ⟨.and, [0,13]⟩
    let D : Circuit :=
      ⟨oldG ++ List.replicate (63 - C.gates.length) pad, q C.output⟩
    let n := 26 + C.gates.length
    have dlen : D.gates.length = C.gates.length + (63 - C.gates.length) := by
      simp [D, oldG]
    have read_mapped (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
        (hj : j < C.gates.length) : D.gates[j]? = some (mapGate g) := by
      change (oldG ++ _)[j]? = _
      rw [List.getElem?_append_left (by simpa only [oldG, List.length_map] using hj)]
      simp only [oldG, List.getElem?_map, hg, Option.map_some]
    have read_pad (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g)
        (hj : C.gates.length ≤ j) : g = pad := by
      change (oldG ++ _)[j]? = _ at hg
      rw [List.getElem?_append_right (by simpa only [oldG, List.length_map] using hj),
        List.getElem?_replicate] at hg
      split at hg
      · exact (Option.some.inj hg).symm
      · cases hg
    have hD : Valid 26 D := by
      intro j g hg
      by_cases hj : j < C.gates.length
      · let g₀ := C.gates[j]
        have hg₀ : C.gates[j]? = some g₀ := List.getElem?_eq_getElem hj
        have heq := Option.some.inj (hg.symm.trans (read_mapped j g₀ hg₀ hj))
        subst g
        obtain ⟨hop, a, b, hin, hne, ha, hb⟩ := hC j g₀ hg₀
        refine ⟨hop, q a, q b, ?_, fun h => hne (hqinj h), ?_, ?_⟩
        · simp only [mapGate, hin, List.map_cons, List.map_nil]
        · exact (label_lt e a _ (by omega)).mpr ha
        · exact (label_lt e b _ (by omega)).mpr hb
      · have heq := read_pad j g hg (by omega)
        subst g
        exact ⟨Or.inl rfl, 0, 13, rfl, by decide, by omega, by omega⟩

    have eval_at (x : Fin 26 → Bool) (i : ℕ) (hi : i < n) :
        val D x (q i) = val C (fun j => x (e j)) i := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        by_cases hi₀ : i < 26
        · have hqi : q i < 26 := (label_lt e i 26 (le_refl _)).mpr hi₀
          rw [val_input D x _ hqi, val_input C _ _ hi₀]
          congr 1
          exact Fin.ext (label_input e (⟨i,hi₀⟩ : Fin 26))
        · let j := i - 26
          have heq : i = 26 + j := by dsimp [j]; omega
          have hj : j < C.gates.length := by dsimp [n] at hi; omega
          let g := C.gates[j]
          have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hC j g hg
          have ha' := (label_lt e a (26+j) (by omega)).mpr ha
          have hb' := (label_lt e b (26+j) (by omega)).mpr hb
          have hm : (mapGate g).inputs = [q a,q b] := by
            simp only [mapGate, hin, List.map_cons, List.map_nil]
          have h₀ := val_gate C (fun k => x (e k)) j g hg a b hin ha hb
          have h₁ := val_gate D x j (mapGate g) (read_mapped j g hg hj) (q a) (q b) hm ha' hb'
          clear hm
          rw [heq, show q (26 + j) = 26 + j from label_gate e (by omega)]
          have ea := ih a (by omega) (by omega)
          have eb := ih b (by omega) (by omega)
          rcases hop with h | h
          · rw [h₁.1 h, h₀.1 h, ea, eb]
          · rw [h₁.2 h, h₀.2 h, ea, eb]

    have hout : C.output < n := by
      have hrow : val C (fun _ : Fin 26 => true) C.output = true :=
        (hI _).mpr ⟨0, 0, by decide, rfl, rfl⟩
      by_contra! h
      exact Bool.noConfusion (hrow.symm.trans (val_outside C _ C.output h))
    have hDI : Computes D := by
      intro x
      change val D x (q C.output) = true ↔ _
      rw [eval_at x _ hout]
      change C.eval (List.ofFn fun j => x (e j)) = true ↔ _
      rw [hI (fun j => x (e j))]
      constructor
      · rintro ⟨u,t,hut,hu,ht⟩
        rw [heP] at hu
        rw [heL] at ht
        exact ⟨α u, β t, (hab u t).mpr hut, hu, ht⟩
      · rintro ⟨u,t,hut,hu,ht⟩
        refine ⟨α.symm u, β.symm t, (hab _ _).mp ?_, ?_, ?_⟩
        · simpa only [Equiv.apply_symm_apply] using hut
        · simpa only [heP, Equiv.apply_symm_apply] using hu
        · simpa only [heL, Equiv.apply_symm_apply] using ht

    have transportTrace (other repeated : Fin 26) (T : ℕ → Bool)
        (hT : LinearTrace 26 C other.val repeated.val T) :
        ∃ T', LinearTrace 26 D (e other).val (e repeated).val T' ∧
          T' D.output = T C.output := by
      let V := val D (oneInput 26 (e other).val)
      let T' (i : ℕ) :=
        if i < n then T (r i) else (V 0 && T (r 13)) || (T (r 0) && V 13)
      have at_old (i : ℕ) (hi : i < n) : T' (q i) = T i := by
        have hqi := (label_lt e i n (by dsimp [n]; omega)).mpr hi
        change (if q i < n then T (r (q i)) else _) = T i
        rw [ite_eq_left hqi, hrq]
      have at_input (i : ℕ) (hi : i < 26) : T' i = T (r i) := by
        have hin : i < n := by dsimp [n]; omega
        simp only [T', ite_eq_left hin]
      have pull : (fun i : Fin 26 => oneInput 26 (e other).val (e i)) = oneInput 26 other.val := by
        funext i
        simp only [oneInput, Fin.val_inj, Equiv.apply_eq_iff_eq]
      have val_at_old (i : ℕ) (hi : i < n) :
          V (q i) = val C (oneInput 26 other.val) i := by
        change val D (oneInput 26 (e other).val) (q i) = _
        rw [eval_at _ _ hi, pull]
      refine ⟨T', ⟨?_, ?_⟩, at_old _ hout⟩
      · intro i hi
        have hri := (label_lt e.symm i 26 (le_refl _)).mpr hi
        rw [at_input i hi, hT.1 _ hri]
        have hp : r i = repeated.val ↔ i = (e repeated).val := by
          have hlabel : q repeated.val = (e repeated).val := label_input e repeated
          constructor
          · intro h
            exact (hqr i).symm.trans ((congrArg q h).trans hlabel)
          · intro h
            rw [h.trans hlabel.symm, hrq]
        change decide (r i = repeated.val) = decide (i = (e repeated).val)
        simp only [hp]
      · intro j g a b hg hab'
        by_cases hj : j < C.gates.length
        · let g₀ := C.gates[j]
          have hg₀ : C.gates[j]? = some g₀ := List.getElem?_eq_getElem hj
          have heq := Option.some.inj (hg.symm.trans (read_mapped j g₀ hg₀ hj))
          subst g
          obtain ⟨_, a₀, b₀, h₀, _, ha₀, hb₀⟩ := hC j g₀ hg₀
          have hi : q a₀ = a ∧ q b₀ = b := by
            simpa only [mapGate, h₀, List.map_cons, List.map_nil, List.cons.injEq, and_true] using hab'
          obtain ⟨rfl,rfl⟩ := hi
          have hjn : 26+j < n := by dsimp [n]; omega
          have han : a₀ < n := by omega
          have hbn : b₀ < n := by omega
          have htj : T' (26+j) = T (26+j) := by
            simpa only [q, label_gate e (show 26 ≤ 26+j by omega)] using at_old (26+j) hjn
          change ((g₀.op = .and → T' (26+j) = (V (q a₀) && T' (q b₀) ||
            T' (q a₀) && V (q b₀))) ∧
            (g₀.op = .or → T' (26+j) = (T' (q a₀) || T' (q b₀))))
          rw [htj, at_old _ han, at_old _ hbn, val_at_old _ han, val_at_old _ hbn]
          exact hT.2 j g₀ a₀ b₀ hg₀ h₀
        · have heq := read_pad j g hg (by omega)
          subst g
          have hi : (0 : ℕ) = a ∧ (13 : ℕ) = b := by
            simpa only [pad, List.cons.injEq, and_true] using hab'
          obtain ⟨rfl,rfl⟩ := hi
          refine ⟨fun _ => ?_, by simp [pad]⟩
          have hjn : ¬(26+j) < n := by dsimp [n]; omega
          change T' (26+j) = (V 0 && T' 13 || T' 0 && V 13)
          rw [at_input 0 (by decide), at_input 13 (by decide)]
          simp only [T', ite_eq_right hjn]

    have pointNorm : e (Fin.castAdd 13 p) = Fin.castAdd 13 0 := by rw [heP, hα]
    have lineNorm : e (Fin.natAdd 13 l) = Fin.natAdd 13 (0 : Fin 13) := by rw [heL, hβ]
    have r' := transportTrace (Fin.castAdd 13 p) (Fin.natAdd 13 l) R hR
    have s' := transportTrace (Fin.natAdd 13 l) (Fin.castAdd 13 p) S hS
    rw [pointNorm, lineNorm] at r' s'
    change C.gates.length ≤ 64 at hmax
    refine ⟨D, ?_, ?_, hD, hDI, r', s'⟩
    · change 63 ≤ D.gates.length
      omega
    · change D.gates.length ≤ 64
      omega

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


  intro _ _ _ C₀ p l R₀ S₀ _ hmax₀ hvalid₀ hinc₀ _ _ hpl hR₀ hS₀
  by_cases hRt : R₀ C₀.output = true
  · exact Or.inl hRt
  by_cases hSt : S₀ C₀.output = true
  · exact Or.inr hSt
  exfalso
  have hRf₀ : R₀ C₀.output = false := by cases h : R₀ C₀.output <;> simp [h] at hRt ⊢
  have hSf₀ : S₀ C₀.output = false := by cases h : S₀ C₀.output <;> simp [h] at hSt ⊢
  obtain ⟨C, hmin, hmax, hvalid, hCI, ⟨R, hR, hRout⟩, S, hS, hSout⟩ :=
    normalizeCircuit C₀ p l R₀ S₀ hmax₀ hvalid₀ hinc₀ hpl hR₀ hS₀
  have hRf := hRout.trans hRf₀
  have hSf := hSout.trans hSf₀
  have hI : Incidence C := by
    simpa only [Computes, Offsets, Incidence, Finset.mem_insert, Finset.mem_singleton,
      sub_eq_iff_eq_add, zero_add, add_zero, add_comm] using hCI
  obtain ⟨hB,hP,hL⟩ := incidence_rows C hI
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
